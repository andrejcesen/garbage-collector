//
//  garbagecollector.c
//  GarbageCollector
//
//  Implementation file for mark-sweep garbage collection in C language.
//  Runs on Mac OS X. Tested on Mac OS X 10.9.
//
//  Created by Andrej Česen
//
//

#include <stdio.h>
#include <pthread.h>
#include <setjmp.h>             // longjmp() used when uthash fails at malloc()
#include <malloc/malloc.h>
#include <mach/mach.h>
#include "uthash.h"
#include "utlist.h"
#include "garbagecollector.h"


#define LOGGING


// anything over threshold is in specified region
#ifdef __LP64__
#define SMALL_THRESHOLD     1008
#else
#define SMALL_THRESHOLD     496
#endif
#define LARGE_THRESHOLD     (127 * 1024)                        // (when system has 1 GB RAM or more)

#define SHIFT_TINY_QUANTUM  4
#define SHIFT_SMALL_QUANTUM 9

#define TINY_QUANTUM        (1 << SHIFT_TINY_QUANTUM)           // 4
#define SMALL_QUANTUM       (1 << SHIFT_SMALL_QUANTUM)          // 9
#define VM_PAGESIZE         4096                                // large are allocated directly as VM pages

#define NUM_TINY_BLOCKS     64520
#define NUM_SMALL_BLOCKS    16320

#define TINY_REGION_SIZE    (TINY_QUANTUM * NUM_TINY_BLOCKS)
#define SMALL_REGION_SIZE   (SMALL_QUANTUM * NUM_SMALL_BLOCKS)

#define TINY_BITMAP_SIZE    (NUM_TINY_BLOCKS >> 3)              // size in bytes (divided by 8)
#define SMALL_BITMAP_SIZE   (NUM_SMALL_BLOCKS >> 3)

#define TINY_BLOCK_MASK     0xfffff                             // 20b boundary
#define SMALL_BLOCK_MASK    0x7fffff                            // 23b boundary

#define GC_TRIGGER_ALLOCS   10000                               // GC triggered at specified number of allocs



int alloc_count = 0;                    // tracks number of allocations made since last GC trigger
malloc_zone_t *zone = NULL;             // memory zone from which alloctions are made (is garbage collected)
static intptr_t *registers = NULL;      // an array for holding values of registers (16 registers, 64b each)



// definition of struct for bitmaps
typedef struct {
    void *address;      // base address of a region/VM page
    uint64_t *bitmap;   // pointer to bitmap
    uint size;          // size of bitmap in bytes
    UT_hash_handle hh;  // used to make hashable
} bitmap;

static bitmap *bitmaps = NULL;          // head of bitmaps hashtable
static bitmap *in_use_bitmaps = NULL;   // head of in use bitmaps hashtable

static jmp_buf buf;                     // used for longjmp(), if malloc() fails in extending hashtable

#define BITMAP_BITS_IN_WORD (sizeof(uint64_t) * 8)



// definition of struct for elements of worklist
typedef struct ptr_element {
    void *block;                // references memory block to process
    struct ptr_element *next;   // used to make singly-linked list
} ptr_element;

// head element of worklist (stack)
static ptr_element *worklist = NULL;


// enumerates allocation types
typedef enum
{
    malloc_type,
    calloc_type
} alloc_type_t;


/* Allocator functions */
static void *gc_internal_alloc(size_t size, alloc_type_t type);
static bitmap *create_bitmap(void *base_address, unsigned int size);


/* Garbage collector functions */
static void mark_from_roots();
static void mark();
static void sweep();
static void sweep_range_recorder(task_t task, void *context, unsigned type_mask,
                          vm_range_t *ranges, unsigned range_count);
static void bitmap_free_range_recorder(task_t task, void *context, unsigned type_mask,
                                       vm_range_t *ranges, unsigned range_count);
static void *get_sp();


/* Bitmap functions */
static int valid_ptr(void *candidate);
static int is_marked(void *block);
static void set_marked(void *block);
static void *get_base_address(void *block);
static unsigned int get_bit_pos_bitmap(void *block);
static void set_bit_bitmap(uint64_t *bitmap, unsigned int bit_pos);
static void clear_bit_bitmap(uint64_t *bitmap, unsigned int bit_pos);
static int get_bit_bitmap(uint64_t *bitmap, unsigned int bit_pos);





/***************************	Alloctor	***************************/

/*
 * Allocates a new garbage-collected memory block of size size.
 * Pointer returned should not be freed explicitly.
 */
void *gc_malloc(size_t size)
{
    void *ptr = gc_internal_alloc(size, malloc_type);
    if (!ptr) {
        gc_collect();                               // if heap is full, collect garbage
        ptr = gc_internal_alloc(size, malloc_type); // try allocating again
        if (!ptr)
            return NULL;                            // if still NULL, heap is exhausted
    }
    // trigger garbage collection automatically after GC_TRIGGER_ALLOCS allocations
    else if (++alloc_count >= GC_TRIGGER_ALLOCS) {
        gc_collect();
        alloc_count = 0;
    }
    
    return ptr;
}


/*
 * Allocates a new garbage-collected memory block of size size; block is cleared.
 * Pointer returned should not be freed explicitly.
 */
void *gc_calloc(size_t num_items, size_t size)
{
    size = size * num_items;                            // use of a single allocation function
    void *ptr = gc_internal_alloc(size, calloc_type);
    if (!ptr) {
        gc_collect();                                   // if heap is full, collect garbage
        ptr = gc_internal_alloc(size, calloc_type);     // try allocating again
        if (!ptr)
            return NULL;                                // if still NULL, heap is exhausted
    }
    // trigger garbage collection automatically after GC_TRIGGER_ALLOCS allocations
    else if (++alloc_count >= GC_TRIGGER_ALLOCS) {
        gc_collect();
        alloc_count = 0;
    }
    
    return ptr;
}


/*
 * Allocates requested memory and creates a new bitmap if new region is created.
 * Returns NULL on error.
 */
static void *gc_internal_alloc(size_t size, alloc_type_t type)
{
    void *ptr = NULL;
    if (type == malloc_type)
        ptr = malloc_zone_malloc(zone, size);
    else if (type == calloc_type)
        ptr = malloc_zone_calloc(zone, 1, size);
    
    if (!ptr) {                     // heap full
        return NULL;
    }
    
    // check if malloc returned a new region
    // tiny allocation
    if (size <= SMALL_THRESHOLD) {
        // checks if it could be a new tiny region (TINY_BLOCK_MASK aligned memory)
        if (((intptr_t)ptr & TINY_BLOCK_MASK) == 0) {
            bitmap *tiny_bitmap = create_bitmap(ptr, TINY_BITMAP_SIZE);
            
            if (!tiny_bitmap) {     // allocation of bitmap failed
                free(ptr);          // free memory and return
                return NULL;
            }
        }
    }
    // small allocation
    else if (size <= LARGE_THRESHOLD) {
        // checks if it could be a new small region (SMALL_BLOCK_MASK aligned memory)
        if (((intptr_t)ptr & SMALL_BLOCK_MASK) == 0) {
            bitmap *small_bitmap = create_bitmap(ptr, SMALL_BITMAP_SIZE);
            
            if (!small_bitmap) {    // allocation of bitmap failed
                free(ptr);          // free memory and return
                return NULL;
            }
        }
    }
    // large allocation
    else {
        bitmap *large_bitmap = create_bitmap(ptr, 1); // large allocations need only mark-bit
        
        if (!large_bitmap) {        // allocation of bitmap failed
            free(ptr);              // free memory and return
            return NULL;
        }
    }
    
    return ptr;
}


/*
 * Function used to help creating and adding a new bitmap.
 * Ensures each bitmap has unique key in hashtable (bitmap->address).
 */
static bitmap *create_bitmap(void *base_address, unsigned int size)
{
    if (setjmp(buf))                                    // if HASH_ADD_PTR fails at allocating memory
        return NULL;
    
    bitmap *to_add;
    HASH_FIND_PTR(bitmaps, &base_address, to_add);
    
    // found bitmap
    if (to_add) {
        if (to_add->size != size) {                     // different size bitmap
            uint64_t *bitmap_alloc = calloc(1, size);   // initialize mark-bits to zero
            if (!bitmap_alloc)                          // not enough memory to reallocate
                return NULL;                            // report error
            
            HASH_DEL(bitmaps, to_add);                  // remove bitmap from hashtable before altering key
            free(to_add->bitmap);                       // free old bitmap
            to_add->bitmap = bitmap_alloc;
            to_add->size = size;
            HASH_ADD_PTR(bitmaps, address, to_add);     // add bitmap back to hashtable
        }
    }
    // create bitmap
    else {
        to_add = (bitmap *) malloc(sizeof(*to_add));
        if (!to_add)                                    // not enough memory
            return NULL;                                // report error
        
        uint64_t *bitmap_alloc = calloc(1, size);       // initialize mark-bits to zero
        if (!bitmap_alloc) {                            // not enough memory
            free(to_add);                               // free struct for bitmap before returning
            return NULL;                                // report error
        }
        
        // if allocations went through, initialize and add bitmap to hashtable
        to_add->address = base_address;
        to_add->bitmap = bitmap_alloc;
        to_add->size = size;
        HASH_ADD_PTR(bitmaps, address, to_add);
    }
    
    return to_add;
}






/***********************	Garbage collector	***********************/

/*
 * Initializes garbage collector.
 * Must be called before allocating memory with gc_malloc().
 */
void gc_init()
{
    zone = malloc_create_zone(1 << 10, 0);  // create a new memory zone and set inital size to 1 KB
    if (!zone) {
        perror("GC: Failed to create a memory zone.");
        exit(1);
    }
    
    registers = malloc(16 * 8);             // 16 general purpose registers, each 64bit
    if (!registers) {
        perror("GC: Failed to initialize memory structure.");
        exit(1);
    }
}


/*
 * Initiates garbage collection.
 */
void gc_collect()
{
    mark_from_roots();
    sweep();
}


/*
 * Marks all objects directly referenced by mutator's roots (local variables and registers).
 */
static void mark_from_roots()
{
    void **candidate; // needs checking if it can be a pointer
    
    // look for pointers in registers
    intptr_t *registers_i = registers;
    // loads all registers' values into memory
    __asm__ __volatile__ ("movq %%rax, %0" : "=r" (*registers_i++));
    __asm__ __volatile__ ("movq %%rbx, %0" : "=r" (*registers_i++));
    __asm__ __volatile__ ("movq %%rcx, %0" : "=r" (*registers_i++));
    __asm__ __volatile__ ("movq %%rdx, %0" : "=r" (*registers_i++));
    __asm__ __volatile__ ("movq %%rsp, %0" : "=r" (*registers_i++));
    __asm__ __volatile__ ("movq %%rbp, %0" : "=r" (*registers_i++));
    __asm__ __volatile__ ("movq %%rsi, %0" : "=r" (*registers_i++));
    __asm__ __volatile__ ("movq %%rdi, %0" : "=r" (*registers_i++));
    __asm__ __volatile__ ("movq %%r8, %0" : "=r" (*registers_i++));
    __asm__ __volatile__ ("movq %%r9, %0" : "=r" (*registers_i++));
    __asm__ __volatile__ ("movq %%r10, %0" : "=r" (*registers_i++));
    __asm__ __volatile__ ("movq %%r11, %0" : "=r" (*registers_i++));
    __asm__ __volatile__ ("movq %%r12, %0" : "=r" (*registers_i++));
    __asm__ __volatile__ ("movq %%r13, %0" : "=r" (*registers_i++));
    __asm__ __volatile__ ("movq %%r14, %0" : "=r" (*registers_i++));
    __asm__ __volatile__ ("movq %%r15, %0" : "=r" (*registers_i++));
    
    for (candidate = (void *)registers; candidate < (void **)registers_i;
         candidate++) {
        
        if (valid_ptr(*candidate) && !is_marked(*candidate)) {
            set_marked(*candidate);
            
            // add memory block to worklist
            ptr_element *element = malloc(sizeof(*element));
            if (!element) {
                perror("GC: Not enough memory left for garbage collection.");
                exit(1);
            }
            element->block = *candidate;
            LL_PREPEND(worklist, element);
            
            mark(); // immediately call mark() to reduce worklist size
        }
    }
    
    
    // look for pointers in the thread stack (stack grows downwards)
    void *stack_base_address = pthread_get_stackaddr_np(pthread_self());
    void *stack_lower_bound = get_sp();
    for (candidate = stack_base_address; (void *)candidate > stack_lower_bound; candidate--) {
        
        if (valid_ptr(*candidate) && !is_marked(*candidate)) {
            set_marked(*candidate);
            
            // add memory block to worklist
            ptr_element *element = malloc(sizeof(*element));
            if (!element) {
                perror("GC: Not enough memory left for garbage collection.");
                exit(1);
            }
            element->block = *candidate;
            LL_PREPEND(worklist, element);
            
            mark(); // immediately call mark() to reduce worklist size
        }
    }
}


/*
 * Marks objects with depth-first traversal of object graph.
 */
static void mark()
{
    // iterate until worklist is empty (it contains only marked objects)
    while (worklist != NULL) {
        // pop element from worklist
        ptr_element *pop_element = worklist;
        void **block = worklist->block;
        LL_DELETE(worklist, worklist);
        free(pop_element);
        
        // mark and add children to worklist
        size_t block_size = malloc_size(block);
        for (int i = 0; i < (block_size / sizeof(void *)); i++) { // pointers are aligned on 8 byte boundary (on 64-bit systems)
            void *child = block[i];

            if (valid_ptr(child) && !is_marked(child)) {
                set_marked(child);
                
                // add child to worklist
                ptr_element *child_el = malloc(sizeof(*child_el));
                if (!child_el) {
                    perror("GC: Not enough memory left for garbage collection.");
                    exit(1);
                }
                child_el->block = child;
                LL_PREPEND(worklist, child_el);
            }
        }
    }
}


/*
 * Sweeps garbage memory blocks and deletes unused bitmaps of regions removed.
 */
static void sweep()
{
    // enumerate through all memory regions in use and free unmarked memory blocks
    zone->introspect->enumerator(mach_task_self(),
                                 NULL,
                                 MALLOC_PTR_IN_USE_RANGE_TYPE,
                                 (vm_address_t)zone,
                                 NULL,
                                 sweep_range_recorder);
    
    // after sweeping move bitmaps of memory regions still in use from bitmaps hashtable to in_use_bitmaps
    zone->introspect->enumerator(mach_task_self(),
                                 NULL,
                                 MALLOC_PTR_REGION_RANGE_TYPE,
                                 (vm_address_t)zone,
                                 NULL,
                                 bitmap_free_range_recorder);
    
    // delete and free unused bitmaps
    bitmap *current_bitmap, *tmp;
    HASH_ITER(hh, bitmaps, current_bitmap, tmp) {
        #ifdef LOGGING
        printf("GC Log: Removing unused bitmap for region: %p\n", current_bitmap->address);
        #endif
        
        HASH_DEL(bitmaps, current_bitmap);
        free(current_bitmap->bitmap);
        free(current_bitmap);
    }
    
    // move in_use_bitmaps to bitmaps
    bitmaps = in_use_bitmaps;
    in_use_bitmaps = NULL;
}


/*
 * Range recorder function used to iterate over specified region and collect (sweep) garbage.
 * Must be used with MALLOC_PTR_IN_USE_RANGE_TYPE enumerator type mask.
 */
static void sweep_range_recorder(task_t task, void *context, unsigned type_mask,
                     vm_range_t *ranges, unsigned range_count)
{
    // get hashmap for range to iterate through
    void *base_address = get_base_address((void *) ranges->address);
    unsigned int bit_pos;
    bitmap *to_check = NULL;
    
    HASH_FIND_PTR(bitmaps, &base_address, to_check);
    if (!to_check) {
        perror("GC: Bitmap not found.");
        exit(2);
    }
    
    // iterate through all allocated memory blocks and free() unmarked ones
    vm_range_t *r, *end;
    for (r = ranges, end = ranges + range_count; r < end; r++) {
        bit_pos = get_bit_pos_bitmap((void *) r->address);
        
        // if marked
        if (get_bit_bitmap(to_check->bitmap, bit_pos)) {
            clear_bit_bitmap(to_check->bitmap, bit_pos);    // clear mark bit
        }
        // if NOT marked
        else {
            #ifdef LOGGING
            printf("GC Log: Freeing unmarked memory block: %p\n", (void *)r->address);
            #endif
            
            free((void *) r->address);                      // free unmarked memory block
        }
    }
}


/*
 * Moves bitmap of each region encountered
 */
static void bitmap_free_range_recorder(task_t task, void *context, unsigned type_mask,
                                 vm_range_t *ranges, unsigned range_count)
{
    if (setjmp(buf)) // if HASH_ADD_PTR fails at allocating memory
        return;
    
    // for each range encountered, copy its bitmap to in_use_bitmaps
    bitmap *to_add;
    vm_range_t *r, *end;
    for (r = ranges, end = ranges + range_count; r < end; r++) {
        HASH_FIND_PTR(bitmaps, &(r->address), to_add);
        HASH_DEL(bitmaps, to_add);
        HASH_ADD_PTR(in_use_bitmaps, address, to_add);
    }
}


/*
 * Checks if pointer references a valid memory block in GC memory zone.
 */
static int valid_ptr(void *candidate)
{
    // check if pointer references allocated memory block from GC zone
    if (malloc_zone_from_ptr(candidate) != zone)
        return 0;
    
    return 1;
}


/*
 * Checks if (valid) memory block is marked.
 */
static int is_marked(void *block)
{
    bitmap *to_check = NULL;
    void *base_address = get_base_address(block);
    unsigned int bit_pos = get_bit_pos_bitmap(block);
    
    HASH_FIND_PTR(bitmaps, &base_address, to_check);
    if (!to_check) {
        perror("GC: Bitmap not found.");
        exit(2);
    }
    
    return get_bit_bitmap(to_check->bitmap, bit_pos);
}


/*
 * Marks (valid) memory block.
 */
static void set_marked(void *block)
{
    bitmap *to_set = NULL;
    void *base_address = get_base_address(block);
    unsigned int bit_pos = get_bit_pos_bitmap(block);
    
    HASH_FIND_PTR(bitmaps, &base_address, to_set);
    if (!to_set) {
        perror("GC: Bitmap not found.");
        exit(2);
    }
    
    set_bit_bitmap(to_set->bitmap, bit_pos);
}


/*
 * Returns the base address of a memory region, which contains memory block passed as a parameter.
 */
static void *get_base_address(void *block)
{
    void *base_address;
    size_t block_size = malloc_size(block);
    
    // tiny allocation
    if (block_size <= SMALL_THRESHOLD) {
        base_address = (void *) ((uintptr_t)block & ~(uintptr_t)TINY_BLOCK_MASK);
    }
    // small allocation
    else if (block_size <= LARGE_THRESHOLD) {
        base_address = (void *) ((uintptr_t)block & ~(uintptr_t)SMALL_BLOCK_MASK);
    }
    // large allocation
    else {
        base_address = block;   // large allocations are allocated directly as VM pages
    }
    
    return base_address;
}


/*
 * Returns the bit position in bitmap of a memory block passed passed as a parameter.
 */
static unsigned int get_bit_pos_bitmap(void *block)
{
    unsigned int bit_pos;
    size_t block_size = malloc_size(block);
    
    // tiny allocation
    if (block_size <= SMALL_THRESHOLD) {
        bit_pos = ((uintptr_t)block & TINY_BLOCK_MASK) >> SHIFT_TINY_QUANTUM;
    }
    // small allocation
    else if (block_size <= LARGE_THRESHOLD) {
        bit_pos = ((uintptr_t)block & SMALL_BLOCK_MASK) >> SHIFT_SMALL_QUANTUM;
    }
    // large allocation
    else {
        bit_pos = 0;            // only 1 bit per large region
    }
    
    return bit_pos;
}


/*
 * Functions used to manipulate bits in bitmap.
 */

static void set_bit_bitmap(uint64_t *bitmap, unsigned int bit_pos)
{
    uint64_t mask = (1ull << (bit_pos % BITMAP_BITS_IN_WORD));
    bitmap[bit_pos / BITMAP_BITS_IN_WORD] |= mask;
}

static void clear_bit_bitmap(uint64_t *bitmap, unsigned int bit_pos)
{
    uint64_t mask = ~(1ull << (bit_pos % BITMAP_BITS_IN_WORD));
    bitmap[bit_pos / BITMAP_BITS_IN_WORD] &= mask;
}

static int get_bit_bitmap(uint64_t *bitmap, unsigned int bit_pos)
{
    uint64_t mask = (1ull << (bit_pos % BITMAP_BITS_IN_WORD));
    uint64_t bit = bitmap[bit_pos / BITMAP_BITS_IN_WORD] & mask;
    
    return bit != 0;
}


/*
 * Returns an estimate of Stack Pointer.
 * Can be used for figuring out the (current) lower bound of the thread stack.
 */
static void *get_sp()
{
    void *sp;
    __asm__ __volatile__ ("movq %%rsp, %0" : "=r" (sp));
    
    return sp;
}