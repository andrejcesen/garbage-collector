//
//  garbagecollector.h
//  GarbageCollector
//
//  Interface header file for mark-sweep garbage collection in C language.
//  Runs on Mac OS X. Tested on Mac OS X 10.9.
//
//  Created by Andrej Česen
//
//



/*********	Alloctor	********************/

/**
 * Allocates a new garbage-collected memory block of size size.
 * Pointer returned should not be freed explicitly.
 */
void *gc_malloc(size_t size);

/**
 * Allocates a new garbage-collected memory block of size size; block is cleared.
 * Pointer returned should not be freed explicitly.
 */
void *gc_calloc(size_t num_items, size_t size);




/*********	Garbage collector	************/

/**
 * Initializes garbage collector.
 * Must be called before allocating memory with gc_malloc().
 */
void gc_init();


/**
 * Initiates garbage collection.
 */
void gc_collect();