#ifndef MEMORY_H
#define MEMORY_H

#include <stdlib.h>
#include "vmtypes.h"

typedef enum {
  tag_FreeBlock = 0,
  tag_RegisterFrame = 1,
  tag_Function = 2,
  tag_String = 3
} tag_t;

typedef struct memory memory;

/* Returns a string identifying the memory system */
char* memory_get_identity(void);

/* Create the memory module */
memory* memory_new(size_t total_byte_size);

/* Free the memory module */
void memory_free(memory* self);

/* Get first memory address */
value_t* memory_get_start(memory* self);

/* Get last memory address */
value_t* memory_get_end(memory* self);

/* Set the heap start, following the code area */
void memory_set_heap_start(memory* self, value_t* heap_start);

/* Allocate block, return physical pointer to the new block */
value_t* memory_allocate(memory* self, tag_t tag, value_t size, value_t* root);

value_t* memory_copy_of_block(memory* self, value_t* block, value_t* root);

void memory_free_block(memory* self, value_t* block);

#endif
