#ifndef ENGINE__H
#define ENGINE__H

#include "vmtypes.h"
#include "memory.h"

typedef struct engine engine;

/* Create an engine */
engine* engine_new(memory* memory);

/* Release the given engine */
void engine_free(engine* self);

/* Emit an instruction */
void engine_emit_instruction(engine* self, value_t instruction);

/* Run the program */
value_t engine_run(engine* self);

#endif // ENGINE__H
