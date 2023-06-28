#ifndef ENGINE_INSTR_H
#define ENGINE_INSTR_H

#include <stdint.h>

#include "vmtypes.h"
#include "opcode.h"

static inline unsigned int instr_extract_u(value_t instr, int start, int len) {
  return (instr >> start) & ((1 << len) - 1);
}

static inline int instr_extract_s(value_t instr, int start, int len) {
  int bits = (int)instr_extract_u(instr, start, len);
  int m = 1 << (len - 1);
  return (bits ^ m) - m;
}

static inline opcode_t instr_opcode(value_t instr) {
  unsigned int opcode = instr_extract_u(instr, 27, 5);
  return (opcode_t)opcode;
}

static inline int instr_d11(value_t instr) {
  return instr_extract_s(instr, 16, 11);
}

static inline int instr_d19(value_t instr) {
  return instr_extract_s(instr, 8, 19);
}

static inline int instr_d27(value_t instr) {
  return instr_extract_s(instr, 0, 27);
}

#endif // ENGINE_INSTR_H
