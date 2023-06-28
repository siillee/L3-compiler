#include <assert.h>
#include <stdio.h>
#include <stdbool.h>
#include <string.h>

#include "vmtypes.h"
#include "engine.h"
#include "opcode.h"
#include "memory.h"
#include "fail.h"

#include "engine_instr.h"
#include "block_header.h"

struct engine {
  memory* memory;
  value_t* memory_start;
  value_t* free_boundary;
  value_t* regs;
  value_t* top_frames[2];
  int top_frame_index;
};

engine* engine_new(memory* memory) {
  engine* self = calloc(1, sizeof(engine));
  if (!self) fail("cannot allocate engine");

  value_t* memory_start = memory_get_start(memory);

  self->memory = memory;
  self->memory_start = memory_start;
  self->free_boundary = memory_start;

  return self;
}

void engine_free(engine* self) {
  free(self);
}

// Virtual <-> physical address translation

inline static value_t* addr_v_to_p(engine* self, value_t v_addr) {
  return &self->memory_start[v_addr >> 2]; /* TODO name that 2 */
}

inline static value_t addr_p_to_v(engine* self, value_t* p_addr) {
  assert(self->memory_start <= p_addr
         && p_addr <= (value_t*)memory_get_end(self->memory));
  return (value_t)(p_addr - self->memory_start) << 2; /* TODO name that 2 */
}

void engine_emit_instruction(engine* self, value_t instruction) {
  *(self->free_boundary++) = instruction;
}

static void emit_top_frames(engine* self) {
  value_t empty_frame[] = {
    header_pack(tag_RegisterFrame, 2),               // header
    0, 0,                                            // context
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,  // registers
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07,  // constant registers
    0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f,
    0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17,
    0x18, 0x19, 0x1a, 0x1b, 0x1c, 0x1d, 0x1e, 0x1f,
  };

  for (int i = 0; i < 2; i += 1) {
    memcpy(self->free_boundary, empty_frame, sizeof(empty_frame));
    self->top_frames[i] = &self->free_boundary[1];
    self->free_boundary += sizeof(empty_frame) / sizeof(value_t);
  }

  self->top_frame_index = 0;
  self->regs = &self->top_frames[self->top_frame_index][2];
}

// Access to top frames

inline static int next_frame_index(engine* self) {
  return 1 - self->top_frame_index;
}

inline static value_t* curr_frame(engine* self) {
  return self->top_frames[self->top_frame_index];
}

inline static value_t* next_frame(engine* self) {
  return self->top_frames[next_frame_index(self)];
}

// Register access macros (unsigned and signed)

#define Ra self->regs[instr_extract_u(*pc,  0, 8)]
#define Rb self->regs[instr_extract_u(*pc,  8, 8)]
#define Rc self->regs[instr_extract_u(*pc, 16, 8)]

#define sRa (svalue_t)Ra
#define sRb (svalue_t)Rb
#define sRc (svalue_t)Rc

// A "bare" instruction (i.e. a labeled block)
#define INSTR(L, B) L: { B; }

// An instruction prefetching the next instruction, to improve performance
// (to see the impact, exchange the "B;" line with its predecessor).
#define INSTR_P(L, P, B)                                        \
  INSTR(L, {                                                    \
      value_t* next_pc = P;                                     \
      void** next_label = labels[instr_opcode(*next_pc)];       \
      B;                                                        \
      pc = next_pc;                                             \
      goto *next_label;                                         \
    })

// A "linear" instruction, whose successor is the one that directly follows it
#define INSTR_L(L, B) INSTR_P(L, pc + 1, B)

// A jump instruction, doing nothing else than computing the next PC (no body)
#define INSTR_J(L, P) INSTR_P(L, P, {})

// A call instruction, which saves the caller's context in the frame
// of the callee, before switching to it.
#define INSTR_C(L, P) INSTR_P(L, P, {                           \
      value_t* callee_frame = next_frame(self);                 \
      callee_frame[0] = addr_p_to_v(self, pc + 1);              \
      callee_frame[1] = addr_p_to_v(self, curr_frame(self));    \
      self->top_frame_index = next_frame_index(self);           \
      self->regs = &curr_frame(self)[2];                        \
    })

value_t engine_run(engine* self) {
  void** labels[] = {
    [opcode_ADD]    = &&l_ADD,
    [opcode_SUB]    = &&l_SUB,
    [opcode_MUL]    = &&l_MUL,
    [opcode_DIV]    = &&l_DIV,
    [opcode_MOD]    = &&l_MOD,
    [opcode_LSL]    = &&l_LSL,
    [opcode_LSR]    = &&l_LSR,
    [opcode_AND]    = &&l_AND,
    [opcode_OR]     = &&l_OR,
    [opcode_XOR]    = &&l_XOR,
    [opcode_JLT]    = &&l_JLT,
    [opcode_JLE]    = &&l_JLE,
    [opcode_JEQ]    = &&l_JEQ,
    [opcode_JNE]    = &&l_JNE,
    [opcode_JUMP_I] = &&l_JUMP_I,
    [opcode_JUMP_D] = &&l_JUMP_D,
    [opcode_CALL_I] = &&l_CALL_I,
    [opcode_CALL_D] = &&l_CALL_D,
    [opcode_RET]    = &&l_RET,
    [opcode_HALT]   = &&l_HALT,
    [opcode_LDLO]   = &&l_LDLO,
    [opcode_LDHI]   = &&l_LDHI,
    [opcode_MOVE]   = &&l_MOVE,
    [opcode_ARGS]   = &&l_ARGS,
    [opcode_FRAME]  = &&l_FRAME,
    [opcode_BALO]   = &&l_BALO,
    [opcode_BSIZ]   = &&l_BSIZ,
    [opcode_BTAG]   = &&l_BTAG,
    [opcode_BGET]   = &&l_BGET,
    [opcode_BSET]   = &&l_BSET,
    [opcode_IO]     = &&l_IO,
  };

  memory* memory = self->memory;

  emit_top_frames(self);
  memory_set_heap_start(memory, self->free_boundary);

  value_t* pc = self->memory_start;
  goto *labels[instr_opcode(*pc)];

  INSTR_L(l_ADD, Ra = Rb + Rc);
  INSTR_L(l_SUB, Ra = Rb - Rc);
  INSTR_L(l_MUL, Ra = Rb * Rc);
  INSTR_L(l_DIV, Ra = (value_t)(sRb / sRc));
  INSTR_L(l_MOD, Ra = (value_t)(sRb % sRc));
  INSTR_L(l_LSL, Ra = Rb << (Rc & 0x1F));
  INSTR_L(l_LSR, Ra = (value_t)(sRb >> (Rc & 0x1F)));
  INSTR_L(l_AND, Ra = Rb & Rc);
  INSTR_L(l_OR,  Ra = Rb | Rc);
  INSTR_L(l_XOR, Ra = Rb ^ Rc);

  INSTR_J(l_JLT, pc + (sRa < sRb ? instr_d11(*pc) : 1));
  INSTR_J(l_JLE, pc + (sRa <= sRb ? instr_d11(*pc) : 1));
  INSTR_J(l_JEQ, pc + (Ra == Rb ? instr_d11(*pc) : 1));
  INSTR_J(l_JNE, pc + (Ra != Rb ? instr_d11(*pc) : 1));
  INSTR_J(l_JUMP_I, addr_v_to_p(self, Ra));
  INSTR_J(l_JUMP_D, pc + instr_d27(*pc));

  INSTR_C(l_CALL_I, addr_v_to_p(self, Rb));
  INSTR_C(l_CALL_D, pc + instr_d19(*pc));

  INSTR_P(l_RET, addr_v_to_p(self, curr_frame(self)[0]), {
      value_t* curr = curr_frame(self);
      value_t call_instr = addr_v_to_p(self, curr[0])[-1];
      unsigned int ret_reg = instr_extract_u(call_instr,  0, 8);
      value_t ret_value = Ra;

      value_t* parent_frame = addr_v_to_p(self, curr[1]);
      if (parent_frame == next_frame(self)) {
        // Parent frame already loaded, switch to it
        self->top_frame_index = next_frame_index(self);
        self->regs = &curr_frame(self)[2];
      } else {
        // Parent frame in heap, copy it to current
        int parent_size = block_size(parent_frame) + 1;
        memcpy(&curr[-1], &parent_frame[-1], parent_size * sizeof(value_t));
        memory_free_block(memory, parent_frame);
      }
      self->regs[ret_reg] = ret_value;
    });

  INSTR(l_HALT, return Ra);

  INSTR_L(l_LDLO, Ra = (value_t)instr_extract_s(*pc, 8, 19));
  INSTR_L(l_LDHI, {
      value_t ms16b = (value_t)instr_extract_u(*pc, 8, 16) << 16;
      Ra = ms16b | (Ra & 0xFFFF);
    });

  INSTR_L(l_MOVE, Ra = Rb);

  // ARGS instructions are "fused", in that a succession of them is
  // interpreted as one instruction by the code below. Therefore, it
  // is defined as a "bare" instruction, without prefetching.
  INSTR(l_ARGS, {
      value_t* curr = curr_frame(self);
      value_t* next = next_frame(self);
      if (curr[1] == addr_p_to_v(self, next)) {
        // Next top frame already occupied, evict it to the heap
        value_t* next_c = memory_copy_of_block(memory, next, curr);
        curr[1] = addr_p_to_v(self, next_c);
      }

      int i = 2;
      do {
        next[i++] = Ra; next[i++] = Rb; next[i++] = Rc;
        pc += 1;
      } while (instr_opcode(*pc) == opcode_ARGS);
      next[-1] = header_pack(tag_RegisterFrame, i);
      goto *labels[instr_opcode(*pc)];
    });

  INSTR_L(l_FRAME, {
      const int size = instr_extract_u(*pc, 0, 8);
      value_t* curr = curr_frame(self);
      int curr_frame_size = block_size(curr) - 2;
      int size_to_clear = (size - curr_frame_size) * sizeof(value_t);
      if (size_to_clear > 0)
        memset(&self->regs[curr_frame_size], 0, size_to_clear);
      curr[-1] = header_pack(tag_RegisterFrame, size + 2);
    });

  INSTR_L(l_BALO, {
      tag_t t = instr_extract_u(*pc, 16, 8);
      Ra = addr_p_to_v(self, memory_allocate(memory, t, Rb, curr_frame(self)));
    });
  INSTR_L(l_BSIZ, Ra = block_size(addr_v_to_p(self, Rb)));
  INSTR_L(l_BTAG, Ra = block_tag(addr_v_to_p(self, Rb)));
  INSTR_L(l_BGET, {
      assert(Rc < block_size(addr_v_to_p(self, Rb)));
      Ra = addr_v_to_p(self, Rb)[Rc];
    });
  INSTR_L(l_BSET, {
      assert(Rc < block_size(addr_v_to_p(self, Rb)));
      addr_v_to_p(self, Rb)[Rc] = Ra;
    });

  INSTR_L(l_IO, {
      switch (instr_extract_u(*pc, 8, 8)) {
      case 0: {
        int maybe_byte = getchar_unlocked();
        Ra = (value_t)(maybe_byte != EOF ? maybe_byte : -1);
      } break;

      case 1: {
        putchar_unlocked((uint8_t)Ra);
      } break;

      default:
        fail("invalid I/O command");
      }
    });
}
