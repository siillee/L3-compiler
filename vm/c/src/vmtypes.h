#ifndef VMTYPES_H
#define VMTYPES_H

#include <limits.h>
#include <stdint.h>
#include <assert.h>

typedef uint32_t value_t;       /* unsigned value (virtual pointer or other) */
typedef int32_t svalue_t;       /* signed value (rarely used!) */

static_assert(sizeof(value_t) == sizeof(svalue_t),
              "unsigned and signed values must have the same size");

#define VALUE_BITS (sizeof(value_t) * CHAR_BIT)

#endif
