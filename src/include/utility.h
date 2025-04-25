#pragma once
#include "checked_math.h"
#include "ints.h"
#include "list_macros.h"
#include "macros.h"
#include <assert.h>
#define ref static 1
#define MAX(x, y)                                                              \
    ({                                                                         \
        auto _x = x;                                                           \
        auto _y = y;                                                           \
        _x > _y ? _x : _y;                                                     \
    })
#define MIN(x, y)                                                              \
    ({                                                                         \
        auto _x = x;                                                           \
        auto _y = y;                                                           \
        _x < _y ? _x : _y;                                                     \
    })
#define ABS(x)                                                                 \
    ({                                                                         \
        auto _x = x;                                                           \
        _x < 0 ? -_x : _x;                                                     \
    })
#define DISCARD_H(arg) (void)(arg);
#define ARRAY_SIZE(arr) (sizeof(arr) / sizeof(*(arr)))
#define DISCARD(...) FOREACH_MACRO(DISCARD_H, __VA_ARGS__)
static inline bool align_usize(usize integer, usize alignment, usize * out) {
    usize mask = alignment - 1;
    usize result;
    if (!ckd_add(integer, mask, &result)) {
        return false;
    }
    *out = result & ~mask;
    return true;
}
static inline bool align_ptr(void * ptr, usize alignment, void ** out) {
    usize mask = alignment - 1;
    usize result;
    if (!ckd_add((usize)ptr, mask, &result)) {
        return false;
    }
    *out = (void *)(result & ~mask);
    return true;
}

static inline bool bitwise_index_get(byte * memory, usize index) {
    byte b = memory[index >> 3];
    return (b >> (7 - (index & 7))) & 1;
}

static inline void bitwise_index_set(byte * memory, usize index, bool set) {
    byte * b = memory + (index >> 3);
    byte bit_index = index & 7;
    byte shiftl = 7 - bit_index;
    byte mask = 1 << shiftl;
    *b = (*b & ~mask) | (set << shiftl);
}

#define TODO (assert(false && "todo reached!"))

#define KB(n) ((n) * 1024)
#define MB(n) ((n) * 1024 * 1024)
#define GB(n) ((n) * 1024 * 1024 * 1024)
#define foreach_span(addr, i)                                                  \
    for (typeof_unqual((addr)->data) i = (addr)->data,                         \
                                     MACRO_VAR(end) = i + (addr)->size;        \
         i != MACRO_VAR(end); ++i)
#define span_index_in_bounds(addr, i) ((i) < (addr)->size)
#define span_at(addr, i)                                                       \
    (assert(span_index_in_bounds(addr, i)), (addr)->data + (i))
#define span_back(addr) span_at(addr, (addr)->size - 1)
#define span_front(addr) span_at(addr, 0)
