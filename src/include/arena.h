#pragma once
#include "checked_math.h"
#include "ints.h"
#include "utility.h"
#include <string.h>

struct Arena {
    void * begin;
    void * end;
    void * current;
    void * commited;
} typedef Arena;

int arena_new(Arena arena[ref], usize size);
void arena_free(Arena arena[ref]);
void * arena_alloc_bytes(Arena arena[ref], usize size, usize alignment);
void arena_reset(Arena arena[ref]);
static void *
arena_alloc_bytes_zeroed(Arena arena[ref], usize size, usize alignment) {
    void * alloc = arena_alloc_bytes(arena, size, alignment);
    if (alloc) {
        memset(alloc, 0, size);
    }
    return alloc;
}
static void *
arena_alloc_bytes_n(Arena arena[ref], usize size, usize alignment, usize n) {
    usize byten;
    if (!ckd_mul(size, n, &byten)) {
        return nullptr;
    }
    return arena_alloc_bytes(arena, byten, alignment);
}
static void * arena_alloc_bytes_zeroed_n(
    Arena arena[ref], usize size, usize alignment, usize n
) {
    usize byten;
    if (!ckd_mul(size, n, &byten)) {
        return nullptr;
    }
    return arena_alloc_bytes_zeroed(arena, byten, alignment);
}
#define arena_alloc_uninit(arena, type)                                        \
    ((type *)arena_alloc_bytes((arena), sizeof(type), alignof(type)))
#define arena_alloc_uninit_n(arena, type, number)                              \
    ((type *)                                                                  \
         arena_alloc_bytes_n((arena), sizeof(type), alignof(type), (number)))
#define arena_alloc(arena, type)                                               \
    ((type *)arena_alloc_bytes_zeroed((arena), sizeof(type), alignof(type)))
#define arena_alloc_n(arena, type, number)                                     \
    ((type *)arena_alloc_bytes_zeroed_n(                                       \
        (arena), sizeof(type), alignof(type), (number)                         \
    ))
