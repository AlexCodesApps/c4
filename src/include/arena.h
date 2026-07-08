#pragma once
#include "ints.h"
#include "platform.h"

typedef struct {
	void * begin;
	void * current;
	void * end;
	void * commited;
} VMemArena;

bool vmem_arena_init(VMemArena * arena, usize size);
NODISCARD void * vmem_arena_alloc_bytes(VMemArena * arena, usize size,
										usize align);
NODISCARD void * vmem_arena_alloc_bytes_n(VMemArena * arena, usize size,
										  usize n, usize align);
void vmem_arena_reset(VMemArena * arena);
void vmem_arena_free(VMemArena * arena);

#define vmem_arena_alloc(arena_addr, type)                                     \
	((type *)vmem_arena_alloc_bytes((arena_addr), sizeof(type), ALIGNOF(type)))
#define vmem_arena_alloc_n(arena_addr, type, n)                                \
	((type *)vmem_arena_alloc_bytes_n(arena_addr, sizeof(type), n,             \
									  ALIGNOF(type)))
