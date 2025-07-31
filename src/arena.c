#include "include/arena.h"
#include "include/utility.h"

#include <sys/mman.h>

bool vmem_arena_init(VMemArena * arena, usize size) {
	bool ok = align_usize(size, 4096, &size);
	void * pages = mmap(nullptr, size, PROT_NONE, MAP_ANON | MAP_PRIVATE, -1, 0);
	ok &= pages != (void *)-1;
	if (UNLIKELY(!ok)) return false;
	arena->begin = pages;
	arena->current = pages;
	arena->end = (u8 *)pages + size;
	arena->commited = pages;
	return true;
}

void * vmem_arena_alloc_bytes(VMemArena * arena, usize size, usize align) {
	void * alloc_start;
	bool ok = align_ptr(arena->current, align, &alloc_start);
	void * new_current;
	ok &= ckd_add_ptr(alloc_start, size, &new_current);
	void * new_commited = arena->commited;
	if (new_commited < new_current) {
		ok &= align_ptr(new_current, 4096, &new_commited);
	}
	ok &= new_current < arena->end;
	if (UNLIKELY(!ok)) {
		return nullptr;
	}
	size_t n_commited_bytes = (uintptr_t)new_commited - (uintptr_t)arena->commited;
	ok = mprotect(arena->commited, n_commited_bytes, PROT_READ | PROT_WRITE) == 0;
	if (UNLIKELY(!ok)) {
		return nullptr;
	}
	arena->current = new_current;
	arena->commited = new_commited;
	return alloc_start;
}

void * vmem_arena_alloc_bytes_n(VMemArena * arena, usize size, usize n, usize align) {
	if (UNLIKELY(!ckd_mul(size, n, &size))) {
		return nullptr;
	}
	return vmem_arena_alloc_bytes(arena, size, align);
}

void vmem_arena_reset(VMemArena * arena) {
	arena->current = arena->begin;
}

void vmem_arena_free(VMemArena * arena) {
	size_t n_bytes = (uintptr_t)arena->end - (uintptr_t)arena->begin;
	munmap(arena->begin, n_bytes);
}
