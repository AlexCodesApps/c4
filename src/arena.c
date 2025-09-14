#include "include/arena.h"
#include "include/utility.h"

#ifdef _WIN32
#include <windows.h>

#define INVALID_PAGE NULL
static void * map_pages(usize size) {
	return VirtualAlloc(NULL, size, MEM_RESERVE, PAGE_NOACCESS);
}
static bool commit_pages(void * start, usize size) {
	return VirtualAlloc(start, size, MEM_COMMIT, PAGE_READWRITE) != NULL;
}
static void free_pages(void * start, usize size) {
	VirtualFree(start, 0, MEM_RELEASE);
}
#else
#include <sys/mman.h>

#define INVALID_PAGE MAP_FAILED
static void * map_pages(usize size) {
	return mmap(NULL, size, PROT_NONE, MAP_ANON | MAP_PRIVATE, -1, 0);
}
static bool commit_pages(void * start, usize size) {
	return mprotect(start, size, PROT_READ | PROT_WRITE) == 0;
}
static void free_pages(void * start, usize size) { munmap(start, size); }
#endif

bool vmem_arena_init(VMemArena * arena, usize size) {
	bool ok = align_usize(size, 4096, &size);
	if (UNLIKELY(!ok))
		return false;
	void * pages = map_pages(size);
	ok = pages != INVALID_PAGE;
	if (UNLIKELY(!ok))
		return false;
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
	ok &= new_current < arena->end;
	void * new_commited = arena->commited;
	if (new_commited < new_current) {
		ok &= align_ptr(new_current, 4096, &new_commited);
		if (UNLIKELY(!ok)) {
			return NULL;
		}
		usize n_commited_bytes =
			(uintptr_t)new_commited - (uintptr_t)arena->commited;
		ok = commit_pages(arena->commited, n_commited_bytes);
	}
	if (UNLIKELY(!ok)) {
		return NULL;
	}
	arena->current = new_current;
	arena->commited = new_commited;
	return alloc_start;
}

void * vmem_arena_alloc_bytes_n(VMemArena * arena, usize size, usize n,
								usize align) {
	if (UNLIKELY(!ckd_mul_usize(size, n, &size))) {
		return NULL;
	}
	return vmem_arena_alloc_bytes(arena, size, align);
}

void vmem_arena_reset(VMemArena * arena) { arena->current = arena->begin; }

void vmem_arena_free(VMemArena * arena) {
	usize n_bytes = (uintptr_t)arena->end - (uintptr_t)arena->begin;
	free_pages(arena->begin, n_bytes);
}
