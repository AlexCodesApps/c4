#include "include/arena.h"
#include "include/utility.h"
#ifdef __GNUC__
#define __USE_MISC 1 // clangd won't stop complaining otherwise
#endif
#include <sys/mman.h>
int arena_new(Arena * arena, usize size) {
    usize aligned_size;
    if (!align_usize(size, 4096, &aligned_size)) {
        return -1;
    }
    void * mem =
        mmap(nullptr, aligned_size, PROT_NONE, MAP_ANON | MAP_PRIVATE, -1, 0);
    if (mem == MAP_FAILED) {
        return -1;
    }
    arena->begin = mem;
    arena->end = mem + aligned_size;
    arena->current = mem;
    arena->commited = mem;
    return 0;
}

void * arena_alloc_bytes(Arena * arena, usize size, usize alignment) {
    void * aligned_current;
    if (!align_ptr(arena->current, alignment, &aligned_current)) {
        return nullptr;
    }
    void * aligned_end;
    if (!ckd_add_ptr(aligned_current, size, &aligned_end)) {
        return nullptr;
    }
    if (aligned_end > arena->end) {
        return nullptr;
    }
    if (aligned_end > arena->commited) {
        usize commit_size;
        if (!align_usize(size, 4096, &commit_size)) {
            return nullptr;
        }
        if (mprotect(arena->commited, commit_size, PROT_READ | PROT_WRITE)) {
            return nullptr;
        }
        void * commited;
        if (!ckd_add_ptr(arena->commited, commit_size, &commited)) {
            return nullptr;
        }
        if (commited > arena->end) {
            return nullptr;
        }
        arena->commited = commited;
    }
    arena->current = aligned_end;
    return aligned_current;
}

void arena_reset(Arena * arena) {
    usize size = ((usize)arena->commited) - ((usize)arena->begin);
    mprotect(arena->begin, size, PROT_NONE);
    madvise(arena->begin, size, MADV_FREE);
}

void arena_free(Arena * arena) {
    munmap(arena, ((usize)arena->end) - ((usize)arena->begin));
}
