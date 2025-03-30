#include "include/arena.hpp"
#include "include/utils.hpp"

/* class synopsis

class Arena {
    void * start;
    void * current;
    void * commited;
    void * end;
};

*/

#ifdef __unix

#include <unistd.h>
#include <sys/mman.h>

static bool init(void ** start, void ** current, void ** commited, void ** end, usize size) {
    void * alloc = mmap(nullptr, align_mul_of_two<usize>(size, 4096), PROT_NONE, MAP_PRIVATE | MAP_ANON, -1, 0);
    if (alloc == MAP_FAILED) {
        return false;
    }
    *start = alloc;
    *current = alloc;
    *commited = alloc;
    *end = (u8 *)alloc + size;
    return true;
}
static bool virtual_commit(void * ptr, usize size) {
    return mprotect(ptr, size, PROT_READ | PROT_WRITE) == 0;
}
static bool virtual_uncommit(void * ptr, usize size) {
    if (madvise(ptr, size, MADV_FREE) != 0) {
        return false;
    }
    return mprotect(ptr, size, PROT_NONE) == 0;
}
#else
#error "unsupported platform"
#endif


Arena::Arena(usize size) {
    if (!init(&start, &current, &commited, &end, size)) {
        throw std::bad_alloc();
    }
}

Arena::~Arena() {
    munmap(start, (usize)end - (usize)start);
}

void * Arena::allocate_bytes(usize size, usize alignment) {
    void * allocation_start = (void *)align_mul_of_two<usize>((usize)current, alignment);
    void * new_current = (u8 *)allocation_start + size;
    if (new_current > end) {
        return nullptr;
    }
    if (new_current > commited) {
        usize commit_size = align_mul_of_two<usize>(size, 4096);
        assert((u8 *)commited + commit_size <= end);
        if (!virtual_commit(commited, commit_size)) {
            return nullptr;
        }
        commited = (u8*)commited + commit_size;
    }
    current = new_current;
    return allocation_start;
}

void Arena::reset_pointer() {
    virtual_uncommit(start, (usize)commited - (usize)start);
    current = commited = start;
}
