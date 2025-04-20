#include <stdlib.h>
#include "include/allocator.h"

static void * general_purpose_allocate(AllocatorPayload _, AllocationRequest request) {
    return aligned_alloc(request.alignment, request.size);
}

static void general_purpose_deallocate(AllocatorPayload _, void * allocation) {
    free(allocation);
}

static void * arena_allocate(AllocatorPayload payload, AllocationRequest request) {
    Arena * arena = payload.pdata;
    return arena_alloc_bytes(arena, request.size, request.alignment);
}

Allocator general_purpose_allocator() {
    return (Allocator) {
        .allocator = general_purpose_allocate,
        .deallocator = general_purpose_deallocate,
        .payload = 0,
    };
}

Allocator arena_allocator(Arena * arena) {
    return (Allocator) {
        .allocator = arena_allocate,
        .deallocator = noop_deallocate,
        .payload.pdata = arena
    };
}

void * allocator_alloc_bytes(Allocator allocator, AllocationRequest request) {
    return allocator.allocator(allocator.payload, request);
}
void allocator_deallocate(Allocator allocator, void * mem) {
    allocator.deallocator(allocator.payload, mem);
}
