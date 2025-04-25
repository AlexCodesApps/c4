#pragma once

#include "arena.h"
#include "checked_math.h"
#include "ints.h"
#include "utility.h"
struct AllocationRequest {
    usize size;
    usize alignment;
} typedef AllocationRequest;
union AllocatorPayload {
    u64 udata;
    void * pdata;
} typedef AllocatorPayload;
typedef void * (*AllocatorAllocateCallback)(
    AllocatorPayload, AllocationRequest request
);
typedef void (*AllocatorDeallocateCallback)(
    AllocatorPayload, void * allocation
);

struct Allocator {
    AllocatorAllocateCallback allocator;
    AllocatorDeallocateCallback deallocator;
    AllocatorPayload payload;
} typedef Allocator;

void * allocator_alloc_bytes(Allocator allocator, AllocationRequest request);
void allocator_deallocate(Allocator allocator, void * mem);
static void *
allocator_alloc_bytes_zeroed(Allocator allocator, AllocationRequest request) {
    void * mem = allocator_alloc_bytes(allocator, request);
    if (mem) {
        memset(mem, 0, request.size);
    }
    return mem;
}
static void * allocator_alloc_bytes_n(
    Allocator allocator, AllocationRequest request, usize n
) {
    if (!ckd_mul(request.size, n, &request.size)) {
        return nullptr;
    }
    return allocator_alloc_bytes(allocator, request);
}

static void * allocator_alloc_bytes_zeroed_n(
    Allocator allocator, AllocationRequest request, usize n
) {
    if (!ckd_mul(request.size, n, &request.size)) {
        return nullptr;
    }
    return allocator_alloc_bytes_zeroed(allocator, request);
}

static AllocationRequest allocation_request_new(usize size, usize alignment) {
    return (AllocationRequest){
        .size = size,
        .alignment = alignment,
    };
}

#define allocator_alloc(allocator, type)                                       \
    (type *)allocator_alloc_bytes_zeroed(                                      \
        (allocator), allocation_request_new(sizeof(type), alignof(type))       \
    )
#define allocator_alloc_uninit(allocator, type)                                \
    (type *)allocator_alloc_bytes(                                             \
        (allocator), allocation_request_new(sizeof(type), alignof(type))       \
    )
#define allocator_alloc_n(allocator, type, n)                                  \
    (type *)allocator_alloc_bytes_zeroed_n(                                    \
        (allocator), allocation_request_new(sizeof(type), alignof(type)), (n)  \
    )
#define allocator_alloc_uninit_n(allocator, type, n)                           \
    (type *)allocator_alloc_bytes_n(                                           \
        (allocator), allocation_request_new(sizeof(type), alignof(type)), (n)  \
    )
extern Allocator general_purpose_allocator();
extern Allocator arena_allocator(Arena[ref]);
static void * noop_allocate(AllocatorPayload _, AllocationRequest _2) {
    return nullptr;
}
static void noop_deallocate(AllocatorPayload _, void * _2){}
#define NOOP_ALLOCATOR                                                         \
    (Allocator) {                                                              \
        .allocator = noop_allocate, .deallocator = noop_deallocate,            \
        .payload.pdata = nullptr,                                              \
    }
