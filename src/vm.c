#include "include/vm.h"
#include "include/utility.h"
#include <stddef.h>

STATIC_ASSERT(ALIGNOF(void **) == ALIGNOF(VMMemoryBoundInfo),
			  "VMMemoryBound info must have pointer alignment");
#define PTR_SIZE sizeof(void **)
#define AGGREGATE_PTR_INFO_SIZE (sizeof(void **) + sizeof(VMMemoryBoundInfo))

void pointer_memory_map_init(PointerMemoryMap * map) {
	map->backing = NULL;
	map->size = 0;
	map->capacity = 0;
}

#define PTR_PTR(ptr) ((void ***)ptr)
#define PTR_ARR(map) PTR_PTR((map)->backing)
#define INFO_PTR(ptr, cap) ((VMMemoryBoundInfo *)((u8 *)ptr + cap * PTR_SIZE))
#define INFO_ARR(map) INFO_PTR((map)->backing, (map)->capacity)
#define FULL_CAPACITY(map) (((map)->size + 1) * 3 / 2 >= (map)->capacity)

bool pointer_memory_map_init_with_capacity(PointerMemoryMap * map,
										   usize capacity) {
	if (capacity == 0) {
		map->backing = NULL;
		map->size = 0;
		map->capacity = 0;
		return true;
	}
	if (capacity > USIZE_MAX >> 2)
		return false;
	capacity = next_pow2_usize(capacity << 2 / 3);
	void * backing = NULL;
	backing = calloc(AGGREGATE_PTR_INFO_SIZE, capacity);
	if (!backing)
		return false;
	memset(backing, 0, capacity * PTR_SIZE);
	map->backing = backing;
	map->size = 0;
	map->capacity = capacity;
	return true;
}

static usize hash_pointer(const void * addr) {
	return (usize)((uintptr_t)addr * 2654435761);
}

VMMemoryBoundInfo * pointer_memory_map_lookup(PointerMemoryMap * map,
											  void ** address) {
	usize hash = hash_pointer(address);
	usize mask = map->capacity - 1;
	usize index = hash & mask;
	void *** ptr_arr = PTR_ARR(map);
	VMMemoryBoundInfo * info_arr = INFO_ARR(map);
	for (;;) {
		void ** ptr = ptr_arr[index];
		if (!ptr)
			return NULL;
		if (ptr == address)
			return &info_arr[index];
		index = (index + 1) & mask;
	}
}

static usize find(PointerMemoryMap * map, void * address) {
	usize hash = hash_pointer(address);
	usize mask = map->capacity - 1;
	usize index = hash & mask;
	void *** ptr_arr = map->backing;
	for (;;) {
		void ** ptr = ptr_arr[index];
		if (!ptr)
			return index;
		if (ptr == address)
			return index;
		index = (index + 1) & mask;
	}
}

VMMemoryBoundInfo * pointer_memory_map_insert_no_alloc(PointerMemoryMap * map,
													   void ** address) {
	if (FULL_CAPACITY(map)) {
		return NULL;
	}
	usize index = find(map, address);
	PTR_ARR(map)[index] = address;
	return &INFO_ARR(map)[index];
}

VMMemoryBoundInfo * pointer_memory_map_reinsert(PointerMemoryMap * map,
												void ** address) {
	usize index = find(map, address);
	if (!PTR_ARR(map)[index])
		return NULL;
	return &INFO_ARR(map)[index];
}

void pointer_memory_map_free(PointerMemoryMap * map) { free(map->backing); }

bool vm_init(VM * vm, VMVarEnv * base) {
	vm->env = base;
	if (!vmem_arena_init(&vm->stack, VM_STACK_SIZE))
		return false;
	return true;
}

VMPtr vm_get_ptr(VM * vm, void ** address) {
	VMVarEnv * env = vm->env;
	ASSERT(env);
	do {
		VMMemoryBoundInfo * info =
			pointer_memory_map_lookup(&env->pointer_map, address);
		if (info) {
			return (VMPtr){*address, info};
		}
		env = env->parent;
	} while (env);
	return (VMPtr){*address, NULL};
}

void vm_store_ptr(VM * vm, VMPtr address, VMPtr value) {
	(void)vm;
	ASSERT(vm_ptr_is_valid(address));
	VMMemoryBoundInfo * info = pointer_memory_map_reinsert(
		&address.info->env->pointer_map, address.ptr);
	ASSERT(info); // reinsertion
	*info = *value.info;
	*(void **)address.ptr = value.ptr;
}

void vm_free(VM * vm) { vmem_arena_free(&vm->stack); }

bool vm_load_u8(VM * vm, VMPtr address, u8 * out) {
	ASSERT(vm_ptr_is_valid(address));
	if ((u8 *)address.info->end - (u8 *)address.info->start < 1)
		return false;
	return *(u8 *)address.ptr;
}
