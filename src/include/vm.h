#pragma once
#include "arena.h"
#include "ints.h"
#include "type.h"
#include "utility.h"

typedef struct VMVarEnv VMVarEnv;
typedef struct VMPointerMemoryMap VMPointerMemoryMap;
typedef struct VMDeclMemoryMap VMDeclMemoryMap;

typedef struct {
	void * start;
	void * end;
	VMVarEnv * env;
	TypeHandle type;
} VMMemoryBoundInfo;
#define VM_MBI(start, end, env, type)                                          \
	((VMMemoryBoundInfo){(start), (end), (env), (type)})

typedef struct {
	void * backing;
	usize size;
	usize capacity;
} PointerMemoryMap;

void pointer_memory_map_init(PointerMemoryMap * map);
bool pointer_memory_map_init_with_capacity(PointerMemoryMap * map,
										   usize capacity);
VMMemoryBoundInfo * pointer_memory_map_lookup(PointerMemoryMap * map,
											  void ** address);
VMMemoryBoundInfo * pointer_memory_map_insert_no_alloc(PointerMemoryMap * map,
													   void ** address);
VMMemoryBoundInfo * pointer_memory_map_reinsert(PointerMemoryMap * map,
												void ** address);
void pointer_memory_map_free(PointerMemoryMap * map);

typedef struct {
	void * backing;
	usize size;
	usize capacity;
} DeclMemoryMap;

struct VMVarEnv {
	VMVarEnv * parent;
	DeclMemoryMap decl_map;
	PointerMemoryMap pointer_map;
	usize frame_size; // only meaningful for function frames
};

typedef struct {
	void * ptr;
	const VMMemoryBoundInfo * info;
} VMPtr;

static inline bool vm_ptr_is_valid(VMPtr ptr) { return ptr.info != NULL; }

#define VM_STACK_SIZE MB(2)

typedef struct {
	VMVarEnv * env;
	VMemArena stack;
} VM;

typedef enum { VM_STATUS_OK, VM_STATUS_OOB } VMStatus;

bool vm_init(VM * vm, VMVarEnv * base);

VMPtr vm_load_ptr(VM * vm, void ** address);
void vm_store_ptr(VM * vm, VMPtr address, VMPtr value);
bool vm_load_u8(VM * vm, VMPtr address, u8 * out);
bool vm_load_u16(VM * vm, VMPtr address, u16 * out);
bool vm_load_u32(VM * vm, VMPtr address, u32 * out);
bool vm_load_u64(VM * vm, VMPtr address, u64 * out);
void vm_free(VM * vm);
