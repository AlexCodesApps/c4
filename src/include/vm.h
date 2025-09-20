#pragma once
#include "ast.h"
#include "ints.h"

typedef struct {
	u64 section_tag : 16; // serves dual purpose of
						  // 1. fractioning VMSymbol lookup times and
						  // 2. Making it so that it is hard to accidentally
						  // underflow/overflow pointers into valid memory, By
						  // scattering virtual addresses obscene lengths apart
	u64 payload : 48;
} VMPtr;

typedef struct VMSymbol VMSymbol;
struct VMSymbol {
	VMPtr vm_ptr;
	Type * type;
	u8 * buffer;
	VMSymbol * next;
};

typedef struct {
	usize count;
	VMSymbol symbols[];
} VMPtrSection;

typedef struct {
	VMemArena buffer_arena;
	VMemArena symbols_arena; // size = sizeof(VMSymbol) * (2 ^ 16)
	VMPtrSection * current_section;
	usize stack_count;
} VMPtrStackTable;

typedef struct {
	VMPtrStackTable stack;
} VM;

void vm_init(VM * vm);
