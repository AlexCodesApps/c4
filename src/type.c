#include "include/type.h"
#include "include/utility.h"
#include <assert.h>
#include <stddef.h>

bool type_handle_is_valid(TypeHandle handle) { return handle.type != NULL; }

TypeHandle type_handle_null(void) {
	return (TypeHandle){
		.type = NULL,
	};
}

TypeHandle type_handle_new(Type * type, bool is_mut, bool is_lvalue) {
	return (TypeHandle){
		.type = type,
		.is_mut = is_mut,
		.is_lvalue = is_lvalue,
	};
}

TypeHandle type_handle_from_ptr(Type * type) {
	return type_handle_new(type, false, false);
}

bool type_handle_eq(TypeHandle a, TypeHandle b) {
	if (a.is_mut != b.is_mut)
		return false;
	return a.type == b.type;
}

static usize get_segmented_slot(usize size) {
	return bit_width_usize(size + 1) - 1;
}

static usize get_segmented_slot_index(usize size, usize slot) {
	return size - ((usize)1 << slot) + 1;
}

static Type * type_intern_table_at(TypeInternTable * table, usize index) {
	usize slot = get_segmented_slot(index);
	usize slot_index = get_segmented_slot_index(index, slot);
	return &table->data[slot][slot_index];
}

static Type * type_intern_table_add(VMemArena * arena, TypeInternTable * table,
									Type type) {
	usize slot = get_segmented_slot(table->size);
	usize index = get_segmented_slot_index(table->size, slot);
	if (index == 0) {
		usize size = slot + 1;
		Type ** data = vmem_arena_alloc_n(arena, Type *, size);
		if (!data) {
			return NULL;
		}
		for (usize i = 0; i < slot; ++i) {
			data[i] = table->data[i];
		}
		Type * slot_ptr = vmem_arena_alloc_n(arena, Type, (usize)1 << slot);
		if (!slot_ptr) {
			return NULL;
		}
		data[slot] = slot_ptr;
		table->data = data;
	}
	++table->size;
	Type * loc = &table->data[slot][index];
	*loc = type;
	return loc;
}

void type_intern_table_init(TypeInternTable * table) {
	table->data = NULL;
	table->size = 0;
	table->void_type = (Type){
		.pass = TYPE_PASS_EVALUATED,
		.kind = TYPE_BUILTIN_VOID,
	};
	table->i32_type = (Type){
		.pass = TYPE_PASS_EVALUATED,
		.kind = TYPE_BUILTIN_I32,
	};
}

Type * type_intern_table_ptr_to(VMemArena * arena, TypeInternTable * table,
								TypeHandle type) {
	for (usize i = 0; i < table->size; ++i) {
		Type * otype = type_intern_table_at(table, i);
		if (otype->kind != TYPE_PTR) {
			continue;
		}
		if (type_handle_eq(otype->as.ptr, type)) {
			return otype;
		}
	}
	Type ntype = {
		.pass = TYPE_PASS_CHECKED,
		.kind = TYPE_PTR,
		.as.ptr = type,
	};
	return type_intern_table_add(arena, table, ntype);
}
Type * type_intern_table_ref_to(VMemArena * arena, TypeInternTable * table,
								TypeHandle type) {
	for (usize i = 0; i < table->size; ++i) {
		Type * otype = type_intern_table_at(table, i);
		if (otype->kind != TYPE_REF) {
			continue;
		}
		if (type_handle_eq(otype->as.ref, type)) {
			return otype;
		}
	}
	Type ntype = {
		.pass = TYPE_PASS_CHECKED,
		.kind = TYPE_PTR,
		.as.ref = type,
	};
	return type_intern_table_add(arena, table, ntype);
}
