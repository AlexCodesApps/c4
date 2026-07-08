#include "include/type.h"
#include "include/segment_list.h"
#include "include/utility.h"
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

bool type_handle_struct_eq(TypeHandle a, TypeHandle b) {
	ASSERT(a.type->pass >= TYPE_PASS_CHECKED);
	ASSERT(b.type->pass >= TYPE_PASS_CHECKED);
	if (a.is_mut != b.is_mut)
		return false;
	if (a.type == b.type)
		return true;
	if (a.type->kind != b.type->kind)
		return false;
	switch (a.type->kind) {
	case TYPE_BUILTIN_VOID:
	case TYPE_BUILTIN_I32:
		return true;
	case TYPE_PTR:
		return type_handle_struct_eq(a.type->as.ptr, b.type->as.ptr);
	case TYPE_REF:
		return type_handle_struct_eq(a.type->as.ref, b.type->as.ref);
	case TYPE_FN:
		if (!type_handle_struct_eq(a.type->as.fn.return_ty,
								   b.type->as.fn.return_ty))
			return false;
		for (usize i = 0; i < a.type->as.fn.params.size; ++i) {
			if (!type_handle_struct_eq(a.type->as.fn.params.data[i],
									   b.type->as.fn.params.data[i]))
				return false;
		}
		return true;
	}
}

bool type_handle_eq(TypeHandle a, TypeHandle b) {
	if (a.is_mut != b.is_mut)
		return false;
	return a.type == b.type;
}

Type * type_list_at(TypeList * list, usize index) {
	word slot = get_segmented_slot(index);
	usize slot_index = get_segmented_slot_index(index, slot);
	return &list->data[slot][slot_index];
}
Type * type_list_add(VMemArena * arena, TypeList * list, Type type) {
	word slot = get_segmented_slot(list->size);
	usize index = get_segmented_slot_index(list->size, slot);
	if (index == 0) {
		word size = slot + 1;
		Type ** data = vmem_arena_alloc_n(arena, Type *, size);
		if (!data) {
			return NULL;
		}
		for (usize i = 0; i < slot; ++i) {
			data[i] = list->data[i];
		}
		Type * slot_ptr = vmem_arena_alloc_n(arena, Type, (usize)1 << slot);
		if (!slot_ptr) {
			return NULL;
		}
		data[slot] = slot_ptr;
		list->data = data;
	}
	++list->size;
	Type * loc = &list->data[slot][index];
	*loc = type;
	return loc;
}

static Type * type_intern_table_at(TypeInternTable * table, usize index) {
	return type_list_at(&table->types, index);
}

static Type * type_intern_table_add(VMemArena * arena, TypeInternTable * table,
									Type type) {
	return type_list_add(arena, &table->types, type);
}

void type_intern_table_init(TypeInternTable * table) {
	ZERO(&table->types);
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
	for (usize i = 0; i < table->types.size; ++i) {
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
	for (usize i = 0; i < table->types.size; ++i) {
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

Type * type_intern_table_fn_of(VMemArena * arena, TypeInternTable * table,
							   TypeHandle return_ty, TypeHandleSpan params) {
	for (usize i = 0; i < table->types.size; ++i) {
		Type * otype = type_intern_table_at(table, i);
		if (otype->kind != TYPE_FN)
			continue;
		if (!type_handle_eq(otype->as.fn.return_ty, return_ty))
			continue;
		if (otype->as.fn.params.size != params.size)
			continue;
		for (usize j = 0; j < params.size; ++j) {
			if (!type_handle_eq(params.data[j], otype->as.fn.params.data[j]))
				continue;
		}
		return otype;
	}
	Type ntype = {.pass = TYPE_PASS_CHECKED,
				  .kind = TYPE_FN,
				  .as.fn = {.return_ty = return_ty, .params = params}};
	return type_intern_table_add(arena, table, ntype);
}
