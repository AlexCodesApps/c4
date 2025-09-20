#pragma once

#include "arena.h"
#include "ints.h"

typedef struct Type Type;
typedef struct TypeAlias TypeAlias;

typedef struct {
	Type * type;
	bool is_mut : 1;
	bool is_lvalue : 1;
} TypeHandle;

bool type_handle_is_valid(TypeHandle handle);
TypeHandle type_handle_null(void);
TypeHandle type_handle_new(Type * type, bool is_mut, bool is_lvalue);
TypeHandle type_handle_from_ptr(Type * type);
bool type_handle_eq(TypeHandle a, TypeHandle b);

typedef enum {
	TYPE_PASS_ERROR,
	TYPE_PASS_CHECKED,
	TYPE_PASS_EVALUATED,
} TypePass;

typedef enum {
	TYPE_BUILTIN_VOID,
	TYPE_BUILTIN_I32,
	TYPE_PTR,
	TYPE_REF,
} TypeKind;

struct Type {
	TypePass pass : 4 * 8;
	TypeKind kind : 4 * 8;
	union {
		TypeHandle ptr;
		TypeHandle ref;
	} as;
	struct {
		usize size;
		usize align;
	} evaluated;
};

typedef struct {
	Type ** data;
	usize size;
} TypeList;

Type * type_list_at(TypeList * list, usize index);
Type * type_list_add(VMemArena * arena, TypeList * list, Type type);

typedef struct {
	TypeList types;
	Type void_type;
	Type i32_type;
} TypeInternTable;

void type_intern_table_init(TypeInternTable * table);
Type * type_intern_table_ptr_to(VMemArena * arena, TypeInternTable * table,
								TypeHandle type);
Type * type_intern_table_ref_to(VMemArena * arena, TypeInternTable * table,
								TypeHandle type);
