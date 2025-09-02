#pragma once
#include "common.h"
#include "lexer.h"

typedef struct Type Type;

typedef enum {
	TYPE_PASS_ERROR,
	TYPE_PASS_PARSED,
} TypePass;

typedef enum {
	TYPE_PTR,
	TYPE_REF,
	TYPE_IDEN,
} TypeType;

struct Type {
	TypePass pass;
	TypeType type;
	union {
		Type * ptr;
		Type * ref;
		Str iden;
	} as;
};

typedef struct {
	Str iden;
	SrcSpan span;

} TypeAlias;

typedef enum {
	VAR_PASS_ERROR,
	VAR_PASS_PARSED,
} VarPass;

typedef struct {
	VarPass pass;
	SrcSpan span;
	bool is_const : 1;
	bool is_mut: 1;
	Type type;
} Var;

typedef enum {
	DECL_ERROR,
	DECL_FN,
	DECL_VAR,
	DECL_TYPE_ALIAS,
} DeclType;

typedef struct {
	DeclType type;
	Str iden;
	struct {
		Var var;
	} as;
} Decl;

typedef struct {
	Decl ** data;
	usize size;
} Ast;

Decl * ast_at(Ast * ast, usize index);
