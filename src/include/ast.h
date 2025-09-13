#pragma once
#include "common.h"
#include "i128.h"

typedef Str Iden;

typedef struct Type Type;

typedef enum {
	TYPE_PASS_ERROR,
	TYPE_PASS_PARSED,
} TypePass;

typedef enum {
	TYPE_PTR,
	TYPE_REF,
	TYPE_IDEN,
} TypeKind;

struct Type {
	TypePass pass;
	TypeKind kind;
	union {
		Type * ptr;
		Type * ref;
		Iden iden;
	} as;
};

Type type_ptr_from_ast(Type * next);
Type type_ref_from_ast(Type * next);
Type type_iden_from_ast(Iden iden);
Type type_error();
void type_set_error(Type * type);
bool type_is_error(const Type * type);

typedef enum {
	EXPR_PASS_ERROR,
	EXPR_PASS_PARSED,
} ExprPass;

typedef enum {
	EXPR_INTEGER,
	EXPR_PLUS,
	EXPR_IDEN,
	EXPR_ADDR,
} ExprKind;

typedef struct Expr Expr;
struct Expr {
	ExprPass pass;
	ExprKind kind;
	struct {
		I128 integer;
		struct {
			Expr * a;
			Expr * b;
		} plus;
		Iden iden;
		Expr * addr;
	} as;
};

Expr expr_int_from_ast(I128 i);
Expr expr_plus_from_ast(Expr * a, Expr * b);
Expr expr_iden_from_ast(Iden iden);
Expr expr_addr_from_ast(Expr * next);
Expr expr_error();
void expr_set_error(Expr * expr);
bool expr_is_error(const Expr * expr);

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
	bool is_mut : 1;
	bool has_expr : 1;
	Type type;
	struct {
		Expr expr;
	} unwrap;
} Var;

Var var_from_ast(SrcSpan span, Type type, bool is_const, bool is_mut,
				 const Expr * opt_expr);
Var var_error();
void var_set_error(Var * var);
bool var_is_error(const Var * var);

typedef enum {
	DECL_ERROR,
	DECL_FN,
	DECL_VAR,
	DECL_TYPE_ALIAS,
} DeclKind;

typedef struct {
	DeclKind kind;
	Str iden;
	struct {
		Var var;
	} as;
} Decl;

Decl decl_var_from_ast(Str iden, Var var);
Decl decl_error();
void decl_set_error(Decl * decl);
bool decl_is_error(const Decl * decl);

typedef struct {
	Decl ** data;
	usize size;
} Ast;

Decl * ast_at(Ast * ast, usize index);
