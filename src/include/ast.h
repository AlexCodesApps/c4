#pragma once
#include "common.h"
#include "i128.h"
#include "type.h"

typedef Str Iden;

typedef struct TypeSig TypeSig;
typedef struct TypeAlias TypeAlias;
typedef struct Decl Decl;

typedef enum {
	TYPE_SIG_PASS_ERROR,
	TYPE_SIG_PASS_PARSED,
	TYPE_SIG_PASS_CYCLE_CHECKED
} TypeSigPass;

typedef enum {
	TYPE_SIG_PTR,
	TYPE_SIG_REF,
	TYPE_SIG_IDEN,
	TYPE_SIG_VOID,
	TYPE_SIG_ALIAS_STUB,
} TypeSigKind;

typedef struct {
	TypeSig ** data;
	usize size;
} TypeSigList;

TypeSig * type_sig_list_at(TypeSigList * list, usize index);

struct TypeSig {
	TypeSigPass pass;
	TypeSigKind kind;
	bool is_mut : 1;
	union {
		TypeSig * ptr;
		TypeSig * ref;
		Iden iden;
		TypeAlias * alias_stub;
	} as;
};

TypeSig type_sig_ptr_from_ast(TypeSig * next);
TypeSig type_sig_ref_from_ast(TypeSig * next);
TypeSig type_sig_iden_from_ast(Iden iden);
void type_sig_set_mut(TypeSig * type);
TypeSig type_sig_void(void);
TypeSig type_sig_error(void);
void type_sig_set_error(TypeSig * type);
bool type_sig_is_error(const TypeSig * type);

typedef enum {
	EXPR_PASS_ERROR,
	EXPR_PASS_PARSED,
} ExprPass;

typedef enum {
	EXPR_INTEGER,
	EXPR_PLUS,
	EXPR_IDEN,
	EXPR_ADDR,
	EXPR_FUNCALL,
	EXPR_VOID,
} ExprKind;

typedef struct Expr Expr;

typedef struct {
	Expr ** data;
	usize size;
} ExprList;

Expr * expr_list_at(ExprList * list, usize index);

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
		struct {
			Expr * fun;
			ExprList args;
		} funcall;
	} as;
};

Expr expr_int_from_ast(I128 i);
Expr expr_plus_from_ast(Expr * a, Expr * b);
Expr expr_iden_from_ast(Iden iden);
Expr expr_addr_from_ast(Expr * next);
Expr expr_funcall_from_ast(Expr * fun, ExprList args);
Expr expr_void(void);
Expr expr_error(void);
void expr_set_error(Expr * expr);
bool expr_is_error(const Expr * expr);

typedef struct Stmt Stmt;

typedef struct {
	Stmt ** data;
	usize size;
} StmtList;
typedef StmtList StmtBlock;

Stmt * stmt_list_at(StmtList * list, usize index);

typedef enum {
	STMT_SEMICOLON,
	STMT_RETURN,
	STMT_EXPR,
	STMT_DECL,
	STMT_BLOCK,
} StmtKind;

struct Stmt {
	StmtKind kind;
	struct {
		Decl * decl;
		Expr expr;
		Expr return_;
		StmtList block;
	} as;
};

Stmt stmt_semicolon(void);
Stmt stmt_decl_from_ast(Decl * decl);
Stmt stmt_expr_from_ast(Expr expr);
Stmt stmt_return_from_ast(Expr expr);
Stmt stmt_block_from_ast(StmtBlock block);

typedef struct {
	TypeSig type;
	bool has_name;
	struct {
		Str name;
	} unwrap;
} Param;

typedef struct {
	Param ** data;
	usize size;
} ParamList;

Param * param_list_at(ParamList * list, usize index);

typedef enum {
	FN_PASS_ERROR,
	FN_PASS_PARSED,
} FnPass;

typedef struct {
	SrcSpan span;
	FnPass pass;
	bool is_const : 1;
	TypeSig return_ty;
	ParamList params;
	StmtBlock block;
} Fn;

Fn fn_from_ast(SrcSpan span, bool is_const, ParamList params, TypeSig return_ty,
			   StmtBlock block);
Fn fn_error(void);
void fn_set_error(Fn * fn);
bool fn_is_error(const Fn * fn);

typedef enum {
	VAR_PASS_ERROR,
	VAR_PASS_PARSED,
} VarPass;

typedef struct {
	SrcSpan span;
	VarPass pass;
	bool is_const : 1;
	bool is_mut : 1;
	bool has_expr : 1;
	TypeSig type;
	struct {
		Expr expr;
	} unwrap;
} Var;

Var var_from_ast(SrcSpan span, TypeSig type, bool is_const, bool is_mut,
				 const Expr * opt_expr);
Var var_error(void);
void var_set_error(Var * var);
bool var_is_error(const Var * var);

typedef enum {
	TYPE_ALIAS_PASS_ERROR,
	TYPE_ALIAS_PASS_PARSED,
	TYPE_ALIAS_PASS_CHECKING,
	TYPE_ALIAS_PASS_CHECKED,
} TypeAliasPass;

struct TypeAlias {
	SrcSpan span;
	TypeAliasPass pass;
	struct {
		TypeSig parsed;
		struct {
			TypeSig parsed;
			VisitIndex visit_index;
		} checking;
		TypeHandle checked;
	} as;
};

TypeAlias type_alias_from_ast(SrcSpan span, TypeSig type);
TypeAlias type_alias_error(void);
void type_alias_set_error(TypeAlias * alias);
void type_alias_set_checking(TypeAlias * alias, VisitIndex visit_index);
void type_alias_set_checked(TypeAlias * alias, TypeHandle type);
bool type_alias_is_error(const TypeAlias * alias);

typedef enum {
	DECL_ERROR,
	DECL_FN,
	DECL_VAR,
	DECL_TYPE_ALIAS,
} DeclKind;

struct Decl {
	DeclKind kind;
	Str iden;
	struct {
		Var var;
		TypeAlias alias;
		Fn fn;
	} as;
};

Decl decl_var_from_ast(Iden iden, Var var);
Decl decl_alias_from_ast(Iden iden, TypeAlias alias);
Decl decl_fn_from_ast(Iden iden, Fn fn);
Decl decl_error(void);
void decl_set_error(Decl * decl);
bool decl_is_error(const Decl * decl);

typedef struct {
	Decl ** data;
	usize size;
} Ast;

Decl * ast_at(Ast * ast, usize index);
