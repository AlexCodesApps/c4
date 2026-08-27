#pragma once
#include "common.h"
#include "i128.h"
#include "type.h"

typedef Str Iden;

typedef struct TypeSig TypeSig;
typedef struct TypeAlias TypeAlias;
typedef struct Decl Decl;
typedef struct Var Var;

typedef enum {
	TYPE_SIG_PASS_ERROR,
	TYPE_SIG_PASS_PARSED,
	TYPE_SIG_PASS_CYCLE_CHECKED
} TypeSigPass;

typedef struct {
	TypeSig ** data;
	usize size;
} TypeSigList;

TypeSig * type_sig_list_at(TypeSigList * list, usize index);

typedef struct FnTypeSig {
	TypeSig * return_ty;
	TypeSigList params;
} FnTypeSig;

typedef enum {
	TYPE_SIG_PTR,
	TYPE_SIG_REF,
	TYPE_SIG_IDEN,
	TYPE_SIG_VOID,
	TYPE_SIG_FN,
	TYPE_SIG_ALIAS_STUB,
	TYPE_SIG_TYPE_STUB,
} TypeSigKind;

struct TypeSig {
	SrcSpan span;
	TypeSigPass pass;
	TypeSigKind kind;
	bool is_mut : 1;
	union {
		TypeSig * ptr_like;
		FnTypeSig fn;
		Iden iden;
		TypeAlias * alias_stub;
		Type * type_stub;
	} as;
};

TypeSig type_sig_ptr_from_ast(SrcSpan span, TypeSig * next);
TypeSig type_sig_ref_from_ast(SrcSpan span, TypeSig * next);
TypeSig type_sig_fn_from_ast(SrcSpan span, TypeSig * return_ty,
							 TypeSigList params);
TypeSig type_sig_iden_from_ast(SrcSpan span, Iden iden);
void type_sig_set_mut(TypeSig * type);
TypeSig type_sig_void(SrcSpan span);
TypeSig type_sig_error(void);
void type_sig_set_error(TypeSig * type);
bool type_sig_is_error(const TypeSig * type);

typedef enum {
	EXPR_PASS_ERROR,
	EXPR_PASS_PARSED,
	EXPR_PASS_EVALLED,
} ExprPass;

typedef struct {
	union {
		I128 integer;
		u8 * aggregate;
	} as;
} ConstValue;

typedef enum {
	EXPR_INTEGER,
	EXPR_PLUS,
	EXPR_IDEN,
	EXPR_ADDR,
	EXPR_DEREF,
	EXPR_FUNCALL,
	EXPR_NULLPTR,
	EXPR_VOID,
} ExprKind;

typedef enum {
	EXPR_SEMA_INTEGER,
	EXPR_SEMA_PLUS,
	EXPR_SEMA_LOAD_PTR,
	EXPR_SEMA_DEREF,
	EXPR_SEMA_FUNCALL,
	EXPR_SEMA_NULLPTR,
	EXPR_SEMA_VOID,
} ExprSemaKind;

typedef struct Expr Expr;

typedef struct {
	Expr ** data;
	usize size;
} ExprList;

Expr * expr_list_at(ExprList * list, usize index);

struct Expr {
	ExprPass pass;
	union {
		ExprKind kind;
		ExprSemaKind sema_kind;
	};
	SrcSpan span;
	union {
		union {
			Iden iden;
			Expr * addr;
			Expr * deref;
		} parsed;
		I128 integer;
		struct {
			Expr * a;
			Expr * b;
		} plus;
		struct {
			Expr * fun;
			ExprList args;
		} funcall;
		struct {
			Decl * load_ptr;
			Expr * deref;
		} sema;
	} as;
};

Expr expr_int_from_ast(SrcSpan span, I128 i);
Expr expr_plus_from_ast(SrcSpan span, Expr * a, Expr * b);
Expr expr_iden_from_ast(SrcSpan span, Iden iden);
Expr expr_addr_from_ast(SrcSpan span, Expr * next);
Expr expr_deref_from_ast(SrcSpan span, Expr * next);
Expr expr_funcall_from_ast(SrcSpan span, Expr * fun, ExprList args);
Expr expr_nullptr(SrcSpan span);
Expr expr_void(SrcSpan span);
Expr expr_error(void);
void expr_set_error(Expr * expr);
bool expr_is_error(const Expr * expr);
TypeHandle expr_evalled_type(const Expr * expr);

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
	union {
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
	FN_PASS_PROTO_CHECKING,
	FN_PASS_PROTO_CHECKED,
	FN_PASS_PROTO,
	FN_PASS_EVAL,
} FnPass;

typedef struct {
	bool is_const : 1;
	TypeSig return_ty;
	ParamList params;
} ParsedFnProto;

typedef struct {
	SrcSpan span;
	FnPass pass;
	ParsedFnProto proto;
	union {
		VisitIndex checking;
		TypeHandle proto;
	} as;
	StmtBlock block;
} Fn;

Fn fn_from_ast(SrcSpan span, bool is_const, ParamList params, TypeSig return_ty,
			   StmtBlock block);
bool fn_is_const(const Fn * fn);
void fn_set_pass_proto_checking(Fn * fn, VisitIndex idx);
void fn_set_pass_proto_checked(Fn * fn);
void fn_set_pass_proto(Fn * fn, TypeHandle type);
Fn fn_error(void);
void fn_set_error(Fn * fn);
bool fn_is_error(const Fn * fn);

typedef enum {
	VAR_MUT_MUT,   // mutable runtime variable
	VAR_MUT_LET,   // runtime constant
	VAR_MUT_CONST, // compile time constant
} VarMutability;

typedef enum {
	VAR_PASS_ERROR,
	VAR_PASS_PARSED,
	VAR_PASS_DECL_CYCLE_CHECKING,
	VAR_PASS_DECL_CYCLE_CHECKED,
	VAR_PASS_DECL_EVALUATED,
	VAR_PASS_EXPR_CYCLE_CHECKING,
	VAR_PASS_EXPR_EVALUATED,
} VarPass;

typedef struct {
	bool is_const : 1;
	bool is_mut : 1;
	bool has_expr : 1;
	TypeSig type;
	struct {
		Expr expr;
	} unwrap;
} ParsedVar;

typedef struct {
	VarMutability mutability;
	bool has_expr;
	TypeHandle type;
	struct {
		Expr expr;
	} unwrap;
} DeclEvalVar;

struct Var {
	SrcSpan span;
	VarPass pass;
	union {
		ParsedVar parsed;
		struct {
			ParsedVar parsed;
			VisitIndex id;
		} checking_decl;
		ParsedVar checked_decl;
		DeclEvalVar decl_evalled;
		struct {
			DeclEvalVar decl_evalled;
			VisitIndex id;
		} checking_expr;
		DeclEvalVar evalled;
	} as;
};

Var var_from_ast(SrcSpan span, TypeSig type, bool is_const, bool is_mut,
				 const Expr * opt_expr);
Var var_error(void);
void var_set_decl_checking(Var * var, VisitIndex id);
void var_set_decl_checked(Var * var);
void var_set_decl_evalled(Var * var, VarMutability mut, TypeHandle type);
void var_set_expr_checking(Var * var, VisitIndex id);
void var_set_expr_evalled(Var * var);
void var_set_error(Var * var);
bool var_is_error(const Var * var);

typedef enum {
	TYPE_ALIAS_PASS_ERROR,
	TYPE_ALIAS_PASS_PARSED,
	TYPE_ALIAS_PASS_CHECKING,
	TYPE_ALIAS_PASS_CHECKED,
	TYPE_ALIAS_PASS_EVALUATED,
} TypeAliasPass;

struct TypeAlias {
	SrcSpan span;
	TypeAliasPass pass;
	union {
		TypeSig parsed;
		struct {
			TypeSig parsed;
			VisitIndex visit_index;
		} checking;
		TypeSig checked;
		TypeHandle evalled;
	} as;
};

TypeAlias type_alias_from_ast(SrcSpan span, TypeSig type);
TypeAlias type_alias_error(void);
void type_alias_set_error(TypeAlias * alias);
void type_alias_set_checking(TypeAlias * alias, VisitIndex visit_index);
void type_alias_set_checked(TypeAlias * alias);
void type_alias_set_evalled(TypeAlias * alias, TypeHandle handle);
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
	union {
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
