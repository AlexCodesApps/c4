#pragma once
#include "ast.h"
#include "str.h"
#include "utility.h"
#include "common.h"
#include "ir.h"
#include <setjmp.h>
#include <stdio.h>

typedef struct SemaDeclNode SemaDeclNode;
typedef struct SemaVar SemaVar;
typedef struct SemaFn SemaFn;
typedef struct SemaDecl SemaDecl;
typedef struct SemaType SemaType;
typedef struct SemaTypeNode SemaTypeNode;
typedef struct SemaTypeHandleNode SemaTypeHandleNode;
typedef struct SemaTypeAlias SemaTypeAlias;
typedef struct SemaValue SemaValue;

// The semantic analyzer is planned to have the various components in stages of declaration
// These stages are transitioned lazily by need, but are forced evaluated before ending semantic analysis
// The main purposes of these stages is to enforce state invariants cleanly in a way that some dodgy passes
// can't, and to make compile time function evaluation very natural and flow with the rest of the code

typedef enum : u8 {
	SEMA_PASS_ERROR, // signifies that the object isn't in a valid state
	SEMA_PASS_AST, // signifies that the object is an AST stub
	SEMA_PASS_CYCLE_UNCHECKED, // signifies that the object has been filled with a workable sema node
	SEMA_PASS_CYCLE_CHECKING, // signifies that the object is getting visited and may be involved in a cycle
	SEMA_PASS_CYCLE_CHECKED, // signifies that the object has been cleared for no cycles
	SEMA_PASS_IMPLEMENTED, // signifies that the object is in its final implemented form
} SemaPass;

typedef struct {
	SemaDeclNode * begin;
	SemaDeclNode * end;
	usize count;
} SemaDeclList;

typedef enum : u8 {
	SEMA_TYPE_I32,
	SEMA_TYPE_VOID,
	SEMA_TYPE_FN,
	SEMA_TYPE_TYPE_ALIAS, // temp graph node stuff
	SEMA_TYPE_PTR,
	SEMA_TYPE_REF,
} SemaTypeType;

typedef struct {
	SemaType * type;
	bool is_mut: 1;
	bool is_lvalue: 1;
} SemaTypeHandle;

typedef struct {
	SemaTypeNode * begin;
	SemaTypeNode * end;
} SemaTypeList;

typedef struct {
	SemaTypeHandleNode * begin;
	SemaTypeHandleNode * end;
	usize count;
} SemaTypeHandleList;

typedef struct {
	SemaType * return_type;
	SemaTypeHandleList params;
} SemaTypeFn;

struct SemaType {
	SemaTypeType type;
	SemaPass pass;
	bool deduped: 1;
	u32 visit_index;
	union {
		SemaTypeFn fn;
		SemaTypeAlias * alias;
		SemaTypeHandle ptr;
		SemaTypeHandle ref;
	} as;
	struct {
		usize size; // computed when fully visited
		usize align;
	} impled;
};

struct SemaTypeNode {
	SemaType type;
	SemaTypeNode * next;
};

struct SemaTypeHandleNode {
	SemaTypeHandle type;
	SemaTypeHandleNode * next;
};

typedef enum {
	SEMA_EXPR1_VOID,
	SEMA_EXPR1_NULLPTR,
	SEMA_EXPR1_I32,
	SEMA_EXPR1_FN,
	SEMA_EXPR1_FUNCALL,
	SEMA_EXPR1_ADDR,
	SEMA_EXPR1_PLUS,
	SEMA_EXPR1_VAR,
	SEMA_EXPR1_DEREF,
} SemaExpr1Type;

typedef enum {
	SEMA_EXPR2_VALUE,
	SEMA_EXPR2_FUNCALL,
	SEMA_EXPR2_DEREF,
	SEMA_EXPR2_ADD_I32,
	SEMA_EXPR2_LOAD_VAR,
} SemaExpr2Type;

typedef struct SemaExpr SemaExpr;
typedef struct SemaExprNode SemaExprNode;

typedef enum {
	SEMA_VALUE_NULLPTR,
	SEMA_VALUE_VOID,
	SEMA_VALUE_I32,
	SEMA_VALUE_FN,
	SEMA_VALUE_RAW_PTR,
	SEMA_VALUE_RAW_REF,
	SEMA_VALUE_VAR_PTR,
	SEMA_VALUE_VAR_REF,
} SemaValueType;

struct SemaValue { // aka Comptime Expressions
	SemaValueType type;
	union {
		i32 i32;
		SemaFn * fn;
		struct {
			usize value;
			SemaTypeHandle to;
		} raw_ptr;
		struct {
			usize value;
			SemaTypeHandle to;
		} raw_ref;
		SemaVar * var_ptr;
		SemaVar * var_ref;
	} as;
};

typedef struct {
	SemaExprNode * begin;
	SemaExprNode * end;
	usize count;
} SemaExprList;

typedef struct {
	SemaExpr * data;
	usize size;
} SemaExprFunCallArgs;

typedef struct {
	SemaExpr * fun;
	SemaExprFunCallArgs args;
	SemaTypeHandle fn_type; // only after implementation
} SemaExprFunCall;

struct SemaExpr {
	SemaPass pass;
	union {
		SemaExpr1Type type1; // unimplemented
		SemaExpr2Type type2; // implemented
	};
	union {
		const Expr * ast;
		union {
			i32 i32;
			struct {
				SemaExpr * a;
				SemaExpr * b;
			} plus;
			SemaVar * var;
			SemaExprFunCall funcall;
			SemaFn * fn;
			SemaExpr * addr;
			SemaExpr * deref;
		} sema1;
		union {
			SemaValue value;
			struct {
				SemaExpr * a;
				SemaExpr * b;
			} add;
			SemaExprFunCall funcall;
			SemaExpr * deref;
			SemaVar * load_var;
		} sema2;
	} as;
};

struct SemaExprNode {
	SemaExpr expr;
	SemaExprNode * next;
};

typedef enum {
	EXPR_EVAL_ERROR = 0, // error occured
	EXPR_EVAL_UNREDUCED, // was not able to evaluate at compile time
	EXPR_EVAL_REDUCED,  // was able to evaluate at compile time
} ExprEvalResult;

typedef struct SemaStmtNode SemaStmtNode;

typedef struct {
	SemaStmtNode * begin;
	SemaStmtNode * end;
} SemaStmtList;

typedef enum {
	SEMA_ENV_MOD,
	SEMA_ENV_FN_BLK,
} SemaEnvType;

typedef struct SemaEnv SemaEnv;
struct SemaEnv {
	SemaEnv * parent;
	SemaDeclList decls;
	SemaEnvType type;
	usize sym_count;
	union {
		struct {
			SemaType * return_type;
			SemaStmtList block;
		} fn;
	} as;
};

typedef enum {
	SEMA_STMT_EXPR,
	SEMA_STMT_RETURN,
	SEMA_STMT_BLOCK,
} SemaStmtType;

typedef struct {
	SemaStmtType type;
	union {
		SemaExpr expr;
		SemaExpr return_;
		SemaEnv block;
	} as;
} SemaStmt;

struct SemaStmtNode {
	SemaStmt stmt;
	SemaStmtNode * next;
};

struct SemaFn {
	// maybe excessive bit packing...
	SemaPass pass : 4;
	enum {
		SEMA_FN_UNEMMITED,
		SEMA_FN_EMMITING,
		SEMA_FN_EMMITED,
	} emmiting : 2; // to avoid excessive reimplementing
	bool is_const: 1;
	struct {
		SemaTypeFn * signature;
		Str * args; // length is length of signature arg list
		struct {
			IrFn fn;
		} unwrap;
	} sema;
	const Fn * ast;
};

struct SemaTypeAlias {
	SemaPass pass;
	struct {
		SemaTypeHandle next;
	} sema;
	const TypeAlias * ast;
};

struct SemaVar {
	bool is_global:  1;
	bool is_const: 1;
	u32 visit_index;
	SemaPass pass;
	union {
		struct {
			bool init_with_expr;
			SemaTypeHandle type;
			struct {
				SemaExpr expr;
			} unwrap;
		} sema;
		const Var * ast;
	} as;
};

typedef enum {
	SEMA_DECL_FN,
	SEMA_DECL_TYPE_ALIAS,
	SEMA_DECL_VAR,
} SemaDeclType;

typedef u32 LocalSymbolIndex;
#define LOCAL_SYMBOL_INDEX_MAX UINT32_MAX

typedef struct {
	bool local;
	SemaFn * fn;
	LocalSymbolIndex index;
} SymbolPos;

typedef struct SemaDecl {
	SemaDeclType type;
	SymbolPos pos;
	Str iden;
	union {
		SemaFn fn;
		SemaTypeAlias alias;
		SemaVar var;

	} as;
} SemaDecl;

struct SemaDeclNode {
	SemaDecl decl;
	SemaDeclNode * next;
};

typedef struct SemaCtx SemaCtx;

typedef struct {
	SemaType void_type;
	SemaType i32_type;
	SemaType void_ptr_type;
	SemaTypeList types;
	SemaTypeHandleList complete_types;
	SemaTypeHandleNode * tpnl_free_list; // deduped function types have their param list nodes saved for reuse
} SemaTypeInternTable;

typedef struct SemaTypePtrPtrNode SemaTypePtrPtrNode;
struct SemaTypePtrPtrNode {
	SemaType ** payload;
	SemaTypePtrPtrNode * next;
};

typedef struct SemaFnPtrNode SemaFnPtrNode;
struct SemaFnPtrNode {
	SemaFn * payload;
	SemaFnPtrNode * next;
};

struct SemaCtx {
	SemaTypeInternTable * table;
	VMemArena * arena;
	SemaEnv * root;
	SemaEnv * env;
	SemaTypePtrPtrNode * free_type_ptrs;
	SemaFnPtrNode * free_fn_ptrs;
	jmp_buf oom_handler;
};

// initializers
void sema_type_init_uninterned(SemaType * type, SemaTypeType typetype);
void sema_value_init(SemaValue * value, SemaValueType type);
void sema_expr_init_implemented(SemaExpr * expr, SemaExpr2Type type);
void sema_expr_init_unimplemented(SemaExpr * expr, SemaExpr1Type type);
void sema_expr_init_with_ast(SemaExpr * expr, const Expr * ast);
void sema_stmt_init(SemaStmt * stmt, SemaStmtType type);
void sema_var_init_with_ast(SemaVar * var, const Var * ast, bool global);
void sema_var_init(SemaVar * var, SemaTypeHandle type, SemaExpr * opt_expr, bool global, bool is_const);
void sema_fn_init(SemaFn * fn, SemaTypeFn * sig, Str * args, bool is_const);
void sema_fn_init_with_ast(SemaFn * fn, const Fn * ast);
SymbolPos symbol_pos_global(void);
SymbolPos symbol_pos_local(SemaFn * fn, LocalSymbolIndex index);
void sema_decl_init(SemaDecl * decl, SemaDeclType type, SymbolPos pos, Str iden);

// mostly ctx functions
SemaDecl * sema_ctx_add_decl(SemaCtx * ctx, SemaDecl decl);
void sema_ctx_init(SemaCtx * ctx, VMemArena * arena, SemaTypeInternTable * table, SemaEnv * env);
SemaTypeHandle sema_ctx_lookup_type(SemaCtx * ctx, Str iden, ReportError report_error);
SemaVar * sema_ctx_lookup_var(SemaCtx * ctx, Str iden, ReportError report_error);
SemaFn * sema_ctx_lookup_fn(SemaCtx * ctx, Str iden, ReportError report_error);
bool sema_ctx_is_global_scope(SemaCtx * ctx);
bool sema_ctx_is_fn_local(SemaCtx * ctx);
_Noreturn void sema_ctx_oom(SemaCtx * ctx);

bool sema_analyze_ast(SemaCtx * ctx, Ast ast);
SemaTypeHandle sema_type_handle_from_ptr(SemaType * type);
bool coerce_expr_to_type(SemaCtx * ctx, SemaExpr * expr, SemaTypeHandle expr_type, SemaTypeHandle target_type);

// declaration pass functions
bool ensure_type_alias_is_cycle_checked(SemaCtx * ctx, VisitorState visitor, SemaTypeAlias * alias);
bool ensure_expr_is_cycle_checked(SemaCtx * ctx, VisitorState visitor, SemaExpr * expr);
bool ensure_var_is_cycle_checked(SemaCtx * ctx, VisitorState visitor, SemaVar * var);
bool ensure_fn_is_cycle_checked(SemaCtx * ctx, VisitorState visitor, SemaFn * fn);
// Ensure the tree is implemented, typechecked and ready for lowering
bool ensure_type_handle_is_implemented(SemaCtx * ctx, VisitorState visitor, SemaTypeHandle * out_handle);
bool ensure_type_ptr_is_implemented(SemaCtx * ctx, VisitorState visitor, SemaType ** type);
bool ensure_type_alias_is_implemented(SemaCtx * ctx, VisitorState visitor, SemaTypeAlias * alias);
ExprEvalResult ensure_expr_is_implemented(SemaCtx * ctx, VisitorState visitor, SemaExpr * expr, SemaTypeHandle * opt_out);
bool ensure_var_is_implemented(SemaCtx * ctx, VisitorState visitor, SemaVar * var);
bool ensure_fn_is_implemented(SemaCtx * ctx, VisitorState visitor, SemaFn * fn);
bool ensure_decl_is_implemented(SemaCtx * ctx, VisitorState visitor, SemaDecl * decl);

SemaType * sema_type_from_interned_fn(SemaTypeFn * fn);
void sema_env_init_push_fn_blk_env(SemaCtx * ctx, SemaEnv * env, SemaType * return_type);
void sema_env_pop(SemaCtx * ctx);

void sema_print_type(FILE * file, SemaTypeHandle type);
void sema_type_intern_table_init(SemaTypeInternTable * table);
void sema_env_init(SemaEnv * env);

// lists, lists, and more lists
void sema_type_list_init(SemaTypeList * list);
SemaType * sema_type_list_push_front(VMemArena * arena, SemaTypeList * list, SemaType type);
void sema_type_handle_list_init(SemaTypeHandleList * list);
void sema_type_handle_list_push_node(SemaTypeHandleList * list, SemaTypeHandle type, SemaTypeHandleNode * node);
bool sema_type_handle_list_push(VMemArena * arena, SemaTypeHandleList * list, SemaTypeHandle type);
void sema_type_handle_list_push_node_front(SemaTypeHandleList * list, SemaTypeHandle type, SemaTypeHandleNode * node);
bool sema_type_handle_list_push_front(VMemArena * arena, SemaTypeHandleList * list, SemaTypeHandle type);
void sema_type_handle_list_pop_front(SemaTypeHandleList * list);
void sema_expr_list_init(SemaExprList * list);
SemaExpr * sema_expr_list_push(VMemArena * arena, SemaExprList * list, SemaExpr expr);
void sema_stmt_list_init(SemaStmtList * list);
SemaStmt * sema_stmt_list_push(VMemArena * arena, SemaStmtList * list, SemaStmt stmt);
void sema_decl_list_init(SemaDeclList * list);
SemaDecl * sema_decl_list_push(VMemArena * arena, SemaDeclList * list, SemaDecl decl);
