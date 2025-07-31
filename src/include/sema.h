#pragma once
#include "ast.h"
#include "str.h"
#include "utility.h"

typedef struct SemaDeclNode SemaDeclNode;
typedef struct SemaVar SemaVar;
typedef struct SemaFn SemaFn;

typedef struct {
	SemaDeclNode * begin;
	SemaDeclNode * end;
} SemaDeclList;

typedef enum : u8 {
	SEMA_TYPE_I32,
	SEMA_TYPE_VOID,
	SEMA_TYPE_FN,
	SEMA_TYPE_TYPE_ALIAS, // temp graph node stuff
} SemaTypeType;

typedef struct SemaType SemaType;
typedef struct SemaTypeNode SemaTypeNode;
typedef struct SemaTypePtrNode SemaTypePtrNode;
typedef struct SemaTypeAlias SemaTypeAlias;

typedef enum : u8 {
	VISIT_STATUS_UNVISITED,
	VISIT_STATUS_VISITING,
	VISIT_STATUS_VISITED,
} VisitStatus;

typedef struct {
	SemaTypeNode * begin;
	SemaTypeNode * end;
} SemaTypeList;

typedef struct {
	SemaTypePtrNode * begin;
	SemaTypePtrNode * end;
	usize count;
} SemaTypePtrList;

typedef struct {
	SemaType * return_type;
	SemaTypePtrList params;
} SemaTypeFn;

struct SemaType {
	SemaTypeType type;
	VisitStatus visited;
	u32 visit_index;
	union {
		SemaTypeFn fn;
		SemaTypeAlias * alias;
	} as;
	struct {
		usize size; // computed when fully visited
		usize align;
	} unwrap;
};

struct SemaTypeNode {
	SemaType type;
	SemaTypeNode * next;
};

struct SemaTypePtrNode {
	SemaType * type;
	SemaTypePtrNode * next;
};

typedef enum {
	SEMA_EXPR_VOID,
	SEMA_EXPR_I32,
	SEMA_EXPR_FN,
	SEMA_EXPR_FUNCALL,
	SEMA_EXPR_PLUS,
	SEMA_EXPR_VAR,
} SemaExprType;

typedef struct SemaExpr SemaExpr;
typedef struct SemaExprNode SemaExprNode;

typedef struct {
	SemaExprNode * begin;
	SemaExprNode * end;
	usize count;
} SemaExprList;

typedef struct {
	SemaExpr * fun;
	SemaExprList args;
} SemaExprFunCall;

struct SemaExpr {
	SemaExprType type;
	bool visited_by_cnst_expr_reducer;
	union {
		struct {
			SemaExpr * a;
			SemaExpr * b;
		} plus;
		i32 i32;
		SemaVar * var;
		SemaExprFunCall funcall;
		SemaFn * fn;
	} as;
};

struct SemaExprNode {
	SemaExpr expr;
	SemaExprNode * next;
};

typedef struct SemaStmtNode SemaStmtNode;

typedef struct {
	SemaStmtNode * begin;
	SemaStmtNode * end;
} SemaStmtList;

typedef enum {
	SEMA_STMT_EXPR,
	SEMA_STMT_RETURN,
	SEMA_STMT_BLOCK,
} SemaStmtType;

typedef struct SemaBlkEnv SemaBlkEnv;
struct SemaBlkEnv {
	SemaType * return_type;
	SemaBlkEnv * parent;
	SemaDeclList variables;
	SemaStmtList block;
};

typedef struct {
	SemaStmtType type;
	union {
		SemaExpr expr;
		SemaExpr return_;
		SemaBlkEnv block;
	} as;
} SemaStmt;

struct SemaStmtNode {
	SemaStmt stmt;
	SemaStmtNode * next;
};

struct SemaFn {
	bool has_sema;
	struct {
		SemaTypeFn * signature;
		Str * args; // length is length of signature arg list
		bool implemented;
		struct {
			SemaBlkEnv body;
		} unwrap;
	} sema;
	const Fn * ast;
};

struct SemaTypeAlias {
	bool has_sema;
	struct {
		SemaType * aliasing;
	} sema;
	const TypeAlias * ast;
};

struct SemaVar {
	bool has_sema;
	bool global;
	VisitStatus visit_status;
	usize visit_index;
	struct {
		bool init_with_expr;
		SemaType * type;
		struct {
			SemaExpr expr;
		} unwrap;
	} sema;
	const Var * ast;
};

typedef enum {
	SEMA_DECL_FN,
	SEMA_DECL_TYPE_ALIAS,
	SEMA_DECL_VAR,
} SemaDeclType;

typedef struct SemaDecl {
	SemaDeclType type;
	Str iden;
	union {
		SemaFn fn;
		SemaTypeAlias alias;
		SemaType type;
		SemaVar var;
	} as;
} SemaDecl;

struct SemaDeclNode {
	SemaDecl decl;
	SemaDeclNode * next;
};

typedef struct SemaCtx SemaCtx;

typedef struct {
	SemaType * (*type_callback)(SemaCtx * ctx, void * payload, Str iden, ReportError report_error);
	SemaVar * (*var_callback)(SemaCtx * ctx, void * payload, Str iden, ReportError report_error);
	SemaFn * (*fn_callback)(SemaCtx * ctx, void * payload, Str iden, ReportError report_error);
	void * payload;
} SemaDeclLookupStrategy;

typedef struct {
	SemaType void_type;
	SemaType i32_type;
	SemaTypeList types;
	SemaTypePtrNode * tpnl_free_list; // deduped function types have their param list nodes saved for reuse
} SemaTypeInternTable;

struct SemaCtx {
	SemaTypeInternTable * table;
	SemaDeclList * env;
	VMemArena * arena;
	SemaDeclLookupStrategy lookup_strategy;
};

void sema_type_intern_table_init(SemaTypeInternTable * table);
void sema_ctx_init(SemaCtx * ctx, VMemArena * arena, SemaTypeInternTable * table, SemaDeclList * env);
SemaType * sema_ctx_lookup_type(SemaCtx * ctx, Str iden, ReportError report_error);
SemaVar * sema_ctx_lookup_var(SemaCtx * ctx, Str iden, ReportError report_error);
SemaFn * sema_ctx_lookup_fn(SemaCtx * ctx, Str iden, ReportError report_error);
bool sema_analyze_ast(SemaCtx * ctx, Ast ast);
void sema_type_list_init(SemaTypeList * list);
SemaType * sema_type_list_push_front(VMemArena * arena, SemaTypeList * list, SemaType type);
void sema_type_ptr_list_init(SemaTypePtrList * list);
void sema_type_ptr_list_push_node(SemaTypePtrList * list, SemaType * type, SemaTypePtrNode * node);
bool sema_type_ptr_list_push(VMemArena * arena, SemaTypePtrList * list, SemaType * type);
void sema_type_ptr_list_push_node_front(SemaTypePtrList * list, SemaType * type, SemaTypePtrNode * node);
bool sema_type_ptr_list_push_front(VMemArena * arena, SemaTypePtrList * list, SemaType * type);
void sema_type_ptr_list_pop_front(SemaTypePtrList * list);
void sema_expr_list_init(SemaExprList * list);
SemaExpr * sema_expr_list_push(VMemArena * arena, SemaExprList * list, SemaExpr expr);
void sema_stmt_list_init(SemaStmtList * list);
SemaStmt * sema_stmt_list_push(VMemArena * arena, SemaStmtList * list, SemaStmt stmt);
void sema_decl_list_init(SemaDeclList * list);
SemaDecl * sema_decl_list_push(VMemArena * arena, SemaDeclList * list, SemaDecl decl);
