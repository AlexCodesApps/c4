#pragma once

#include "lexer.h"
#include "arena.h"

typedef enum {
	TYPE_VOID,
	TYPE_IDEN,
	TYPE_FN,
} TypeType;

typedef struct Type Type;
typedef struct TypeNode TypeNode;
typedef struct {
	TypeNode * begin;
	TypeNode * end;
} TypeList;

typedef struct {
	Type * return_type;
	TypeList params;
} TypeFn;

struct Type {
	TypeType type;
	union {
		Str iden;
		TypeFn fn;
	} as;
};

struct TypeNode {
	Type type;
	TypeNode * next;
};

typedef enum {
	EXPR_INT,
	EXPR_IDEN,
	EXPR_FUNCALL,
	EXPR_PLUS,
} ExprType;

typedef struct Expr Expr;
typedef struct ExprNode ExprNode;

typedef struct {
	ExprNode * begin;
	ExprNode * end;
} ExprList;

typedef struct {
	const Expr * fun;
	ExprList args;
} ExprFuncall;

typedef struct {
	const Expr * a;
	const Expr * b;
} ExprPlus;

struct Expr {
	ExprType type;
	union {
		usize int_;
		Str iden;
		ExprPlus plus;
		ExprFuncall funcall;
	} as;
};

extern const Expr poisoned_expr;

struct ExprNode {
	const Expr * expr;
	ExprNode * next;
};

typedef enum {
	STMT_SEMICOLON,
	STMT_RETURN,
	STMT_EXPR,
	STMT_BLOCK,
} StmtType;

typedef struct {
	bool has_expr;
	struct {
		const Expr * expr;
	} unwrap;
} StmtReturn;

typedef struct StmtNode StmtNode;
typedef struct {
	StmtNode * begin;
	StmtNode * end;
} StmtList;

typedef struct {
	StmtType type;
	union {
		StmtReturn return_;
		const Expr * expr;
		StmtList block;
	} as;
} Stmt;

struct StmtNode {
	Stmt stmt;
	StmtNode * next;
};

typedef struct {
	bool has_iden;
	struct {
		Str iden;
	} unwrap;
	Type type;
} FnParam;

typedef struct FnParamNode FnParamNode;

typedef struct {
	FnParamNode * begin;
	FnParamNode * end;
} FnParamList;

extern const FnParamList poisoned_fn_param_list;

struct FnParamNode {
	FnParam param;
	FnParamNode * next;
};

typedef struct {
	Str iden;
	Type return_type;
	const FnParamList * params;
	StmtList body;
} Fn;

typedef struct {
	Str iden;
	Type type;
} TypeAlias;

typedef struct {
	bool init_with_expr;
	Str iden;
	Type type;
	struct {
		const Expr * expr;
	} unwrap;
} Var;

typedef enum {
	DECL_POISONED,
	DECL_FN,
	DECL_TYPE_ALIAS,
	DECL_VAR,
} DeclType;

typedef struct Decl Decl;
typedef struct DeclNode DeclNode;

typedef struct {
	DeclNode * begin;
	DeclNode * end;
} DeclList;

struct Decl {
	DeclType type;
	union {
		TypeAlias alias;
		Fn fn;
		Var var;
	} as;
};

struct DeclNode {
	Decl decl;
	DeclNode * next;
};

typedef DeclList Ast;

typedef struct {
	VMemArena * arena;
	Lexer lexer;
	Token current;
	Token next;
	bool panic_mode;
	bool had_error;
} Parser;

void parser_init(Parser * parser, Str src, VMemArena * arena);
Ast parser_run(Parser * parser);

void type_list_init(TypeList * list);
bool type_list_push(VMemArena * arena, TypeList * list, Type type);
void expr_list_init(ExprList * list);
bool expr_list_push(VMemArena * arena, ExprList * list, const Expr * expr);
void stmt_list_init(StmtList * list);
bool stmt_list_push(VMemArena * arena, StmtList * list, Stmt stmt);
void fn_param_list_init(FnParamList * list);
bool fn_param_list_push(VMemArena * arena, FnParamList * list, FnParam param);
void decl_list_init(DeclList * list);
bool decl_list_push(VMemArena * arena, DeclList * list, Decl decl);
