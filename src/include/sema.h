#pragma once
#include "ast.h"
#include "platform.h"
#include "type.h"
#include <setjmp.h>

typedef struct SemaCtx SemaCtx;
typedef struct VarEnv VarEnv;
typedef struct FnFrame FnFrame;
typedef struct FnScope FnScope;
typedef struct DeclNode DeclNode;

typedef struct {
	Decl ** decls;
	usize count;
	usize capacity;
} DeclPtrList;

struct DeclNode {
	Decl * decl;
	DeclNode * next;
};

bool decl_ptr_list_init(VMemArena * arena, DeclPtrList * list, usize capacity);
Decl ** decl_ptr_list_push(DeclPtrList * list);

struct FnScope {
	FnScope * parent;
	DeclNode * decls;
	DeclNode * end_decls;
};

struct FnFrame {
	TypeHandle return_ty;
	FnScope scope;
	bool is_const;
};

typedef enum {
	VAR_ENV_FN,
} VarEnvKind;

struct VarEnv {
	VarEnv * prev;
	VarEnvKind kind;
	union {
		FnFrame fn_frame;
	} as;
};

void fn_frame_init(FnFrame * frame, TypeHandle ty, bool is_const);
void fn_frame_push_decl(SemaCtx * ctx, FnFrame * frame, Decl * decl);
void fn_frame_push_scope(FnFrame * frame, FnScope * buf);
void fn_frame_pop_scope(SemaCtx * ctx, FnFrame * frame);
Decl * fn_frame_lookup_decl(FnFrame * frame, Iden iden, bool allow_non_const);

void var_env_push(SemaCtx * ctx, VarEnv * replace);
void var_env_pop(SemaCtx * ctx);
/* env can be null */
bool var_const_env(VarEnv * env);
/* env can be null */
Decl * var_env_lookup_decl(VarEnv * env, Iden iden, bool allow_non_const);

struct SemaCtx {
	VarEnv * env;
	Ast * base;
	TypeInternTable * table;
	VMemArena * arena;
	VisitorState visitor;
	Str src;
	Str path;
	jmp_buf oom_handler;
	struct {
		DeclNode * nodes;
	} free;
};

void sema_ctx_init(SemaCtx * ctx, Ast * ast, VMemArena * arena,
				   TypeInternTable * table, Str src, Str path);
NORETURN void sema_oom(SemaCtx * ctx);
NODISCARD bool sema_ctx_run(SemaCtx * ctx);
