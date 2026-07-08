#pragma once
#include "ast.h"
#include "platform.h"
#include "type.h"
#include <setjmp.h>

typedef struct VarEnv VarEnv;
typedef struct Frame Frame;

typedef struct {
	Decl ** decls;
	usize count;
	usize capacity;
} DeclPtrList;

bool decl_ptr_list_init(VMemArena * arena, DeclPtrList * list, usize capacity);
Decl ** decl_ptr_list_push(DeclPtrList * list);

struct Frame {
	VarEnv * parent;
	DeclPtrList list;
};

typedef enum {
	VAR_ENV_FN,
} VarEnvKind;

struct VarEnv {
	bool is_const;
	Frame frame;
};

bool var_env_init_scope(VMemArena * arena, VarEnv * env, VarEnv * parent,
						usize capacity, bool is_const);
bool var_env_push_decl(VarEnv * env, Decl * decl);
/* env can be null */
bool var_const_env(VarEnv * env);
/* env can be null */
Decl * var_env_lookup_decl(VarEnv * env, Iden iden);

typedef struct {
	VarEnv * env;
	Ast * base;
	TypeInternTable * table;
	VMemArena * arena;
	VisitorState visitor;
	Str src;
	Str path;
	jmp_buf oom_handler;
} SemaCtx;

void sema_ctx_init(SemaCtx * ctx, Ast * ast, VMemArena * arena,
				   TypeInternTable * table, Str src, Str path);
NORETURN void sema_oom(SemaCtx * ctx);
NODISCARD bool sema_ctx_run(SemaCtx * ctx);
