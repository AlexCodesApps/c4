#pragma once
#include "ast.h"
#include "platform.h"
#include "type.h"
#include <setjmp.h>

typedef struct Frame Frame;
struct Frame {
	Decl * decl;
	usize index;
};

typedef enum {
	EVAL_ENV_GLOBAL,
	EVAL_ENV_CONST_EVAL,
	EVAL_ENV_FN,
} EvalEnvKind;

typedef struct EvalEnv EvalEnv;
struct EvalEnv {
	EvalEnv * prev;
	EvalEnvKind kind;
	union {
		Ast * global;
		Frame frame;
	} as;
};

void eval_env_init(EvalEnv * env);

typedef struct {
	EvalEnv env;
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
bool sema_ctx_run(SemaCtx * ctx);
