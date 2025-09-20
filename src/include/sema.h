#pragma once
#include "ast.h"
#include "type.h"
#include "vm.h"

typedef struct {
	Ast * base;
	TypeInternTable * table;
	VMemArena * arena;
	VisitorState visitor;
	VM vm;
} SemaCtx;

void sema_ctx_init(SemaCtx * ctx, Ast * ast, VMemArena * arena,
				   TypeInternTable * table);
bool sema_ctx_run(SemaCtx * ctx);
