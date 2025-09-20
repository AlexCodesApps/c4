#include "include/sema.h"
#include "include/eval.h"

void sema_ctx_init(SemaCtx * ctx, Ast * ast, VMemArena * arena,
				   TypeInternTable * table) {
	ctx->base = ast;
	ctx->arena = arena;
	ctx->table = table;
	ctx->visitor = visitor_state_new();
	vm_init(&ctx->vm);
}

bool sema_ctx_run(SemaCtx * ctx) {
	bool ok = true;
	for (usize i = 0; i < ctx->base->size; ++i) {
		Decl * decl = ast_at(ctx->base, i);
		switch (decl->kind) {
		case DECL_ERROR:
			continue;
		case DECL_FN:
			ok = ok && eval_fn(ctx, &decl->as.fn);
			break;
		case DECL_TYPE_ALIAS:
			ok = ok && eval_type_alias(ctx, &decl->as.alias);
			break;
		case DECL_VAR:
			ok = ok && eval_var(ctx, &decl->as.var);
			break;
		}
	}
	return ok;
}
