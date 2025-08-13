#include "include/ir.h"
#include "include/sema.h"
#include <stddef.h>
#include <assert.h>

typedef struct {
	SemaFnPtrNode * head;
	SemaFnPtrNode * tail;
} FnWorkStack;

typedef struct {
	SemaCtx * sema_ctx;
	SemaFn * fn;
	FnWorkStack * stack;
	VisitorState visitor;
} FnCompletionCtx;

bool fn_work_stack_push(SemaCtx * ctx, FnWorkStack * stack, SemaFn * ptr) {
	SemaFnPtrNode * node;
	if (ctx->free_fn_ptrs) {
		node = ctx->free_fn_ptrs;
		ctx->free_fn_ptrs = node->next;
	} else {
		node = vmem_arena_alloc(ctx->arena, SemaFnPtrNode);
		if (!node) {
			return false;
		}
	}
	node->next = stack->head;
	node->payload = ptr;
	if (!stack->tail) {
		stack->tail = node;
	}
	stack->head = node;
	return true;
}

void fn_work_stack_pop(SemaCtx * ctx, FnWorkStack * stack, SemaFn ** out) {
	SemaFnPtrNode * node = stack->head;
	if (out) {
		*out = node->payload;
	}
	stack->head = node->next;
	if (stack->tail == node) {
		stack->tail = nullptr;
	}
	node->next = ctx->free_fn_ptrs;
	ctx->free_fn_ptrs = node;
}

void fn_work_stack_free(SemaCtx  * ctx, FnWorkStack * stack) {
	if (!stack->tail) {
		return;
	}
	stack->tail = ctx->free_fn_ptrs;
	ctx->free_fn_ptrs = stack->head;
}

static void emit_byte(SemaCtx * ctx, IrFn * fn, u8 byte) {
	if (fn->count == fn->capacity) {
		usize new_cap = (fn->capacity + 1) * 2;
		u8 * new_array = vmem_arena_alloc_n(ctx->arena, u8, new_cap);
		if (!new_array) {
			sema_ctx_oom(ctx);
		}
		memcpy(new_array, fn->code, fn->count);
		fn->code = new_array;
		fn->capacity = new_cap;
	}
	fn->code[fn->count++] = byte;
}

static void emit_bytes(SemaCtx * ctx, IrFn * fn, const void * bytes, usize nbytes) {
	if (fn->count + nbytes >= fn->capacity) {
		usize new_cap = (fn->capacity + nbytes) * 2;
		u8 * new_array = vmem_arena_alloc_n(ctx->arena, u8, new_cap);
		if (!new_array) {
			sema_ctx_oom(ctx);
		}
		memcpy(new_array, fn->code, fn->count);
		fn->code = new_array;
		fn->capacity = new_cap;
	}
	memcpy(fn->code, bytes, nbytes);
	fn->count += nbytes;
}

static void emit_u64(SemaCtx * ctx, IrFn * fn, u64 u) {
	emit_bytes(ctx, fn, &u, sizeof(u));
}

static bool emit_blk(FnCompletionCtx ctx, IrFn * ir, StmtList stmts);

static void emit_var_ptr(SemaCtx * ctx, IrFn * fn, SemaVar * var) {
	emit_byte(ctx, fn, IR_INST_VAR);
	emit_bytes(ctx, fn, &var, sizeof(SemaVar *));
}

static void emit_load(SemaCtx * ctx, IrFn * fn, SemaTypeHandle to_type) {
	switch (to_type.type->type) {
	case SEMA_TYPE_I32:
		emit_byte(ctx, fn, IR_INST_LOAD_I32);
		break;
	case SEMA_TYPE_PTR:
		emit_byte(ctx, fn, IR_INST_LOAD_I64);
		break;
	case SEMA_TYPE_VOID:
		emit_byte(ctx, fn, IR_INST_POP);
		break;
	case SEMA_TYPE_FN:
		emit_byte(ctx, fn, IR_INST_LOAD_I64);
		break;
	case SEMA_TYPE_REF:
		emit_byte(ctx, fn, IR_INST_LOAD_I64);
		break;
	case SEMA_TYPE_TYPE_ALIAS:
		UNREACHABLE();
	}
}

static void emit_expr(SemaCtx * ctx, IrFn * fn, SemaExpr * expr, SemaTypeHandle type, FnWorkStack * stack) {
	switch (expr->type2) {
	case SEMA_EXPR2_VALUE:
		switch (expr->as.sema2.value.type) {
			case SEMA_VALUE_NULLPTR:
				emit_byte(ctx, fn, IR_INST_I64);
				emit_u64(ctx, fn, 0);
				break;
			case SEMA_VALUE_I32:
				emit_byte(ctx, fn, IR_INST_I32);
				emit_bytes(ctx, fn, &expr->as.sema2.value.as.i32, sizeof(i32));
				break;
			case SEMA_VALUE_VOID:
				// noop
				break;
			case SEMA_VALUE_FN:
				if (!fn_work_stack_push(ctx, stack, expr->as.sema2.value.as.fn)) {
				
				}
				emit_byte(ctx, fn, IR_INST_FN);
				emit_bytes(ctx, fn, &expr->as.sema2.value.as.fn, sizeof(SemaFn *));
				break;
			case SEMA_VALUE_RAW_PTR:
			case SEMA_VALUE_RAW_REF:
				emit_byte(ctx, fn, IR_INST_I64);
				static_assert(sizeof(void *) == sizeof(u64));
				emit_bytes(ctx, fn, &expr->as.sema2.value.as.raw_ptr.value, sizeof(i64));
				break;
			case SEMA_VALUE_VAR_PTR:
			case SEMA_VALUE_VAR_REF:
				emit_var_ptr(ctx, fn, expr->as.sema2.value.as.var_ptr);
				break;
		}
		break;
	case SEMA_EXPR2_ADD_I32:
		emit_expr(ctx, fn, expr->as.sema2.add.a, type, stack);
		emit_expr(ctx, fn, expr->as.sema2.add.b, type, stack);
		emit_byte(ctx, fn, IR_INST_ADD_I32);
		break;
	case SEMA_EXPR2_LOAD_VAR:
		emit_var_ptr(ctx, fn, expr->as.sema2.load_var);
		emit_load(ctx, fn, type);
		break;
	case SEMA_EXPR2_DEREF:
		emit_load(ctx, fn, type);
		break;
	case SEMA_EXPR2_FUNCALL: {
			usize i = 0;
			for (auto node = type.type->as.fn.params.begin; node && i < expr->as.sema2.funcall.args.size; ++i) {
				SemaExpr * arg = &expr->as.sema2.funcall.args.data[i];
				emit_expr(ctx, fn, arg, node->type, stack);
			}
			emit_expr(ctx, fn, expr->as.sema2.funcall.fun, expr->as.sema2.funcall.fn_type, stack);
			emit_byte(ctx, fn, IR_INST_CALL);
		}
		break;
	}
}

static bool emit_ast_expr(SemaCtx * ctx, VisitorState visitor, IrFn * fn, const Expr * ast,
		const SemaTypeHandle * expected, SemaTypeHandle * out, FnWorkStack * stack) {
	SemaExpr expr;
	SemaTypeHandle handle;
	sema_expr_init_with_ast(&expr, ast);
	if (!ensure_expr_is_implemented(ctx, visitor, &expr, &handle)) {
		return false;
	}
	if (expected) {
		if (!coerce_expr_to_type(ctx, &expr, handle, *expected)) {
			return false;
		}
	}
	if (out) {
		*out = handle;
	}
	emit_expr(ctx, fn, &expr, handle, stack);
	return true;
}

static bool emit_decl(FnCompletionCtx ctx, VisitorState visitor, IrFn * fn, const Decl * ast) {
	// Im don't think its neccesary to emit anything
	(void)fn;
	SemaDecl decl;
	Str iden;
	SymbolPos pos = symbol_pos_local(ctx.fn, (LocalSymbolIndex)ctx.sema_ctx->env->decls.count); // TODO: overflow
	switch (ast->type) {
	case DECL_FN:
	    if (!str_copy(ctx.sema_ctx->arena, ast->as.fn.iden, &iden)) {
			sema_ctx_oom(ctx.sema_ctx);
	    }
	    sema_decl_init(&decl, SEMA_DECL_FN, pos, iden);
	    sema_fn_init_with_ast(&decl.as.fn, &ast->as.fn);
		break;
	case DECL_TYPE_ALIAS:
		if (!str_copy(ctx.sema_ctx->arena, ast->as.alias.iden, &iden)) {
			sema_ctx_oom(ctx.sema_ctx);
		}
		sema_decl_init(&decl, SEMA_DECL_TYPE_ALIAS, pos, iden);
		decl.as.alias.pass = SEMA_PASS_AST;
		decl.as.alias.ast = &ast->as.alias;
		break;
	case DECL_VAR:
		if (!str_copy(ctx.sema_ctx->arena, ast->as.var.iden, &iden)) {
			sema_ctx_oom(ctx.sema_ctx);
		}
		sema_decl_init(&decl, SEMA_DECL_VAR, pos, iden);
		sema_var_init_with_ast(&decl.as.var, &ast->as.var, false);
		break;
	}
	SemaDecl * ndecl = sema_ctx_add_decl(ctx.sema_ctx, decl);
	if (!ndecl) {
		sema_ctx_oom(ctx.sema_ctx);
	}
	if (ndecl->type != SEMA_DECL_FN) {
		if (!ensure_decl_is_implemented(ctx.sema_ctx, visitor, ndecl)) {
			return false;
		}
	} else {
		if (!fn_work_stack_push(ctx.sema_ctx, ctx.stack, &ndecl->as.fn)) {
			sema_ctx_oom(ctx.sema_ctx);
		}
	}
	return true;
}

static bool emit_stmt(FnCompletionCtx ctx, IrFn * fn, const Stmt * stmt) {
	switch (stmt->type) {
	case STMT_SEMICOLON:
		return true;
	case STMT_RETURN:
		if (stmt->as.return_.has_expr) {
			const SemaTypeHandle type = sema_type_handle_from_ptr(ctx.sema_ctx->env->as.fn.return_type);
			if (!emit_ast_expr(ctx.sema_ctx, ctx.visitor, fn, &stmt->as.return_.unwrap.expr, &type, nullptr, ctx.stack)) {
				return false;
			}
		}
		emit_byte(ctx.sema_ctx, fn, IR_INST_RET);
		return true;
	case STMT_EXPR:
		{
			SemaTypeHandle handle;
			if (!emit_ast_expr(ctx.sema_ctx, ctx.visitor, fn, &stmt->as.expr, nullptr, &handle, ctx.stack)) {
				return false;
			}
			emit_byte(ctx.sema_ctx, fn, IR_INST_POP);
		}
		return true;
	case STMT_BLOCK:
		{
			SemaEnv env;
			sema_env_init_push_fn_blk_env(ctx.sema_ctx, &env, ctx.sema_ctx->env->as.fn.return_type);
			bool result = emit_blk(ctx, fn, stmt->as.block);
			sema_env_pop(ctx.sema_ctx);
			return result;
		}
	case STMT_DECL:
		return emit_decl(ctx, ctx.visitor, fn, stmt->as.decl);
	}
}

static bool emit_blk(FnCompletionCtx ctx, IrFn * ir, StmtList stmts) {
	for (StmtNode * node = stmts.begin; node; node = node->next) {
		if (!emit_stmt(ctx, ir, &node->stmt)) {
			return false;
		}
	}
	return true;
}

bool emit_fn_iter(FnCompletionCtx ctx) {
	switch (ctx.fn->pass) {
	case SEMA_PASS_ERROR:
		return false;
	case SEMA_PASS_AST:
	case SEMA_PASS_CYCLE_UNCHECKED:
	case SEMA_PASS_CYCLE_CHECKING:
		if (!ensure_fn_is_cycle_checked(ctx.sema_ctx, ctx.visitor, ctx.fn)) {
			return false;
		}
		[[fallthrough]];
	case SEMA_PASS_CYCLE_CHECKED: {
			ctx.fn->emmiting = SEMA_FN_EMMITING;
			SemaType * fn_type = sema_type_from_interned_fn(ctx.fn->sema.signature);
			if (!ensure_type_ptr_is_implemented(ctx.sema_ctx, ctx.visitor, &fn_type)) {
				goto error;
			}
			ctx.fn->sema.signature = &fn_type->as.fn;
			SemaEnv env;
			IrFn ir = {0};
			sema_env_init_push_fn_blk_env(ctx.sema_ctx, &env, fn_type->as.fn.return_type);
			usize i = 0;
			for (auto node = ctx.fn->sema.signature->params.begin; node; node = node->next) {
				Str iden;
				if (!str_copy(ctx.sema_ctx->arena, ctx.fn->sema.args[i], &iden)) {
					sema_ctx_oom(ctx.sema_ctx);
				}
				SemaDecl decl;
				sema_decl_init(&decl, SEMA_DECL_VAR, symbol_pos_local(ctx.fn, (LocalSymbolIndex)i), iden); // TODO: overflow
				sema_var_init(&decl.as.var, node->type, nullptr, false, false);
				if (!sema_ctx_add_decl(ctx.sema_ctx, decl)) {
					sema_ctx_oom(ctx.sema_ctx);
				}
				++i;
			}
			bool result = emit_blk(ctx, &ir, ctx.fn->ast->body);
			sema_env_pop(ctx.sema_ctx);
			if (!result) {
				goto error;
			}
			ctx.fn->sema.unwrap.fn = ir;
			ctx.fn->pass = SEMA_PASS_IMPLEMENTED; // just the signature is needed
			ctx.fn->emmiting = SEMA_FN_EMMITED;
		}
		[[fallthrough]];
	case SEMA_PASS_IMPLEMENTED:
		return true;
	}
error:
	ctx.fn->pass = SEMA_PASS_ERROR;
	return false;
}

bool emit_fn(SemaCtx * ctx, VisitorState visitor, SemaFn * fn) {
	FnWorkStack stack;
	ZERO(&stack);
	FnCompletionCtx fn_ctx = {
		.sema_ctx = ctx,
		.fn = fn,
		.stack = &stack,
		.visitor = visitor,
	};
	if (!emit_fn_iter(fn_ctx)) {
		return false;
	}
	while (stack.head) {
		fn_work_stack_pop(ctx, &stack, &fn);
		if (!emit_fn_iter(fn_ctx)) {
			return false;
		}
	}
	return true;
}

bool run_implemented_const_fn(SemaCtx * ctx, SemaFn * fn, SemaValue * out) {
	TODO();
}
