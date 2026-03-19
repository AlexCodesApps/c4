#include "include/sema.h"
#include "include/platform.h"
#include "include/utility.h"

typedef enum {
	EVAL_STATUS_ERROR = 0,
	EVAL_STATUS_OK,
	EVAL_STATUS_UNAVAIL,
} EvalStatus;

NODISCARD static bool type_sig_cycle_check(SemaCtx * ctx, TypeSig * sig);
NODISCARD static bool type_alias_cycle_check(SemaCtx * ctx, TypeAlias * alias);
NODISCARD static bool type_alias_eval(SemaCtx * ctx, TypeAlias * alias);
NODISCARD static TypeHandle type_handle_from_sig(SemaCtx * ctx, TypeSig * sig);
NODISCARD static bool type_handle_eval(SemaCtx * ctx, TypeHandle type);
NODISCARD static usize type_evalled_size(Type * type);
NODISCARD static usize type_evalled_align(Type * type);
NODISCARD static bool var_cycle_check(SemaCtx * ctx, Var * var);
NODISCARD static bool var_eval(SemaCtx * ctx, Var * var);
NODISCARD static bool fn_proto_cycle_check(SemaCtx * ctx, Fn * fn);
NODISCARD static Decl * lookup_decl(SemaCtx * ctx, Iden iden,
									ReportError report);

static void print_error(SemaCtx * ctx, SrcSpan span, const char * msg, ...) {
	Str src = ctx->src;
	if (span.begin > span.end) {
		c4printf(stderr, "in %s[?]: ", ctx->path);
	} else {
		usize row = 1;
		usize col = 1;
		for (usize i = 0; i < span.begin; ++i) {
			if (src.data[i] == '\n') {
				col = 0;
				++row;
			}
			++col;
		}
		c4printf(stderr, "in %s[%uq, %uq]: ", ctx->path, row, col);
	}
	va_list va;
	va_start(va, msg);
	c4vaprintf(stderr, msg, va);
	va_end(va);
	putc('\n', stderr);
}

static usize type_evalled_size(Type * type) {
	assert(type->pass == TYPE_PASS_EVALUATED);
	switch (type->kind) {
	case TYPE_BUILTIN_VOID:
	case TYPE_FN:
		return 0;
	case TYPE_BUILTIN_I32:
		return 4;
	case TYPE_PTR:
	case TYPE_REF:
		return 8;
	}
}

static usize type_evalled_align(Type * type) {
	assert(type->pass == TYPE_PASS_EVALUATED);
	switch (type->kind) {
	case TYPE_BUILTIN_VOID:
	case TYPE_FN:
		return 0;
	case TYPE_BUILTIN_I32:
		return 4;
	case TYPE_PTR:
	case TYPE_REF:
		return 8;
	}
}

static bool type_handle_eval(SemaCtx * ctx, TypeHandle handle) {
	switch (handle.type->pass) {
	case TYPE_PASS_ERROR:
		return false;
	case TYPE_PASS_CHECKED:
		handle.type->pass = TYPE_PASS_EVALUATED;
		switch (handle.type->kind) {
		case TYPE_BUILTIN_VOID:
		case TYPE_BUILTIN_I32:
			break;
		case TYPE_PTR:
			if (!type_handle_eval(ctx, handle.type->as.ptr))
				goto error;
			break;
		case TYPE_REF:
			if (!type_handle_eval(ctx, handle.type->as.ref))
				goto error;
			break;
		case TYPE_FN:
			if (!type_handle_eval(ctx, handle.type->as.fn.return_ty))
				goto error;
			for (usize i = 0; i < handle.type->as.fn.params.size; ++i)
				if (!type_handle_eval(ctx, handle.type->as.fn.params.data[i]))
					goto error;
			if (handle.is_mut) {
				print_error(ctx, INVALID_SRC_SPAN,
							"functions cannot be directly mutable");
				c4println(stderr, "hint: add indirection with '*' or '&'?");
				goto error;
			}
			break;
		}
		FALLTHROUGH();
	case TYPE_PASS_EVALUATED:
		return true;
	}
error:
	handle.type->pass = TYPE_PASS_ERROR;
	return false;
}

static bool type_alias_eval(SemaCtx * ctx, TypeAlias * alias) {
	switch (alias->pass) {
	case TYPE_ALIAS_PASS_ERROR:
		return false;
	case TYPE_ALIAS_PASS_PARSED:
	case TYPE_ALIAS_PASS_CHECKING:
		if (!type_alias_cycle_check(ctx, alias)) {
			return false;
		}
		ASSERT(alias->pass == TYPE_ALIAS_PASS_CHECKED);
		FALLTHROUGH();
	case TYPE_ALIAS_PASS_CHECKED: {
		TypeHandle handle = type_handle_from_sig(ctx, &alias->as.checked);
		if (!type_handle_is_valid(handle))
			goto error;
		type_alias_set_evalled(alias, handle);
		if (!type_handle_eval(ctx, handle))
			goto error;
		FALLTHROUGH();
	}
	case TYPE_ALIAS_PASS_EVALUATED:
		return true;
	}
error:
	type_alias_set_error(alias);
	return false;
}

NODISCARD static Decl * lookup_decl(SemaCtx * ctx, Iden iden,
									ReportError report) {
	for (usize i = 0; i < ctx->base->size; ++i) {
		Decl * decl = ast_at(ctx->base, i);
		if (str_equal(iden, decl->iden))
			return decl;
	}
	if (report == DO_REPORT_ERROR)
		print_error(ctx, INVALID_SRC_SPAN, "unexpected identifier '%s'\n",
					iden);
	return NULL;
}

static bool type_alias_cycle_check(SemaCtx * ctx, TypeAlias * alias) {
	switch (alias->pass) {
	case TYPE_ALIAS_PASS_ERROR:
		return false;
	case TYPE_ALIAS_PASS_PARSED: {
		VisitStructural checkpoint = visitor_structural(&ctx->visitor);
		type_alias_set_checking(alias, checkpoint.visit_id);
		if (!type_sig_cycle_check(ctx, &alias->as.checking.parsed))
			goto error;
		visitor_structural_restore(&ctx->visitor, checkpoint);
		type_alias_set_checked(alias);
		return true;
	}
	case TYPE_ALIAS_PASS_CHECKING:
		LOG("detected potential cycle in type alias %p", alias);
		if (!visitor_check_structural(&ctx->visitor,
									  alias->as.checking.visit_index)) {
			print_error(ctx, alias->span, "detected cycle in alias");
			goto error;
		}
		FALLTHROUGH();
	case TYPE_ALIAS_PASS_CHECKED:
	case TYPE_ALIAS_PASS_EVALUATED:
		return true;
	}
error:
	type_alias_set_error(alias);
	return false;
}

static bool type_sig_cycle_check(SemaCtx * ctx, TypeSig * sig) {
	VisitIndex idx;
	switch (sig->pass) {
	case TYPE_SIG_PASS_ERROR:
		return false;
	case TYPE_SIG_PASS_PARSED:
		switch (sig->kind) {
		case TYPE_SIG_IDEN: {
			if (str_equal(sig->as.iden, s("int"))) {
				sig->kind = TYPE_SIG_TYPE_STUB;
				sig->as.type_stub = &ctx->table->i32_type;
				break;
			} else if (str_equal(sig->as.iden, s("void"))) {
				sig->kind = TYPE_SIG_TYPE_STUB;
				sig->as.type_stub = &ctx->table->void_type;
				break;
			}
			Decl * decl = lookup_decl(ctx, sig->as.iden, DO_REPORT_ERROR);
			if (!decl)
				goto error;
			switch (decl->kind) {
			case DECL_ERROR:
				goto error;
			case DECL_FN:
				print_error(ctx, decl->as.fn.span,
							"expected type, found fn '%s'", decl->iden);
				goto error;
			case DECL_VAR:
				print_error(ctx, decl->as.var.span,
							"expected type, found var '%s'", decl->iden);
				goto error;
			case DECL_TYPE_ALIAS:
				if (!type_alias_cycle_check(ctx, &decl->as.alias))
					goto error;
				sig->kind = TYPE_SIG_ALIAS_STUB;
				sig->as.alias_stub = &decl->as.alias;
				return true;
			}
		}
		case TYPE_SIG_PTR:
			idx = visitor_push_indirection(&ctx->visitor);
			if (!type_sig_cycle_check(ctx, sig->as.ptr))
				goto error;
			visitor_pop_indirection(&ctx->visitor, idx);
			break;
		case TYPE_SIG_REF:
			idx = visitor_push_indirection(&ctx->visitor);
			if (!type_sig_cycle_check(ctx, sig->as.ref))
				goto error;
			visitor_pop_indirection(&ctx->visitor, idx);
			break;
		case TYPE_SIG_FN:
			idx = visitor_push_indirection(&ctx->visitor);
			if (!type_sig_cycle_check(ctx, sig->as.fn.return_ty))
				goto error;
			for (usize i = 0; i < sig->as.fn.params.size; ++i) {
				TypeSig * param = type_sig_list_at(&sig->as.fn.params, i);
				if (!type_sig_cycle_check(ctx, param))
					goto error;
			}
			visitor_pop_indirection(&ctx->visitor, idx);
			break;
		case TYPE_SIG_VOID:
		case TYPE_SIG_ALIAS_STUB:
		case TYPE_SIG_TYPE_STUB:
			break;
		}
		sig->pass = TYPE_SIG_PASS_CYCLE_CHECKED;
		FALLTHROUGH();
	case TYPE_SIG_PASS_CYCLE_CHECKED:
		return true;
	}
error:
	type_sig_set_error(sig);
	return false;
}

static TypeHandle type_handle_from_sig(SemaCtx * ctx, TypeSig * sig) {
	TypeHandle handle;
	switch (sig->pass) {
	case TYPE_SIG_PASS_ERROR:
		goto error;
	case TYPE_SIG_PASS_PARSED:
		if (!type_sig_cycle_check(ctx, sig))
			goto error;
		ASSERT(sig->pass == TYPE_SIG_PASS_CYCLE_CHECKED);
		FALLTHROUGH();
	case TYPE_SIG_PASS_CYCLE_CHECKED:
		switch (sig->kind) {
		case TYPE_SIG_PTR: {
			handle = type_handle_from_sig(ctx, sig->as.ptr);
			if (!type_handle_is_valid(handle))
				goto error;
			Type * ty =
				type_intern_table_ptr_to(ctx->arena, ctx->table, handle);
			if (!ty)
				sema_oom(ctx);
			handle = type_handle_from_ptr(ty);
			break;
		}
		case TYPE_SIG_REF: {
			handle = type_handle_from_sig(ctx, sig->as.ptr);
			if (!type_handle_is_valid(handle))
				goto error;
			Type * ty =
				type_intern_table_ptr_to(ctx->arena, ctx->table, handle);
			if (!ty)
				sema_oom(ctx);
			handle = type_handle_from_ptr(ty);
			break;
		}
		case TYPE_SIG_FN: {
			TypeHandle return_ty =
				type_handle_from_sig(ctx, sig->as.fn.return_ty);
			if (!type_handle_is_valid(return_ty))
				goto error;
			TypeHandle * params_mem = vmem_arena_alloc_n(
				ctx->arena, TypeHandle, sig->as.fn.params.size);
			if (!params_mem)
				sema_oom(ctx);
			for (usize i = 0; i < sig->as.fn.params.size; ++i) {
				TypeSig * param_sig = type_sig_list_at(&sig->as.fn.params, i);
				TypeHandle param = type_handle_from_sig(ctx, param_sig);
				if (!type_handle_is_valid(param))
					goto error;
				params_mem[i] = param;
			}
			TypeHandleSpan params = {.data = params_mem,
									 .size = sig->as.fn.params.size};
			Type * ty = type_intern_table_fn_of(ctx->arena, ctx->table,
												return_ty, params);
			if (!ty)
				sema_oom(ctx);
			handle = type_handle_from_ptr(ty);
			break;
		}
		case TYPE_SIG_VOID:
			handle = type_handle_new(&ctx->table->void_type, false, false);
			break;
		case TYPE_SIG_ALIAS_STUB:
			if (!type_alias_eval(ctx, sig->as.alias_stub))
				goto error;
			handle = sig->as.alias_stub->as.evalled;
			break;
		case TYPE_SIG_TYPE_STUB:
			handle = type_handle_new(sig->as.type_stub, false, false);
			break;
		case TYPE_SIG_IDEN:
			UNREACHABLE();
		}
	}
	handle.is_mut = sig->is_mut;
	return handle;
error:
	type_sig_set_error(sig);
	return type_handle_null();
}

NODISCARD static bool fn_proto_cycle_check(SemaCtx * ctx, Fn * fn) {
	switch (fn->pass) {
	case FN_PASS_ERROR:
		return false;
	case FN_PASS_PARSED: {
		VisitStructural checkpoint = visitor_structural(&ctx->visitor);
		fn_set_pass_proto_checking(fn, checkpoint.visit_id);
		if (!type_sig_cycle_check(ctx, &fn->proto.return_ty))
			goto error;
		ParamList * list = &fn->proto.params;
		for (usize i = 0; i < list->size; ++i) {
			Param * param = param_list_at(list, i);
			if (!type_sig_cycle_check(ctx, &param->type))
				goto error;
		}
		visitor_structural_restore(&ctx->visitor, checkpoint);
		fn_set_pass_proto_checked(fn);
		return true;
	}
	case FN_PASS_PROTO_CHECKING:
		LOG("detected potential cycle in type fn %p", fn);
		if (!visitor_check_structural(&ctx->visitor, fn->as.checking)) {
			print_error(ctx, fn->span, "detected cycle in fn");
			goto error;
		}
		FALLTHROUGH();
	case FN_PASS_PROTO_CHECKED:
	case FN_PASS_PROTO:
	case FN_PASS_EVAL:
		return true;
	}
error:
	fn_set_error(fn);
	return false;
}

static bool var_cycle_check(SemaCtx * ctx, Var * var) {
	switch (var->pass) {
	case VAR_PASS_ERROR:
		return false;
	case VAR_PASS_PARSED: {
		VisitStructural checkpoint = visitor_structural(&ctx->visitor);
		var_set_checking(var, checkpoint.visit_id);
		ParsedVar * inner = &var->as.checking.parsed;
		VarMutability mut = VAR_MUT_LET;
		if (inner->is_const) {
			mut = VAR_MUT_CONST;
		}
		if (inner->is_mut) {
			if (mut == VAR_MUT_CONST) {
				print_error(ctx, var->span,
							"variable cannot be both const and mut");
				goto error;
			}
			mut = VAR_MUT_MUT;
		}
		if (!type_sig_cycle_check(ctx, &inner->type))
			goto error;
		// Expressions don't get cycle checked, rather they get interpreted.
		visitor_structural_restore(&ctx->visitor, checkpoint);
		var_set_checked(var);
		return true;
	}
	case VAR_PASS_CHECKING:
		// FRAGILE:
		// only mutual recursion in variables and types are detected here,
		// which is a complete no-go
		print_error(ctx, var->span, "detected cycle in var");
		goto error;
	case VAR_PASS_CHECKED:
	case VAR_PASS_EVALUATED:
		return true;
	}
error:
	var_set_error(var);
	return false;
}

static bool var_eval(SemaCtx * ctx, Var * var) {
	switch (var->pass) {
	case VAR_PASS_ERROR:
		return false;
	case VAR_PASS_PARSED:
	case VAR_PASS_CHECKING:
		if (!var_cycle_check(ctx, var))
			return false;
		ASSERT(var->pass == VAR_PASS_CHECKED);
		FALLTHROUGH();
	case VAR_PASS_CHECKED:
	case VAR_PASS_EVALUATED:
		return true;
	}
}

void eval_env_init(EvalEnv * env) {
	env->kind = EVAL_ENV_GLOBAL;
	env->prev = NULL;
}

void sema_ctx_init(SemaCtx * ctx, Ast * ast, VMemArena * arena,
				   TypeInternTable * table, Str src, Str path) {
	ZERO(ctx);
	eval_env_init(&ctx->env);
	ctx->base = ast;
	ctx->arena = arena;
	ctx->table = table;
	ctx->visitor = visitor_state_new();
	ctx->src = src;
	ctx->path = path;
}

NORETURN void sema_oom(SemaCtx * ctx) {
	ASSERT(false && "OOM triggered");
	longjmp(ctx->oom_handler, 1);
}

bool sema_ctx_run(SemaCtx * ctx) {
	if (setjmp(ctx->oom_handler)) {
		return false;
	}
	bool ok = true;
	for (usize i = 0; i < ctx->base->size; ++i) {
		Decl * decl = ast_at(ctx->base, i);
		switch (decl->kind) {
		case DECL_ERROR:
			continue;
		case DECL_FN:
			continue;
		case DECL_TYPE_ALIAS:
			LOG("evaluating alias %s[%p]", decl->iden, &decl->as.alias);
			ok = ok && type_alias_eval(ctx, &decl->as.alias);
			break;
		case DECL_VAR:
			LOG("evaluating var %s[%p]", decl->iden, &decl->as.var);
			ok = ok && var_eval(ctx, &decl->as.var);
		}
	}
	return ok;
}
