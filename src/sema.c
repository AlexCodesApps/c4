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
NODISCARD static bool var_decl_cycle_check(SemaCtx * ctx, Var * var);
NODISCARD static bool var_decl_eval(SemaCtx * ctx, Var * var);
NODISCARD static bool var_eval(SemaCtx * ctx, Var * var);
NODISCARD static bool fn_proto_cycle_check(SemaCtx * ctx, Fn * fn);
NODISCARD static bool fn_proto_eval(SemaCtx * ctx, Fn * fn);
NODISCARD static bool fn_eval(SemaCtx * ctx, Fn * fn);
NODISCARD static Decl * sema_lookup_decl(SemaCtx * ctx, Iden iden,
										 ReportError report);
NODISCARD static bool check_type_covariance(SemaCtx * ctx, TypeHandle super,
											TypeHandle sub);
NODISCARD static bool check_type_contravariance(SemaCtx * ctx, TypeHandle super,
												TypeHandle sub);
NODISCARD static bool expr_coerce_assignment(SemaCtx * ctx, TypeHandle to,
											 TypeHandle from, Expr * expr);
NODISCARD static bool expr_eval(SemaCtx * ctx, Expr * expr, TypeHandle * out);

static void * sema_alloc_bytes(SemaCtx * ctx, usize size, usize align) {
	void * ptr = vmem_arena_alloc_bytes(ctx->arena, size, align);
	if (UNLIKELY(!ptr)) {
		sema_oom(ctx);
	}
	return ptr;
}

static void * sema_alloc_bytes_n(SemaCtx * ctx, usize size, usize n,
								 usize align) {
	void * ptr = vmem_arena_alloc_bytes_n(ctx->arena, size, n, align);
	if (UNLIKELY(!ptr)) {
		sema_oom(ctx);
	}
	return ptr;
}

#define sema_alloc(ctx, T) (T *)sema_alloc_bytes((ctx), sizeof(T), ALIGNOF(T))
#define sema_alloc_n(ctx, T, n)                                                \
	(T *)sema_alloc_bytes_n((ctx), sizeof(T), (n), ALIGNOF(T))

#define TABWIDTH 4

static usize cell_width(Str line) {
	usize count = 0;
	for (usize i = 0; i < line.size; ++i) {
		count += line.data[i] == '\t' ? TABWIDTH : 1;
	}
	return count;
}

static void print_errline(usize count) {
	c4print(stderr, "\x1b[31m");
	for (usize i = 0; i < count; ++i)
		fputc('~', stderr);
	c4print(stderr, "\x1b[0m");
}

static void print_space(usize count) {
	for (usize i = 0; i < count; ++i)
		fputc(' ', stderr);
}

static void print_line(Str line) {
	for (usize i = 0; i < line.size; ++i) {
		char ch = line.data[i];
		if (ch == '\t')
			print_space(TABWIDTH);
		else
			fputc(ch, stderr);
	}
}

static void print_grid(Str src, SrcSpan span, usize brow, usize bcol,
					   usize erow, usize ecol) {
	if (brow == erow) {
		Str line = str_get_line_at_idx(src, span.begin);
		Str before_line, middle, after_line;
		str_split_at_idx(line, bcol, &before_line, &middle);
		str_split_at_idx(middle, ecol - bcol, &middle, &after_line);
		print_line(line);
		fputc('\n', stderr);
		print_space(cell_width(before_line));
		print_errline(cell_width(middle));
		print_space(cell_width(after_line));
		fputc('\n', stderr);
		return;
	}
	StrLineIter begin, middle, end;
	str_line_iter_new(&begin, src, span.begin);
	middle = begin;
	str_line_iter_new(&end, src, span.end);
	Str begin_line = str_line_iter_current_line(&begin);
	Str end_line = str_line_iter_current_line(&end);
	{
		Str ctx;
		if (str_line_iter_last_line(&begin, &ctx)) {
			print_line(ctx);
			fputc('\n', stderr);
		}
		Str before_line, err_line;
		str_split_at_idx(begin_line, bcol, &before_line, &err_line);
		print_line(begin_line);
		fputc('\n', stderr);
		print_space(cell_width(before_line));
		print_errline(cell_width(err_line));
		fputc('\n', stderr);
	}
	Str line;
	while (str_line_iter_next_line(&middle, &line)) {
		if (line.data == end_line.data)
			break;
		print_line(line);
		fputc('\n', stderr);
		print_errline(cell_width(line));
		fputc('\n', stderr);
	}
	if (end_line.size > 0 && ecol > 0) {
		Str err_line, after_line;
		str_split_at_idx(end_line, ecol, &err_line, &after_line);
		print_line(end_line);
		fputc('\n', stderr);
		print_errline(cell_width(err_line));
		print_space(cell_width(after_line));
		fputc('\n', stderr);
		Str ctx;
		if (str_line_iter_next_line(&end, &ctx)) {
			print_line(ctx);
			fputc('\n', stderr);
		}
	} else {
		print_line(end_line);
		fputc('\n', stderr);
	}
}

static void print_error(SemaCtx * ctx, SrcSpan span, const char * msg, ...) {
	Str src = ctx->src;
	if (!src_span_is_text(&span)) {
		c4printf(stderr, "in %s[?]: ", ctx->path);
	} else {
		usize i;
		usize row = 1;
		usize col = 1;
		usize brow, bcol;
		for (i = 0; i < span.begin; ++i) {
			if (src.data[i] == '\n') {
				col = 0;
				++row;
			}
			++col;
		}
		brow = row;
		bcol = col;
		for (; i < span.end; ++i) {
			if (src.data[i] == '\n') {
				col = 0;
				++row;
			}
			++col;
		}
		c4printf(stderr, "in %s[%uq, %uq]:\n", ctx->path, brow, bcol);
		print_grid(src, span, brow - 1, bcol - 1, row - 1, col - 1);
	}
	c4print(stderr, "\x1b[31merror: ");
	va_list va;
	va_start(va, msg);
	c4vaprintf(stderr, msg, va);
	va_end(va);
	c4print(stderr, "\x1b[0m\n");
}

static void expected_type(SemaCtx * ctx, SrcSpan span, TypeHandle expected,
						  TypeHandle found) {
	print_error(ctx, span, "expected %th, found %th", expected, found);
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

static TypeHandle void_type_handle(SemaCtx * ctx) {
	return type_handle_from_ptr(&ctx->table->void_type);
}

static TypeHandle nullptr_type_handle(SemaCtx * ctx) {
	TypeHandle voidh = type_handle_new(&ctx->table->void_type, true, false);
	Type * ptr = type_intern_table_ptr_to(ctx->arena, ctx->table, voidh,
										  TYPE_PASS_EVALUATED);
	if (!ptr)
		sema_oom(ctx);
	return type_handle_from_ptr(ptr);
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
		case TYPE_REF:
			if (!type_handle_eval(ctx, handle.type->as.ptr_like))
				goto error;
			break;
			if (!type_handle_eval(ctx, handle.type->as.ptr_like))
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
							"functions cannot be directly mutable [%th]",
							handle);
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

NODISCARD static Decl * sema_lookup_decl(SemaCtx * ctx, Iden iden,
										 ReportError report) {
	Decl * decl = var_env_lookup_decl(ctx->env, iden);
	if (decl)
		return decl;
	for (usize i = 0; i < ctx->base->size; ++i) {
		decl = ast_at(ctx->base, i);
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
			print_error(ctx, alias->span, "detected cycle in type alias");
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
			Decl * decl = sema_lookup_decl(ctx, sig->as.iden, DO_REPORT_ERROR);
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
			if (!type_sig_cycle_check(ctx, sig->as.ptr_like))
				goto error;
			visitor_pop_indirection(&ctx->visitor, idx);
			break;
		case TYPE_SIG_REF:
			idx = visitor_push_indirection(&ctx->visitor);
			if (!type_sig_cycle_check(ctx, sig->as.ptr_like))
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
			handle = type_handle_from_sig(ctx, sig->as.ptr_like);
			if (!type_handle_is_valid(handle))
				goto error;
			Type * ty = type_intern_table_ptr_to(ctx->arena, ctx->table, handle,
												 TYPE_PASS_CHECKED);
			if (!ty)
				sema_oom(ctx);
			handle = type_handle_from_ptr(ty);
			break;
		}
		case TYPE_SIG_REF: {
			handle = type_handle_from_sig(ctx, sig->as.ptr_like);
			if (!type_handle_is_valid(handle))
				goto error;
			Type * ty = type_intern_table_ptr_to(ctx->arena, ctx->table, handle,
												 TYPE_PASS_CHECKED);
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
			TypeHandle * params_mem =
				sema_alloc_n(ctx, TypeHandle, sig->as.fn.params.size);
			for (usize i = 0; i < sig->as.fn.params.size; ++i) {
				TypeSig * param_sig = type_sig_list_at(&sig->as.fn.params, i);
				TypeHandle param = type_handle_from_sig(ctx, param_sig);
				if (!type_handle_is_valid(param))
					goto error;
				params_mem[i] = param;
			}
			TypeHandleSpan params = {.data = params_mem,
									 .size = sig->as.fn.params.size};
			Type * ty = type_intern_table_fn_of(
				ctx->arena, ctx->table, return_ty, params, TYPE_PASS_CHECKED);
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

NODISCARD static bool fn_proto_eval(SemaCtx * ctx, Fn * fn) {
	switch (fn->pass) {
	case FN_PASS_ERROR:
		return false;
	case FN_PASS_PARSED:
	case FN_PASS_PROTO_CHECKING:
		if (!fn_proto_cycle_check(ctx, fn))
			return false;
		FALLTHROUGH();
	case FN_PASS_PROTO_CHECKED: {
		TypeHandle ret = type_handle_from_sig(ctx, &fn->proto.return_ty);
		if (!type_handle_eval(ctx, ret))
			goto error;
		size_t size = fn->proto.params.size;
		TypeHandleSpan span = {.data = sema_alloc_n(ctx, TypeHandle, size),
							   .size = size};
		for (usize i = 0; i < size; ++i) {
			span.data[i] = type_handle_from_sig(
				ctx, &param_list_at(&fn->proto.params, i)->type);
			if (!type_handle_eval(ctx, span.data[i]))
				goto error;
		}
		Type * fnty = type_intern_table_fn_of(ctx->arena, ctx->table, ret, span,
											  TYPE_PASS_EVALUATED);
		if (!fnty)
			sema_oom(ctx);
		TypeHandle handle = type_handle_new(fnty, false, true);
		if (!type_handle_eval(ctx, handle))
			goto error;
		fn_set_pass_proto(fn, handle);
		FALLTHROUGH();
	}
	case FN_PASS_PROTO:
	case FN_PASS_EVAL:
		return true;
	}
error:
	fn_set_error(fn);
	return false;
}

NODISCARD static bool fn_eval(SemaCtx * ctx, Fn * fn) {
	switch (fn->pass) {
	case FN_PASS_ERROR:
		return false;
	case FN_PASS_PARSED:
	case FN_PASS_PROTO_CHECKING:
	case FN_PASS_PROTO_CHECKED:
	case FN_PASS_PROTO:
		if (!fn_proto_eval(ctx, fn))
			return false;
		FALLTHROUGH();
	case FN_PASS_EVAL:
		// TODO("implement functions :)");
		return true;
	}
error:
	fn_set_error(fn);
	return false;
}

bool decl_ptr_list_init(VMemArena * arena, DeclPtrList * list, usize capacity) {
	Decl ** decls = vmem_arena_alloc_n(arena, Decl *, capacity);
	if (!decls)
		return false;
	list->decls = decls;
	list->count = 0;
	list->capacity = capacity;
	return true;
}

Decl ** decl_ptr_list_push(DeclPtrList * list) {
	if (list->count == list->capacity) {
		FAIL("Capacity should be deterministic");
		return NULL;
	}
	return &list->decls[list->count++];
}

NODISCARD static bool var_decl_cycle_check(SemaCtx * ctx, Var * var) {
	switch (var->pass) {
	case VAR_PASS_ERROR:
		return false;
	case VAR_PASS_PARSED: {
		VisitStructural visit = visitor_structural(&ctx->visitor);
		var_set_decl_checking(var, visit.visit_id);
		if (!type_sig_cycle_check(ctx, &var->as.checking_decl.parsed.type))
			return false;
		visitor_structural_restore(&ctx->visitor, visit);
		var_set_decl_checked(var);
		return true;
	}
	case VAR_PASS_DECL_CYCLE_CHECKING:
		print_error(ctx, var->span, "detected cycle in variable type");
		goto error;
	case VAR_PASS_DECL_CYCLE_CHECKED:
	case VAR_PASS_DECL_EVALUATED:
	case VAR_PASS_EXPR_CYCLE_CHECKING:
	case VAR_PASS_EXPR_EVALUATED:
		return true;
	}
error:
	var_set_error(var);
	return false;
}

static bool var_decl_eval(SemaCtx * ctx, Var * var) {
	switch (var->pass) {
	case VAR_PASS_ERROR:
		return false;
	case VAR_PASS_PARSED:
	case VAR_PASS_DECL_CYCLE_CHECKING:
		if (!var_decl_cycle_check(ctx, var))
			goto error;
		FALLTHROUGH();
	case VAR_PASS_DECL_CYCLE_CHECKED: {
		TypeHandle handle = type_handle_from_sig(ctx, &var->as.parsed.type);
		if (!type_handle_eval(ctx, handle))
			goto error;
		bool is_mut = var->as.parsed.is_mut;
		bool is_const = var->as.parsed.is_const;
		VarMutability mut = VAR_MUT_LET;
		if (is_const) {
			if (is_mut) {
				print_error(ctx, var->span,
							"const variables cannot be declared mutable");
				goto error;
			}
			mut = VAR_MUT_CONST;
		} else if (is_mut) {
			mut = VAR_MUT_MUT;
		}
		var_set_decl_evalled(var, mut, handle);
		FALLTHROUGH();
	}
	case VAR_PASS_EXPR_CYCLE_CHECKING:
	case VAR_PASS_DECL_EVALUATED:
	case VAR_PASS_EXPR_EVALUATED:
		return true;
	}
error:
	var_set_error(var);
	return false;
}

NODISCARD static bool var_eval(SemaCtx * ctx, Var * var) {
	switch (var->pass) {
	case VAR_PASS_ERROR:
		return false;
	case VAR_PASS_PARSED:
	case VAR_PASS_DECL_CYCLE_CHECKING:
	case VAR_PASS_DECL_CYCLE_CHECKED:
		if (!var_decl_eval(ctx, var))
			return false;
		FALLTHROUGH();
	case VAR_PASS_DECL_EVALUATED: {
		VisitStructural checkpoint = visitor_structural(&ctx->visitor);
		var_set_expr_checking(var, checkpoint.visit_id);
		if (var->as.checking_expr.decl_evalled.has_expr) {
			TypeHandle handle;
			if (!expr_eval(ctx, &var->as.checking_expr.decl_evalled.unwrap.expr,
						   &handle))
				goto error;
			if (!expr_coerce_assignment(ctx, var->as.decl_evalled.type, handle,
										&var->as.decl_evalled.unwrap.expr))
				goto error;
		}
		var_set_expr_evalled(var);
		return true;
	}
	case VAR_PASS_EXPR_CYCLE_CHECKING:
		if (!visitor_check_structural(&ctx->visitor,
									  var->as.checking_expr.id)) {
			print_error(ctx, var->span,
						"circular dependency found in variable initialization");
			goto error;
		}
		FALLTHROUGH();
	case VAR_PASS_EXPR_EVALUATED:
		return true;
	}
error:
	var_set_error(var);
	return false;
}

bool var_env_push_scope(VMemArena * arena, VarEnv * env, VarEnv * parent,
						usize capacity, bool is_const) {
	if (!decl_ptr_list_init(arena, &env->frame.list, capacity))
		return false;
	env->frame.parent = parent;
	env->is_const = is_const;
	return true;
}

bool var_env_push_decl(VarEnv * env, Decl * decl) {
	ASSERT(env);
	Decl ** ptr = decl_ptr_list_push(&env->frame.list);
	if (!ptr)
		return false;
	*ptr = decl;
	return true;
}

bool var_const_env(VarEnv * env) { return env ? env->is_const : true; }

Decl * var_env_lookup_decl(VarEnv * env, Iden iden) {
	while (env) {
		DeclPtrList * list = &env->frame.list;
		for (usize i = 0; i < list->count; ++i) {
			Decl * decl = list->decls[i];
			if (str_equal(decl->iden, iden))
				return decl;
		}
		env = env->frame.parent;
	}
	return NULL;
}

typedef enum {
	TYPE_COVARIANT,
	TYPE_CONTRAVARIANT,
	TYPE_INVARIANT
} TypeVariance;

bool check_type_covariance(SemaCtx * ctx, TypeHandle super, TypeHandle sub) {
	ASSERT(super.type->pass == TYPE_PASS_EVALUATED);
	ASSERT(sub.type->pass == TYPE_PASS_EVALUATED);
	if (type_handle_eq(super, sub))
		return true;
	if (super.is_mut && !sub.is_mut)
		return false;
	if (super.type == sub.type)
		return true;
	switch (super.type->kind) {
	case TYPE_BUILTIN_VOID:
	case TYPE_BUILTIN_I32:
	case TYPE_REF:
		return false;
	case TYPE_PTR:
		if (sub.type->kind == TYPE_PTR || sub.type->kind == TYPE_REF)
			return check_type_covariance(ctx, super.type->as.ptr_like,
										 sub.type->as.ptr_like);
		break;
	case TYPE_FN:
		if (sub.type->kind == TYPE_FN) {
			FnType * super_fn = &super.type->as.fn;
			FnType * sub_fn = &sub.type->as.fn;
			if (super_fn->params.size != sub_fn->params.size)
				return false;
			if (!check_type_covariance(ctx, super_fn->return_ty,
									   sub_fn->return_ty))
				return false;
			for (usize i = 0; i < super_fn->params.size; ++i) {
				TypeHandle super_param = super_fn->params.data[i];
				TypeHandle sub_param = sub_fn->params.data[i];
				if (!check_type_contravariance(ctx, super_param, sub_param))
					return false;
			}
			return true;
		}
	}
	return false;
}

NODISCARD static bool check_type_contravariance(SemaCtx * ctx, TypeHandle super,
												TypeHandle sub) {
	return check_type_covariance(ctx, sub, super);
}

bool expr_coerce_assignment(SemaCtx * ctx, TypeHandle to, TypeHandle from,
							Expr * expr) {
	ASSERT(to.type->pass == TYPE_PASS_EVALUATED);
	ASSERT(from.type->pass == TYPE_PASS_EVALUATED);
	if (to.type == from.type)
		return true;
	if (!to.is_lvalue) {
		print_error(ctx, expr->span, "expected expression to be lvalue", to);
		return false;
	}
	switch (to.type->kind) {
	case TYPE_BUILTIN_VOID:
	case TYPE_BUILTIN_I32:
		break;
	case TYPE_FN:
		TODO("functions don't do 'assignment', make a good err msg");
		break;
	case TYPE_PTR:
		if (from.type->kind == TYPE_PTR || from.type->kind == TYPE_REF) {
			if (!check_type_covariance(ctx, to.type->as.ptr_like,
									   from.type->as.ptr_like)) {
				goto mismatch;
			}
			return true;
		}
		break;
	case TYPE_REF:
		if (from.type->kind == TYPE_REF) {
			if (!check_type_covariance(ctx, to.type->as.ptr_like,
									   from.type->as.ptr_like)) {
				goto mismatch;
			}
			return true;
		}
		break;
	}
mismatch:
	expected_type(ctx, expr->span, to, from);
	return false;
}

bool expr_coerce_binary(SemaCtx * ctx, TypeHandle type_a, Expr * a,
						TypeHandle type_b, Expr * b, TypeHandle * out) {
	ASSERT(type_a.type->pass == TYPE_PASS_EVALUATED);
	ASSERT(type_b.type->pass == TYPE_PASS_EVALUATED);
	if (type_a.type == type_b.type) {
		*out = type_handle_new(type_a.type, false, false);
		return true;
	}
	TODO("coerce binary expr");
}

bool expr_type_coerce_addr(SemaCtx * ctx, TypeHandle in, TypeHandle * out) {
	ASSERT(in.type->pass == TYPE_PASS_EVALUATED);
	// TODO: error handling
	if (!in.is_lvalue) {
		print_error(ctx, INVALID_SRC_SPAN, "expected lvalue");
		return false;
	}
	Type * ty = type_intern_table_ref_to(ctx->arena, ctx->table, in,
										 TYPE_PASS_EVALUATED);
	if (!ty) {
		sema_oom(ctx);
	}
	*out = type_handle_from_ptr(ty);
	return true;
}

bool expr_type_coerce_deref(SemaCtx * ctx, TypeHandle in, TypeHandle * out) {
	ASSERT(in.type->pass == TYPE_PASS_EVALUATED);
	// TODO: error handling
	if (!type_is_pointer_like(in.type)) {
		print_error(ctx, INVALID_SRC_SPAN, "expected reference or pointer");
		return false;
	}
	*out = in.type->as.ptr_like;
	return true;
}

bool expr_type_coerce_function(SemaCtx * ctx, TypeHandle in, FnType ** out) {
	ASSERT(in.type->pass == TYPE_PASS_EVALUATED);
	// TODO: error handling
	if (in.type->kind != TYPE_FN) {
		print_error(ctx, INVALID_SRC_SPAN, "expected function, found %th", in);
		return false;
	}
	*out = &in.type->as.fn;
	return true;
}

bool expr_eval_inner(SemaCtx * ctx, Expr * expr, TypeHandle * out, bool addr) {
	switch (expr->pass) {
	case EXPR_PASS_ERROR:
		return false;
	case EXPR_PASS_PARSED:
		switch (expr->kind) {
		case EXPR_INTEGER:
			expr->sema_kind = EXPR_SEMA_INTEGER;
			*out = type_handle_from_ptr(&ctx->table->i32_type);
			break;
		case EXPR_PLUS: {
			expr->sema_kind = EXPR_SEMA_PLUS;
			TypeHandle a;
			TypeHandle b;
			if (!expr_eval_inner(ctx, expr->as.plus.a, &a, false))
				goto error;
			if (!expr_eval_inner(ctx, expr->as.plus.b, &b, false))
				goto error;
			if (!expr_coerce_binary(ctx, a, expr->as.plus.a, b, expr->as.plus.b,
									out))
				goto error;
			break;
		}
		case EXPR_IDEN: {
			Decl * decl =
				sema_lookup_decl(ctx, expr->as.parsed.iden, DO_REPORT_ERROR);
			if (!decl)
				goto error;
			switch (decl->kind) {
			case DECL_ERROR:
				goto error;
			case DECL_FN:
				if (!fn_proto_eval(ctx, &decl->as.fn))
					goto error;
				*out = decl->as.fn.as.proto;
				break;
			case DECL_VAR:
				if (addr) {
					if (!var_decl_eval(ctx, &decl->as.var))
						goto error;
				} else {
					if (!var_eval(ctx, &decl->as.var))
						goto error;
				}
				*out = decl->as.var.as.decl_evalled.type;
				break;
			case DECL_TYPE_ALIAS:
				TODO("report error");
				goto error;
			}
			if (addr) {
				expr->sema_kind = EXPR_SEMA_LOAD_PTR;
			} else {
				expr->sema_kind = EXPR_SEMA_DEREF;
			}
			expr->as.sema.load_ptr = decl;
			break;
		}
		case EXPR_ADDR: {
			TypeHandle in;
			if (!expr_eval_inner(ctx, expr->as.parsed.addr, &in, true))
				goto error;
			*expr = *expr->as.parsed.addr;
			if (!expr_type_coerce_addr(ctx, in, out)) {
				goto error;
			}
			break;
		}
		case EXPR_DEREF: {
			TypeHandle in;
			if (!expr_eval_inner(ctx, expr->as.parsed.deref, &in, false))
				goto error;
			if (!expr_type_coerce_deref(ctx, in, out))
				goto error;
			expr->sema_kind = EXPR_SEMA_DEREF;
			expr->as.sema.deref = expr->as.parsed.deref;
			break;
		}
		case EXPR_NULLPTR:
			expr->sema_kind = EXPR_SEMA_NULLPTR;
			*out = nullptr_type_handle(ctx);
			break;
		case EXPR_VOID:
			expr->sema_kind = EXPR_SEMA_VOID;
			*out = void_type_handle(ctx);
			break;
		case EXPR_FUNCALL: {
			expr->sema_kind = EXPR_SEMA_FUNCALL;
			TypeHandle in;
			FnType * fn;
			if (!expr_eval_inner(ctx, expr->as.funcall.fun, &in, false))
				goto error;
			if (!expr_type_coerce_function(ctx, in, &fn))
				goto error;
			for (usize i = 0; i < expr->as.funcall.args.size; ++i) {
				Expr * arg = expr->as.funcall.args.data[i];
				TypeHandle expected = fn->params.data[i];
				TypeHandle actual;
				if (!expr_eval_inner(ctx, arg, &actual, false))
					goto error;
				if (!expr_coerce_assignment(ctx, expected, actual, arg))
					goto error;
			}
			*out = fn->return_ty;
			break;
		}
		}
		expr->pass = EXPR_PASS_EVALLED;
		FALLTHROUGH();
	case EXPR_PASS_EVALLED:
		return true;
	}
error:
	expr_set_error(expr);
	return false;
}

bool expr_eval(SemaCtx * ctx, Expr * expr, TypeHandle * out) {
	return expr_eval_inner(ctx, expr, out, false);
}

void sema_ctx_init(SemaCtx * ctx, Ast * ast, VMemArena * arena,
				   TypeInternTable * table, Str src, Str path) {
	ZERO(ctx);
	ctx->env = NULL;
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
			LOG("evaluating fn %s[%p]", decl->iden, &decl->as.alias);
			ok = ok && fn_eval(ctx, &decl->as.fn);
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
