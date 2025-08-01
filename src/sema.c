#include "include/sema.h"
#include "include/arena.h"
#include "include/utility.h"
#include <assert.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>

static SemaExpr void_expr() {
	SemaExpr expr;
	expr.visited_by_cnst_expr_reducer = false;
	expr.type = SEMA_EXPR_VOID;
	return expr;
}

static SemaTypeHandle null_sema_type_handle = {0};

static SemaTypeHandle sema_type_handle_from_ptr(SemaType * type) {
	SemaTypeHandle handle = {
		.type = type
	};
	return handle;
}

static bool sema_type_handle_eq(SemaTypeHandle a, SemaTypeHandle b) {
	if (a.type != b.type) {
		return false;
	}
	if (a.is_lvalue != b.is_lvalue) {
		return false;
	}
	if (a.is_mut != b.is_mut) {
		return false;
	}
	return true;
}

void sema_type_intern_table_init(SemaTypeInternTable * table) {
	sema_type_init_uninterned(&table->void_type, SEMA_TYPE_VOID);
	sema_type_init_uninterned(&table->i32_type, SEMA_TYPE_I32);
	table->tpnl_free_list = nullptr;
	sema_type_list_init(&table->types);
}

static bool sema_ctx_is_global_scope(SemaCtx * ctx) {
	return ctx->lookup_strategy.payload == nullptr;
}

static SemaTypeHandle lookup_type(SemaCtx * ctx, Str iden, ReportError report_error);
static SemaVar * lookup_var(SemaCtx * ctx, Str iden, ReportError report_error);
// here lookup_fn is a hack to make up for the uncomfortable difference between a variable
// and a actual function, which can be self recursively called even if defined in function scopes
// what is likely optimal is some sort of special SemaVar type
// is a hack bc it reiterates the whole env
// a list for each type would be better but haven't gotten around to that
static SemaFn * lookup_fn(SemaCtx * ctx, Str iden, ReportError report_error);


static SemaTypeHandle _lookup_type(SemaCtx * ctx, void * _, Str iden, ReportError report_error) {
	(void)_;
	return lookup_type(ctx, iden, report_error);
}

static SemaVar * _lookup_var(SemaCtx * ctx, void * _, Str iden, ReportError report_error) {
	(void)_;
	return lookup_var(ctx, iden, report_error);
}

static SemaFn * _lookup_fn(SemaCtx * ctx, void * _, Str iden, ReportError report_error) {
	(void)_;
	return lookup_fn(ctx, iden, report_error);
}

static SemaTypeHandle lookup_type_after_completion(SemaCtx * ctx, Str iden, ReportError report_error);

static SemaTypeHandle _lookup_type_after_completion(SemaCtx * ctx, void * _, Str iden, ReportError report_error) {
	(void)_;
	return lookup_type_after_completion(ctx, iden, report_error);
}
static SemaType * unsafe_sema_type_from_fn(SemaTypeFn * fn) {
	const usize offset = offsetof(SemaType, as.fn);
	void * ptr = (u8 *)fn - offset;
	return ptr;
}

void sema_ctx_init(SemaCtx * ctx, VMemArena * arena, SemaTypeInternTable * table, SemaDeclList * env) {
	ctx->env = env;
	ctx->arena = arena;
	ctx->table = table;
	ctx->lookup_strategy.payload = nullptr;
	ctx->lookup_strategy.type_callback = _lookup_type;
	ctx->lookup_strategy.var_callback = _lookup_var;
	ctx->lookup_strategy.fn_callback = _lookup_fn;
}

SemaTypeHandle sema_ctx_lookup_type(SemaCtx * ctx, Str iden, ReportError report_error) {
	return ctx->lookup_strategy.type_callback
		(ctx, ctx->lookup_strategy.payload, iden, report_error);
}
SemaVar * sema_ctx_lookup_var(SemaCtx * ctx, Str iden, ReportError report_error) {
	return ctx->lookup_strategy.var_callback
		(ctx, ctx->lookup_strategy.payload, iden, report_error);
}

SemaFn * sema_ctx_lookup_fn(SemaCtx * ctx, Str iden, ReportError report_error) {
	return ctx->lookup_strategy.fn_callback
		(ctx, ctx->lookup_strategy.payload, iden, report_error);
}

static void sema_type_handle_list_free_with_ctx(SemaCtx * ctx, SemaTypeHandleList * list) {
	if (!list->end) {
		return;
	}
	list->end->next = ctx->table->tpnl_free_list;
	ctx->table->tpnl_free_list = list->begin;
}

static SemaType * sema_type_intern(SemaCtx * ctx, SemaType type) {
	SemaTypeInternTable * table = ctx->table;
	SemaTypeFn * fn;
	SemaType * ptype;
	switch (type.type) {
		case SEMA_TYPE_VOID:
			return &table->void_type;
		case SEMA_TYPE_I32:
			return &table->i32_type;
		case SEMA_TYPE_FN:
			for (SemaTypeNode * node = table->types.begin; node; node = node->next) {
				if (node->type.type != SEMA_TYPE_FN) {
					continue;
				}
				fn = &node->type.as.fn;
				if (fn->return_type != type.as.fn.return_type) {
					continue;
				}
				if (fn->params.count != type.as.fn.params.count) {
					continue;
				}
				for (SemaTypeHandleNode *
					 node = fn->params.begin,
					 *node2 = type.as.fn.params.begin;
				     node;
				     node = node->next, node2 = node2->next) {
				    if (!sema_type_handle_eq(node->type,
							     node2->type)) {
					goto outer;
				    }
				}
				// duplicate found

				// try attach param nodes to free list
				sema_type_handle_list_free_with_ctx(ctx, &type.as.fn.params);
				return &node->type;
outer:

			}
			ptype = sema_type_list_push_front(ctx->arena, &table->types, type);
			if (!ptype) {
				abort();
			}
			return ptype;
		case SEMA_TYPE_TYPE_ALIAS:
			for (SemaTypeNode * node = table->types.begin; node; node = node->next) {
				if (node->type.type != SEMA_TYPE_TYPE_ALIAS) {
					continue;
				}
				if (node->type.as.alias == type.as.alias) {
					return &node->type;
				}
			}
			ptype = sema_type_list_push_front(ctx->arena, &table->types, type);
			if (!ptype) {
				abort();
			}
			return ptype;
	}
	unreachable();
}

static bool sema_type_handle_list_push_with_ctx(SemaCtx * ctx, SemaTypeHandleList * list, SemaTypeHandle type) {
	SemaTypeHandleNode * node;
	if (ctx->table->tpnl_free_list) {
		node = ctx->table->tpnl_free_list;
		ctx->table->tpnl_free_list = node->next;
	} else {
		node = vmem_arena_alloc(ctx->arena, SemaTypeHandleNode);
		if (!node) {
			abort();
		}
	}
	sema_type_handle_list_push_node(list, type, node);
	return true;
}

// requires stable pointer!
static SemaTypeHandle sema_type_alias_intern_with_stable_ptr(SemaCtx * ctx, SemaTypeAlias * alias) {
	SemaType type;
	sema_type_init_uninterned(&type, SEMA_TYPE_TYPE_ALIAS);
	type.as.alias = alias;
	SemaType * ptype = sema_type_intern(ctx, type);
	return sema_type_handle_from_ptr(ptype);
}

static SemaTypeHandle lookup_type(SemaCtx * ctx, Str iden, ReportError report_error) {
	if (str_equal(iden, s("int"))) {
		return sema_type_handle_from_ptr(&ctx->table->i32_type);
	}
	for (SemaDeclNode * node = ctx->env->begin; node; node = node->next) {
		if (!str_equal(node->decl.iden, iden)) {
			continue;
		}
		switch (node->decl.type) {
		case SEMA_DECL_TYPE_ALIAS:
			return sema_type_alias_intern_with_stable_ptr(ctx, &node->decl.as.alias);
		case SEMA_DECL_FN:
		case SEMA_DECL_VAR:
			if (report_error == DO_REPORT_ERROR) {
				fprintf(stderr, "error: identifier '%.*s' is not a type\n", (int)iden.size, iden.data);
			}
			return null_sema_type_handle;
		}
	}
	if (report_error == DO_REPORT_ERROR) {
		fprintf(stderr, "error: unknown identifier '%.*s'\n", (int)iden.size, iden.data);
	}
	return null_sema_type_handle;
}

static SemaTypeHandle lookup_type_after_completion(SemaCtx * ctx, Str iden, ReportError error) {
	SemaTypeHandle handle = lookup_type(ctx, iden, error);
	if (handle.type && handle.type->type == SEMA_TYPE_TYPE_ALIAS) {
		handle = handle.type->as.alias->sema.next;
	}
	return handle;
}

static SemaFn * lookup_fn(SemaCtx * ctx, Str iden, ReportError report_error) {
	for (auto node = ctx->env->begin; node; node = node->next) {
		if (!str_equal(node->decl.iden, iden)) {
			continue;
		}
		switch (node->decl.type) {
		case SEMA_DECL_FN:
			return &node->decl.as.fn;
		case SEMA_DECL_VAR:
			if (report_error == DO_REPORT_ERROR) {
				fprintf(stderr, "error: variable '%.*s' is not a true function\n", (int)iden.size, iden.data);
				// this is a weird edgecase that should ever come up
			}
			return nullptr;
		case SEMA_DECL_TYPE_ALIAS:
			if (report_error == DO_REPORT_ERROR) {
				fprintf(stderr, "error: identifier '%.*s' is not a variable\n", (int)iden.size, iden.data);
			}
			return nullptr;
		}
	}
	if (report_error == DO_REPORT_ERROR) {
		fprintf(stderr, "error: unknown identifier '%.*s'\n", (int)iden.size, iden.data);
	}
	return nullptr;
}

static SemaVar * lookup_var(SemaCtx * ctx, Str iden, ReportError report_error) {
	for (auto node = ctx->env->begin; node; node = node->next) {
		if (!str_equal(node->decl.iden, iden)) {
			continue;
		}
		switch (node->decl.type) {
		case SEMA_DECL_VAR:
			return &node->decl.as.var;
		case SEMA_DECL_TYPE_ALIAS:
		case SEMA_DECL_FN:
			if (report_error == DO_REPORT_ERROR) {
				fprintf(stderr, "error: identifier '%.*s' is not a variable\n", (int)iden.size, iden.data);
			}
			return nullptr;
		}
	}
	if (report_error == DO_REPORT_ERROR) {
		fprintf(stderr, "error: unknown identifier '%.*s'\n", (int)iden.size, iden.data);
	}
	return nullptr;
}

static SemaTypeHandle sema_type_from_ast(SemaCtx * ctx, const Type * type) {
	switch (type->type) {
		case TYPE_VOID:
			return sema_type_handle_from_ptr(&ctx->table->void_type);
		case TYPE_IDEN:
			return sema_ctx_lookup_type(ctx, type->as.iden, DO_REPORT_ERROR);
		case TYPE_FN:
			const TypeFn * ast_fn = &type->as.fn;
			SemaTypeHandle return_handle = sema_type_from_ast(ctx, ast_fn->return_type);
			if (!return_handle.type) {
				return null_sema_type_handle;
			}
			SemaTypeHandleList param_types;
			sema_type_handle_list_init(&param_types);
			for (auto node = ast_fn->params.begin; node; node = node->next) {
				SemaTypeHandle handle = sema_type_from_ast(ctx, &node->type);
				if (!handle.type) {
					return null_sema_type_handle;
				}
				if (!sema_type_handle_list_push_with_ctx(ctx, &param_types, handle)) { // reuses unused nodes
					abort();
				}
			}
			SemaType uninterned_fn_type;
			sema_type_init_uninterned(&uninterned_fn_type, SEMA_TYPE_FN);
			uninterned_fn_type.as.fn.return_type = return_handle.type;
			uninterned_fn_type.as.fn.params = param_types;
			SemaType * fn_type = sema_type_intern(ctx, uninterned_fn_type);
			assert(fn_type);
			return sema_type_handle_from_ptr(fn_type);
		case TYPE_MUT:
			SemaTypeHandle handle = sema_type_from_ast(ctx, type->as.mut);
			handle.is_mut = true;
			return handle;
	}
	unreachable();
}

static bool sema_expr_from_ast(SemaCtx * ctx, const Expr * expr, SemaExpr * out) {
	SemaFn * fn;
	SemaVar * var;
	SemaExpr * a;
	SemaExpr * b;
	SemaExprList list;
	switch (expr->type) {
	case EXPR_POISONED:
		return false;
	case EXPR_INT:
		if (expr->as.int_ > INT32_MAX) {
			fprintf(stderr, "error: integer overflow\n");
			return false;
		}
		sema_expr_init(out, SEMA_EXPR_I32);
		out->as.i32 = (i32)expr->as.int_;
		break;
	case EXPR_IDEN:
		fn = sema_ctx_lookup_fn(ctx, expr->as.iden, DONT_REPORT_ERROR);
		if (fn) {
			sema_expr_init(out, SEMA_EXPR_FN);
			out->as.fn = fn;
			break;
		}
		var = sema_ctx_lookup_var(ctx, expr->as.iden, DO_REPORT_ERROR);
		if (!var) {
			return false;
		}
		sema_expr_init(out, SEMA_EXPR_VAR);
		out->as.var = var;
		break;
	case EXPR_PLUS:
		a = vmem_arena_alloc(ctx->arena, SemaExpr);
		b = vmem_arena_alloc(ctx->arena, SemaExpr);
		if (!a || !b) {
			abort();
		}
		if (!sema_expr_from_ast(ctx, expr->as.plus.a, a)) {
			return false;
		}
		if (!sema_expr_from_ast(ctx, expr->as.plus.b, b)) {
			return false;
		}
		sema_expr_init(out, SEMA_EXPR_PLUS);
		out->as.plus.a = a;
		out->as.plus.b = b;
		break;
	case EXPR_FUNCALL:
		a = vmem_arena_alloc(ctx->arena, SemaExpr);
		if (!a) {
			abort();
		}
		if (!sema_expr_from_ast(ctx, expr->as.funcall.fun, a)) {
			return false;
		}
		sema_expr_list_init(&list);
		for (auto node = expr->as.funcall.args.begin; node; node = node->next) {
			SemaExpr expr;
			if (!sema_expr_from_ast(ctx, &node->expr, &expr)) {
				return false;
			}
			if (!sema_expr_list_push(ctx->arena, &list, expr)) {
				abort();
			}
		}
		sema_expr_init(out, SEMA_EXPR_FUNCALL);
		out->as.funcall.fun = a;
		out->as.funcall.args = list;
		break;
	}
	return true;
}

static bool declare_ast_type_alias(SemaCtx * ctx, SemaTypeAlias * alias) {
	const TypeAlias * ast = alias->ast;
	SemaTypeHandle handle = sema_type_from_ast(ctx, &ast->type);
	if (!handle.type) {
		return false;
	}
	alias->has_sema = true;
	alias->sema.next = handle;
	return true;
}

static bool declare_ast_fn(SemaCtx * ctx, SemaFn * fn) {
	const Fn * ast = fn->ast;
	if (ast->params == &poisoned_fn_param_list) {
		return false;
	}
	SemaTypeHandle return_type = sema_type_from_ast(ctx, &ast->return_type);
	if (!return_type.type) {
		return false;
	}
	SemaTypeHandleList param_types;
	sema_type_handle_list_init(&param_types);
	for (auto node = ast->params->begin; node; node = node->next) {
		SemaTypeHandle type = sema_type_from_ast(ctx, &node->param.type);
		if (!type.type) {
			return false;
		}
		if (!sema_type_handle_list_push_with_ctx(ctx, &param_types, type)) { // reuses unused nodes
			abort();
		}
	}
	SemaType uninterned_fn_type;
	sema_type_init_uninterned(&uninterned_fn_type, SEMA_TYPE_FN);
	uninterned_fn_type.as.fn.return_type = return_type.type;
	uninterned_fn_type.as.fn.params = param_types;
	SemaType * fn_type = sema_type_intern(ctx, uninterned_fn_type);
	assert(fn_type);
	Str * args = vmem_arena_alloc_n(ctx->arena, Str, param_types.count);
	if (!args) {
		abort();
	}
	usize i = 0;
	for (auto node = ast->params->begin; node; node = node->next) {
		if (!str_copy(ctx->arena,
					node->param.has_iden ? node->param.unwrap.iden : s(""),
					args + i)) {
			abort();
		}
		++i;
	}
	fn->has_sema = true;
	fn->sema.signature = &fn_type->as.fn;
	fn->sema.implemented = false;
	fn->sema.args = args;
	return true;
}

static bool declare_ast_var(SemaCtx * ctx, SemaVar * var) {
	const Var * ast = var->as.ast;
	SemaExpr expr;
	SemaTypeHandle type = sema_type_from_ast(ctx, &ast->type);
	if (!type.type) {
		return false;
	}
	type.is_lvalue = true;
	type.is_mut |= ast->is_mut;
	if (ast->init_with_expr) {
		bool result = sema_expr_from_ast(ctx, &ast->unwrap.expr, &expr);
		if (!result) {
			return false;
		}
	}
	sema_var_init(var, type, ast->init_with_expr ? &expr : nullptr, var->global);
	return true;
}

static bool declare_decl(SemaCtx * ctx, SemaDecl * decl) {
	switch (decl->type) {
	case SEMA_DECL_FN:
		if (decl->as.fn.has_sema) {
			return true;
		}
		return declare_ast_fn(ctx, &decl->as.fn);
	case SEMA_DECL_TYPE_ALIAS:
		if (decl->as.alias.has_sema) {
			return true;
		}
		return declare_ast_type_alias(ctx, &decl->as.alias);
	case SEMA_DECL_VAR:
		if (decl->as.var.is_sema) {
			return true;
		}
		return declare_ast_var(ctx, &decl->as.var);
	}
	return false;
}

// this should be a very happy path :)
// populate the type and nested types with size and alignment
// indirect cycles will be ignored as they will get populated eventually
// also will resolve alias indirection here
static SemaTypeHandle populate_type(SemaType * type) {
	SemaTypeHandle ntype;
	type->visited = VISIT_STATUS_VISITED;
	switch (type->type) {
		case SEMA_TYPE_I32:
			type->unwrap.align = alignof(i32);
			type->unwrap.size = sizeof(i32);
			break;
		case SEMA_TYPE_VOID:
			type->unwrap.align = 0; // not complete a type, so 0 it is
			type->unwrap.size = 0;
			break;
		case SEMA_TYPE_TYPE_ALIAS:
			assert(type->as.alias->has_sema);
			ntype = populate_type(type->as.alias->sema.next.type);
			assert(ntype.type->type != SEMA_TYPE_TYPE_ALIAS);
			type->as.alias->sema.next = ntype;
			return ntype;
		case SEMA_TYPE_FN:
			type->unwrap.align = 0; // also not a complete type
			type->unwrap.size = 0;
			// members are indirect cycles, so no work further done
			break;
	}
	return sema_type_handle_from_ptr(type);
}

static SemaTypeHandle complete_type_iter(SemaCtx * ctx, SemaType * type,
				     u32 visit_index_counter,
				     u32 last_indirection_index,
				     u32 last_opaque_index);

static SemaTypeHandle complete_type(SemaCtx * ctx, SemaType * type);

// TODO: use or ensure its not necessary
[[maybe_unused]]static bool complete_and_reduce_type_iter(SemaCtx * ctx, SemaTypeHandle * type,
				     u32 visit_index_counter,
				     u32 last_indirection_index,
				     u32 last_opaque_index) {
	SemaTypeHandle ntype = complete_type_iter(ctx, type->type,
			visit_index_counter, last_indirection_index, last_opaque_index);
	if (!ntype.type) {
		return false;
	}
	*type = ntype;
	return true;
}

static bool complete_and_reduce_type(SemaCtx * ctx, SemaTypeHandle * type) {
	SemaTypeHandle ntype = complete_type(ctx, type->type);
	if (!ntype.type) {
		return false;
	}
	*type = ntype;
	return true;
}

static SemaTypeHandle complete_type_iter(SemaCtx * ctx, SemaType * type,
		u32 visit_index_counter, u32 last_indirection_index, u32 last_opaque_index) {
	if (type->visited == VISIT_STATUS_VISITED) {
		while (type->type == SEMA_TYPE_TYPE_ALIAS) {
			assert(type->as.alias->sema.next.type);
			type = type->as.alias->sema.next.type;
		}
		return sema_type_handle_from_ptr(type);
	}
	if (type->visited == VISIT_STATUS_VISITING) { // potential cycle
		if (type->visit_index < last_indirection_index
			&& type->visit_index <= last_opaque_index) {
			return sema_type_handle_from_ptr(type); // indirect circular dependency all good
		}
		fprintf(stderr, "error: detected cycle\n");
		return null_sema_type_handle;
	}
	type->visit_index = visit_index_counter;
	++visit_index_counter;
	type->visited = VISIT_STATUS_VISITING;
	switch (type->type) {
		case SEMA_TYPE_VOID:
		case SEMA_TYPE_I32:
			break;
		case SEMA_TYPE_FN:
			last_indirection_index = type->visit_index;
			if (!complete_type_iter(ctx, type->as.fn.return_type,
						 visit_index_counter, last_indirection_index, last_opaque_index).type) {
				return null_sema_type_handle;
			}
			for (auto node = type->as.fn.params.begin; node; node = node->next) {
				if (!complete_type_iter(ctx, node->type.type,
							visit_index_counter, last_indirection_index, last_opaque_index).type) {
					return null_sema_type_handle;
				}
			}
			break;
		case SEMA_TYPE_TYPE_ALIAS:
			if (!type->as.alias->has_sema) {
				return null_sema_type_handle;
			}
			if (!complete_type_iter(ctx, type->as.alias->sema.next.type,
						visit_index_counter, last_indirection_index, last_opaque_index).type) {
				return null_sema_type_handle;
			}
			break;
	}
	return populate_type(type);
}

static SemaTypeHandle complete_type(SemaCtx * ctx, SemaType * type) {
	u32 visit_index_counter = 1; // keeps track of the current nodes position in the trace
	u32 last_indirection_index = 0; // stuff like pointers
	u32 last_opaque_index = 0; // stuff like structs that provide a name to avoid infinitely recursive signature
	return complete_type_iter(ctx, type, visit_index_counter, last_indirection_index, last_opaque_index);
}

static bool complete_expr_iter(SemaCtx * ctx, SemaExpr * expr,
								u32 visit_index_counter, u32 last_indirection_index) {
	switch (expr->type) {
	case SEMA_EXPR_VOID:
	case SEMA_EXPR_I32:
		break;
	case SEMA_EXPR_FN:
		break;
	case SEMA_EXPR_PLUS:
		if (!complete_expr_iter(ctx, expr->as.plus.a, visit_index_counter, last_indirection_index)) {
			return false;
		}
		if (!complete_expr_iter(ctx, expr->as.plus.b, visit_index_counter, last_indirection_index)) {
			return false;
		}
		break;
	case SEMA_EXPR_FUNCALL:
		if (!complete_expr_iter(ctx, expr->as.funcall.fun, visit_index_counter, last_indirection_index)) {
			return false;
		}
		for (auto node = expr->as.funcall.args.begin; node; node = node->next) {
			if (!complete_expr_iter(ctx, &node->expr, visit_index_counter, last_indirection_index)) {
				return false;
			}
		}
		break;
	case SEMA_EXPR_VAR:
		if (!expr->as.var->is_sema) {
			return false;
		}
		if (!expr->as.var->as.sema.init_with_expr) {
			fprintf(stderr, "warning: uninitialized global used in constant expression\n");
			break;
		}
		if (expr->as.var->visit_status == VISIT_STATUS_VISITED) {
			break;
		}
		if (expr->as.var->visit_status == VISIT_STATUS_VISITING) {
			if (expr->as.var->visit_index < last_indirection_index) {
				break; // all good again
			}
			fprintf(stderr, "error: detected cycle\n");
			return false;
		}
		expr->as.var->visit_status = VISIT_STATUS_VISITING;
		expr->as.var->visit_index = visit_index_counter++;
		if (!complete_and_reduce_type(ctx, &expr->as.var->as.sema.type)) {
			return false;
		}
		if (!complete_expr_iter(ctx, &expr->as.var->as.sema.unwrap.expr,
					visit_index_counter,
					last_indirection_index)) {
		    return false;
		}
		expr->as.var->visit_status = VISIT_STATUS_VISITED;
		break;
	}
	return true;
}

static bool complete_fn(SemaCtx * ctx, SemaFn * fn) {
	if (!fn->has_sema) {
		return false;
	}
	SemaTypeHandle handle = sema_type_handle_from_ptr(fn->sema.signature->return_type);
	if (!complete_and_reduce_type(ctx, &handle)) {
		return false;
	}
	fn->sema.signature->return_type = handle.type;
	for (auto node = fn->sema.signature->params.begin; node; node = node->next) {
		if (!complete_and_reduce_type(ctx, &node->type)) {
			return false;
		}
	}
	return true;
}

static bool complete_var(SemaCtx * ctx, SemaVar * var) {
	if (!var->is_sema) {
		return false;
	}
	if (!complete_and_reduce_type(ctx, &var->as.sema.type)) {
		return false;
	}
	if (var->visit_status == VISIT_STATUS_VISITED) {
		return true;
	}
	if (!var->as.sema.init_with_expr) {
		var->visit_status = VISIT_STATUS_VISITED;
		return true;
	}
	assert(var->visit_status != VISIT_STATUS_VISITING);
	var->visit_status = VISIT_STATUS_VISITING;
	u32 visit_index_counter = 1;
	u32 last_indirection_index = 0;
	var->visit_index = visit_index_counter++;
	bool result = complete_expr_iter(ctx, &var->as.sema.unwrap.expr,
			visit_index_counter, last_indirection_index);
	var->visit_status = VISIT_STATUS_VISITED;
	return result;
}

static bool complete_decl(SemaCtx * ctx, SemaDecl * decl) {
	switch (decl->type) {
		case SEMA_DECL_FN:
			if (!decl->as.fn.has_sema) {
				return false;
			}
			if (!complete_fn(ctx, &decl->as.fn)) {
				return false;
			}
			break;
		case SEMA_DECL_TYPE_ALIAS:
			if (!decl->as.alias.has_sema) {
				return false;
			}
			if (!complete_and_reduce_type(ctx, &decl->as.alias.sema.next)) {
				return false;
			}
			break;
		case SEMA_DECL_VAR:
			if (!complete_var(ctx, &decl->as.var)) {
				return false;
			}
			break;
	}
	return true;
}

static SemaExpr * coerce_expr_to_type(SemaCtx * ctx, SemaExpr * expr, SemaTypeHandle expr_type, SemaTypeHandle target_type) {
	(void)ctx;
	if (expr_type.type == target_type.type) {
		return expr;
	}
	fputs("error: mismatched types (", stderr);
	sema_print_type(stderr, expr_type);
	fputs(") (", stderr);
	sema_print_type(stderr, target_type);
	fputs(")\n", stderr);
	return nullptr; // for now
}

static bool coerce_exprs_binary_arithmetic(SemaCtx * ctx, SemaExpr * a, SemaTypeHandle at, SemaExpr * b, SemaTypeHandle bt, SemaTypeHandle * out) {
	(void)a; (void)b;
	bool check = at.type->type == SEMA_TYPE_I32 && (at.type == bt.type);
	if (!check) {
		fprintf(stderr, "error: binary arithmetic (expected integers)\n");
		return false;
	}
	*out = sema_type_handle_from_ptr(&ctx->table->i32_type);
	return true;
}

typedef enum {
	EXPR_EVAL_ERROR = 0, // error occured
	EXPR_EVAL_UNREDUCED, // was not able to evaluate at compile time
	EXPR_EVAL_REDUCED,  // was able to evaluate at compile time
} ExprEvalResult;

static ExprEvalResult typecheck_and_reduce_expr(SemaCtx * ctx, SemaExpr * expr, SemaTypeHandle * result);

static ExprEvalResult typecheck_and_reduce_plus_expr(SemaCtx * ctx, SemaExpr * expr, SemaTypeHandle * result_type) {
	auto plus = expr->as.plus;
	SemaTypeHandle a_type;
	SemaTypeHandle b_type;
	if (!typecheck_and_reduce_expr(ctx, plus.a, &a_type)) {
		return EXPR_EVAL_ERROR;
	}
	if (!typecheck_and_reduce_expr(ctx, plus.b, &b_type)) {
		return EXPR_EVAL_ERROR;
	}
	if (!coerce_exprs_binary_arithmetic(ctx, plus.a, a_type, plus.b, b_type, result_type)) {
		return EXPR_EVAL_ERROR;
	}
	if (plus.a->type == SEMA_EXPR_I32 && plus.b->type == SEMA_EXPR_I32) {
		i32 result;
		if (!ckd_add(plus.a->as.i32, plus.b->as.i32, &result)) {
			fprintf(stderr, "error: integer overflow\n");
			return EXPR_EVAL_ERROR;
		}
		expr->type = SEMA_EXPR_I32;
		expr->as.i32 = result;
		return EXPR_EVAL_REDUCED;
	}
	return EXPR_EVAL_UNREDUCED;
}

static ExprEvalResult typecheck_and_reduce_funcall_expr(SemaCtx * ctx, SemaExpr * expr, SemaTypeHandle * result) {
	auto funcall = expr->as.funcall;
	SemaTypeHandle fn_type;
	if (!typecheck_and_reduce_expr(ctx, funcall.fun, &fn_type)) {
		return EXPR_EVAL_ERROR;
	}
	if (fn_type.type->type != SEMA_TYPE_FN) {
		fprintf(stderr, "tried to call non function\n");
		return EXPR_EVAL_ERROR;
	}
	SemaExprNode * node;
	SemaTypeHandleNode * node2;
	if (fn_type.type->as.fn.params.count != funcall.args.count) {
		fprintf(stderr, "called function with wrong arity %lu %lu\n",
				fn_type.type->as.fn.params.count, funcall.args.count);
		return EXPR_EVAL_ERROR;
	}
	for (node = funcall.args.begin, node2 = fn_type.type->as.fn.params.begin; node; node = node->next, node2 = node2->next) {
		if (!typecheck_and_reduce_expr(ctx, &node->expr, result)) {
			return EXPR_EVAL_ERROR;
		}
		if (!coerce_expr_to_type(ctx, &node->expr, *result, node2->type)) {
			return EXPR_EVAL_ERROR;
		}
	}
	*result = sema_type_handle_from_ptr(fn_type.type->as.fn.return_type);
	return EXPR_EVAL_UNREDUCED; // compile time function eval not supported yet
}

static ExprEvalResult typecheck_and_reduce_var_expr(SemaCtx * ctx, SemaExpr * expr, SemaTypeHandle * result) {
	auto var = expr->as.var;
	assert(var->is_sema);
	*result = var->as.sema.type;
	if (!var->as.sema.init_with_expr) {
		return EXPR_EVAL_UNREDUCED;
	}
	ExprEvalResult reduction_status = typecheck_and_reduce_expr(ctx, &var->as.sema.unwrap.expr, result);
	if (!typecheck_and_reduce_expr(ctx, &var->as.sema.unwrap.expr, result)) {
		return EXPR_EVAL_ERROR;
	}
	if (result->type == nullptr) {
		*result = var->as.sema.type;
	}
	if (!coerce_expr_to_type(ctx, &var->as.sema.unwrap.expr, *result, var->as.sema.type)) {
		return EXPR_EVAL_ERROR;
	}
	if (sema_ctx_is_global_scope(ctx)) {
		*expr = var->as.sema.unwrap.expr;
		if (reduction_status == EXPR_EVAL_REDUCED) {
			return EXPR_EVAL_REDUCED;
		}
	}
	return EXPR_EVAL_UNREDUCED;
}

static ExprEvalResult typecheck_and_reduce_expr(SemaCtx * ctx, SemaExpr * expr, SemaTypeHandle * result) {
	if (expr->visited_by_cnst_expr_reducer) {
		switch (expr->type) {
			case SEMA_EXPR_I32:
				*result = sema_type_handle_from_ptr(&ctx->table->i32_type);
				return EXPR_EVAL_REDUCED;
			case SEMA_EXPR_VOID:
				*result = sema_type_handle_from_ptr(&ctx->table->void_type);
				return EXPR_EVAL_REDUCED;
			case SEMA_EXPR_FN:
				*result = sema_type_handle_from_ptr(unsafe_sema_type_from_fn(expr->as.fn->sema.signature));
				return EXPR_EVAL_REDUCED;
			case SEMA_EXPR_FUNCALL:
			case SEMA_EXPR_VAR:
			case SEMA_EXPR_PLUS:
				*result = null_sema_type_handle;
				return EXPR_EVAL_UNREDUCED;
		}
	}
	expr->visited_by_cnst_expr_reducer = true;
	switch (expr->type) {
		case SEMA_EXPR_I32:
			*result = sema_type_handle_from_ptr(&ctx->table->i32_type);
			return EXPR_EVAL_REDUCED;
		case SEMA_EXPR_VOID:
			*result = sema_type_handle_from_ptr(&ctx->table->i32_type);
			return EXPR_EVAL_REDUCED;
		case SEMA_EXPR_FN:
			assert(expr->as.fn->has_sema);
			*result = sema_type_handle_from_ptr(unsafe_sema_type_from_fn(expr->as.fn->sema.signature));
			return EXPR_EVAL_REDUCED;
		case SEMA_EXPR_PLUS:
			return typecheck_and_reduce_plus_expr(ctx, expr, result);
		case SEMA_EXPR_FUNCALL:
			return typecheck_and_reduce_funcall_expr(ctx, expr, result);
		case SEMA_EXPR_VAR:
			return typecheck_and_reduce_var_expr(ctx, expr, result);
	}
	unreachable();
}

static bool implement_var(SemaCtx * ctx, SemaVar * var) {
	// constant evaluation basically
	assert(var->is_sema);
	if (!var->as.sema.init_with_expr) {
		return true;
	}
	SemaExpr * expr = &var->as.sema.unwrap.expr;
	SemaTypeHandle result;
	ExprEvalResult eval_result = typecheck_and_reduce_expr(ctx, expr, &result);
	if (eval_result == EXPR_EVAL_ERROR) {
		return false;
	}
	assert(result.type && "how did you get here?\n");
	if (eval_result == EXPR_EVAL_UNREDUCED) {
		fprintf(stderr, "error: global variable initialized with non-constant expression\n");
		return false;
	}
	if (!coerce_expr_to_type(ctx, expr, result, var->as.sema.type)) {
		return false;
	}
	return true;
}

static SemaTypeHandle lookup_type_blk_env(SemaCtx * ctx, void * payload, Str iden, ReportError report_error) {
	SemaBlkEnv * env = payload;
	for (auto node = env->variables.begin; node; node = node->next) {
		if (!str_equal(iden, node->decl.iden)) {
			continue;
		}
		switch (node->decl.type) {
		case SEMA_DECL_TYPE_ALIAS:
			assert(node->decl.as.alias.has_sema);
			return node->decl.as.alias.sema.next;
		case SEMA_DECL_FN:
		case SEMA_DECL_VAR:
			if (report_error == DO_REPORT_ERROR) {
				if (report_error == DO_REPORT_ERROR) {
					fprintf(stderr, "error: identifier '%.*s' is not a type\n", (int)iden.size, iden.data);
				}
				return null_sema_type_handle;
			}
		}
	}
	if (env->parent) {
		return lookup_type_blk_env(ctx, env->parent, iden, report_error);
	}
	return lookup_type_after_completion(ctx, iden, report_error);
}

static SemaVar * lookup_var_blk_env(SemaCtx * ctx, void * payload, Str iden, ReportError report_error) {
	SemaBlkEnv * env = payload;
	for (auto node = env->variables.begin; node; node = node->next) {
		if (!str_equal(iden, node->decl.iden)) {
			continue;
		}
		switch (node->decl.type) {
		case SEMA_DECL_VAR:
			assert(node->decl.as.var.is_sema);
			return &node->decl.as.var;
		case SEMA_DECL_TYPE_ALIAS:
		case SEMA_DECL_FN:
			if (report_error == DO_REPORT_ERROR) {
				if (report_error == DO_REPORT_ERROR) {
					fprintf(stderr, "error: identifier '%.*s' is not a variable\n", (int)iden.size, iden.data);
				}
				return nullptr;
			}
		}
	}
	if (env->parent) {
		return lookup_var_blk_env(ctx, env->parent, iden, report_error);
	}
	return lookup_var(ctx, iden, report_error);
}

static SemaFn * lookup_fn_blk_env(SemaCtx * ctx, void * payload, Str iden, ReportError report_error) {
	SemaBlkEnv * env = payload;
	for (auto node = env->variables.begin; node; node = node->next) {
		if (!str_equal(iden, node->decl.iden)) {
			continue;
		}
		switch (node->decl.type) {
		case SEMA_DECL_FN:
			assert(node->decl.as.fn.has_sema);
			return &node->decl.as.fn;
		case SEMA_DECL_VAR:
		case SEMA_DECL_TYPE_ALIAS:
			if (report_error == DO_REPORT_ERROR) {
				if (report_error == DO_REPORT_ERROR) {
					fprintf(stderr, "error: identifier '%.*s' is not a function\n", (int)iden.size, iden.data);
				}
				return nullptr;
			}
		}
	}
	if (env->parent) {
		return lookup_fn_blk_env(ctx, env->parent, iden, report_error);
	}
	return lookup_fn(ctx, iden, report_error);
}

static bool implement_stmt_block(SemaCtx * ctx, StmtList block, SemaStmtList * out);

static bool implement_local_decl(SemaCtx * ctx, Decl * ast, SemaDecl * out) {
	Str iden;
	switch (ast->type) {
		case DECL_TYPE_ALIAS:
			if (!str_copy(ctx->arena, ast->as.alias.iden, &iden)) {
				abort();
			}
			sema_decl_init(out, SEMA_DECL_TYPE_ALIAS, iden);
			out->as.alias.has_sema = false;
			out->as.alias.ast = &ast->as.alias;
			return declare_ast_type_alias(ctx, &out->as.alias);
		case DECL_FN:
			if (!str_copy(ctx->arena, ast->as.fn.iden, &iden)) {
				abort();
			}
			sema_decl_init(out, SEMA_DECL_FN, iden);
			out->as.fn.has_sema = false;
			out->as.fn.ast = &ast->as.fn;
			return declare_ast_fn(ctx, &out->as.fn);
		case DECL_VAR:
			if (!str_copy(ctx->arena, ast->as.var.iden, &iden)) {
				abort();
			}
			sema_decl_init(out, SEMA_DECL_VAR, iden);
			out->as.var.is_sema = false;
			out->as.var.as.ast = &ast->as.var;
			return declare_ast_var(ctx, &out->as.var);
	}
	unreachable();
}

static bool implement_stmt(SemaCtx * ctx, Stmt stmt, SemaStmtList * blk_out) {
	SemaBlkEnv * env = ctx->lookup_strategy.payload;
	SemaStmt out_stmt;
	SemaBlkEnv chld_env;
	SemaTypeHandle type;
	switch (stmt.type) {
	case STMT_SEMICOLON:
		return true;
	case STMT_RETURN:
		sema_stmt_init(&out_stmt, SEMA_STMT_RETURN);
		if (stmt.as.return_.has_expr) {
			if (!sema_expr_from_ast(ctx, &stmt.as.return_.unwrap.expr, &out_stmt.as.return_)) {
				return false;
			}
			if (!typecheck_and_reduce_expr(ctx, &out_stmt.as.return_, &type)) {
				return false;
			}
			if (!coerce_expr_to_type(ctx, &out_stmt.as.return_, type, 
						sema_type_handle_from_ptr(env->return_type))) {
				return false;
			}
		} else {
			out_stmt.as.return_ = void_expr();
		}
		break;
	case STMT_BLOCK:
		sema_decl_list_init(&chld_env.variables);
		chld_env.parent = env;
		chld_env.return_type = env->return_type;
		ctx->lookup_strategy.payload = &chld_env;
		bool result = implement_stmt_block(ctx, stmt.as.block, &chld_env.block);
		ctx->lookup_strategy.payload = env;
		if (!result) {
			return false;
		}
		sema_stmt_init(&out_stmt, SEMA_STMT_BLOCK);
		out_stmt.as.block = chld_env;
		break;
	case STMT_EXPR:
		sema_stmt_init(&out_stmt, SEMA_STMT_EXPR);
		if (!sema_expr_from_ast(ctx, &stmt.as.expr, &out_stmt.as.expr)) {
			return false;
		}
		// fprintf(stderr, "> %d\n", out_stmt.as.expr.type);
		if (!typecheck_and_reduce_expr(ctx, &out_stmt.as.expr, &type)) {
			return false;
		}
		break;
	case STMT_DECL:
		SemaDecl decl;
		if (!implement_local_decl(ctx, stmt.as.decl, &decl)) {
			return false;
		}
		if (!sema_decl_list_push(ctx->arena, &env->variables, decl)) {
			abort();
		}
		return true;
	}
	if (!sema_stmt_list_push(ctx->arena, blk_out, out_stmt)) {
		abort();
	}
	return true;
}

static bool implement_stmt_block(SemaCtx * ctx, StmtList block, SemaStmtList * out) {
	sema_stmt_list_init(out);
	for (auto node = block.begin; node; node = node->next) {
		if (!implement_stmt(ctx, node->stmt, out)) {
			return false;
		}
	}
	return true;
}

static bool implement_fn(SemaCtx * ctx, SemaFn * fn) {
	SemaBlkEnv env;
	assert(fn->has_sema);
	env.parent = nullptr;
	env.return_type = fn->sema.signature->return_type;
	sema_decl_list_init(&env.variables);
	usize index = 0;
	for (auto node = fn->sema.signature->params.begin; node; node = node->next) {
		SemaTypeHandle type = node->type;
		type.is_lvalue = true;
		Str arg = fn->sema.args[index++];
		if (str_empty(arg)) {
			continue;
		}
		SemaDecl decl;
		decl.type = SEMA_DECL_VAR;
		sema_decl_init(&decl, SEMA_DECL_VAR, arg);
		sema_var_init(&decl.as.var, type, nullptr, false);
		if (!sema_decl_list_push(ctx->arena, &env.variables, decl)) {
			abort();
		}
	}
	SemaDeclLookupStrategy strategy = ctx->lookup_strategy;
	ctx->lookup_strategy.payload = &env;
	ctx->lookup_strategy.type_callback = &lookup_type_blk_env;
	ctx->lookup_strategy.var_callback = &lookup_var_blk_env;
	ctx->lookup_strategy.fn_callback = &lookup_fn_blk_env;
	bool result = implement_stmt_block(ctx, fn->ast->body, &env.block);
	ctx->lookup_strategy = strategy;
	if (!result) {
		return false;
	}
	fn->sema.implemented = true;
	fn->sema.unwrap.body = env;
	return true;
}

static bool implement_decl(SemaCtx * ctx, SemaDecl * decl) {
	switch (decl->type) {
	case SEMA_DECL_TYPE_ALIAS:
		return true;
	case SEMA_DECL_FN:
		return implement_fn(ctx, &decl->as.fn);
	case SEMA_DECL_VAR:
		return implement_var(ctx, &decl->as.var);
	}
	unreachable();
}

bool sema_analyze_ast(SemaCtx * ctx, Ast ast) {
	for (DeclNode * node = ast.begin; node; node = node->next) {
		SemaDecl decl;
		Str iden;
		switch (node->decl.type) {
		case DECL_TYPE_ALIAS:
			if (!str_copy(ctx->arena, node->decl.as.alias.iden, &iden)) {
				abort();
			}
			sema_decl_init(&decl, SEMA_DECL_TYPE_ALIAS, iden);
			decl.as.alias.has_sema = false;
			decl.as.alias.ast = &node->decl.as.alias;
			SemaDecl * pdecl = sema_decl_list_push(ctx->arena, ctx->env, decl);
			if (!pdecl) {
				abort();
			}
			assert(sema_type_alias_intern_with_stable_ptr(ctx, &pdecl->as.alias).type);
			break;
		case DECL_FN:
			if (!str_copy(ctx->arena, node->decl.as.fn.iden, &iden)) {
				abort();
			}
			sema_decl_init(&decl, SEMA_DECL_FN, iden);
			decl.as.fn.has_sema = false;
			decl.as.fn.ast = &node->decl.as.fn;
			if (!sema_decl_list_push(ctx->arena, ctx->env, decl)) {
				abort();
			}
			break;
		case DECL_VAR:
			if (!str_copy(ctx->arena, node->decl.as.var.iden, &iden)) {
				abort();
			}
			sema_decl_init(&decl, SEMA_DECL_VAR, iden);
			sema_var_init_with_ast(&decl.as.var, &node->decl.as.var, true);
			if (!sema_decl_list_push(ctx->arena, ctx->env, decl)) {
				abort();
			}
			break;
		}
	}

	for (SemaDeclNode * node = ctx->env->begin; node; node = node->next) {
	    if (!declare_decl(ctx, &node->decl)) {
	    }
	}
	for (auto node = ctx->env->begin; node; node = node->next) {
		if (!complete_decl(ctx, &node->decl)) {
			return false; // just throw the towel in now
		}
	}
	ctx->lookup_strategy.type_callback = _lookup_type_after_completion;
	for (auto node = ctx->env->begin; node; node = node->next) {
		if (!implement_decl(ctx, &node->decl)) {
			return false; // the real guts
		}
	}
	return true;
}

void sema_print_type(FILE * file, SemaTypeHandle handle) {
	switch (handle.type->type) {
	case SEMA_TYPE_I32:
		fprintf(file, "int");
		break;
	case SEMA_TYPE_VOID:
		fprintf(file, "void");
		break;
	case SEMA_TYPE_FN:
		fputs("fn(", file);
		const char * sep = "";
		for (auto node = handle.type->as.fn.params.begin; node; node = node->next) {
			fputs(sep, file);
			sep = ", ";
			sema_print_type(file, node->type);
		}
		fputs("): ", file);
		sema_print_type(file, 
				sema_type_handle_from_ptr(handle.type->as.fn.return_type));
		break;
	case SEMA_TYPE_TYPE_ALIAS:
		assert(false && "no current context where this makes sense");
		break;
	}
}

void sema_type_init_uninterned(SemaType * type, SemaTypeType typetype) {
	type->type = typetype;
	type->visited = VISIT_STATUS_UNVISITED;
}

void sema_expr_init(SemaExpr * expr, SemaExprType type) {
	expr->type = type;
	expr->visited_by_cnst_expr_reducer = false;
}

void sema_stmt_init(SemaStmt * stmt, SemaStmtType type) {
	stmt->type = type;
}

void sema_var_init_with_ast(SemaVar * var, const Var * ast, bool global) {
	var->global = global;
	var->is_sema = false;
	var->as.ast = ast;
	var->visit_status = VISIT_STATUS_UNVISITED;
}

void sema_var_init(SemaVar * var, SemaTypeHandle type, SemaExpr * opt_expr, bool global) {
	var->global = global;
	var->is_sema = true;
	var->as.sema.init_with_expr = opt_expr != nullptr;
	var->as.sema.type = type;
	if (opt_expr != nullptr) {
		var->as.sema.unwrap.expr = *opt_expr;
	}
	var->visit_status = global ? VISIT_STATUS_VISITED : VISIT_STATUS_UNVISITED;
}

void sema_decl_init(SemaDecl * decl, SemaDeclType type, Str iden) {
	decl->type = type;
	decl->iden = iden;
}

void sema_type_list_init(SemaTypeList * list) {
	ZERO(list);
}

SemaType * sema_type_list_push_front(VMemArena * arena, SemaTypeList * list, SemaType type) {
	auto node = vmem_arena_alloc(arena, SemaTypeNode);
	if (!node) {
		return nullptr;
	}
	node->type = type;
	node->next = list->begin;
	list->begin = node;
	if (!list->end) {
		list->end = node;
	}
	return &node->type;
}

void sema_type_handle_list_init(SemaTypeHandleList * list) {
	ZERO(list);
}

void sema_type_handle_list_push_node(SemaTypeHandleList * list, SemaTypeHandle type, SemaTypeHandleNode * node) {
	node->type = type;
	node->next = nullptr;
	if (!list->begin) {
		list->begin = node;
	}
	if (list->end) {
		list->end->next = node;
	}
	list->end = node;
	++list->count;
}

bool sema_type_handle_list_push(VMemArena * arena, SemaTypeHandleList * list, SemaTypeHandle type) {
	auto node = vmem_arena_alloc(arena, SemaTypeHandleNode);
	if (!node) {
		return false;
	}
	sema_type_handle_list_push_node(list, type, node);
	return true;
}

void sema_type_handle_list_push_node_front(SemaTypeHandleList * list, SemaTypeHandle type, SemaTypeHandleNode * node) {
	node->type = type;
	node->next = list->begin;
	list->begin = node;
	if (!list->end) {
		list->end = node;
	}
}

bool sema_type_handle_list_push_front(VMemArena * arena, SemaTypeHandleList * list, SemaTypeHandle type) {
	auto node = vmem_arena_alloc(arena, SemaTypeHandleNode);
	if (!node) {
		return false;
	}
	sema_type_handle_list_push_node_front(list, type, node);
	return true;
}

void sema_type_handle_list_pop_front(SemaTypeHandleList * list) {
	list->begin = list->begin->next;
	if (list->begin == nullptr) {
		list->end = nullptr;
	}
}

void sema_expr_list_init(SemaExprList * list) {
	ZERO(list);
}

SemaExpr * sema_expr_list_push(VMemArena * arena, SemaExprList * list, SemaExpr expr) {
	auto node = vmem_arena_alloc(arena, SemaExprNode);
	if (!node) {
		return nullptr;
	}
	node->expr = expr;
	node->next = nullptr;
	if (!list->begin) {
		list->begin = node;
	} else {
		list->end->next = node;
	}
	list->end = node;
	++list->count;
	return &node->expr;
}

void sema_stmt_list_init(SemaStmtList * list) {
	ZERO(list);
}

SemaStmt * sema_stmt_list_push(VMemArena * arena, SemaStmtList * list, SemaStmt stmt) {
	auto node = vmem_arena_alloc(arena, SemaStmtNode);
	if (!node) {
		return nullptr;
	}
	node->stmt = stmt;
	node->next = nullptr;
	if (!list->begin) {
		list->begin = node;
	} else {
		list->end->next = node;
	}
	list->end = node;
	return &node->stmt;
}

void sema_decl_list_init(SemaDeclList * list) {
	ZERO(list);
}

SemaDecl * sema_decl_list_push(VMemArena * arena, SemaDeclList * list, SemaDecl decl) {
	auto node = vmem_arena_alloc(arena, SemaDeclNode);
	if (!node) {
		return nullptr;
	}
	node->decl = decl;
	node->next = nullptr;
	if (!list->begin) {
		list->begin = node;
	} else {
		list->end->next = node;
	}
	list->end = node;
	return &node->decl;
}
