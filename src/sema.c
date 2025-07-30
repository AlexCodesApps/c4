#include "include/sema.h"
#include "include/arena.h"
#include "include/utility.h"
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>

void sema_type_intern_table_init(SemaTypeInternTable * table) {
	table->void_type.type = SEMA_TYPE_VOID;
	table->void_type.visited = VISIT_STATUS_UNVISITED;
	table->i32_type.type = SEMA_TYPE_I32;
	table->i32_type.visited = VISIT_STATUS_UNVISITED;
	table->tpnl_free_list = nullptr;
	sema_type_list_init(&table->types);
}

void sema_ctx_init(SemaCtx * ctx, VMemArena * arena, SemaTypeInternTable * table, SemaDeclList * env) {
	ctx->env = env;
	ctx->arena = arena;
	ctx->table = table;
}

static void sema_type_ptr_list_free_with_ctx(SemaCtx * ctx, SemaTypePtrList * list) {
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
				for (SemaTypePtrNode * node = fn->params.begin, * node2 = type.as.fn.params.begin; node; node = node->next, node2 = node2->next) {
					if (node->type != node2->type) {
						goto outer;
					}
				}
				// duplicate found

				// try attach param nodes to free list
				sema_type_ptr_list_free_with_ctx(ctx, &type.as.fn.params);
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
	assert(false && "unreachable");
}

static bool sema_type_ptr_list_push_with_ctx(SemaCtx * ctx, SemaTypePtrList * list, SemaType * type) {
	SemaTypePtrNode * node;
	if (ctx->table->tpnl_free_list) {
		node = ctx->table->tpnl_free_list;
		ctx->table->tpnl_free_list = node->next;
	} else {
		node = vmem_arena_alloc(ctx->arena, SemaTypePtrNode);
		if (!node) {
			abort();
		}
	}
	sema_type_ptr_list_push_node(list, type, node);
	return true;
}

static bool sema_type_ptr_list_push_front_with_ctx(SemaCtx * ctx, SemaTypePtrList * list, SemaType * type) {
	SemaTypePtrNode * node;
	if (ctx->table->tpnl_free_list) {
		node = ctx->table->tpnl_free_list;
		ctx->table->tpnl_free_list = node->next;
	} else {
		node = vmem_arena_alloc(ctx->arena, SemaTypePtrNode);
		if (!node) {
			abort();
		}
	}
	sema_type_ptr_list_push_node_front(list, type, node);
	return true;
}

// requires stable pointer!
static SemaType * sema_type_alias_intern(SemaCtx * ctx, SemaTypeAlias * alias) {
	SemaType type;
	type.type = SEMA_TYPE_TYPE_ALIAS;
	type.visited = VISIT_STATUS_UNVISITED;
	type.as.alias = alias;
	return sema_type_intern(ctx, type);
}

static SemaType * lookup_type(SemaCtx * ctx, Str iden, ReportError report_error) {
	if (str_equal(iden, s("int"))) {
		return &ctx->table->i32_type;
	}
	for (SemaDeclNode * node = ctx->env->begin; node; node = node->next) {
		if (!str_equal(node->decl.iden, iden)) {
			continue;
		}
		switch (node->decl.type) {
		case SEMA_DECL_TYPE_ALIAS:
			return sema_type_alias_intern(ctx, &node->decl.as.alias);
		case SEMA_DECL_FN:
		case SEMA_DECL_VAR:
			if (report_error == DO_REPORT_ERROR) {
				fprintf(stderr, "error: identifier '%.*s' is not a type\n", (int)iden.size, iden.data);
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

static SemaType * sema_type_from_ast(SemaCtx * ctx, const Type * type) {
	switch (type->type) {
		case TYPE_VOID:
			return &ctx->table->void_type;
		case TYPE_IDEN:
			return lookup_type(ctx, type->as.iden, DO_REPORT_ERROR);
		case TYPE_FN:
			const TypeFn * ast_fn = &type->as.fn;
			SemaType * return_type = sema_type_from_ast(ctx, ast_fn->return_type);
			if (!return_type) {
				return nullptr;
			}
			SemaTypePtrList param_types;
			sema_type_ptr_list_init(&param_types);
			for (auto node = ast_fn->params.begin; node; node = node->next) {
				SemaType * type = sema_type_from_ast(ctx, &node->type);
				if (!type) {
					return nullptr;
				}
				if (!sema_type_ptr_list_push_with_ctx(ctx, &param_types, type)) { // reuses unused nodes
					abort();
				}
			}
			SemaType uninterned_fn_type;
			uninterned_fn_type.type = SEMA_TYPE_FN;
			uninterned_fn_type.visited = VISIT_STATUS_UNVISITED;
			uninterned_fn_type.as.fn.return_type = return_type;
			uninterned_fn_type.as.fn.params = param_types;
			SemaType * fn_type = sema_type_intern(ctx, uninterned_fn_type);
			assert(fn_type);
			return fn_type;
	}
	assert(false && "unreachable");
}

static bool sema_expr_from_ast(SemaCtx * ctx, const Expr * expr, SemaExpr * out) {
	SemaVar * var;
	SemaExpr * a;
	SemaExpr * b;
	SemaExprList list;
	switch (expr->type) {
	case EXPR_INT:
		out->type = SEMA_EXPR_I32;
		if (expr->as.int_ > INT32_MAX) {
			return false;
		}
		out->as.i32 = expr->as.int_;
		break;
	case EXPR_IDEN:
		var = lookup_var(ctx, expr->as.iden, DO_REPORT_ERROR);
		if (!var) {
			return false;
		}
		out->type = SEMA_EXPR_VAR;
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
		out->type = SEMA_EXPR_PLUS;
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
			if (!sema_expr_from_ast(ctx, node->expr, &expr)) {
				return false;
			}
			if (!sema_expr_list_push(ctx->arena, &list, expr)) {
				abort();
			}
		}
		break;
	}
	return true;
}

static bool declare_ast_type_alias(SemaCtx * ctx, SemaTypeAlias * alias) {
	const TypeAlias * ast = alias->incomplete;
	SemaType * type = sema_type_from_ast(ctx, &ast->type);
	if (!type) {
		return false;
	}
	alias->is_complete = true;
	alias->complete.aliasing = type;
	return true;
}

static bool declare_ast_fn(SemaCtx * ctx, SemaFn * fn) {
	const Fn * ast = fn->incomplete;
	SemaType * return_type = sema_type_from_ast(ctx, &ast->return_type);
	if (!return_type) {
		return false;
	}
	SemaTypePtrList param_types;
	sema_type_ptr_list_init(&param_types);
	for (auto node = ast->params->begin; node; node = node->next) {
		SemaType * type = sema_type_from_ast(ctx, &node->param.type);
		if (!type) {
			return false;
		}
		if (!sema_type_ptr_list_push_with_ctx(ctx, &param_types, type)) { // reuses unused nodes
			abort();
		}
	}
	SemaType uninterned_fn_type;
	uninterned_fn_type.type = SEMA_TYPE_FN;
	uninterned_fn_type.visited = VISIT_STATUS_UNVISITED;
	uninterned_fn_type.as.fn.return_type = return_type;
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
	fn->is_complete = true;
	fn->complete.signature = &fn_type->as.fn;
	fn->complete.implemented = false;
	fn->complete.args = args;
	return true;
}

static bool declare_ast_var(SemaCtx * ctx, SemaVar * var) {
	SemaType * type = sema_type_from_ast(ctx, &var->incomplete->type);
	if (!type) {
		return false;
	}
	var->complete.type = type;
	var->complete.init_with_expr = var->incomplete->init_with_expr;
	if (var->incomplete->init_with_expr) {
		bool result = sema_expr_from_ast(ctx, var->incomplete->unwrap.expr, &var->complete.unwrap.expr);
		if (!result) {
			return false;
		}
	}
	var->is_complete = true;
	return true;
}

static bool declare_decl(SemaCtx * ctx, SemaDecl * decl) {
	switch (decl->type) {
	case SEMA_DECL_FN:
		if (decl->as.fn.is_complete) {
			return true;
		}
		return declare_ast_fn(ctx, &decl->as.fn);
	case SEMA_DECL_TYPE_ALIAS:
		if (decl->as.alias.is_complete) {
			return true;
		}
		return declare_ast_type_alias(ctx, &decl->as.alias);
	case SEMA_DECL_VAR:
		if (decl->as.var.is_complete) {
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
static SemaType * populate_type(SemaType * type) {
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
			assert(type->as.alias->is_complete);
			return populate_type(type->as.alias->complete.aliasing);
			break;
		case SEMA_TYPE_FN:
			type->unwrap.align = 0; // also not a complete type
			type->unwrap.size = 0;
			// members are indirect cycles, so no work further done
			break;
	}
	return type;
}


static bool complete_type_iter(SemaCtx * ctx, SemaType * type,
		u32 visit_index_counter, u32 last_indirection_index, u32 last_opaque_index) {
	if (type->visited == VISIT_STATUS_VISITED) {
		return true;
	}
	if (type->visited == VISIT_STATUS_VISITING) { // potential cycle
		if (type->visit_index < last_indirection_index
			&& type->visit_index <= last_opaque_index) {
			return true; // indirect circular dependency all good
		}
		fprintf(stderr, "error: detected cycle\n");
		return false;
	outer:
	}
	type->visit_index = visit_index_counter;
	++visit_index_counter;
	type->visited = VISIT_STATUS_VISITING;
	switch (type->type) {
		u32 saved_index;
		case SEMA_TYPE_VOID:
		case SEMA_TYPE_I32:
			break;
		case SEMA_TYPE_FN:
			last_indirection_index = type->visit_index;
			if (!complete_type_iter(ctx, type->as.fn.return_type,
						 visit_index_counter, last_indirection_index, last_opaque_index)) {
				return false;
			}
			for (auto node = type->as.fn.params.begin; node; node = node->next) {
				if (!complete_type_iter(ctx, node->type,
							visit_index_counter, last_indirection_index, last_opaque_index)) {
					return false;
				}
			}
			break;
		case SEMA_TYPE_TYPE_ALIAS:
			if (!type->as.alias->is_complete) {
				return false;
			}
			if (!complete_type_iter(ctx, type->as.alias->complete.aliasing,
						visit_index_counter, last_indirection_index, last_opaque_index)) {
				return false;
			}
			break;
	}
	populate_type(type);
	return true;
}

static bool complete_type(SemaCtx * ctx, SemaType * type) {
	u32 visit_index_counter = 1; // keeps track of the current nodes position in the trace
	u32 last_indirection_index = 0; // stuff like pointers
	u32 last_opaque_index = 0; // stuff like structs that provide a name to avoid infinitely recursive signature
	if (!complete_type_iter(ctx, type, visit_index_counter, last_indirection_index, last_opaque_index)) {
		return false;
	}
	return true;
}

static bool complete_expr_iter(SemaCtx * ctx, SemaExpr * expr,
								u32 visit_index_counter, u32 last_indirection_index) {
	switch (expr->type) {
	case SEMA_EXPR_VOID:
	case SEMA_EXPR_I32:
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
		if (!expr->as.var->is_complete) {
			return false;
		}
		if (!expr->as.var->complete.init_with_expr) {
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
		expr->as.var->visit_status = VISIT_STATUS_VISITED;
		expr->as.var->visit_index = visit_index_counter++;
		return complete_expr_iter(ctx, &expr->as.var->complete.unwrap.expr,
				visit_index_counter, last_indirection_index);
	}
	return true;
}

static bool complete_var(SemaCtx * ctx, SemaVar * var) {
	if (!var->is_complete) { // the naming is awkward but this is entirely different
		return false;
	}
	if (!var->complete.init_with_expr) {
		return true;
	}
	if (var->visit_status == VISIT_STATUS_VISITED) {
		return true;
	}
	if (!complete_type(ctx, var->complete.type)) {
		return false;
	}
	assert(var->visit_status != VISIT_STATUS_VISITING);
	var->visit_status = VISIT_STATUS_VISITING;
	u32 visit_index_counter = 1;
	u32 last_indirection_index = 0;
	var->visit_index = visit_index_counter++;
	bool result = complete_expr_iter(ctx, &var->complete.unwrap.expr,
			visit_index_counter, last_indirection_index);
	var->visit_status = VISIT_STATUS_VISITED;
	return result;
}

static bool complete_decl(SemaCtx * ctx, SemaDecl * decl) {
	switch (decl->type) {
		case SEMA_DECL_FN:
			if (!decl->as.fn.is_complete) {
				return false;
			}
			if (!complete_type(ctx, decl->as.fn.complete.signature->return_type)) {
				return false;
			}
			for (auto node = decl->as.fn.complete.signature->params.begin; node; node = node->next) {
				if (!complete_type(ctx, node->type)) {
					return false;
				}
			}
			break;
		case SEMA_DECL_TYPE_ALIAS:
			if (!decl->as.alias.is_complete) {
				return false;
			}
			if (!complete_type(ctx, decl->as.alias.complete.aliasing)) {
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

static bool implement_fn(SemaCtx * ctx, SemaFn * fn) {
}

static bool implement_var(SemaCtx * ctx, SemaVar * var) {
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
}

bool sema_analyze_ast(SemaCtx * ctx, Ast ast) {
	for (DeclNode * node = ast.begin; node; node = node->next) {
		SemaDecl decl;
		Str iden;
		switch (node->decl.type) {
		case DECL_POISONED:
			continue;
		case DECL_TYPE_ALIAS:
			if (!str_copy(ctx->arena, node->decl.as.alias.iden, &iden)) {
				abort();
			}
			decl.iden = iden;
			if (str_equal(decl.iden, s("bar"))) {

			}
			decl.type = SEMA_DECL_TYPE_ALIAS;
			decl.as.alias.is_complete = false;
			decl.as.alias.incomplete = &node->decl.as.alias;
			SemaDecl * pdecl = sema_decl_list_push(ctx->arena, ctx->env, decl);
			if (!pdecl) {
				abort();
			}
			assert(sema_type_alias_intern(ctx, &pdecl->as.alias));
			break;
		case DECL_FN:
			if (!str_copy(ctx->arena, node->decl.as.fn.iden, &iden)) {
				abort();
			}
			decl.iden = iden;
			decl.type = SEMA_DECL_FN;
			decl.as.fn.is_complete = false;
			decl.as.fn.incomplete = &node->decl.as.fn;
			if (!sema_decl_list_push(ctx->arena, ctx->env, decl)) {
				abort();
			}
			break;
		case DECL_VAR:
			if (!str_copy(ctx->arena, node->decl.as.var.iden, &iden)) {
				abort();
			}
			decl.iden = iden;
			decl.type = SEMA_DECL_VAR;
			decl.as.var.visit_status = VISIT_STATUS_UNVISITED;
			decl.as.var.is_complete = false;
			decl.as.var.cnst_init = true;
			decl.as.var.incomplete = &node->decl.as.var;
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
	for (auto node = ctx->env->begin; node; node = node->next) {
		implement_decl(ctx, &node->decl); // the real guts
	}
	return true;
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

void sema_type_ptr_list_init(SemaTypePtrList * list) {
	ZERO(list);
}

void sema_type_ptr_list_push_node(SemaTypePtrList * list, SemaType * type, SemaTypePtrNode * node) {
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

bool sema_type_ptr_list_push(VMemArena * arena, SemaTypePtrList * list, SemaType * type) {
	auto node = vmem_arena_alloc(arena, SemaTypePtrNode);
	if (!node) {
		return false;
	}
	sema_type_ptr_list_push_node(list, type, node);
	return true;
}

void sema_type_ptr_list_push_node_front(SemaTypePtrList * list, SemaType * type, SemaTypePtrNode * node) {
	node->type = type;
	node->next = list->begin;
	list->begin = node;
	if (!list->end) {
		list->end = node;
	}
}

bool sema_type_ptr_list_push_front(VMemArena * arena, SemaTypePtrList * list, SemaType * type) {
	auto node = vmem_arena_alloc(arena, SemaTypePtrNode);
	if (!node) {
		return false;
	}
	sema_type_ptr_list_push_node_front(list, type, node);
	return true;
}

void sema_type_ptr_list_pop_front(SemaTypePtrList * list) {
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
	return &node->expr;
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
