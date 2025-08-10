#include "include/sema.h"
#include "include/arena.h"
#include "include/utility.h"
#include <assert.h>
#include <stddef.h>
#include <stdio.h>

static SemaTypeHandle null_sema_type_handle = {0};

SemaTypeHandle sema_type_handle_from_ptr(SemaType * type) {
	SemaTypeHandle handle = {
		.type = type
	};
	return handle;
}

static bool sema_type_handle_eq(SemaTypeHandle a, SemaTypeHandle b) {
	if (a.type != b.type) {
		return false;
	}
	if (a.is_mut != b.is_mut) {
		return false;
	}
	return true;
}

static VisitorState new_visitor_state(void) {
	return (VisitorState) {
		.last_fn_id = 0,
		.last_indirection_id = 0,
		.last_opaque_id = 0,
		.visit_id = 1,
	};
}

void sema_type_intern_table_init(SemaTypeInternTable * table) {
	sema_type_init_uninterned(&table->void_type, SEMA_TYPE_VOID);
	sema_type_init_uninterned(&table->i32_type, SEMA_TYPE_I32);
	sema_type_init_uninterned(&table->void_ptr_type, SEMA_TYPE_PTR);
	table->void_ptr_type.as.ptr = sema_type_handle_from_ptr(&table->void_type);
	table->void_ptr_type.as.ptr.is_mut = true; // TIL that the type of nullptr is actually a *mut void,
											   // ... or its own type. but that machinery
											   // is probably unnessecary
	table->tpnl_free_list = nullptr;
	sema_type_list_init(&table->types);
	sema_type_handle_list_init(&table->complete_types);
}

SemaDecl * sema_ctx_add_decl(SemaCtx * ctx, SemaDecl decl) {
	SemaDecl * ndecl = sema_decl_list_push(ctx->arena, &ctx->env->decls, decl);
	if (!ndecl) {
		return nullptr;
	}
	if (decl.type == SEMA_DECL_FN || decl.type == SEMA_DECL_VAR) {
		++ctx->root->sym_count;
	}
	return ndecl;
}

void sema_env_init(SemaEnv * env) {
	sema_decl_list_init(&env->decls);
	env->type = SEMA_ENV_MOD;
	env->parent = nullptr;
	env->sym_count = 0;
}

void sema_env_init_push_fn_blk_env(SemaCtx * ctx, SemaEnv * env, SemaType * return_type) {
	sema_decl_list_init(&env->decls);
	env->type = SEMA_ENV_FN_BLK;
	env->parent = ctx->env;
	env->sym_count = 0;
	env->as.fn.return_type = return_type;
	ctx->env = env;
}

void sema_env_pop(SemaCtx * ctx) {
	ctx->env = ctx->env->parent;
}

bool sema_ctx_is_global_scope(SemaCtx * ctx) {
	return ctx->env->type == SEMA_ENV_MOD;
}

bool sema_ctx_is_fn_local(SemaCtx * ctx) {
	return ctx->env->type == SEMA_ENV_FN_BLK;
}

SemaType * sema_type_from_interned_fn(SemaTypeFn * fn) {
	const usize offset = offsetof(SemaType, as.fn);
	void * ptr = (u8 *)fn - offset;
	return ptr;
}

void sema_ctx_init(SemaCtx * ctx, VMemArena * arena, SemaTypeInternTable * table, SemaEnv * env) {
	ctx->env = env;
	ctx->root = env;
	ctx->arena = arena;
	ctx->table = table;
}

_Noreturn void sema_ctx_oom(SemaCtx * ctx) {
	longjmp(ctx->oom_handler, 1);
}

static bool sema_type_handle_list_push_with_ctx(SemaCtx * ctx, SemaTypeHandleList * list, SemaTypeHandle type) {
	SemaTypeHandleNode * node;
	if (ctx->table->tpnl_free_list) {
		node = ctx->table->tpnl_free_list;
		ctx->table->tpnl_free_list = node->next;
	} else {
		node = vmem_arena_alloc(ctx->arena, SemaTypeHandleNode);
		if (!node) {
			sema_ctx_oom(ctx);
		}
	}
	sema_type_handle_list_push_node(list, type, node);
	return true;
}

static void sema_type_handle_list_free_with_ctx(SemaCtx * ctx, SemaTypeHandleList * list) {
	if (!list->end) {
		return;
	}
	list->end->next = ctx->table->tpnl_free_list;
	ctx->table->tpnl_free_list = list->begin;
}

static bool _check_fn(SemaType * type, SemaType * type2) {
	if (type2->type != SEMA_TYPE_FN) {
		return false;
	}
	SemaTypeFn * fn = &type2->as.fn;
	if (fn->return_type != type->as.fn.return_type) {
		return false;
	}
	if (fn->params.count != type->as.fn.params.count) {
		return false;
	}
	for (SemaTypeHandleNode *
		 node = fn->params.begin,
		 *node2 = type->as.fn.params.begin;
		 node;
		 node = node->next, node2 = node2->next) {
		if (!sema_type_handle_eq(node->type,
					 node2->type)) {
			return false;
		}
	}
	return true;
}

static SemaType * sema_type_intern(SemaCtx * ctx, SemaType type) {
	SemaTypeInternTable * table = ctx->table;
	SemaType * ptype;
	switch (type.type) {
		case SEMA_TYPE_VOID:
			return &table->void_type;
		case SEMA_TYPE_I32:
			return &table->i32_type;
		case SEMA_TYPE_FN:
			for (SemaTypeHandleNode * node = table->complete_types.begin; node; node = node->next) {
				if (!_check_fn(&type, node->type.type)) {
					continue;
				}
				sema_type_handle_list_free_with_ctx(ctx, &type.as.fn.params);
				return node->type.type;
			}
			for (SemaTypeNode * node = table->types.begin; node; node = node->next) {
				if (!_check_fn(&type, &node->type)) {
					continue;
				}
				// try attach param nodes to free list
				sema_type_handle_list_free_with_ctx(ctx, &type.as.fn.params);
				return &node->type;
			}
			ptype = sema_type_list_push_front(ctx->arena, &table->types, type);
			if (!ptype) {
				sema_ctx_oom(ctx);
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
				sema_ctx_oom(ctx);
			}
			return ptype;
		case SEMA_TYPE_PTR:
			if (sema_type_handle_eq(type.as.ptr, table->void_ptr_type.as.ptr)) {
				return &table->void_ptr_type;
			}
			for (SemaTypeNode * node = table->types.begin; node; node = node->next) {
				if (node->type.type != SEMA_TYPE_PTR) {
					continue;
				}
				if (sema_type_handle_eq(node->type.as.ptr, type.as.ptr)) {
					return &node->type;
				}
			}
			ptype = sema_type_list_push_front(ctx->arena, &table->types, type);
			if (!ptype) {
				sema_ctx_oom(ctx);
			}
			return ptype;
		case SEMA_TYPE_REF:
			for (SemaTypeNode * node = table->types.begin; node; node = node->next) {
				if (node->type.type != SEMA_TYPE_REF) {
					continue;
				}
				if (sema_type_handle_eq(node->type.as.ref, type.as.ref)) {
					return &node->type;
				}
			}
			ptype = sema_type_list_push_front(ctx->arena, &table->types, type);
			if (!ptype) {
				sema_ctx_oom(ctx);
			}
			return ptype;
	}
	UNREACHABLE();
}

SemaType * sema_type_dedup_implemented(SemaCtx * ctx, SemaType * type) {
	assert(type->pass >= SEMA_PASS_IMPLEMENTED);
	if (type->deduped) {
		return type;
	}
	SemaTypeHandleNode * node1;
	SemaTypeHandleNode * node2;
	for (auto node = ctx->table->complete_types.begin; node; node = node->next) {
		SemaType * type2 = node->type.type;
		if (type->type != type2->type) {
			continue;
		}
		switch (type->type) {
		case SEMA_TYPE_VOID:
		case SEMA_TYPE_I32:
			return type2;
		case SEMA_TYPE_PTR:
			type->as.ptr.type = sema_type_dedup_implemented(ctx, type->as.ptr.type);
			if (sema_type_handle_eq(type->as.ptr, type2->as.ptr)) {
				return type2;
			}
			break;
		case SEMA_TYPE_REF:
			type->as.ref.type = sema_type_dedup_implemented(ctx, type->as.ref.type);
			if (sema_type_handle_eq(type->as.ref, type2->as.ref)) {
				return type2;
			}
			break;
		case SEMA_TYPE_FN:
			type->as.fn.return_type = sema_type_dedup_implemented(ctx, type->as.fn.return_type);
			if (type->as.fn.params.count != type2->as.fn.params.count) {
				break;
			}
			for (node1 = type->as.fn.params.begin, node2 = type2->as.fn.params.begin;
				node1;
				node1 = node1->next, node2 = node2->next) {
				node1->type.type = sema_type_dedup_implemented(ctx, node1->type.type);
				if (!sema_type_handle_eq(node1->type, node2->type)) {
					goto outer;
				}
			}
			return type2;
		case SEMA_TYPE_TYPE_ALIAS:
			UNREACHABLE();
		}
	outer:
	}
	if (!sema_type_handle_list_push_with_ctx(ctx, 
				&ctx->table->complete_types, sema_type_handle_from_ptr(type))) {
		sema_ctx_oom(ctx);
	}
	type->deduped = true;
	return type;
}

// requires stable pointer!
static SemaTypeHandle sema_type_alias_intern_with_stable_ptr(SemaCtx * ctx, SemaTypeAlias * alias) {
	SemaType type;
	sema_type_init_uninterned(&type, SEMA_TYPE_TYPE_ALIAS);
	type.as.alias = alias;
	SemaType * ptype = sema_type_intern(ctx, type);
	return sema_type_handle_from_ptr(ptype);
}

SemaTypeHandle sema_ctx_lookup_type(SemaCtx * ctx, Str iden, ReportError report_error) {
	SemaEnv * env = ctx->env;
	if (str_equal(iden, s("int"))) {
	    return sema_type_handle_from_ptr(&ctx->table->i32_type);
	}
	do {
		for (SemaDeclNode * node = env->decls.begin; node; node = node->next) {
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
		env = env->parent;
	} while (env);
	if (report_error == DO_REPORT_ERROR) {
		fprintf(stderr, "error: unknown identifier '%.*s'\n", (int)iden.size, iden.data);
	}
	return null_sema_type_handle;
}

SemaVar * sema_ctx_lookup_var(SemaCtx * ctx, Str iden, ReportError report_error) {
	SemaEnv * env = ctx->env;
	do {
		for (SemaDeclNode * node = env->decls.begin; node; node = node->next) {
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
		env = env->parent;
	} while (env);
	if (report_error == DO_REPORT_ERROR) {
		fprintf(stderr, "error: unknown identifier '%.*s'\n", (int)iden.size, iden.data);
	}
	return nullptr;
}

SemaFn * sema_ctx_lookup_fn(SemaCtx * ctx, Str iden, ReportError report_error) {
	SemaEnv * env = ctx->env;
	do {
		for (SemaDeclNode * node = env->decls.begin; node; node = node->next) {
			if (!str_equal(node->decl.iden, iden)) {
				continue;
			}
			switch (node->decl.type) {
				case SEMA_DECL_FN:
					return &node->decl.as.fn;
				case SEMA_DECL_VAR:
				case SEMA_DECL_TYPE_ALIAS:
					if (report_error == DO_REPORT_ERROR) {
						fprintf(stderr, "error: identifier '%.*s' is not a function\n", (int)iden.size, iden.data);
					}
					return nullptr;
			}
		}
		env = env->parent;
	} while (env);
	if (report_error == DO_REPORT_ERROR) {
		fprintf(stderr, "error: unknown identifier '%.*s'\n", (int)iden.size, iden.data);
	}
	return nullptr;
}

static SemaType * sema_type_intern_ptr_to(SemaCtx * ctx, SemaTypeHandle type) {
	type.is_lvalue = false; // just to be sure
	SemaType type2;
	sema_type_init_uninterned(&type2, SEMA_TYPE_PTR);
	type2.as.ptr = type;
	return sema_type_intern(ctx, type2);
}

static SemaType * sema_type_intern_ref_to(SemaCtx * ctx, SemaTypeHandle type) {
	type.is_lvalue = false; // just to be sure
	SemaType type2;
	sema_type_init_uninterned(&type2, SEMA_TYPE_REF);
	type2.as.ref = type;
	return sema_type_intern(ctx, type2);
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
					sema_ctx_oom(ctx);
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
		case TYPE_PTR:
			handle = sema_type_from_ast(ctx, type->as.ptr);
			if (!handle.type) {
				return null_sema_type_handle;
			}
			return sema_type_handle_from_ptr(sema_type_intern_ptr_to(ctx, handle));
		case TYPE_REF:
			handle = sema_type_from_ast(ctx, type->as.ref);
			if (!handle.type) {
				return null_sema_type_handle;
			}
			return sema_type_handle_from_ptr(sema_type_intern_ref_to(ctx, handle));
	}
	UNREACHABLE();
}

static bool declare_ast_type_alias(SemaCtx * ctx, SemaTypeAlias * alias) {
	const TypeAlias * ast = alias->ast;
	SemaTypeHandle handle = sema_type_from_ast(ctx, &ast->type);
	if (!handle.type) {
		alias->pass = SEMA_PASS_ERROR;
		return false;
	}
	alias->pass = SEMA_PASS_CYCLE_UNCHECKED;
	alias->sema.next = handle;
	return true;
}

static bool sema_type_type_is_ptrlike(SemaTypeType type) {
	return type == SEMA_TYPE_PTR || type == SEMA_TYPE_REF;
}

bool coerce_expr_to_type(SemaCtx * ctx, SemaExpr * expr, SemaTypeHandle expr_type, SemaTypeHandle target_type) {
	(void)ctx;
	if (expr_type.type == target_type.type) {
		return expr;
	}
	if (sema_type_type_is_ptrlike(expr_type.type->type) && sema_type_type_is_ptrlike(target_type.type->type)) {
		SemaTypeHandle e = expr_type;
		SemaTypeHandle t = target_type;
		do {
			if (e.type->type == SEMA_TYPE_PTR && t.type->type == SEMA_TYPE_REF) {
				goto error;
			}
			e = e.type->as.ptr;
			t = t.type->as.ptr;
			if (!e.is_mut && t.is_mut) {
				goto error;
			}
		} while (sema_type_type_is_ptrlike(e.type->type) && sema_type_type_is_ptrlike(t.type->type));
		if (e.type != t.type && t.type->type != SEMA_TYPE_VOID) {
			goto error;
		}
		return expr;
	}
error:
	fputs("error: mismatched types (", stderr);
	sema_print_type(stderr, expr_type);
	fputs(") (", stderr);
	sema_print_type(stderr, target_type);
	fputs(")\n", stderr);
	return false; // for now
}

static bool check_type_addr(SemaCtx * ctx, SemaTypeHandle type, SemaTypeHandle * out) {
	if (!type.is_lvalue) {
		fprintf(stderr, "error: attempted to get address of expression that is not an lvalue\n");
		return false;
	}
	*out = sema_type_handle_from_ptr(sema_type_intern_ref_to(ctx, type));
	return true;
}

static bool check_type_deref(SemaCtx * ctx, SemaTypeHandle type, SemaTypeHandle * out) {
	(void)ctx;
	if (!sema_type_type_is_ptrlike(type.type->type)) {
		fprintf(stderr, "error: attemped to deref ");
		sema_print_type(stderr, type);
		fputc('\n', stderr);
		return false;
	}
	if (type.type->type == SEMA_TYPE_PTR) {
		*out = type.type->as.ptr;
		out->is_lvalue = true;
		return true;
	}
	if (type.type->type == SEMA_TYPE_REF) {
		*out = type.type->as.ref;
		out->is_lvalue = true;
		return true;
	}
	UNREACHABLE();
}

// Ensure the tree has been converted into a tree suitable for semantic analysis
bool ensure_type_alias_is_sema(SemaCtx * ctx, SemaTypeAlias * alias);
bool ensure_expr_is_sema(SemaCtx * ctx, SemaExpr * expr);
bool ensure_var_is_sema(SemaCtx * ctx, SemaVar * var);
bool ensure_fn_is_sema(SemaCtx * ctx, SemaFn * fn);
// Ensure the tree doesn't contain any illegal cycles
bool ensure_type_is_cycle_checked(SemaCtx * ctx, VisitorState visitor, SemaType * type);
bool ensure_type_alias_is_cycle_checked(SemaCtx * ctx, VisitorState visitor, SemaTypeAlias * alias);
bool ensure_expr_is_cycle_checked(SemaCtx * ctx, VisitorState visitor, SemaExpr * expr);
bool ensure_var_is_cycle_checked(SemaCtx * ctx, VisitorState visitor, SemaVar * var);
// Ensure the tree is implemented, typechecked and ready for lowering
bool ensure_type_handle_is_implemented(SemaCtx * ctx, VisitorState visitor, SemaTypeHandle * out_handle);
bool ensure_type_ptr_is_implemented(SemaCtx * ctx, VisitorState visitor, SemaType ** type);
bool ensure_type_alias_is_implemented(SemaCtx * ctx, VisitorState visitor, SemaTypeAlias * alias);
ExprEvalResult ensure_expr_is_implemented(SemaCtx * ctx, VisitorState visitor, SemaExpr * expr, SemaTypeHandle * opt_out);
bool ensure_var_is_implemented(SemaCtx * ctx, VisitorState visitor, SemaVar * var);
bool ensure_fn_is_implemented(SemaCtx * ctx, VisitorState visitor, SemaFn * fn);
bool run_implemented_fn(SemaCtx * ctx, VisitorState visitor, SemaFn * fn, SemaValue * out); // the dream
// (Somewhat)? likely to be factored out
bool ensure_decl_is_implemented(SemaCtx * ctx, VisitorState visitor, SemaDecl * decl);

bool ensure_type_alias_is_sema(SemaCtx * ctx, SemaTypeAlias * alias) {
	if (alias->pass == SEMA_PASS_ERROR) {
		return false;
	}
	if (alias->pass > SEMA_PASS_AST) {
		return true;
	}
	alias->pass = SEMA_PASS_CYCLE_UNCHECKED;
	return declare_ast_type_alias(ctx, alias);
}

bool ensure_expr_is_sema(SemaCtx * ctx, SemaExpr * expr) {
	if (expr->pass == SEMA_PASS_ERROR) {
		return false;
	}
	if (expr->pass > SEMA_PASS_AST) {
		return true;
	}
	expr->pass = SEMA_PASS_CYCLE_UNCHECKED;
	const Expr * ast = expr->as.ast;
	SemaFn * fn;
	SemaVar * var;
	SemaExpr * a;
	SemaExpr * b;
	SemaExprFunCallArgs args;
	switch (ast->type) {
	case EXPR_POISONED:
		goto error;
	case EXPR_INT:
		sema_expr_init_unimplemented(expr, SEMA_EXPR1_I32);
		expr->as.sema1.i32 = (i32)ast->as.int_; // TODO : more ints and proper handling
		break;
	case EXPR_NULLPTR:
		sema_expr_init_unimplemented(expr, SEMA_EXPR1_NULLPTR);
		break;
	case EXPR_IDEN:
		fn = sema_ctx_lookup_fn(ctx, ast->as.iden, DONT_REPORT_ERROR);
		if (fn) {
			if (!ensure_fn_is_sema(ctx, fn)) {
				goto error;
			}
			sema_expr_init_unimplemented(expr, SEMA_EXPR1_FN);
			expr->as.sema1.fn = fn;
			break;
		}
		var = sema_ctx_lookup_var(ctx, ast->as.iden, DO_REPORT_ERROR);
		if (!var) {
			goto error;
		}
		if (!ensure_var_is_sema(ctx, var)) {
			goto error;
		}
		sema_expr_init_unimplemented(expr, SEMA_EXPR1_VAR);
		expr->as.sema1.var = var;
		break;
	case EXPR_PLUS:
		a = vmem_arena_alloc(ctx->arena, SemaExpr);
		b = vmem_arena_alloc(ctx->arena, SemaExpr);
		if (!a || !b) {
			sema_ctx_oom(ctx);
		}
		sema_expr_init_with_ast(a, ast->as.plus.a);
		sema_expr_init_with_ast(b, ast->as.plus.b);
		if (!ensure_expr_is_sema(ctx, a) ||
			!ensure_expr_is_sema(ctx, b)) {
			goto error;
		}
		sema_expr_init_unimplemented(expr, SEMA_EXPR1_PLUS);
		expr->as.sema1.plus.a = a;
		expr->as.sema1.plus.b = b;
		break;
	case EXPR_ADDR:
		a = vmem_arena_alloc(ctx->arena, SemaExpr);
		if (!a) {
			sema_ctx_oom(ctx);
		}
		sema_expr_init_with_ast(a, ast->as.addr);
		if (!ensure_expr_is_sema(ctx, a)) {
			goto error;
		}
		sema_expr_init_unimplemented(expr, SEMA_EXPR1_ADDR);
		expr->as.sema1.addr = a;
		break;
	case EXPR_FUNCALL:
		a = vmem_arena_alloc(ctx->arena, SemaExpr);
		if (!a) {
			sema_ctx_oom(ctx);
		}
		sema_expr_init_with_ast(a, ast->as.funcall.fun);
		if (!ensure_expr_is_sema(ctx, a)) {
			goto error;
		}
		ZERO(&args);
		args.data = vmem_arena_alloc_n(ctx->arena, SemaExpr, ast->as.funcall.args.count);
		if (!args.data) {
			sema_ctx_oom(ctx);
		}
		for (auto node = ast->as.funcall.args.begin; node; node = node->next) {
			SemaExpr * expr = &args.data[args.size];
			sema_expr_init_with_ast(expr, &node->expr);
			if (!ensure_expr_is_sema(ctx, expr)) {
				goto error;
			}
			++args.size;
		}
		assert(args.size == ast->as.funcall.args.count);
		sema_expr_init_unimplemented(expr, SEMA_EXPR1_FUNCALL);
		expr->as.sema1.funcall.fun = a;
		expr->as.sema1.funcall.args = args;
		expr->as.sema1.funcall.fn_type = null_sema_type_handle;
		break;
	}
	return true;
error:
	expr->pass = SEMA_PASS_ERROR;
	return false;
}

bool ensure_var_is_sema(SemaCtx * ctx, SemaVar * var) {
	if (var->pass == SEMA_PASS_ERROR) {
		return false;
	}
	if (var->pass > SEMA_PASS_AST) {
		return true;
	}
	var->pass = SEMA_PASS_CYCLE_UNCHECKED;
	const Var * ast = var->as.ast;
	Str iden;
	if (!str_copy(ctx->arena, ast->iden, &iden)) {
		sema_ctx_oom(ctx);
	}
	SemaTypeHandle type = sema_type_from_ast(ctx, &ast->type);
	if (!type.type) {
		var->pass = SEMA_PASS_ERROR;
		return false;
	}
	type.is_lvalue = true;
	type.is_mut |= ast->is_mut;
	bool init_with_expr = ast->init_with_expr;
	SemaExpr expr;
	if (init_with_expr) {
		sema_expr_init_with_ast(&expr, &ast->unwrap.expr);
		if (!ensure_expr_is_sema(ctx, &expr)) {
			var->pass = SEMA_PASS_ERROR;
			return false;
		}
	}
	sema_var_init(var, type, init_with_expr ? &expr : nullptr, sema_ctx_is_global_scope(ctx));
	return true;
}

bool ensure_fn_is_sema(SemaCtx * ctx, SemaFn * fn) {
	if (fn->pass == SEMA_PASS_ERROR) {
		return false;
	}
	if (fn->pass > SEMA_PASS_AST) {
		return true;
	}
	fn->pass = SEMA_PASS_CYCLE_UNCHECKED;
	const Fn * ast = fn->ast;
	if (ast->params == &poisoned_fn_param_list) {
		fn->pass = SEMA_PASS_ERROR;
		return false;
	}
	SemaTypeHandleList params;
	sema_type_handle_list_init(&params);
	SemaTypeHandle return_type = sema_type_from_ast(ctx, &ast->return_type);
	if (!return_type.type) {
		fn->pass = SEMA_PASS_ERROR;
		return false;
	}
	Str * args = vmem_arena_alloc_n(ctx->arena, Str, ast->params->count);
	if (!args) {
		sema_ctx_oom(ctx);
	}
	usize i = 0;
	for (auto node = ast->params->begin; node; node = node->next) {
	    FnParam * param = &node->param;
		args[i] = s("");
		if (param->has_iden) {
			if (!str_copy(ctx->arena, param->unwrap.iden, &args[i])) {
				sema_ctx_oom(ctx);
			}
		}
		args[i] = param->has_iden ? param->unwrap.iden : s("");
		SemaTypeHandle handle = sema_type_from_ast(ctx, &param->type);
		if (!handle.type) {
			fn->pass = SEMA_PASS_ERROR;
			return false;
		}
		if (!sema_type_handle_list_push_with_ctx(ctx, &params, handle)) {
			sema_ctx_oom(ctx);
		}
		++i;
	}
	SemaType type_uninterned;
	sema_type_init_uninterned(&type_uninterned, SEMA_TYPE_FN);
	type_uninterned.as.fn.return_type = return_type.type;
	type_uninterned.as.fn.params = params;
	SemaType * type = sema_type_intern(ctx, type_uninterned);
	assert(type);
	sema_fn_init(fn, &type->as.fn, args);
	return true;
}

bool ensure_type_is_cycle_checked(SemaCtx * ctx, VisitorState visitor, SemaType * type) {
	switch (type->pass) {
	case SEMA_PASS_ERROR:
		return false;
	case SEMA_PASS_AST: // types don't have this
		UNREACHABLE();
	case SEMA_PASS_CYCLE_UNCHECKED:
		type->visit_index = visitor.last_indirection_id++;
		switch (type->type) {
			case SEMA_TYPE_I32:
			case SEMA_TYPE_VOID:
				break;
			case SEMA_TYPE_PTR:
				visitor.last_indirection_id = type->visit_index;
				if (!ensure_type_is_cycle_checked(ctx, visitor, type->as.ptr.type)) {
					goto error;
					
				}
				break;
			case SEMA_TYPE_REF:
				visitor.last_indirection_id = type->visit_index;
				if (!ensure_type_is_cycle_checked(ctx, visitor, type->as.ref.type)) {
					goto error;
					
				}
				break;
			case SEMA_TYPE_TYPE_ALIAS:
				if (!ensure_type_alias_is_cycle_checked(ctx, visitor, type->as.alias)) {
					goto error;
					
				}
				break;
			case SEMA_TYPE_FN:
				if (!ensure_type_is_cycle_checked(ctx, visitor, type->as.fn.return_type)) {
					goto error;
					
				}
				for (auto node = type->as.fn.params.begin; node; node = node->next) {
					if (!ensure_type_is_cycle_checked(ctx, visitor, node->type.type)) {
						goto error;
					}
				}
				break;
		}
		type->pass = SEMA_PASS_CYCLE_CHECKED;
		break;
	case SEMA_PASS_CYCLE_CHECKING:
		if (!(type->visit_index < visitor.last_indirection_id
			&& type->visit_index <= visitor.last_opaque_id)) {
			fprintf(stderr, "error: detected cycle\n");
			goto error;
		}
		break;
	case SEMA_PASS_CYCLE_CHECKED:
	case SEMA_PASS_IMPLEMENTED:
		break;
	}
	return true;
error:
	type->pass = SEMA_PASS_ERROR;
	return false;
}

bool ensure_type_alias_is_cycle_checked(SemaCtx * ctx, VisitorState visitor, SemaTypeAlias * alias) {
	switch (alias->pass) {
	case SEMA_PASS_ERROR:
		return false;
	case SEMA_PASS_AST:
		if (!ensure_type_alias_is_sema(ctx, alias)) {
			return false;
		}
		[[fallthrough]];
	case SEMA_PASS_CYCLE_UNCHECKED:
	case SEMA_PASS_CYCLE_CHECKING:
		if (!ensure_type_is_cycle_checked(ctx, visitor, alias->sema.next.type)) {
			alias->pass = SEMA_PASS_ERROR;
			return false;
		}
		alias->pass = SEMA_PASS_CYCLE_CHECKED;
		[[fallthrough]];
	case SEMA_PASS_CYCLE_CHECKED:
	case SEMA_PASS_IMPLEMENTED:
		return true;
	}
}

bool ensure_expr_is_cycle_checked(SemaCtx * ctx, VisitorState visitor, SemaExpr * expr) {
	switch (expr->pass) {
	case SEMA_PASS_ERROR:
		return false;
	case SEMA_PASS_AST:
		if (!ensure_expr_is_sema(ctx, expr)) {
			return false;
		}
		[[fallthrough]];
	case SEMA_PASS_CYCLE_UNCHECKED:
	case SEMA_PASS_CYCLE_CHECKING:
		switch (expr->type1) {
		case SEMA_EXPR1_VOID:
		case SEMA_EXPR1_I32:
		case SEMA_EXPR1_NULLPTR:
			break;
		case SEMA_EXPR1_FN:
			if (!ensure_fn_is_cycle_checked(ctx, visitor, expr->as.sema1.fn)) {
				expr->pass = SEMA_PASS_ERROR;
				return false;
			}
			break;
		case SEMA_EXPR1_ADDR:
			visitor.last_indirection_id = visitor.visit_id++;
			if (!ensure_expr_is_cycle_checked(ctx, visitor, expr->as.sema1.addr)) {
				return false;
			}
			break;
		case SEMA_EXPR1_FUNCALL:
			if (!ensure_expr_is_cycle_checked(ctx, visitor, expr->as.sema1.funcall.fun)) {
				return false;
			}
			for (usize i = 0; i < expr->as.sema1.funcall.args.size; ++i) {
				if (!ensure_expr_is_cycle_checked(ctx, visitor, &expr->as.sema1.funcall.args.data[i])) {
					return false;
				}
			}
			break;
		case SEMA_EXPR1_PLUS:
			if (!ensure_expr_is_cycle_checked(ctx, visitor, expr->as.sema1.plus.a)) {
				return false;
			}
			if (!ensure_expr_is_cycle_checked(ctx, visitor, expr->as.sema1.plus.b)) {
				return false;
			}
			break;
		case SEMA_EXPR1_VAR:
			if (!ensure_var_is_cycle_checked(ctx, visitor, expr->as.sema1.var)) {
				return false;
			}
			break;
		case SEMA_EXPR1_DEREF:
			if (!ensure_expr_is_cycle_checked(ctx, visitor, expr->as.sema1.deref)) {
				return false;
			}
			break;
		}
		expr->pass = SEMA_PASS_CYCLE_CHECKED;
		[[fallthrough]];
	case SEMA_PASS_CYCLE_CHECKED:
	case SEMA_PASS_IMPLEMENTED:
		return true;
	}
}

bool ensure_var_is_cycle_checked(SemaCtx * ctx, VisitorState visitor, SemaVar * var) {
	switch (var->pass) {
	case SEMA_PASS_ERROR:
		return false;
	case SEMA_PASS_AST:
		if (!ensure_var_is_sema(ctx, var)) {
			return false;
		}
		[[fallthrough]];
	case SEMA_PASS_CYCLE_CHECKING:
		if (var->visit_index < visitor.last_indirection_id) {
			var->pass = SEMA_PASS_ERROR;
			fprintf(stderr, "error: cycle detected\n");
			return false;
		}
		return true;
		break;
	case SEMA_PASS_CYCLE_UNCHECKED:
		var->pass = SEMA_PASS_CYCLE_CHECKING;
		var->visit_index = visitor.visit_id++;
		if (!ensure_type_is_cycle_checked(ctx, visitor, var->as.sema.type.type)) {
			var->pass = SEMA_PASS_ERROR;
			return false;
		}
		if (var->as.sema.init_with_expr) {
			if (!ensure_expr_is_cycle_checked(ctx, visitor, &var->as.sema.unwrap.expr)) {
				var->pass = SEMA_PASS_ERROR;
				return false;
			}
		}
		var->pass = SEMA_PASS_CYCLE_CHECKED;
		[[fallthrough]];
	case SEMA_PASS_CYCLE_CHECKED:
	case SEMA_PASS_IMPLEMENTED:
		return true;
	}
}

bool ensure_fn_is_cycle_checked(SemaCtx * ctx, VisitorState visitor, SemaFn * fn) {
	SemaType * fn_type;
	switch (fn->pass) {
	case SEMA_PASS_ERROR:
		return false;
	case SEMA_PASS_AST:
		if (!ensure_fn_is_sema(ctx, fn)) {
			return false;
		}
		[[fallthrough]];
	case SEMA_PASS_CYCLE_UNCHECKED:
	case SEMA_PASS_CYCLE_CHECKING:
		fn_type = sema_type_from_interned_fn(fn->sema.signature);
		if (!ensure_type_is_cycle_checked(ctx, visitor, fn_type)) {
			fn->pass = SEMA_PASS_ERROR;
			return false;
		}
		fn->pass = SEMA_PASS_CYCLE_CHECKED;
		[[fallthrough]];
	case SEMA_PASS_CYCLE_CHECKED:
	case SEMA_PASS_IMPLEMENTED:
		return true;
	}
}

bool ensure_type_alias_is_implemented(SemaCtx * ctx, VisitorState visitor, SemaTypeAlias * alias) {
	if (alias->pass == SEMA_PASS_ERROR) {
		return false;
	}
	if (alias->pass >= SEMA_PASS_IMPLEMENTED) {
		return true;
	}
	if (!ensure_type_alias_is_cycle_checked(ctx, visitor, alias)) {
		return false;
	}
	if (!ensure_type_handle_is_implemented(ctx, visitor, &alias->sema.next)) {
		alias->pass = SEMA_PASS_ERROR;
		return false;
	}
	alias->pass = SEMA_PASS_IMPLEMENTED;
	return true;
}


typedef struct {
	SemaTypePtrPtrNode * head;
	SemaTypePtrPtrNode * tail;
} TypeWorkStack;

bool type_worklist_push(SemaCtx * ctx, TypeWorkStack * list, SemaType ** type) {
	SemaTypePtrPtrNode * node;
	if (ctx->free_type_ptrs) {
		node = ctx->free_type_ptrs;
		ctx->free_type_ptrs = node->next;
	} else {
		node = vmem_arena_alloc(ctx->arena, SemaTypePtrPtrNode);
		if (UNLIKELY(!node)) {
			return false;
		}
	}
	node->payload = type;
	node->next = list->head;
	list->head = node;
	if (!list->tail) {
		list->tail = node;
	}
	return true;
}

static void type_worklist_pop(SemaCtx * ctx, TypeWorkStack * list, SemaType *** out)
// my first legimatimit-ish use of a triple pointer
{
	SemaTypePtrPtrNode * node = list->head;
	list->head = node->next;
	if (list->tail == node) {
		list->tail = nullptr;
	}
	if (out) {
		*out = node->payload;
	}
	node->next = ctx->free_type_ptrs;
	ctx->free_type_ptrs = node;
}

static void type_worklist_free(SemaCtx * ctx, TypeWorkStack * list) {
	if (!list->tail) {
		return;
	}
	list->tail = ctx->free_type_ptrs;
	ctx->free_type_ptrs = list->head;
}

bool ensure_type_handle_is_implemented_iter
	(SemaCtx * ctx, VisitorState visitor, SemaTypeHandle * out_handle, TypeWorkStack * list) {
	SemaType * type = out_handle->type;
	if (type->pass == SEMA_PASS_ERROR) {
		return false;
	}
	if (type->pass >= SEMA_PASS_IMPLEMENTED) {
		if (type->type == SEMA_TYPE_TYPE_ALIAS) {
			out_handle->type = type->as.alias->sema.next.type;
			out_handle->is_lvalue |= type->as.alias->sema.next.is_lvalue;
			out_handle->is_mut |= type->as.alias->sema.next.is_mut;
		}
		return true;
	}
	if (!ensure_type_is_cycle_checked(ctx, visitor, out_handle->type)) {
		goto error;
	}
	type->pass = SEMA_PASS_IMPLEMENTED;
	switch (type->type) {
	case SEMA_TYPE_I32:
		type->impled.size = 4;
		type->impled.align = 4;
		break;
	case SEMA_TYPE_PTR:
		if (!type_worklist_push(ctx, list, &type->as.ptr.type)) {
			sema_ctx_oom(ctx);
		}
		type->impled.size = 8;
		type->impled.align = 8;
		break;
	case SEMA_TYPE_REF:
		if (!type_worklist_push(ctx, list, &type->as.ref.type)) {
			sema_ctx_oom(ctx);
		}
		type->impled.size = 8;
		type->impled.align = 8;
		break;
	case SEMA_TYPE_VOID:
		type->impled.size = 0;
		type->impled.align = 0;
		break;
	case SEMA_TYPE_FN:
		if (!type_worklist_push(ctx, list, &type->as.fn.return_type)) {
			sema_ctx_oom(ctx);
		}
		for (auto node = type->as.fn.params.begin; node; node = node->next) {
			if (!type_worklist_push(ctx, list, &node->type.type)) {
				sema_ctx_oom(ctx);
			}
		}
		break;
	case SEMA_TYPE_TYPE_ALIAS:
		if (!ensure_type_alias_is_implemented(ctx, visitor, type->as.alias)) {
			goto error;
		}
		out_handle->type = type->as.alias->sema.next.type;
		out_handle->is_lvalue |= type->as.alias->sema.next.is_lvalue;
		out_handle->is_mut |= type->as.alias->sema.next.is_mut;
		break;
	}
	return true;
error:
	type->pass = SEMA_PASS_ERROR;
	return false;

}

bool ensure_type_handle_is_implemented(SemaCtx * ctx, VisitorState visitor, SemaTypeHandle * out_handle) {
	TypeWorkStack stack;
	ZERO(&stack);
	if (!ensure_type_handle_is_implemented_iter(ctx, visitor, out_handle, &stack)) {
		type_worklist_free(ctx, &stack);
		return false;
	}
	SemaType ** type;
	SemaTypeHandle handle;
	while (stack.head) {
		type_worklist_pop(ctx, &stack, &type);
		assert(type);
		handle = sema_type_handle_from_ptr(*type);
		if (!ensure_type_handle_is_implemented_iter(ctx, visitor, &handle, &stack)) {
			type_worklist_free(ctx, &stack);
			return false;
		}
		*type = handle.type;
	}
	out_handle->type = sema_type_dedup_implemented(ctx, out_handle->type);
	return true;
}

bool ensure_type_ptr_is_implemented(SemaCtx * ctx, VisitorState visitor, SemaType ** type) {
	SemaTypeHandle handle = sema_type_handle_from_ptr(*type);
	if (!ensure_type_handle_is_implemented(ctx, visitor, &handle)) {
		return false;
	}
	*type = handle.type;
	return true;
}

ExprEvalResult _implement_add_expr(SemaCtx * ctx, SemaExpr * target,
		SemaExpr * a, SemaTypeHandle at, SemaExpr * b, SemaTypeHandle bt, SemaTypeHandle * type, bool fst) {
	switch (at.type->type) {
	case SEMA_TYPE_I32:
		if (!coerce_expr_to_type(ctx, b, bt, at)) {
			goto error;
		}
		*type = sema_type_handle_from_ptr(&ctx->table->i32_type);
		if (a->type2 == SEMA_EXPR2_VALUE && b->type2 == SEMA_EXPR2_VALUE) {
			sema_expr_init_implemented(target, SEMA_EXPR2_VALUE);
			sema_value_init(&target->as.sema2.value, SEMA_VALUE_I32);
			target->as.sema2.value.as.i32 =
				a->as.sema2.value.as.i32 +
				b->as.sema2.value.as.i32;
			return EXPR_EVAL_REDUCED;
		}
		return EXPR_EVAL_UNREDUCED;
		break;
	default:
	error:
		if (fst) {
			return _implement_add_expr(ctx, target, b, bt, a, at, type, false);
		}
	}
	return EXPR_EVAL_ERROR;
}

ExprEvalResult _ensure_expr_is_implemented(SemaCtx * ctx,
						  VisitorState visitor,
						  SemaExpr * expr,
						  SemaTypeHandle * opt_out,
						  bool deref) {
    SemaTypeHandle type;
    ExprEvalResult result;
    SemaTypeHandle itype;
    ExprEvalResult iresult;
    switch (expr->pass) {
    case SEMA_PASS_ERROR:
    case SEMA_PASS_AST:
    case SEMA_PASS_CYCLE_UNCHECKED:
    case SEMA_PASS_CYCLE_CHECKING:
	if (!ensure_expr_is_cycle_checked(ctx, visitor, expr)) {
	    return EXPR_EVAL_ERROR;
	}
	[[fallthrough]];
    case SEMA_PASS_CYCLE_CHECKED:
	expr->pass = SEMA_PASS_IMPLEMENTED; // if not true this is is corrected anyways
	switch (expr->type1) {
	case SEMA_EXPR1_VOID:
	    sema_expr_init_implemented(expr, SEMA_EXPR2_VALUE);
	    sema_value_init(&expr->as.sema2.value, SEMA_VALUE_VOID);
	    type = sema_type_handle_from_ptr(&ctx->table->void_type);
	    result = EXPR_EVAL_REDUCED;
	    break;
	case SEMA_EXPR1_NULLPTR:
	    sema_expr_init_implemented(expr, SEMA_EXPR2_VALUE);
	    sema_value_init(&expr->as.sema2.value, SEMA_VALUE_NULLPTR);
	    type = sema_type_handle_from_ptr(&ctx->table->void_ptr_type);
	    result = EXPR_EVAL_REDUCED;
	    break;
	case SEMA_EXPR1_I32: {
	    i32 i32 = expr->as.sema1.i32;
	    sema_expr_init_implemented(expr, SEMA_EXPR2_VALUE);
	    sema_value_init(&expr->as.sema2.value, SEMA_VALUE_I32);
	    expr->as.sema2.value.as.i32 = i32;
	    type = sema_type_handle_from_ptr(&ctx->table->i32_type);
	    result = EXPR_EVAL_REDUCED;
		break;
	}
	case SEMA_EXPR1_FN: {
		if (expr->as.sema1.fn->emmiting == SEMA_FN_UNEMMITED) {
			if (!ensure_fn_is_implemented(ctx, visitor, expr->as.sema1.fn)) {
				goto error;
			}
		}
	    SemaFn * fn = expr->as.sema1.fn;
	    sema_expr_init_implemented(expr, SEMA_EXPR2_VALUE);
	    sema_value_init(&expr->as.sema2.value, SEMA_VALUE_FN);
	    expr->as.sema2.value.as.fn = fn;
	    type = sema_type_handle_from_ptr(
		sema_type_from_interned_fn(fn->sema.signature));
	    result = EXPR_EVAL_REDUCED;
		break;
	}
	case SEMA_EXPR1_ADDR: {
	    iresult = _ensure_expr_is_implemented(
		ctx, visitor, expr->as.sema1.addr, &itype, false);
	    if (!iresult) {
			goto error;
		}
	    if (!check_type_addr(ctx, itype, &type)) {
			goto error;
	    }
	    SemaExpr * addr = expr->as.sema1.addr;
	    *expr = *addr; // correct semantics when vars are pointers
	    result = iresult;
	    break;
	}
	case SEMA_EXPR1_DEREF:
		iresult = _ensure_expr_is_implemented(ctx, visitor, expr->as.sema1.deref, &itype, true);
		if (!iresult) {
			goto error;
		}
		if (!check_type_deref(ctx, itype, &type)) {
			goto error;
		}
		if (iresult == EXPR_EVAL_REDUCED) {
			SemaExpr * deref = expr->as.sema1.deref;
			*expr = *deref;
			result = EXPR_EVAL_REDUCED;
			break;
		}
		{
			SemaExpr * deref = expr->as.sema1.deref;
			sema_expr_init_implemented(expr, SEMA_EXPR2_DEREF);
			expr->as.sema2.deref = deref;
			result = EXPR_EVAL_UNREDUCED;
			break;
		}
		break;
	case SEMA_EXPR1_FUNCALL: {
			iresult = _ensure_expr_is_implemented(ctx, visitor, expr->as.sema1.funcall.fun, &itype, true);
			if (!iresult) {
				goto error;
			}
			if (itype.type->type != SEMA_TYPE_FN) {
				fprintf(stderr, "error: expected function type, found (");
				sema_print_type(stderr, itype);
				fprintf(stderr, ")\n");
				goto error;
			}
			if (itype.type->as.fn.params.count != expr->as.sema1.funcall.args.size) {
				fprintf(stderr, "error: incorrect arity\n");
				goto error;
			}
			SemaTypeHandleNode * node = itype.type->as.fn.params.begin;
			for (usize i = 0; i < expr->as.sema1.funcall.args.size; ++i, node = node->next) {
				SemaExpr * arg = &expr->as.sema1.funcall.args.data[i];
				SemaTypeHandle atype;
				ExprEvalResult aresult = _ensure_expr_is_implemented(ctx, visitor, arg, &atype, true);
				if (!aresult) {
					goto error;
				}
				iresult = aresult == EXPR_EVAL_REDUCED ? iresult : EXPR_EVAL_UNREDUCED;
			}
			sema_expr_init_implemented(expr, SEMA_EXPR2_FUNCALL);
			expr->as.sema2.funcall.fn_type = itype;
			type = sema_type_handle_from_ptr(itype.type->as.fn.return_type);
			if (expr->as.sema2.funcall.fun->type2 == SEMA_EXPR2_VALUE) {
				// TODO: const fn evaluation
			}
			result = EXPR_EVAL_UNREDUCED;
			break;
		}
	case SEMA_EXPR1_PLUS: {
			SemaTypeHandle itype2;
			ExprEvalResult iresult2;
			SemaExpr * a = expr->as.sema1.plus.a;
			SemaExpr * b = expr->as.sema1.plus.b;
			iresult =
			    ensure_expr_is_implemented(ctx, visitor, a, &itype);
			iresult2 =
				ensure_expr_is_implemented(ctx, visitor, b, &itype2);
			if (!iresult || !iresult2) {
			    goto error;
			}
			result = _implement_add_expr(ctx, expr, a, itype, b, itype2, &type, true);
			if (!result) {
				goto error;
			}
		}
		break;
	case SEMA_EXPR1_VAR: {
			SemaVar * var = expr->as.sema1.var;
			if (!ensure_var_is_implemented(ctx, visitor, var)) {
				goto error;
			}
			type = var->as.sema.type;
			if (deref) {
				if (!var->as.sema.init_with_expr) {
					if (sema_ctx_is_global_scope(ctx)) {
						fprintf(stderr, "warning: uninitialized global used in constant expression\n");
						goto error;
					}
					sema_expr_init_implemented(expr, SEMA_EXPR2_LOAD_VAR);
					expr->as.sema2.load_var = var;
					result = EXPR_EVAL_UNREDUCED;
					break;
				}
				*expr = var->as.sema.unwrap.expr;
				result = expr->type2 == SEMA_EXPR2_VALUE ? EXPR_EVAL_REDUCED : EXPR_EVAL_UNREDUCED;
				// TODO: subtly broken
			} else {
				sema_expr_init_implemented(expr, SEMA_EXPR2_VALUE);
				sema_value_init(&expr->as.sema2.value, SEMA_VALUE_VAR_REF);
				expr->as.sema2.value.as.var_ref = var;
				result = EXPR_EVAL_REDUCED;
			}
			break;
		}
	}
	// do work
	break;
    case SEMA_PASS_IMPLEMENTED:
		type = null_sema_type_handle;
		return expr->type2 == SEMA_EXPR2_VALUE ? EXPR_EVAL_REDUCED
							   : EXPR_EVAL_UNREDUCED;
	}
	if (opt_out) {
		*opt_out = type;
	}
    return result;
error:
	expr->pass = SEMA_PASS_ERROR;
	return EXPR_EVAL_ERROR;
}

ExprEvalResult ensure_expr_is_implemented(SemaCtx * ctx, VisitorState visitor, SemaExpr * expr, SemaTypeHandle * opt_out) {
	return _ensure_expr_is_implemented(ctx, visitor, expr, opt_out, true);
}

bool ensure_var_is_implemented(SemaCtx * ctx, VisitorState visitor, SemaVar * var) {
	switch (var->pass) {
	case SEMA_PASS_ERROR:
		return false;
	case SEMA_PASS_AST:
	case SEMA_PASS_CYCLE_UNCHECKED:
	case SEMA_PASS_CYCLE_CHECKING:
		if (!ensure_var_is_cycle_checked(ctx, visitor, var)) {
			return false;
		}
	[[fallthrough]];
	case SEMA_PASS_CYCLE_CHECKED:
		if (!ensure_type_handle_is_implemented(ctx, visitor, &var->as.sema.type)) {
			goto error;
		}
		if (var->as.sema.init_with_expr) {
			SemaTypeHandle type;
			ExprEvalResult result = ensure_expr_is_implemented(
			    ctx, visitor, &var->as.sema.unwrap.expr, &type);
			if (!result) {
				goto error;
			}
			if (!type.type) {
				type = var->as.sema.type;
			} else {
				if (!coerce_expr_to_type(ctx, &var->as.sema.unwrap.expr, type, var->as.sema.type)) {
					goto error;
				}
			}
			if (result == EXPR_EVAL_UNREDUCED && var->is_global) {
				fprintf(stderr, "error: initalization of global variable with non const expression");
				goto error;
			}
		}
		var->pass = SEMA_PASS_IMPLEMENTED;
		[[fallthrough]];
	case SEMA_PASS_IMPLEMENTED:
		return true;
	}
error:
	var->pass = SEMA_PASS_ERROR;
	return false;
}

bool ensure_fn_is_implemented(SemaCtx * ctx, VisitorState visitor, SemaFn * fn) {
	return emit_fn(ctx, visitor, fn);
}

bool ensure_decl_is_implemented(SemaCtx * ctx, VisitorState visitor, SemaDecl * decl) {
	switch (decl->type) {
		case SEMA_DECL_TYPE_ALIAS:
			return ensure_type_alias_is_implemented(ctx, visitor, &decl->as.alias);
		case SEMA_DECL_FN:
			return ensure_fn_is_implemented(ctx, visitor, &decl->as.fn);
		case SEMA_DECL_VAR:
			return ensure_var_is_implemented(ctx, visitor, &decl->as.var);
	}
}

bool sema_analyze_ast(SemaCtx * ctx, Ast ast) {
	if (setjmp(ctx->oom_handler) != 0) {
		fprintf(stderr, "fatal error: OOM\n");
		return false;
	}
	for (DeclNode * node = ast.begin; node; node = node->next) {
		SemaDecl decl;
		Str iden;
		switch (node->decl.type) {
		case DECL_TYPE_ALIAS:
			if (!str_copy(ctx->arena, node->decl.as.alias.iden, &iden)) {
				sema_ctx_oom(ctx);
			}
			sema_decl_init(&decl, SEMA_DECL_TYPE_ALIAS, symbol_pos_global(), iden);
			decl.as.alias.pass = SEMA_PASS_AST;
			decl.as.alias.ast = &node->decl.as.alias;
			SemaDecl * pdecl = sema_ctx_add_decl(ctx, decl);
			if (!pdecl) {
				sema_ctx_oom(ctx);
			}
			assert(sema_type_alias_intern_with_stable_ptr(ctx, &pdecl->as.alias).type);
			break;
		case DECL_FN:
			if (!str_copy(ctx->arena, node->decl.as.fn.iden, &iden)) {
				sema_ctx_oom(ctx);
			}
			sema_decl_init(&decl, SEMA_DECL_FN, symbol_pos_global(), iden);
			sema_fn_init_with_ast(&decl.as.fn, &node->decl.as.fn);
			if (!sema_ctx_add_decl(ctx, decl)) {
				sema_ctx_oom(ctx);
			}
			break;
		case DECL_VAR:
			if (!str_copy(ctx->arena, node->decl.as.var.iden, &iden)) {
				sema_ctx_oom(ctx);
			}
			sema_decl_init(&decl, SEMA_DECL_VAR, symbol_pos_global(), iden);
			sema_var_init_with_ast(&decl.as.var, &node->decl.as.var, true);
			if (!sema_ctx_add_decl(ctx, decl)) {
				sema_ctx_oom(ctx);
			}
			break;
		}
	}
	bool ok = true;
	for (auto node = ctx->env->decls.begin; node; node = node->next) {
		ok &= ensure_decl_is_implemented(ctx, new_visitor_state(), &node->decl);
	}
	return ok;
}

void sema_print_type(FILE * file, SemaTypeHandle handle) {
	if (handle.is_mut) {
		fprintf(file, "mut ");
	}
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
			fputs(sep, file); sep = ", ";
			sema_print_type(file, node->type);
		}
		fputs("): ", file);
		sema_print_type(file, 
				sema_type_handle_from_ptr(handle.type->as.fn.return_type));
		break;
	case SEMA_TYPE_PTR:
		fputs("*", file);
		sema_print_type(file, handle.type->as.ptr);
		break;
	case SEMA_TYPE_REF:
		fputs("&", file);
		sema_print_type(file, handle.type->as.ref);
		break;
	case SEMA_TYPE_TYPE_ALIAS:
		assert(false && "no current context where this makes sense");
		break;
	}
}

void sema_type_init_uninterned(SemaType * type, SemaTypeType typetype) {
	type->pass = SEMA_PASS_CYCLE_UNCHECKED;
	type->type = typetype;
	type->deduped = false;
}

void sema_value_init(SemaValue * value, SemaValueType type) {
	value->type = type;
}

void sema_expr_init_with_ast(SemaExpr * expr, const Expr * ast) {
	expr->pass = SEMA_PASS_AST;
	expr->as.ast = ast;
}

void sema_expr_init_implemented(SemaExpr * expr, SemaExpr2Type type) {
	expr->pass = SEMA_PASS_IMPLEMENTED;
	expr->type2 = type;
}

void sema_expr_init_unimplemented(SemaExpr * expr, SemaExpr1Type type) {
	expr->pass = SEMA_PASS_CYCLE_UNCHECKED;
	expr->type1 = type;
}

void sema_stmt_init(SemaStmt * stmt, SemaStmtType type) {
	stmt->type = type;
}

void sema_var_init_with_ast(SemaVar * var, const Var * ast, bool global) {
	var->pass = SEMA_PASS_AST;
	var->is_global = global;
	var->as.ast = ast;
}

void sema_var_init(SemaVar * var, SemaTypeHandle type, SemaExpr * opt_expr, bool global) {
	var->is_global = global;
	var->as.sema.init_with_expr = opt_expr != nullptr;
	var->as.sema.type = type;
	var->pass = SEMA_PASS_CYCLE_UNCHECKED;
	if (opt_expr != nullptr) {
		var->as.sema.unwrap.expr = *opt_expr;
	}
}

void sema_fn_init(SemaFn * fn, SemaTypeFn * sig, Str * args) {
	fn->pass = SEMA_PASS_CYCLE_UNCHECKED;
	fn->sema.signature = sig;
	fn->sema.args = args;
	fn->emmiting = SEMA_FN_UNEMMITED;
}

void sema_fn_init_with_ast(SemaFn * fn, const Fn * ast) {
	fn->pass = SEMA_PASS_AST;
	fn->ast = ast;
	fn->emmiting = SEMA_FN_UNEMMITED;
}

SymbolPos symbol_pos_global(void) {
	return (SymbolPos) {
		.local = false,
	};
}

SymbolPos symbol_pos_local(SemaFn * fn) {
	return (SymbolPos) {
		.local = true,
		.fn = fn,
	};
}

void sema_decl_init(SemaDecl * decl, SemaDeclType type, SymbolPos pos, Str iden) {
	decl->type = type;
	decl->pos = pos;
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
	++list->count;
	return &node->decl;
}
