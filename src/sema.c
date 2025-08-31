#include "include/sema.h"
#include "include/arena.h"
#include "include/utility.h"
#include <assert.h>
#include <stddef.h>
#include <stdio.h>
#include <stdbit.h>

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
	table->void_ptr_type.as.ptr.is_mut = true;
				// TIL that the type of nullptr is actually a *mut void,
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

void sema_env_init_push_fn_base_env(SemaCtx * ctx, SemaEnv * env, SemaFn * fn) {
	sema_decl_list_init(&env->decls);
	env->type = SEMA_ENV_FN_BLK;
	env->parent = ctx->env;
	env->sym_count = 0;
	env->as.fn.return_type = fn->sema.signature->return_type;
	env->as.fn.ptr = fn;
	sema_stmt_list_init(&env->as.fn.blk);
	ctx->env = env;
}

void sema_env_init_push_fn_blk_env(SemaCtx * ctx, SemaEnv * env) {
	sema_decl_list_init(&env->decls);
	env->type = SEMA_ENV_FN_BLK;
	env->parent = ctx->env;
	env->sym_count = 0;
	assert(ctx->env->type == SEMA_ENV_FN_BLK);
	env->as.fn.ptr = ctx->env->as.fn.ptr;
	env->as.fn.return_type = ctx->env->as.fn.return_type;
	sema_stmt_list_init(&env->as.fn.blk);
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
	ZERO(&ctx->worklist);
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
		for (usize i = 0; i < env->decls.size; ++i) {
			SemaDecl * decl = sema_decl_list_at(&env->decls, i);
			if (!str_equal(decl->iden, iden)) {
				continue;
			}
			switch (decl->type) {
				case SEMA_DECL_TYPE_ALIAS:
					return sema_type_alias_intern_with_stable_ptr(ctx, &decl->as.alias);
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

SemaVar * sema_ctx_lookup_var_with_pos(SemaCtx * ctx, Str iden, ReportError report_error, SymbolPos * out_pos) {
	SemaEnv * env = ctx->env;
	do {
		for (usize i = 0; i < env->decls.size; ++i) {
			SemaDecl * decl = sema_decl_list_at(&env->decls, i);
			if (!str_equal(decl->iden, iden)) {
				continue;
			}
			switch (decl->type) {
				case SEMA_DECL_VAR:
					if (out_pos) {
						*out_pos = decl->pos;
					}
					return &decl->as.var;
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

// Callers should handle non const variable in const function edge case
SemaVar * sema_ctx_lookup_var(SemaCtx * ctx, Str iden, ReportError report_error) {
	return sema_ctx_lookup_var_with_pos(ctx, iden, report_error, nullptr);
}

SemaFn * sema_ctx_lookup_fn_with_pos(SemaCtx * ctx, Str iden, ReportError report_error, SymbolPos * out_pos) {
	SemaEnv * env = ctx->env;
	do {
		for (usize i = 0; i < env->decls.size; ++i) {
			SemaDecl * decl = sema_decl_list_at(&env->decls, i);
			if (!str_equal(decl->iden, iden)) {
				continue;
			}
			switch (decl->type) {
				case SEMA_DECL_FN:
					if (out_pos) {
						*out_pos = decl->pos;
					}
					return &decl->as.fn;
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

SemaFn * sema_ctx_lookup_fn(SemaCtx * ctx, Str iden, ReportError report_error) {
	return sema_ctx_lookup_fn_with_pos(ctx, iden, report_error, nullptr);
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

static SemaDecl sema_decl_from_ast(SemaCtx * ctx, const Decl * ast, SymbolPos pos) {
	Str iden;
	SemaDecl decl;
	switch (ast->type) {
	case DECL_FN:
		if (!str_copy(ctx->arena, ast->as.fn.iden, &iden)) {
			sema_ctx_oom(ctx);
		}
		sema_decl_init(&decl, SEMA_DECL_FN, pos, iden);
		sema_fn_init_with_ast(&decl.as.fn, &ast->as.fn);
		break;
	case DECL_TYPE_ALIAS:
		if (!str_copy(ctx->arena, ast->as.alias.iden, &iden)) {
			sema_ctx_oom(ctx);
		}
		sema_decl_init(&decl, SEMA_DECL_TYPE_ALIAS, pos, iden);
		decl.as.alias.pass = SEMA_PASS_AST;
		decl.as.alias.ast = &ast->as.alias;
		break;
	case DECL_VAR:
		if (!str_copy(ctx->arena, ast->as.var.iden, &iden)) {
			sema_ctx_oom(ctx);
		}
		sema_decl_init(&decl, SEMA_DECL_VAR, pos, iden);
		sema_var_init_with_ast(&decl.as.var, &ast->as.var, !pos.local);
		break;
	}
	return decl;
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
bool run_implemented_fn(SemaCtx * ctx, SemaFn * fn, SemaValue * out, ReportError report_error); // the dream
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

static bool ensure_var_is_accessible(SemaCtx * ctx, SemaVar * var, SymbolPos pos, ReportError report_error) {
	SemaFn * current_fn = ctx->env->type == SEMA_ENV_FN_BLK ? ctx->env->as.fn.ptr : nullptr;
	if (var->is_const) {
		return true;
	}
	if (!pos.local) {
		if (!current_fn) { // getting address is legal? TODO
			return true;
		}
		if (current_fn->is_const) {
			if (report_error == DO_REPORT_ERROR) {
				fprintf(stderr, "error: non-constant global variable used in const fn scope\n");
			}
			return false;
		}
		return true;
	}
	if (pos.fn == current_fn) {
		return true;
	}
	if (report_error == DO_REPORT_ERROR) {
		fprintf(stderr, "error: closures aren't supported\n");
		return false;
	}
	return true;
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
	case EXPR_IDEN: {
			SymbolPos pos;
			fn = sema_ctx_lookup_fn_with_pos(ctx, ast->as.iden, DONT_REPORT_ERROR, &pos);
			if (fn) {
				if (!ensure_fn_is_sema(ctx, fn)) {
					goto error;
				}
				sema_expr_init_unimplemented(expr, SEMA_EXPR1_FN);
				expr->as.sema1.fn = fn;
				break;
			}
			var = sema_ctx_lookup_var_with_pos(ctx, ast->as.iden, DO_REPORT_ERROR, &pos);
			if (!var) {
				goto error;
			}
			if (!ensure_var_is_accessible(ctx, var, pos, DO_REPORT_ERROR)) {
				goto error;
			}
			if (!ensure_var_is_sema(ctx, var)) {
				goto error;
			}
			sema_expr_init_unimplemented(expr, SEMA_EXPR1_VAR);
			expr->as.sema1.var = var;
			break;
		}
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
	if (var->pass == SEMA_VAR_PASS_ERROR) {
		return false;
	}
	if (var->pass > SEMA_VAR_PASS_AST) {
		return true;
	}
	var->pass = SEMA_VAR_PASS_CYCLE_UNCHECKED;
	const Var * ast = var->as.ast;
	Str iden;
	if (!str_copy(ctx->arena, ast->iden, &iden)) {
		sema_ctx_oom(ctx);
	}
	SemaTypeHandle type = sema_type_from_ast(ctx, &ast->type);
	if (!type.type) {
		var->pass = SEMA_VAR_PASS_ERROR;
		return false;
	}
	type.is_lvalue = true;
	type.is_mut |= ast->is_mut;
	if (type.is_mut && ast->is_const) {
		fprintf(stderr, "error: attempted to give 'mut' specifier to constant variable\n");
		var->pass = SEMA_VAR_PASS_ERROR;
		return false;
	}
	bool init_with_expr = ast->init_with_expr;
	SemaExpr expr;
	if (init_with_expr) {
		sema_expr_init_with_ast(&expr, &ast->unwrap.expr);
		if (!ensure_expr_is_sema(ctx, &expr)) {
			var->pass = SEMA_VAR_PASS_ERROR;
			return false;
		}
	}
	sema_var_init(var, type, init_with_expr ? &expr : nullptr, sema_ctx_is_global_scope(ctx), ast->is_const);
	return true;
}

bool ensure_fn_is_sema(SemaCtx * ctx, SemaFn * fn) {
	if (fn->pass == SEMA_FN_PASS_ERROR) {
		return false;
	}
	if (fn->pass > SEMA_FN_PASS_AST) {
		return true;
	}
	fn->pass = SEMA_FN_PASS_CYCLE_UNCHECKED;
	const Fn * ast = fn->ast;
	if (ast->params == &poisoned_fn_param_list) {
		fn->pass = SEMA_FN_PASS_ERROR;
		return false;
	}
	SemaTypeHandleList params;
	sema_type_handle_list_init(&params);
	SemaTypeHandle return_type = sema_type_from_ast(ctx, &ast->return_type);
	if (!return_type.type) {
		fn->pass = SEMA_FN_PASS_ERROR;
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
			fn->pass = SEMA_FN_PASS_ERROR;
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
	sema_fn_init(fn, &type->as.fn, args, ast->is_const);
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
	case SEMA_VAR_PASS_ERROR:
		return false;
	case SEMA_VAR_PASS_AST:
		if (!ensure_var_is_sema(ctx, var)) {
			return false;
		}
		[[fallthrough]];
	case SEMA_VAR_PASS_CYCLE_CHECKING:
		if (var->visit_index < visitor.last_indirection_id) {
			var->pass = SEMA_VAR_PASS_ERROR;
			fprintf(stderr, "error: cycle detected\n");
			return false;
		}
		return true;
	case SEMA_VAR_PASS_CYCLE_UNCHECKED:
		var->pass = SEMA_VAR_PASS_CYCLE_CHECKING;
		var->visit_index = visitor.visit_id++;
		if (!ensure_type_is_cycle_checked(ctx, visitor, var->as.sema.type.type)) {
			var->pass = SEMA_VAR_PASS_ERROR;
			return false;
		}
		if (var->as.sema.init_with_expr) {
			if (!ensure_expr_is_cycle_checked(ctx, visitor, &var->as.sema.unwrap.expr)) {
				var->pass = SEMA_VAR_PASS_ERROR;
				return false;
			}
		}
		var->pass = SEMA_VAR_PASS_CYCLE_CHECKED;
		[[fallthrough]];
	case SEMA_VAR_PASS_CYCLE_CHECKED:
	case SEMA_VAR_PASS_IMPLEMENTED:
	case SEMA_VAR_PASS_REDUCED:
		return true;
	}
}

bool ensure_fn_is_cycle_checked(SemaCtx * ctx, VisitorState visitor, SemaFn * fn) {
	SemaType * fn_type;
	switch (fn->pass) {
	case SEMA_FN_PASS_ERROR:
		return false;
	case SEMA_FN_PASS_AST:
		if (!ensure_fn_is_sema(ctx, fn)) {
			return false;
		}
		[[fallthrough]];
	case SEMA_FN_PASS_CYCLE_UNCHECKED:
	case SEMA_FN_PASS_CYCLE_CHECKING:
		fn_type = sema_type_from_interned_fn(fn->sema.signature);
		if (!ensure_type_is_cycle_checked(ctx, visitor, fn_type)) {
			fn->pass = SEMA_FN_PASS_ERROR;
			return false;
		}
		fn->pass = SEMA_FN_PASS_CYCLE_CHECKED;
		[[fallthrough]];
	case SEMA_FN_PASS_CYCLE_CHECKED:
	case SEMA_FN_PASS_IMPLEMENTING:
	case SEMA_FN_PASS_IMPLEMENTED:
	case SEMA_FN_PASS_REDUCED:
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
		if (!ensure_fn_is_implemented(ctx, visitor, expr->as.sema1.fn)) {
			goto error;
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
	case SEMA_EXPR1_DEREF: {
		iresult = _ensure_expr_is_implemented(ctx, visitor, expr->as.sema1.deref, &itype, false);
		if (!iresult) {
			goto error;
		}
		if (!check_type_deref(ctx, itype, &type)) {
			goto error;
		}
		SemaExpr * derefed_expr = expr->as.sema1.deref;
		if (deref) {
			sema_expr_init_implemented(expr, SEMA_EXPR2_DEREF);
			expr->as.sema2.deref = derefed_expr;
			result = EXPR_EVAL_UNREDUCED;
		} else {
			*expr = *derefed_expr;
			result = EXPR_EVAL_REDUCED;
		}
		break;
	}
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
				bool global = sema_ctx_is_global_scope(ctx);
				if (global || var->is_const) {
					if (global && !var->as.sema.init_with_expr) {
						fprintf(stderr, "error: uninitialized global used in constant expression\n");
						goto error;
					}
					*expr = var->as.sema.unwrap.expr;
					result = expr->type2 == SEMA_EXPR2_VALUE ? EXPR_EVAL_REDUCED : EXPR_EVAL_UNREDUCED;
					break;
				}
				sema_expr_init_implemented(expr, SEMA_EXPR2_LOAD_VAR);
				expr->as.sema2.load_var = var;
				result = EXPR_EVAL_UNREDUCED;
				break;
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
	case SEMA_VAR_PASS_ERROR:
		return false;
	case SEMA_VAR_PASS_AST:
	case SEMA_VAR_PASS_CYCLE_UNCHECKED:
	case SEMA_VAR_PASS_CYCLE_CHECKING:
		if (!ensure_var_is_cycle_checked(ctx, visitor, var)) {
			return false;
		}
	[[fallthrough]];
	case SEMA_VAR_PASS_CYCLE_CHECKED:
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
			// TODO: move this to appropriate block
			// if (result == EXPR_EVAL_UNREDUCED && var->is_global) {
			// 	fprintf(stderr, "error: initalization of global variable with non-constant expression\n");
			// 	goto error;
			// }
		} else if (var->is_const) {
			fprintf(stderr, "error: uninitialized const variable\n");
			goto error;
		}
		var->pass = SEMA_VAR_PASS_IMPLEMENTED;
		[[fallthrough]];
	case SEMA_VAR_PASS_IMPLEMENTED:
	case SEMA_VAR_PASS_REDUCED:
		return true;
	}
error:
	var->pass = SEMA_VAR_PASS_ERROR;
	return false;
}
bool fn_worklist_push_with_ctx(SemaCtx * ctx, SemaFnWorklist * list, SemaFn * fn) {
	SemaFnPtrNode * node;
	if (ctx->free_fn_ptrs) {
		node = ctx->free_fn_ptrs;
		ctx->free_fn_ptrs = node->next;
	} else {
		node = vmem_arena_alloc(ctx->arena, SemaFnPtrNode);
		if (UNLIKELY(!node)) {
			return false;
		}
	}
	node->fn = fn;
	node->next = list->begin;
	list->begin = node;
	if (!list->end) {
		list->end = node;
	}
	return true;
}

SemaFn * fn_worklist_pop_with_ctx(SemaCtx * ctx, SemaFnWorklist * list) {
	SemaFnPtrNode * node = list->begin;
	list->begin = node->next;
	if (list->end == node) {
		list->end = nullptr;
	}
	node->next = ctx->free_fn_ptrs;
	ctx->free_fn_ptrs = node;
	return node->fn;
}

void fn_worklist_free_with_ctx(SemaCtx * ctx, SemaFnWorklist * list) {
	if (!list->end) {
		return;
	}
	list->end->next = ctx->free_fn_ptrs;
	ctx->free_fn_ptrs = list->begin;
}

static bool complete_block(SemaCtx * ctx, VisitorState visitor, StmtList blk, SemaFnWorklist * list);

static bool complete_stmt(SemaCtx * ctx, VisitorState visitor, const Stmt * ast, SemaFnWorklist * list) {
	SemaEnv * env = ctx->env;
	SemaStmtList * blk = &env->as.fn.blk;
	SemaStmt stmt;
	switch (ast->type) {
	case STMT_SEMICOLON:
		return true;
	case STMT_BLOCK: {
			SemaEnv chld;
			sema_env_init_push_fn_blk_env(ctx, &chld);
			bool ok = complete_block(ctx, visitor, ast->as.block, list);
			sema_env_pop(ctx);
			sema_stmt_init(&stmt, SEMA_STMT_BLOCK);
			stmt.as.block = chld;
			if (!sema_stmt_list_push(ctx->arena, blk, stmt)) {
				sema_ctx_oom(ctx);
			}
			return ok;
		}
	case STMT_DECL: {
			SemaDecl decl = sema_decl_from_ast(ctx, ast->as.decl,
						symbol_pos_local(env->as.fn.ptr, (LocalSymbolIndex)env->decls.size)); // <- TODO
			if (decl.type == SEMA_DECL_FN) {
				SemaDecl * pdecl = sema_ctx_add_decl(ctx, decl);
				if (!sema_ctx_add_decl(ctx, decl)) {
					sema_ctx_oom(ctx);
				}
				if (!fn_worklist_push_with_ctx(ctx, list, &pdecl->as.fn)) {
					sema_ctx_oom(ctx);
				}
			} else {
				if (!ensure_decl_is_implemented(ctx, visitor, &decl)) {
					return false;
				}
				if (!sema_ctx_add_decl(ctx, decl)) {
					sema_ctx_oom(ctx);
				}
			}
			return true;
		}
	case STMT_RETURN: {
			SemaExpr expr;
			SemaTypeHandle type;
			if (!ast->as.return_.has_expr) {
				sema_expr_init_implemented(&expr, SEMA_EXPR2_VALUE);
				sema_value_init(&expr.as.sema2.value, SEMA_VALUE_VOID);
			} else {
				sema_expr_init_with_ast(&expr, &ast->as.return_.unwrap.expr);
				if (!ensure_expr_is_implemented(ctx, visitor, &expr, &type)) {
					return false;
				}
				if (!coerce_expr_to_type(ctx, &expr, type, sema_type_handle_from_ptr(env->as.fn.return_type))) {
					return false;
				}
			}
			sema_stmt_init(&stmt, SEMA_STMT_RETURN);
			stmt.as.return_ = expr;
			if (!sema_stmt_list_push(ctx->arena, blk, stmt)) {
				sema_ctx_oom(ctx);
			}
			return true;
		}
	case STMT_EXPR: {
			SemaExpr expr;
			sema_expr_init_with_ast(&expr, &ast->as.expr);
			if (!ensure_expr_is_implemented(ctx, visitor, &expr, nullptr)) {
				return false;
			}
			sema_stmt_init(&stmt, SEMA_STMT_EXPR);
			stmt.as.expr = expr;
			if (!sema_stmt_list_push(ctx->arena, blk, stmt)) {
				sema_ctx_oom(ctx);
			}
			return true;
		}
	}
}

static bool complete_block(SemaCtx * ctx, VisitorState visitor, StmtList blk, SemaFnWorklist * list) {
	bool ok = true;
	for (auto node = blk.begin; node; node = node->next) {
		const Stmt * stmt = &node->stmt;
		ok &= complete_stmt(ctx, visitor, stmt, list);
	}
	return ok;
}

static bool complete_fn_iter(SemaCtx * ctx, VisitorState visitor, SemaFn * fn, SemaFnWorklist * list) {
	switch (fn->pass) {
	case SEMA_FN_PASS_ERROR:
		return false;
	case SEMA_FN_PASS_AST:
	case SEMA_FN_PASS_CYCLE_UNCHECKED:
	case SEMA_FN_PASS_CYCLE_CHECKING:
		if (!ensure_fn_is_cycle_checked(ctx, visitor, fn)) {
			return false;
		}
		[[fallthrough]];
	case SEMA_FN_PASS_CYCLE_CHECKED: {
			fn->pass = SEMA_FN_PASS_IMPLEMENTING;
			SemaType * type = sema_type_from_interned_fn(fn->sema.signature);
			if (!ensure_type_ptr_is_implemented(ctx, visitor, &type)) {
				fn->pass = SEMA_FN_PASS_ERROR;
				return false;
			}
			fn->sema.signature = &type->as.fn;
			SemaEnv env;
			sema_env_init_push_fn_base_env(ctx, &env, fn);
			usize i = 0;
			for (auto node = fn->sema.signature->params.begin; node; node = node->next) {
				SemaTypeHandle type = node->type;
				Str iden = fn->sema.args[i];
				SemaVar var;
				sema_var_init(&var, type, nullptr, false, false);
				SemaDecl decl;
				sema_decl_init(&decl, SEMA_DECL_VAR, symbol_pos_local(fn, (LocalSymbolIndex)env.decls.size), iden);
				// TODO: overflow
				decl.as.var = var;
				if (!sema_ctx_add_decl(ctx, decl)) {
					sema_ctx_oom(ctx);
				}
				++i;
			}
			bool ok = complete_block(ctx, visitor, fn->ast->body, list);
			sema_env_pop(ctx);
			if (!ok) {
				fn->pass = SEMA_FN_PASS_ERROR;
				return false;
			}
			fn->pass = SEMA_FN_PASS_IMPLEMENTED;
			fn->sema.unwrap.env = env;
			return true;
		}
	case SEMA_FN_PASS_IMPLEMENTING:
	case SEMA_FN_PASS_IMPLEMENTED:
	case SEMA_FN_PASS_REDUCED:
		return true;
	}
}

ExprEvalResult reduce_implemented_expr(SemaCtx * ctx, SemaExpr * expr) {
	if (expr->pass == SEMA_PASS_ERROR) {
		return EXPR_EVAL_ERROR;
	}
	switch (expr->type2) {
	case SEMA_EXPR2_VALUE:
		return EXPR_EVAL_REDUCED;
	case SEMA_EXPR2_ADD_I32: {
			SemaExpr * a = expr->as.sema2.add.a;
			SemaExpr * b = expr->as.sema2.add.b;
			ExprEvalResult aresult = reduce_implemented_expr(ctx, a);
			ExprEvalResult bresult = reduce_implemented_expr(ctx, b);
			if (!aresult || !bresult) {
				return EXPR_EVAL_ERROR;
			}
			if (aresult == EXPR_EVAL_REDUCED && bresult == EXPR_EVAL_REDUCED) {
				i32 value = a->as.sema2.value.as.i32
						+	b->as.sema2.value.as.i32;
				sema_expr_init_reduced(expr, SEMA_EXPR2_VALUE);
				sema_value_init(&expr->as.sema2.value, SEMA_VALUE_I32);
				expr->as.sema2.value.as.i32 = value;
				return EXPR_EVAL_REDUCED;
			}
			return EXPR_EVAL_UNREDUCED;
		}
	case SEMA_EXPR2_FUNCALL: {
			// TODO: find more errors
			SemaExpr * fn_expr = expr->as.sema2.funcall.fun;
			ExprEvalResult result = reduce_implemented_expr(ctx, fn_expr);
			if (result != EXPR_EVAL_ERROR) {
				return EXPR_EVAL_ERROR;
			}
			for (usize i = 0; i < expr->as.sema2.funcall.args.size; ++i) {
				SemaExpr * arg = &expr->as.sema2.funcall.args.data[i];
				ExprEvalResult aresult = reduce_implemented_expr(ctx, arg);
				if (!result) {
					return EXPR_EVAL_ERROR;
				}
				result = aresult == EXPR_EVAL_REDUCED ? result : EXPR_EVAL_UNREDUCED;
			}
			if (result != EXPR_EVAL_REDUCED) {
				return EXPR_EVAL_UNREDUCED;
			}
			SemaFn * fn = fn_expr->as.sema2.value.as.fn;
			SemaValue value;
			if (!run_implemented_fn(ctx, fn, &value, DO_REPORT_ERROR)) {
				return EXPR_EVAL_UNREDUCED;
			}
			sema_expr_init_reduced(expr, SEMA_EXPR2_VALUE);
			expr->as.sema2.value = value;
			return EXPR_EVAL_REDUCED;
		}
	case SEMA_EXPR2_DEREF: {
			SemaExpr * deref_expr = expr->as.sema2.deref;
			ExprEvalResult result = reduce_implemented_expr(ctx, deref_expr);
			if (!result) {
				return EXPR_EVAL_ERROR;
			}
			if (result != EXPR_EVAL_REDUCED) {
				return EXPR_EVAL_UNREDUCED;
			}
			SemaValue * value = &deref_expr->as.sema2.value;
			switch (value->type) {
			case SEMA_VALUE_VAR_REF:
			case SEMA_VALUE_VAR_PTR:
				assert(value->as.var_ptr->as.sema.init_with_expr);
				*expr = value->as.var_ptr->as.sema.unwrap.expr;
				assert(expr->type2 == SEMA_EXPR2_VALUE);
				return EXPR_EVAL_REDUCED;
			case SEMA_VALUE_RAW_PTR:
			case SEMA_VALUE_RAW_REF:
				return EXPR_EVAL_UNREDUCED;
			case SEMA_VALUE_NULLPTR:
				fprintf(stderr, "error: tried to deref a nullptr constant\n");
				return false;
			case SEMA_VALUE_VOID:
			case SEMA_VALUE_I32:
			case SEMA_VALUE_FN:
				UNREACHABLE();
			}
		}
	case SEMA_EXPR2_LOAD_VAR: {
			ExprEvalResult result = reduce_implemented_var(ctx, expr->as.sema2.load_var);
			if (!result) {
				return EXPR_EVAL_ERROR;
			}
			if (result == EXPR_EVAL_UNREDUCED) {
				return EXPR_EVAL_UNREDUCED;
			}
			assert(expr->as.sema2.load_var->as.sema.init_with_expr);
			*expr = expr->as.sema2.load_var->as.sema.unwrap.expr;
			return EXPR_EVAL_REDUCED;
		}
	}
}

ExprEvalResult reduce_implemented_var(SemaCtx * ctx, SemaVar * var) {
	if (var->pass == SEMA_VAR_PASS_ERROR) {
		goto error;
	}
	if (!var->is_const) {
		goto error;
	}
	assert(var->as.sema.init_with_expr);
	ExprEvalResult result = reduce_implemented_expr(ctx, &var->as.sema.unwrap.expr);
	if (!result) {
		goto error;
	}
	if (result == EXPR_EVAL_REDUCED) {
		// TODO: check if scope is global
		return var->is_const || var->is_global ? EXPR_EVAL_REDUCED : EXPR_EVAL_UNREDUCED;
	}
	// result == EXPR_EVAL_UNREDUCED
	if (var->is_const) {
		fprintf(stderr, "error: non-constant expression assigned to constant variable\n");
		goto error;
	}
	if (var->is_global) {
		fprintf(stderr, "error: global variable initialized with non-constant expression\n");
		goto error;
	}
	return EXPR_EVAL_UNREDUCED;
error:
	var->pass = SEMA_VAR_PASS_ERROR;
	return EXPR_EVAL_ERROR;
}

static bool reduce_implemented_blk(SemaCtx * ctx, SemaStmtList * blk);

static bool reduce_implemented_stmt(SemaCtx * ctx, SemaStmt * stmt) {
	switch (stmt->type) {
	case SEMA_STMT_EXPR:
		return reduce_implemented_expr(ctx, &stmt->as.expr);
	case SEMA_STMT_RETURN:
		return reduce_implemented_expr(ctx, &stmt->as.return_);
	case SEMA_STMT_BLOCK:
		return reduce_implemented_blk(ctx, &stmt->as.block.as.fn.blk);
	}
}

static bool reduce_implemented_blk(SemaCtx * ctx, SemaStmtList * blk) {
	bool ok = true;
	for (usize i = 0; i < blk->size; ++i) {
		SemaStmt * stmt = sema_stmt_list_at(blk, i);
		ok &= reduce_implemented_stmt(ctx, stmt);
	}
	return ok;
}

bool reduce_implemented_fn(SemaCtx * ctx, SemaFn * fn) {
	if (fn->pass == SEMA_FN_PASS_ERROR) {
		return false;
	}
	return reduce_implemented_blk(ctx, &fn->sema.unwrap.env.as.fn.blk);
}

bool ensure_fn_is_implemented(SemaCtx * ctx, VisitorState visitor, SemaFn * fn) {
	SemaFnWorklist * worklist = &ctx->worklist;
	SemaFnWorklist reduction_worklist = {};
	complete_fn_iter(ctx, visitor, fn, worklist);
	// TODO: see if I can make this not shortcircuit
	if (!complete_fn_iter(ctx, visitor, fn, worklist)) {
		return false;
	}
	while (worklist->begin) {
		SemaFn * fn = fn_worklist_pop_with_ctx(ctx, worklist);
		if (!complete_fn_iter(ctx, visitor, fn, worklist)) {
			return false;
		}
		// should never fail due to free list being populated ^
		assert(fn_worklist_push_with_ctx(ctx, &reduction_worklist, fn));
	}
	bool ok = true;
	while (reduction_worklist.begin) {
		SemaFn * fn = fn_worklist_pop_with_ctx(ctx, &reduction_worklist);
		if (!reduce_implemented_fn(ctx, fn) && fn->is_const) {
			fn->pass = SEMA_FN_PASS_ERROR;
			ok = false;
		}
	}
	fn_worklist_free_with_ctx(ctx, &reduction_worklist);
	return ok;
}

bool run_implemented_fn(SemaCtx * ctx, SemaFn * fn, SemaValue * out, ReportError report_error) {
	if (fn->pass == SEMA_FN_PASS_ERROR) {
		return false;
	}
	assert(fn->pass == SEMA_FN_PASS_IMPLEMENTED);
	TODO();
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
		SemaDecl decl = sema_decl_from_ast(ctx, &node->decl, symbol_pos_global());
		if (!sema_ctx_add_decl(ctx, decl)) {
			sema_ctx_oom(ctx);
		}
	}
	bool ok = true;
	for (usize i = 0; i < ctx->env->decls.size; ++i) {
		ok &= ensure_decl_is_implemented(ctx, new_visitor_state(), sema_decl_list_at(&ctx->env->decls, i));
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
		UNREACHABLE();
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

void sema_expr_init_unimplemented(SemaExpr * expr, SemaExpr1Type type) {
	expr->pass = SEMA_PASS_CYCLE_UNCHECKED;
	expr->type1 = type;
}

void sema_expr_init_implemented(SemaExpr * expr, SemaExpr2Type type) {
	expr->pass = SEMA_PASS_IMPLEMENTED;
	expr->type2 = type;
}

void sema_expr_init_reduced(SemaExpr * expr, SemaExpr2Type type) {
	expr->pass = SEMA_PASS_IMPLEMENTED;
	expr->type2 = type;
}

void sema_stmt_init(SemaStmt * stmt, SemaStmtType type) {
	stmt->type = type;
}

void sema_var_init_with_ast(SemaVar * var, const Var * ast, bool global) {
	var->pass = SEMA_VAR_PASS_AST;
	var->is_global = global;
	var->is_const = ast->is_const;
	var->as.ast = ast;
}

void sema_var_init(SemaVar * var, SemaTypeHandle type, SemaExpr * opt_expr, bool global, bool is_const) {
	var->is_global = global;
	var->is_const = is_const;
	var->as.sema.init_with_expr = opt_expr != nullptr;
	var->as.sema.type = type;
	var->pass = SEMA_VAR_PASS_CYCLE_UNCHECKED;
	if (opt_expr != nullptr) {
		var->as.sema.unwrap.expr = *opt_expr;
	}
}

void sema_fn_init(SemaFn * fn, SemaTypeFn * sig, Str * args, bool is_const) {
	fn->pass = SEMA_FN_PASS_CYCLE_UNCHECKED;
	fn->is_const = is_const;
	fn->sema.signature = sig;
	fn->sema.args = args;
}

void sema_fn_init_with_ast(SemaFn * fn, const Fn * ast) {
	fn->pass = SEMA_FN_PASS_AST;
	fn->is_const = ast->is_const;
	fn->ast = ast;
}

SymbolPos symbol_pos_global(void) {
	return (SymbolPos) {
		.local = false,
	};
}

SymbolPos symbol_pos_local(SemaFn * fn, LocalSymbolIndex index) {
	return (SymbolPos) {
		.local = true,
		.fn = fn,
		.index = index,
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

static usize segmented_list_get_slot(usize index) {
	return stdc_bit_width(index + 1) - 1;
}

static usize segmented_list_get_index_in_slot(usize slot, usize index) {
	return index - ((usize)1 << slot) + 1;
}

void sema_stmt_list_init(SemaStmtList * list) {
	ZERO(list);
}

SemaStmt * sema_stmt_list_push(VMemArena * arena, SemaStmtList * list, SemaStmt stmt) {
	usize slot = segmented_list_get_slot(list->size);
	if (slot == list->slots_size) {
		usize slots_size = slot + 1;
		SemaStmt ** slots = vmem_arena_alloc_n(arena, SemaStmt *, slots_size);
		if (UNLIKELY(!slots)) {
			return NULL;
		}
		usize slot_size = (1U << slot);
		SemaStmt * slot_ptr = vmem_arena_alloc_n(arena, SemaStmt, slot_size);
		if (UNLIKELY(!slot_ptr)) {
			return NULL;
		}
		for (usize i = 0; i < slot; ++i) {
			slots[i] = list->slots[i];
		}
		slots[slot] = slot_ptr;
		list->slots = slots;
		list->slots_size = slots_size;
	}
	usize index = segmented_list_get_index_in_slot(slot, list->size);
	if (UNLIKELY(!ckd_add(list->size, 1, &list->size))) {
		return NULL;
	}
	SemaStmt * stmt_ptr = &list->slots[slot][index];
	*stmt_ptr = stmt;
	return stmt_ptr;
}

SemaStmt * sema_stmt_list_at(SemaStmtList * list, usize index) {
	usize slot = segmented_list_get_slot(index);
	usize slot_index = segmented_list_get_index_in_slot(slot, index);
	return &list->slots[slot][slot_index];
}

void sema_decl_list_init(SemaDeclList * list) {
	ZERO(list);
}

SemaDecl * sema_decl_list_push(VMemArena * arena, SemaDeclList * list, SemaDecl decl) {
	usize slot = segmented_list_get_slot(list->size);
	if (slot == list->slots_size) {
		usize slots_size = slot + 1;
		SemaDecl ** slots = vmem_arena_alloc_n(arena, SemaDecl *, slots_size);
		if (UNLIKELY(!slots)) {
			return NULL;
		}
		usize slot_size = (1U << slot);
		SemaDecl * slot_ptr = vmem_arena_alloc_n(arena, SemaDecl, slot_size);
		if (UNLIKELY(!slot_ptr)) {
			return NULL;
		}
		for (usize i = 0; i < slot; ++i) {
			slots[i] = list->slots[i];
		}
		slots[slot] = slot_ptr;
		list->slots = slots;
		list->slots_size = slots_size;
	}
	usize index = segmented_list_get_index_in_slot(slot, list->size);
	if (UNLIKELY(!ckd_add(list->size, 1, &list->size))) {
		return NULL;
	}
	SemaDecl * decl_ptr = &list->slots[slot][index];
	*decl_ptr = decl;
	return decl_ptr;
}

SemaDecl * sema_decl_list_at(SemaDeclList * list, usize index) {
	assert(index < list->size);
	usize slot = segmented_list_get_slot(index);
	usize slot_index = segmented_list_get_index_in_slot(slot, index);
	return &list->slots[slot][slot_index];
}
