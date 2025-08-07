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

static bool sema_type_alias_is_sema(SemaTypeAlias * alias) {
	return alias->pass > SEMA_PASS_AST;
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

static bool sema_ctx_is_global_scope(SemaCtx * ctx) {
	return ctx->env->type == SEMA_ENV_MOD;
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
	unreachable();
}

SemaType * sema_type_dedup_implemented(SemaCtx * ctx, SemaType * type) {
	assert(type->pass >= SEMA_PASS_IMPLEMENTED);
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
			if (sema_type_handle_eq(type->as.ptr, type2->as.ptr)) {
				return type2;
			}
			break;
		case SEMA_TYPE_REF:
			if (sema_type_handle_eq(type->as.ref, type2->as.ref)) {
				return type2;
			}
			break;
		case SEMA_TYPE_FN:
			if (type->as.fn.return_type != type2->as.fn.return_type) {
				break;
			}
			if (type->as.fn.params.count != type2->as.fn.params.count) {
				break;
			}
			for (node1 = type->as.fn.params.begin, node2 = type2->as.fn.params.begin;
				node1;
				node1 = node1->next, node2 = node2->next) {
				if (!sema_type_handle_eq(node1->type, node2->type)) {
					break;
				}
			}
			return type2;
		case SEMA_TYPE_TYPE_ALIAS:
			unreachable(); // git out
		}
	}
	if (!sema_type_handle_list_push_with_ctx(ctx, 
				&ctx->table->complete_types, sema_type_handle_from_ptr(type))) {
		sema_ctx_oom(ctx);
	}
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
	do {
		if (str_equal(iden, s("int"))) {
			return sema_type_handle_from_ptr(&ctx->table->i32_type);
		}
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
	unreachable();
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
			sema_ctx_oom(ctx);
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
		sema_ctx_oom(ctx);
	}
	usize i = 0;
	for (auto node = ast->params->begin; node; node = node->next) {
		if (!str_copy(ctx->arena,
					node->param.has_iden ? node->param.unwrap.iden : s(""),
					args + i)) {
			sema_ctx_oom(ctx);
		}
		++i;
	}
	fn->pass = SEMA_PASS_CYCLE_UNCHECKED;
	fn->sema.signature = &fn_type->as.fn;
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
		assert(false && "TODO to remove");
		// if (!sema_expr_from_ast(ctx, &ast->unwrap.expr, &expr)) {
		// 	return false;
		// }
	}
	sema_var_init(var, type, ast->init_with_expr ? &expr : nullptr, var->is_global);
	return true;
}

// static bool declare_decl(SemaCtx * ctx, SemaDecl * decl) {
// 	switch (decl->type) {
// 	case SEMA_DECL_FN:
// 		assert(false && "TODO to remove");
// 		// if (decl->as.fn.has_sema) {
// 		// 	return true;
// 		// }
// 		return declare_ast_fn(ctx, &decl->as.fn);
// 	case SEMA_DECL_TYPE_ALIAS:
// 		if (sema_type_alias_is_sema(&decl->as.alias)) {
// 			return true;
// 		}
// 		return declare_ast_type_alias(ctx, &decl->as.alias);
// 	case SEMA_DECL_VAR:
// 		if (decl->as.var.pass > SEMA_PASS_AST) {
// 			return true;
// 		}
// 		return declare_ast_var(ctx, &decl->as.var);
// 	}
// 	return false;
// }

// this should be a very happy path :)
// populate the type and nested types with size and alignment
// indirect cycles will be ignored as they will get populated eventually
// also will resolve alias indirection here
static SemaTypeHandle populate_type(SemaType * type) {
	SemaTypeHandle ntype;
	type->pass = SEMA_PASS_CYCLE_CHECKED;
	switch (type->type) {
		case SEMA_TYPE_I32:
			type->impled.align = alignof(i32);
			type->impled.size = sizeof(i32);
			break;
		case SEMA_TYPE_VOID:
			type->impled.align = 0; // not complete a type, so 0 it is
			type->impled.size = 0;
			break;
		case SEMA_TYPE_TYPE_ALIAS:
			assert(sema_type_alias_is_sema(type->as.alias));
			ntype = populate_type(type->as.alias->sema.next.type);
			assert(ntype.type->type != SEMA_TYPE_TYPE_ALIAS);
			type->as.alias->sema.next = ntype;
			return ntype;
		case SEMA_TYPE_FN:
			type->impled.align = 0; // also not a complete type
			type->impled.size = 0;
			// members are indirect cycles, so no work further done
			break;
		case SEMA_TYPE_PTR:
			SemaTypeHandle handle = populate_type(type->as.ptr.type);
			type->as.ptr.type = handle.type;
			type->as.ptr.is_mut |= handle.is_mut;
			type->as.ptr.is_lvalue = false; // this doesn't really make any sense here
			break;
		case SEMA_TYPE_REF:
			handle = populate_type(type->as.ref.type);
			type->as.ref.type = handle.type;
			type->as.ref.is_mut |= handle.is_mut;
			type->as.ref.is_lvalue = false;
			break;
	}
	return sema_type_handle_from_ptr(type);
}

static SemaTypeHandle complete_type_iter(SemaCtx * ctx, SemaType * type,
				     u32 visit_index_counter,
				     u32 last_indirection_index,
				     u32 last_opaque_index);

// static SemaTypeHandle complete_type(SemaCtx * ctx, SemaType * type);

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

// static bool complete_and_reduce_type(SemaCtx * ctx, SemaTypeHandle * type) {
// 	SemaTypeHandle ntype = complete_type(ctx, type->type);
// 	if (!ntype.type) {
// 		return false;
// 	}
// 	ntype.is_mut = type->is_mut;
// 	ntype.is_lvalue = type->is_lvalue;
// 	*type = ntype;
// 	return true;
// }

static SemaTypeHandle complete_type_iter(SemaCtx * ctx, SemaType * type,
		u32 visit_index_counter, u32 last_indirection_index, u32 last_opaque_index) {
	if (type->pass >= SEMA_PASS_CYCLE_CHECKED) {
		while (type->type == SEMA_TYPE_TYPE_ALIAS) {
			assert(type->as.alias->sema.next.type);
			type = type->as.alias->sema.next.type;
		}
		return sema_type_handle_from_ptr(type);
	}
	if (type->pass == SEMA_PASS_CYCLE_CHECKING) { // potential cycle
		if (type->visit_index < last_indirection_index
			&& type->visit_index <= last_opaque_index) {
			return sema_type_handle_from_ptr(type); // indirect circular dependency all good
		}
		fprintf(stderr, "error: detected cycle\n");
		return null_sema_type_handle;
	}
	type->visit_index = visit_index_counter;
	++visit_index_counter;
	type->pass = SEMA_PASS_CYCLE_CHECKING;
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
		case SEMA_TYPE_PTR:
			last_indirection_index = type->visit_index;
			if (!complete_type_iter(ctx, type->as.ptr.type,
						visit_index_counter, last_indirection_index, last_indirection_index).type) {
				return null_sema_type_handle;
			}
			break;
		case SEMA_TYPE_REF:
			last_indirection_index = type->visit_index;
			if (!complete_type_iter(ctx, type->as.ref.type,
						visit_index_counter, last_indirection_index, last_opaque_index).type) {
				return null_sema_type_handle;
			}
			break;
		case SEMA_TYPE_TYPE_ALIAS:
			if (!sema_type_alias_is_sema(type->as.alias)) {
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

// static SemaTypeHandle complete_type(SemaCtx * ctx, SemaType * type) {
// 	u32 visit_index_counter = 1; // keeps track of the current nodes position in the trace
// 	u32 last_indirection_index = 0; // stuff like pointers
// 	u32 last_opaque_index = 0; // stuff like structs that provide a name to avoid infinitely recursive signature
// 	return complete_type_iter(ctx, type, visit_index_counter, last_indirection_index, last_opaque_index);
// }

// static bool complete_expr_iter(SemaCtx * ctx, SemaExpr * expr,
// 								u32 visit_index_counter, u32 last_indirection_index) {
// 	switch (expr->type) {
// 	case SEMA_EXPR1_VOID:
// 	case SEMA_EXPR1_I32:
// 	case SEMA_EXPR1_NULLPTR:
// 		break;
// 	case SEMA_EXPR1_FN:
// 		break;
// 	case SEMA_EXPR1_PLUS:
// 		if (!complete_expr_iter(ctx, expr->as.plus.a, visit_index_counter, last_indirection_index)) {
// 			return false;
// 		}
// 		if (!complete_expr_iter(ctx, expr->as.plus.b, visit_index_counter, last_indirection_index)) {
// 			return false;
// 		}
// 		break;
// 	case SEMA_EXPR1_FUNCALL:
// 		if (!complete_expr_iter(ctx, expr->as.funcall.fun, visit_index_counter, last_indirection_index)) {
// 			return false;
// 		}
// 		for (usize i = 0; i < expr->as.funcall.args.size; ++i) {
// 			if (!complete_expr_iter(ctx, &expr->as.funcall.args.data[i], visit_index_counter, last_indirection_index)) {
// 				return false;
// 			}
// 		}
// 		break;
// 	case SEMA_EXPR1_ADDR:
// 		last_indirection_index = visit_index_counter++;
// 		if (!complete_expr_iter(ctx, expr->as.addr, visit_index_counter, last_indirection_index)) {
// 			return false;
// 		}
// 		break;
// 	case SEMA_EXPR1_DEREF:
// 		if (!complete_expr_iter(ctx, expr->as.deref, visit_index_counter, last_indirection_index)) {
// 			return false;
// 		}
// 		break;
// 	case SEMA_EXPR1_VAR:
// 		if (expr->as.var->pass == SEMA_PASS_AST) {
// 			return false;
// 		}
// 		if (!expr->as.var->as.sema.init_with_expr) {
// 			fprintf(stderr, "warning: uninitialized global used in constant expression\n");
// 			break;
// 		}
// 		if (expr->as.var->visit_status == VISIT_STATUS_VISITED) {
// 			break;
// 		}
// 		if (expr->as.var->visit_status == VISIT_STATUS_VISITING) {
// 			if (expr->as.var->visit_index < last_indirection_index) {
// 				break; // all good again
// 			}
// 			fprintf(stderr, "error: detected cycle\n");
// 			return false;
// 		}
// 		expr->as.var->visit_status = VISIT_STATUS_VISITING;
// 		expr->as.var->visit_index = visit_index_counter++;
// 		if (!complete_and_reduce_type(ctx, &expr->as.var->as.sema.type)) {
// 			return false;
// 		}
// 		if (!complete_expr_iter(ctx, &expr->as.var->as.sema.unwrap.expr,
// 					visit_index_counter,
// 					last_indirection_index)) {
// 		    return false;
// 		}
// 		expr->as.var->visit_status = VISIT_STATUS_VISITED;
// 		break;
// 	case SEMA_EXPR1_LOAD_VAR:
// 		unreachable(); // again generated by compiler
// 	}
// 	return true;
// }

// static bool complete_fn(SemaCtx * ctx, SemaFn * fn) {
// 	if (fn->pass == SEMA_PASS_AST) {
// 		return false;
// 	}
// 	SemaTypeHandle handle = sema_type_handle_from_ptr(fn->sema.signature->return_type);
// 	if (!complete_and_reduce_type(ctx, &handle)) {
// 		return false;
// 	}
// 	fn->sema.signature->return_type = handle.type;
// 	for (auto node = fn->sema.signature->params.begin; node; node = node->next) {
// 		if (!complete_and_reduce_type(ctx, &node->type)) {
// 			return false;
// 		}
// 	}
// 	return true;
// }

// static bool complete_var(SemaCtx * ctx, SemaVar * var) {
// 	if (var->pass == SEMA_PASS_AST) {
// 		return false;
// 	}
// 	if (!complete_and_reduce_type(ctx, &var->as.sema.type)) {
// 		return false;
// 	}
// 	if (var->visit_status == VISIT_STATUS_VISITED) {
// 		return true;
// 	}
// 	if (!var->as.sema.init_with_expr) {
// 		var->visit_status = VISIT_STATUS_VISITED;
// 		return true;
// 	}
// 	assert(var->visit_status != VISIT_STATUS_VISITING); // why?
// 														// update, i've realize its because there is duplicate
// 														// for checking cycles in the complete_expr_iter fn
// 														// which could (possibly)? be factored out. TODO: see this
// 	var->visit_status = VISIT_STATUS_VISITING;
// 	u32 visit_index_counter = 1;
// 	u32 last_indirection_index = 0;
// 	var->visit_index = visit_index_counter++;
// 	bool result = complete_expr_iter(ctx, &var->as.sema.unwrap.expr,
// 			visit_index_counter, last_indirection_index);
// 	var->visit_status = VISIT_STATUS_VISITED;
// 	return result;
// }

// static bool complete_decl(SemaCtx * ctx, SemaDecl * decl) {
// 	switch (decl->type) {
// 		case SEMA_DECL_FN:
// 			if (decl->as.fn.pass == SEMA_PASS_AST) {
// 				return false;
// 			}
// 			if (!complete_fn(ctx, &decl->as.fn)) {
// 				return false;
// 			}
// 			break;
// 		case SEMA_DECL_TYPE_ALIAS:
// 			if (!sema_type_alias_is_sema(&decl->as.alias)) {
// 				return false;
// 			}
// 			if (!complete_and_reduce_type(ctx, &decl->as.alias.sema.next)) {
// 				return false;
// 			}
// 			break;
// 		case SEMA_DECL_VAR:
// 			if (!complete_var(ctx, &decl->as.var)) {
// 				return false;
// 			}
// 			break;
// 	}
// 	return true;
// }

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
			return false;
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
	unreachable();
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

//
// static ExprEvalResult typecheck_and_reduce_expr(SemaCtx * ctx, SemaExpr * expr, SemaTypeHandle * result, bool deref);
//
// static ExprEvalResult typecheck_and_reduce_plus_expr(SemaCtx * ctx, SemaExpr * expr, SemaTypeHandle * result_type) {
// 	auto plus = expr->as.plus;
// 	SemaTypeHandle a_type;
// 	SemaTypeHandle b_type;
// 	if (!typecheck_and_reduce_expr(ctx, plus.a, &a_type, true)) {
// 		return EXPR_EVAL_ERROR;
// 	}
// 	if (!typecheck_and_reduce_expr(ctx, plus.b, &b_type, true)) {
// 		return EXPR_EVAL_ERROR;
// 	}
// 	if (!coerce_exprs_binary_arithmetic(ctx, plus.a, a_type, plus.b, b_type, result_type)) {
// 		return EXPR_EVAL_ERROR;
// 	}
// 	if (plus.a->type == SEMA_EXPR1_I32 && plus.b->type == SEMA_EXPR1_I32) {
// 		i32 result;
// 		if (!ckd_add(plus.a->as.i32, plus.b->as.i32, &result)) {
// 			fprintf(stderr, "error: integer overflow\n");
// 			return EXPR_EVAL_ERROR;
// 		}
// 		expr->type = SEMA_EXPR1_I32;
// 		expr->as.i32 = result;
// 		return EXPR_EVAL_REDUCED;
// 	}
// 	return EXPR_EVAL_UNREDUCED;
// }
//
// static ExprEvalResult typecheck_and_reduce_funcall_expr(SemaCtx * ctx, SemaExpr * expr, SemaTypeHandle * result) {
// 	auto funcall = expr->as.funcall;
// 	SemaTypeHandle fn_type;
// 	if (!typecheck_and_reduce_expr(ctx, funcall.fun, &fn_type, true)) {
// 		return EXPR_EVAL_ERROR;
// 	}
// 	if (fn_type.type->type != SEMA_TYPE_FN) {
// 		fprintf(stderr, "tried to call non function\n");
// 		return EXPR_EVAL_ERROR;
// 	}
// 	if (fn_type.type->as.fn.params.count != funcall.args.size) {
// 		fprintf(stderr, "called function with wrong arity %lu %lu\n",
// 				fn_type.type->as.fn.params.count, funcall.args.size);
// 		return EXPR_EVAL_ERROR;
// 	}
// 	auto node = fn_type.type->as.fn.params.begin;
// 	for (usize i = 0; i < funcall.args.size; ++i) {
// 		SemaExpr * expr = &funcall.args.data[i];
// 		if (!typecheck_and_reduce_expr(ctx, expr, result, true)) {
// 			return EXPR_EVAL_ERROR;
// 		}
// 		if (!coerce_expr_to_type(ctx, expr, *result, node->type)) {
// 			return EXPR_EVAL_ERROR;
// 		}
// 		node = node->next;
// 	}
// 	*result = sema_type_handle_from_ptr(fn_type.type->as.fn.return_type);
// 	return EXPR_EVAL_UNREDUCED; // compile time function eval not supported yet
// }
//
// static ExprEvalResult typecheck_and_reduce_var_expr(SemaCtx * ctx, SemaExpr * expr, SemaTypeHandle * result, bool deref) {
// 	auto var = expr->as.var;
// 	assert(var->pass > SEMA_PASS_AST);
// 	*result = var->as.sema.type;
// 	if (!var->as.sema.init_with_expr) {
// 		if (deref) {
// 			sema_expr_init(expr, SEMA_EXPR1_LOAD_VAR, SEMA_PASS_IMPLEMENTED);
// 			expr->as.load_var = var;
// 			return EXPR_EVAL_UNREDUCED;
// 		}
// 		return EXPR_EVAL_REDUCED;
// 	}
// 	SemaTypeHandle ntype;
// 	ExprEvalResult reduction_status = typecheck_and_reduce_expr(ctx, &var->as.sema.unwrap.expr, &ntype, true);
// 	if (!reduction_status) {
// 		return EXPR_EVAL_ERROR;
// 	}
// 	if (ntype.type == nullptr) {
// 		ntype = var->as.sema.type; // This looks unsound but only time this should happen is
// 								   // if the var was already visited and typechecked
// 								   // also should be the only possible case where
// 								   // typecheck_and_reduce_expr can return nullptr
// 	}
// 	if (!coerce_expr_to_type(ctx, &var->as.sema.unwrap.expr, ntype, var->as.sema.type)) {
// 		return EXPR_EVAL_ERROR;
// 	}
// 	if (!deref) {
// 		return EXPR_EVAL_REDUCED;
// 	}
// 	if (sema_ctx_is_global_scope(ctx) || !var->as.sema.type.is_mut) {
// 		*expr = var->as.sema.unwrap.expr;
// 		if (reduction_status == EXPR_EVAL_REDUCED) {
// 			return EXPR_EVAL_REDUCED;
// 		}
// 	}
// 	return EXPR_EVAL_UNREDUCED;
// }
//
// static ExprEvalResult typecheck_and_reduce_addr(SemaCtx * ctx, SemaExpr * expr, SemaTypeHandle * result) {
// 	SemaTypeHandle type;
// 	if (!typecheck_and_reduce_expr(ctx, expr->as.addr, &type, false)) {
// 		return EXPR_EVAL_ERROR;
// 	}
// 	if (!coerce_expr_addr(ctx, type, result)) {
// 		return EXPR_EVAL_ERROR;
// 	}
// 	if (expr->as.addr->type == SEMA_EXPR1_VAR) {
// 		*expr = *expr->as.addr;
// 		return EXPR_EVAL_REDUCED;
// 	}
// 	return EXPR_EVAL_UNREDUCED;
// }
//
//
// static ExprEvalResult typecheck_and_reduce_deref(SemaCtx * ctx, SemaExpr * expr, SemaTypeHandle * result) {
// 	SemaTypeHandle type;
// 	if (!typecheck_and_reduce_expr(ctx, expr->as.deref, &type, true)) {
// 		return EXPR_EVAL_ERROR;
// 	}
// 	if (!coerce_expr_deref(ctx, expr, type, result)) {
// 		return EXPR_EVAL_ERROR;
// 	}
// 	return EXPR_EVAL_UNREDUCED;
// }
//
// static ExprEvalResult typecheck_and_reduce_expr(SemaCtx * ctx, SemaExpr * expr, SemaTypeHandle * result, bool deref) {
// 	if (expr->pass == SEMA_PASS_IMPLEMENTED) {
// 		switch (expr->type) {
// 			case SEMA_EXPR1_I32:
// 				*result = sema_type_handle_from_ptr(&ctx->table->i32_type);
// 				return EXPR_EVAL_REDUCED;
// 			case SEMA_EXPR1_VOID:
// 				*result = sema_type_handle_from_ptr(&ctx->table->void_type);
// 				return EXPR_EVAL_REDUCED;
// 			case SEMA_EXPR1_FN:
// 				*result = sema_type_handle_from_ptr(unsafe_sema_type_from_fn(expr->as.fn->sema.signature));
// 				return EXPR_EVAL_REDUCED;
// 			case SEMA_EXPR1_NULLPTR:
// 				*result = sema_type_handle_from_ptr(&ctx->table->void_ptr_type);
// 				return EXPR_EVAL_REDUCED;
// 			case SEMA_EXPR1_FUNCALL:
// 			case SEMA_EXPR1_VAR:
// 			case SEMA_EXPR1_PLUS:
// 			case SEMA_EXPR1_DEREF:
// 			case SEMA_EXPR1_ADDR:
// 			case SEMA_EXPR1_LOAD_VAR:
// 				*result = null_sema_type_handle;
// 				return EXPR_EVAL_UNREDUCED;
// 		}
// 	}
// 	expr->pass = SEMA_PASS_IMPLEMENTED;
// 	switch (expr->type) {
// 		case SEMA_EXPR1_I32:
// 			*result = sema_type_handle_from_ptr(&ctx->table->i32_type);
// 			return EXPR_EVAL_REDUCED;
// 		case SEMA_EXPR1_VOID:
// 			*result = sema_type_handle_from_ptr(&ctx->table->i32_type);
// 			return EXPR_EVAL_REDUCED;
// 		case SEMA_EXPR1_NULLPTR:
// 			*result = sema_type_handle_from_ptr(&ctx->table->void_ptr_type);
// 			return EXPR_EVAL_REDUCED;
// 		case SEMA_EXPR1_FN:
// 			assert(expr->as.fn->pass > SEMA_PASS_AST);
// 			*result = sema_type_handle_from_ptr(unsafe_sema_type_from_fn(expr->as.fn->sema.signature));
// 			return EXPR_EVAL_REDUCED;
// 		case SEMA_EXPR1_PLUS:
// 			return typecheck_and_reduce_plus_expr(ctx, expr, result);
// 		case SEMA_EXPR1_FUNCALL:
// 			return typecheck_and_reduce_funcall_expr(ctx, expr, result);
// 		case SEMA_EXPR1_VAR:
// 			return typecheck_and_reduce_var_expr(ctx, expr, result, deref);
// 		case SEMA_EXPR1_ADDR:
// 			return typecheck_and_reduce_addr(ctx, expr, result);
// 		case SEMA_EXPR1_DEREF:
// 			return typecheck_and_reduce_deref(ctx, expr, result);
// 		case SEMA_EXPR1_LOAD_VAR:
// 			unreachable(); // this is exclusively generated by the compiler
// 	}
// 	unreachable();
// }
//
// static bool implement_var(SemaCtx * ctx, SemaVar * var) {
// 	// constant evaluation basically
// 	assert(var->pass > SEMA_PASS_AST);
// 	if (!var->as.sema.init_with_expr) {
// 		return true;
// 	}
// 	SemaExpr * expr = &var->as.sema.unwrap.expr;
// 	SemaTypeHandle result;
// 	ExprEvalResult eval_result = typecheck_and_reduce_expr(ctx, expr, &result, true);
// 	if (eval_result == EXPR_EVAL_ERROR) {
// 		return false;
// 	}
// 	assert(result.type && "how did you get here?\n");
// 	if (eval_result == EXPR_EVAL_UNREDUCED && var->global) {
// 		fprintf(stderr, "error: global variable initialized with non-constant expression\n");
// 		return false;
// 	}
// 	if (!coerce_expr_to_type(ctx, expr, result, var->as.sema.type)) {
// 		return false;
// 	}
// 	return true;
// }
//
// static bool implement_stmt_block(SemaCtx * ctx, StmtList block, SemaStmtList * out);
//
// static bool implement_local_decl(SemaCtx * ctx, Decl * ast, SemaDecl * out) {
// 	Str iden;
// 	switch (ast->type) {
// 		case DECL_TYPE_ALIAS:
// 			if (!str_copy(ctx->arena, ast->as.alias.iden, &iden)) {
// 				sema_ctx_oom(ctx);
// 			}
// 			sema_decl_init(out, SEMA_DECL_TYPE_ALIAS, iden);
// 			out->as.alias.pass = SEMA_PASS_AST;
// 			out->as.alias.ast = &ast->as.alias;
// 			return declare_ast_type_alias(ctx, &out->as.alias);
// 		case DECL_FN:
// 			if (!str_copy(ctx->arena, ast->as.fn.iden, &iden)) {
// 				sema_ctx_oom(ctx);
// 			}
// 			sema_decl_init(out, SEMA_DECL_FN, iden);
// 			out->as.fn.pass = SEMA_PASS_AST;
// 			out->as.fn.ast = &ast->as.fn;
// 			return declare_ast_fn(ctx, &out->as.fn);
// 		case DECL_VAR:
// 			if (!str_copy(ctx->arena, ast->as.var.iden, &iden)) {
// 				sema_ctx_oom(ctx);
// 			}
// 			sema_decl_init(out, SEMA_DECL_VAR, iden);
// 			sema_var_init_with_ast(&out->as.var, &ast->as.var, false);
// 			if (!declare_ast_var(ctx, &out->as.var)) {
// 				return false;
// 			}
// 			return implement_var(ctx, &out->as.var);
// 	}
// 	unreachable();
// }
//
// static bool implement_stmt(SemaCtx * ctx, Stmt stmt, SemaStmtList * blk_out) {
// 	SemaEnv * env = ctx->env;
// 	SemaStmt out_stmt;
// 	SemaEnv chld_env;
// 	SemaTypeHandle type;
// 	switch (stmt.type) {
// 	case STMT_SEMICOLON:
// 		return true;
// 	case STMT_RETURN:
// 		sema_stmt_init(&out_stmt, SEMA_STMT_RETURN);
// 		if (stmt.as.return_.has_expr) {
// 			assert(false && "TODO to remove");
// 			// if (!sema_expr_from_ast(ctx, &stmt.as.return_.unwrap.expr, &out_stmt.as.return_)) {
// 			// 	return false;
// 			// }
// 			if (!typecheck_and_reduce_expr(ctx, &out_stmt.as.return_, &type, true)) {
// 				return false;
// 			}
// 			if (!coerce_expr_to_type(ctx, &out_stmt.as.return_, type, 
// 						sema_type_handle_from_ptr(env->as.fn.return_type))) {
// 				return false;
// 			}
// 		} else {
// 			out_stmt.as.return_ = void_expr();
// 		}
// 		break;
// 	case STMT_BLOCK:
// 		sema_env_init_push_fn_blk_env(ctx, &chld_env, env->as.fn.return_type);
// 		if (!implement_stmt_block(ctx, stmt.as.block, &chld_env.as.fn.block)) {
// 			sema_env_pop(ctx);
// 			return false;
// 		}
// 		sema_env_pop(ctx);
// 		sema_stmt_init(&out_stmt, SEMA_STMT_BLOCK);
// 		out_stmt.as.block = chld_env;
// 		break;
// 	case STMT_EXPR:
// 		sema_stmt_init(&out_stmt, SEMA_STMT_EXPR);
// 		assert(false && "TODO to remove");
// 		// if (!sema_expr_from_ast(ctx, &stmt.as.expr, &out_stmt.as.expr)) {
// 		// 	return false;
// 		// }
// 		if (!typecheck_and_reduce_expr(ctx, &out_stmt.as.expr, &type, true)) {
// 			return false;
// 		}
// 		break;
// 	case STMT_DECL:
// 		SemaDecl decl;
// 		if (!implement_local_decl(ctx, stmt.as.decl, &decl)) {
// 			return false;
// 		}
// 		if (!sema_ctx_add_decl(ctx, decl)) {
// 			sema_ctx_oom(ctx);
// 		}
// 		return true;
// 	}
// 	if (!sema_stmt_list_push(ctx->arena, blk_out, out_stmt)) {
// 		sema_ctx_oom(ctx);
// 	}
// 	return true;
// }
//
// static bool implement_stmt_block(SemaCtx * ctx, StmtList block, SemaStmtList * out) {
// 	sema_stmt_list_init(out);
// 	for (auto node = block.begin; node; node = node->next) {
// 		if (!implement_stmt(ctx, node->stmt, out)) {
// 			return false;
// 		}
// 	}
// 	return true;
// }
//
// static bool implement_fn(SemaCtx * ctx, SemaFn * fn) {
// 	SemaEnv env;
// 	sema_env_init_push_fn_blk_env(ctx, &env, fn->sema.signature->return_type);
// 	usize index = 0;
// 	for (auto node = fn->sema.signature->params.begin; node; node = node->next) {
// 		SemaTypeHandle type = node->type;
// 		type.is_lvalue = true;
// 		Str arg = fn->sema.args[index++];
// 		if (str_empty(arg)) {
// 			continue;
// 		}
// 		SemaDecl decl;
// 		decl.type = SEMA_DECL_VAR;
// 		sema_decl_init(&decl, SEMA_DECL_VAR, arg);
// 		sema_var_init(&decl.as.var, type, nullptr, false);
// 		if (!sema_ctx_add_decl(ctx, decl)) {
// 			sema_ctx_oom(ctx);
// 		}
// 	}
// 	bool result = implement_stmt_block(ctx, fn->ast->body, &env.as.fn.block);
// 	sema_env_pop(ctx);
// 	if (!result) {
// 		return false;
// 	}
// 	fn->sema.implemented = true;
// 	fn->sema.unwrap.body = env;
// 	return true;
// }

// static bool implement_decl(SemaCtx * ctx, SemaDecl * decl) {
// 	switch (decl->type) {
// 	case SEMA_DECL_TYPE_ALIAS:
// 		return true;
// 	case SEMA_DECL_FN:
// 		return implement_fn(ctx, &decl->as.fn);
// 	case SEMA_DECL_VAR:
// 		return implement_var(ctx, &decl->as.var);
// 	}
// 	unreachable();
// }

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
	return declare_ast_type_alias(ctx, alias);
}

bool ensure_expr_is_sema(SemaCtx * ctx, SemaExpr * expr) {
	if (expr->pass == SEMA_PASS_ERROR) {
		return false;
	}
	if (expr->pass > SEMA_PASS_AST) {
		return true;
	}
	const Expr * ast = expr->as.ast;
	SemaFn * fn;
	SemaVar * var;
	SemaExpr * a;
	SemaExpr * b;
	SemaExprFunCallArgs args;
	switch (ast->type) {
	case EXPR_POISONED:
		expr->pass = SEMA_PASS_ERROR;
		return false;
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
				expr->pass = SEMA_PASS_ERROR;
				return false;
			}
			sema_expr_init_unimplemented(expr, SEMA_EXPR1_FN);
			expr->as.sema1.fn = fn;
			break;
		}
		var = sema_ctx_lookup_var(ctx, ast->as.iden, DO_REPORT_ERROR);
		if (!var) {
			expr->pass = SEMA_PASS_ERROR;
			return false;
		}
		if (!ensure_var_is_sema(ctx, var)) {
			expr->pass = SEMA_PASS_ERROR;
			return false;
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
			expr->pass = SEMA_PASS_ERROR;
			return false;
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
			expr->pass = SEMA_PASS_ERROR;
			return false;
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
			expr->pass = SEMA_PASS_ERROR;
			return false;
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
				expr->pass = SEMA_PASS_ERROR;
				return false;
			}
			++args.size;
		}
		assert(args.size == ast->as.funcall.args.count);
		sema_expr_init_unimplemented(expr, SEMA_EXPR1_FUNCALL);
		expr->as.sema1.funcall.fun = a;
		expr->as.sema1.funcall.args = args;
		break;
	}
	return true;
}

bool ensure_var_is_sema(SemaCtx * ctx, SemaVar * var) {
	if (var->pass == SEMA_PASS_ERROR) {
		return false;
	}
	if (var->pass > SEMA_PASS_AST) {
		return true;
	}
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
		unreachable();
	case SEMA_PASS_CYCLE_CHECKING:
		if (!(type->visit_index < visitor.last_indirection_id
			&& type->visit_index <= visitor.last_opaque_id)) {
			fprintf(stderr, "error: detected cycle\n");
			type->pass = SEMA_PASS_ERROR;
			return false;
		}
		type->pass = SEMA_PASS_CYCLE_UNCHECKED;
		[[fallthrough]];
	case SEMA_PASS_CYCLE_UNCHECKED:
		type->visit_index = visitor.last_indirection_id++;
		switch (type->type) {
			case SEMA_TYPE_I32:
			case SEMA_TYPE_VOID:
				break;
			case SEMA_TYPE_PTR:
				visitor.last_indirection_id = type->visit_index;
				if (!ensure_type_is_cycle_checked(ctx, visitor, type->as.ptr.type)) {
					type->pass = SEMA_PASS_ERROR;
					return false;
				}
				break;
			case SEMA_TYPE_REF:
				visitor.last_indirection_id = type->visit_index;
				if (!ensure_type_is_cycle_checked(ctx, visitor, type->as.ref.type)) {
					type->pass = SEMA_PASS_ERROR;
					return false;
				}
				break;
			case SEMA_TYPE_TYPE_ALIAS:
				if (!ensure_type_alias_is_cycle_checked(ctx, visitor, type->as.alias)) {
					type->pass = SEMA_PASS_ERROR;
					return false;
				}
				break;
			case SEMA_TYPE_FN:
				if (!ensure_type_is_cycle_checked(ctx, visitor, type->as.fn.return_type)) {
					type->pass = SEMA_PASS_ERROR;
					return false;
				}
				for (auto node = type->as.fn.params.begin; node; node = node->next) {
					if (!ensure_type_is_cycle_checked(ctx, visitor, node->type.type)) {
						type->pass = SEMA_PASS_ERROR;
						return false;
					}
				}
				break;
		}
		type->pass = SEMA_PASS_CYCLE_CHECKED;
		break;
	case SEMA_PASS_CYCLE_CHECKED:
	case SEMA_PASS_IMPLEMENTED:
		break;
	}
	return true;
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
		var->pass = SEMA_PASS_CYCLE_UNCHECKED;
		[[fallthrough]];
	case SEMA_PASS_CYCLE_UNCHECKED:
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

bool ensure_type_handle_is_implemented(SemaCtx * ctx, VisitorState visitor, SemaTypeHandle * out_handle) {
	SemaType * type = out_handle->type;
	if (type->pass == SEMA_PASS_ERROR) {
		return false;
	}
	if (type->pass >= SEMA_PASS_IMPLEMENTED) {
		return true;
	}
	if (!ensure_type_is_cycle_checked(ctx, visitor, out_handle->type)) {
		return false;
	}
	type->pass = SEMA_PASS_IMPLEMENTED;
	switch (type->type) {
	case SEMA_TYPE_I32:
		type->impled.size = 4;
		type->impled.align = 4;
		break;
	case SEMA_TYPE_PTR:
		if (!ensure_type_handle_is_implemented(ctx, visitor, &type->as.ptr)) {
			return false;
		}
		type->impled.size = 8;
		type->impled.align = 8;
		break;
	case SEMA_TYPE_REF:
		if (!ensure_type_handle_is_implemented(ctx, visitor, &type->as.ref)) {
			return false;
		}
		type->impled.size = 8;
		type->impled.align = 8;
		break;
	case SEMA_TYPE_VOID:
		type->impled.size = 0;
		type->impled.align = 0;
		break;
	case SEMA_TYPE_FN:
		if (!ensure_type_ptr_is_implemented(ctx, visitor, &type->as.fn.return_type)) {
			return false;
		}
		for (auto node = type->as.fn.params.begin; node; node = node->next) {
			if (!ensure_type_handle_is_implemented(ctx, visitor, &node->type)) {
				return false;
			}
		}
		break;
	case SEMA_TYPE_TYPE_ALIAS:
		if (!ensure_type_alias_is_implemented(ctx, visitor, type->as.alias)) {
			return false;
		}
		out_handle->type = type->as.alias->sema.next.type;
		out_handle->is_lvalue |= type->as.alias->sema.next.is_lvalue;
		out_handle->is_mut |= type->as.alias->sema.next.is_mut;
		break;
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
	    type = sema_type_handle_from_ptr(&ctx->table->void_ptr_type);
	    result = EXPR_EVAL_REDUCED;
	} break;
	case SEMA_EXPR1_FN:
		if (!ensure_fn_is_implemented(ctx, visitor, expr->as.sema1.fn)) {
			goto error;
		}
		
		{
			SemaFn * fn = expr->as.sema1.fn;
			sema_expr_init_implemented(expr, SEMA_EXPR2_VALUE);
			sema_value_init(&expr->as.sema2.value, SEMA_VALUE_FN);
			expr->as.sema2.value.as.fn = fn;
			type = sema_type_handle_from_ptr(sema_type_from_interned_fn(fn->sema.signature));
			result = EXPR_EVAL_REDUCED;
		}
		break;
	case SEMA_EXPR1_ADDR:
		iresult = _ensure_expr_is_implemented(ctx, visitor, expr->as.sema1.addr, &itype, false);
		if (!iresult) {
			goto error;
		}
		if (!check_type_addr(ctx, itype, &type)) {
			goto error;
		}
		
		{
			SemaExpr * addr = expr->as.sema1.addr;
			*expr = *addr; // correct semantics when vars are pointers
			result = iresult;
		}
		break;
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
	case SEMA_EXPR1_FUNCALL:
		iresult = _ensure_expr_is_implemented(ctx, visitor, expr->as.sema1.funcall.fun, &type, true);
		if (!iresult) {
			goto error;
		}
		for (usize i = 0; i < expr->as.sema1.funcall.args.size; ++i) {
			SemaExpr * arg = &expr->as.sema1.funcall.args.data[i];
			SemaTypeHandle atype;
			ExprEvalResult aresult = _ensure_expr_is_implemented(ctx, visitor, arg, &atype, true);
			if (!aresult) {
				goto error;
			}
			iresult = aresult == EXPR_EVAL_REDUCED ? iresult : EXPR_EVAL_UNREDUCED;
		}
		if (iresult == EXPR_EVAL_REDUCED) {
			// TODO: const fn evaluation
		}
		result = EXPR_EVAL_UNREDUCED;
		break;
	case SEMA_EXPR1_PLUS:
		{
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
			assert(false && "TODO: this needs a proper redesign");
			break;
		}
	case SEMA_EXPR1_VAR:
		{
			SemaVar * var = expr->as.sema1.var;
			iresult = ensure_var_is_implemented(ctx, visitor, var);
			if (!iresult) {
				goto error;
			}
			if (deref) {
				if (!var->as.sema.init_with_expr) {
					if (sema_ctx_is_global_scope(ctx)) {
						fprintf(stderr, "warning: uninitialized global used in constant expression\n");
					}
					goto error;
					sema_expr_init_implemented(expr, SEMA_EXPR2_LOAD_VAR);
					expr->as.sema2.load_var = var;
					result = EXPR_EVAL_UNREDUCED;
					break;
				}
				*expr = var->as.sema.unwrap.expr;
				result = EXPR_EVAL_REDUCED;
				break;
			} else {
				sema_expr_init_implemented(expr, SEMA_EXPR2_VALUE);
				sema_value_init(&expr->as.sema2.value, SEMA_VALUE_VAR_REF);
				expr->as.sema2.value.as.var_ref = var;
				result = EXPR_EVAL_REDUCED;
				break;
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
			if (!coerce_expr_to_type(ctx, &var->as.sema.unwrap.expr, type, var->as.sema.type)) {
				goto error;
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
			sema_decl_init(&decl, SEMA_DECL_TYPE_ALIAS, iden);
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
			sema_decl_init(&decl, SEMA_DECL_FN, iden);
			sema_fn_init_with_ast(&decl.as.fn, &node->decl.as.fn);
			if (!sema_ctx_add_decl(ctx, decl)) {
				sema_ctx_oom(ctx);
			}
			break;
		case DECL_VAR:
			if (!str_copy(ctx->arena, node->decl.as.var.iden, &iden)) {
				sema_ctx_oom(ctx);
			}
			sema_decl_init(&decl, SEMA_DECL_VAR, iden);
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
	type->type = typetype;
	type->pass = SEMA_PASS_CYCLE_UNCHECKED;
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
	var->is_global = global;
	var->pass = SEMA_PASS_AST;
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
}

void sema_fn_init_with_ast(SemaFn * fn, const Fn * ast) {
	fn->pass = SEMA_PASS_AST;
	fn->ast = ast;
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
