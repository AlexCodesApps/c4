#include "include/graph.h"
#include "include/utility.h"

static bool ensure_type_sig_is_cycle_checked(GraphResolverCtx * ctx,
											 TypeSig * sig);

static TypeHandle checked_sig_to_type(GraphResolverCtx * ctx, TypeSig * sig) {
	TypeHandle type;
	assert(sig->pass == TYPE_SIG_PASS_CYCLE_CHECKED);
	switch (sig->kind) {
	case TYPE_SIG_VOID:
		type = type_handle_from_ptr(&ctx->table->void_type);
		break;
	case TYPE_SIG_PTR: {
		Type * _type = type_intern_table_ptr_to(
			ctx->arena, ctx->table, checked_sig_to_type(ctx, sig->as.ptr));
		type = type_handle_from_ptr(_type);
		break;
	}
	case TYPE_SIG_REF: {
		Type * _type = type_intern_table_ref_to(
			ctx->arena, ctx->table, checked_sig_to_type(ctx, sig->as.ref));
		type = type_handle_from_ptr(_type);
		break;
	}
	case TYPE_SIG_ALIAS_STUB: {
		TypeAlias * alias = sig->as.alias_stub;
		if (alias->pass != TYPE_ALIAS_PASS_CHECKED) {
			assert(alias->pass == TYPE_ALIAS_PASS_CHECKING);
			type_alias_set_checked(
				alias, checked_sig_to_type(ctx, &alias->as.checking.parsed));
		}
		type = alias->as.checked;
		break;
	}
	case TYPE_SIG_IDEN:
		UNREACHABLE();
	}
	type.is_mut |= sig->is_mut;
	return type;
}

// does not set to CYCLE_CHECKED!
static bool ensure_type_alias_free_of_cycles(GraphResolverCtx * ctx,
											 TypeAlias * alias) {
	switch (alias->pass) {
	case TYPE_ALIAS_PASS_ERROR:
		return false;
	case TYPE_ALIAS_PASS_PARSED:
		type_alias_set_checking(alias, ctx->visitor.visit_id++);
		if (!ensure_type_sig_is_cycle_checked(ctx,
											  &alias->as.checking.parsed)) {
			type_alias_set_error(alias);
			return false;
		}
		return true;
	case TYPE_ALIAS_PASS_CHECKING:
		if (alias->as.checking.visit_index > ctx->visitor.last_indirection_id ||
			alias->as.checking.visit_index > ctx->visitor.last_opaque_id) {
			TODO("cycle detected");
			type_alias_set_error(alias);
			return false;
		}
		FALLTHROUGH();
	case TYPE_ALIAS_PASS_CHECKED:
		return true;
	}
}

static bool etsicc_iden_helper(GraphResolverCtx * ctx, TypeSig * sig,
							   Iden iden) {
	for (usize i = 0; i < ctx->base->size; ++i) {
		Decl * decl = ast_at(ctx->base, i);
		if (!str_equal(decl->iden, iden)) {
			continue;
		}
		if (decl->kind != DECL_TYPE_ALIAS) {
			TODO();
			return false;
		}
		if (!ensure_type_alias_free_of_cycles(ctx, &decl->as.alias)) {
			return false;
		}
		sig->kind = TYPE_SIG_ALIAS_STUB;
		sig->as.alias_stub = &decl->as.alias;
		return true;
	}
	TODO();
	return false;
}

static bool ensure_type_sig_is_cycle_checked(GraphResolverCtx * ctx,
											 TypeSig * sig) {
	VisitorState * visitor = &ctx->visitor;
	switch (sig->pass) {
	case TYPE_SIG_PASS_ERROR:
		return false;
	case TYPE_SIG_PASS_PARSED:
		switch (sig->kind) {
		case TYPE_SIG_VOID:
			break;
		case TYPE_SIG_PTR: {
			VisitIndex sv = visitor->last_indirection_id;
			visitor->last_indirection_id = visitor->visit_id++;
			bool result = ensure_type_sig_is_cycle_checked(ctx, sig->as.ptr);
			visitor->last_indirection_id = sv;
			if (!result) {
				return false;
			}
			break;
		}
		case TYPE_SIG_REF: {
			VisitIndex sv = visitor->last_indirection_id;
			visitor->last_indirection_id = visitor->visit_id++;
			bool result = ensure_type_sig_is_cycle_checked(ctx, sig->as.ref);
			visitor->last_indirection_id = sv;
			if (!result) {
				return false;
			}
			break;
		}
		case TYPE_SIG_IDEN: {
			if (!etsicc_iden_helper(ctx, sig, sig->as.iden)) {
				return false;
			}
			break;
		}
		case TYPE_SIG_ALIAS_STUB:
			UNREACHABLE();
		}
		sig->pass = TYPE_SIG_PASS_CYCLE_CHECKED;
		FALLTHROUGH();
	case TYPE_SIG_PASS_CYCLE_CHECKED:
		return true;
	}
}

TypeHandle resolve_type_sig_graph(GraphResolverCtx * ctx, TypeSig * sig) {
	if (!ensure_type_sig_is_cycle_checked(ctx, sig)) {
		return type_handle_null();
	}
	return checked_sig_to_type(ctx, sig);
}

bool resolve_type_alias_graph(GraphResolverCtx * ctx, TypeAlias * alias) {
	if (!ensure_type_alias_free_of_cycles(ctx, alias)) {
		return false;
	}
	if (alias->pass == TYPE_ALIAS_PASS_CHECKING) {
		type_alias_set_checked(
			alias, checked_sig_to_type(ctx, &alias->as.checking.parsed));
	}
	return true;
}
