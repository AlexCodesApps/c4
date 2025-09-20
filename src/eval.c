#include "include/eval.h"
#include "include/graph.h"
#include "include/utility.h"

bool eval_type(SemaCtx * ctx, Type * type) {
	(void)ctx; // will be needed when types can contain constant expressions
	switch (type->pass) {
	case TYPE_PASS_ERROR:
		return false;
	case TYPE_PASS_CHECKED:
		switch (type->kind) {
		case TYPE_BUILTIN_VOID:
			type->evaluated.size = 0;
			type->evaluated.align = 0;
			break;
		case TYPE_BUILTIN_I32:
			type->evaluated.size = 4;
			type->evaluated.align = 4;
			break;
		case TYPE_PTR:
			if (!eval_type(ctx, type->as.ptr.type)) {
				type->pass = TYPE_PASS_ERROR;
				return false;
			}
			type->evaluated.size = 8;
			type->evaluated.align = 8;
			break;
		case TYPE_REF:
			if (!eval_type(ctx, type->as.ref.type)) {
				type->pass = TYPE_PASS_ERROR;
				return false;
			}
			type->evaluated.size = 8;
			type->evaluated.align = 8;
			break;
		}
		type->pass = TYPE_PASS_EVALUATED;
		FALLTHROUGH();
	case TYPE_PASS_EVALUATED:
		return true;
	}
}

bool eval_type_alias(SemaCtx * ctx, TypeAlias * alias) {
	switch (alias->pass) {
	case TYPE_ALIAS_PASS_ERROR:
		return false;
	case TYPE_ALIAS_PASS_PARSED:
	case TYPE_ALIAS_PASS_CHECKING:
		if (!resolve_type_alias_graph(ctx, alias)) {
			return false;
		}
		FALLTHROUGH();
	case TYPE_ALIAS_PASS_CHECKED:
		if (!eval_type(ctx, alias->as.checked.type)) {
			type_alias_set_error(alias);
			return false;
		}
		alias->pass = TYPE_ALIAS_PASS_EVALUATED;
		FALLTHROUGH();
	case TYPE_ALIAS_PASS_EVALUATED:
		return true;
	}
}

bool eval_var(SemaCtx * ctx, Var * var) {
	switch (var->pass) {
	case VAR_PASS_ERROR:
		return false;
	case VAR_PASS_PARSED:
	case VAR_PASS_CHECKING:
		if (!resolve_var_graph(ctx, var)) {
			return false;
		}
		FALLTHROUGH();
	case VAR_PASS_CHECKED:
		TODO();
	case VAR_PASS_EVALUATED:
		return true;
	}
}

bool eval_fn(SemaCtx * ctx, Fn * fn) { TODO(); }
