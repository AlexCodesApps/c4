#include "include/ast.h"
#include "include/debug.h"
#include <assert.h>

TypeSig type_sig_ptr_from_ast(TypeSig * next) {
	return (TypeSig){
		.pass = TYPE_SIG_PASS_PARSED,
		.is_mut = false,
		.kind = TYPE_SIG_PTR,
		.as.ptr = next,
	};
}

TypeSig type_sig_ref_from_ast(TypeSig * next) {
	return (TypeSig){
		.pass = TYPE_SIG_PASS_PARSED,
		.is_mut = false,
		.kind = TYPE_SIG_REF,
		.as.ref = next,
	};
}

TypeSig type_sig_fn_from_ast(TypeSig * return_ty, TypeSigList params) {
	return (TypeSig){.pass = TYPE_SIG_PASS_PARSED,
					 .is_mut = false,
					 .kind = TYPE_SIG_FN,
					 .as.fn = {.return_ty = return_ty, .params = params}};
}

TypeSig type_sig_iden_from_ast(Iden iden) {
	return (TypeSig){
		.pass = TYPE_SIG_PASS_PARSED,
		.is_mut = false,
		.kind = TYPE_SIG_IDEN,
		.as.iden = iden,
	};
}

void type_sig_set_mut(TypeSig * type) { type->is_mut = true; }

TypeSig type_sig_void(void) {
	return (TypeSig){
		.pass = TYPE_SIG_PASS_PARSED,
		.kind = TYPE_SIG_VOID,
	};
}

TypeSig type_sig_error(void) {
	return (TypeSig){
		.pass = TYPE_SIG_PASS_ERROR,
	};
}

void type_sig_set_error(TypeSig * type) { type->pass = TYPE_SIG_PASS_ERROR; }

bool type_sig_is_error(const TypeSig * type) {
	return type->pass == TYPE_SIG_PASS_ERROR;
}

Expr expr_int_from_ast(SrcSpan span, I128 i) {
	return (Expr){
		.pass = EXPR_PASS_PARSED,
		.kind = EXPR_INTEGER,
		.span = span,
		.as.integer = i,
	};
}

Expr expr_plus_from_ast(SrcSpan span, Expr * a, Expr * b) {
	return (Expr){
		.pass = EXPR_PASS_PARSED,
		.kind = EXPR_PLUS,
		.span = span,
		.as.plus = {.a = a, .b = b},
	};
}

Expr expr_iden_from_ast(SrcSpan span, Iden iden) {
	return (Expr){
		.pass = EXPR_PASS_PARSED,
		.kind = EXPR_IDEN,
		.span = span,
		.as.iden = iden,
	};
}

Expr expr_addr_from_ast(SrcSpan span, Expr * next) {
	return (Expr){
		.pass = EXPR_PASS_PARSED,
		.kind = EXPR_ADDR,
		.span = span,
		.as.addr = next,
	};
}

Expr expr_funcall_from_ast(SrcSpan span, Expr * fun, ExprList args) {
	return (Expr){
		.pass = EXPR_PASS_PARSED,
		.kind = EXPR_FUNCALL,
		.span = span,
		.as.funcall = {.fun = fun, .args = args},
	};
}

Expr expr_nullptr(SrcSpan span) {
	return (Expr){
		.pass = EXPR_PASS_PARSED,
		.kind = EXPR_NULLPTR,
		.span = span,
	};
}

Expr expr_void(SrcSpan span) {
	return (Expr){
		.pass = EXPR_PASS_PARSED,
		.kind = EXPR_VOID,
		.span = span,
	};
}

Expr expr_error(void) {
	return (Expr){
		.pass = EXPR_PASS_ERROR,
	};
}

void expr_set_error(Expr * expr) { expr->pass = EXPR_PASS_ERROR; }

bool expr_is_error(const Expr * expr) { return expr->pass == EXPR_PASS_ERROR; }

Stmt stmt_semicolon(void) { return (Stmt){.kind = STMT_SEMICOLON}; }

Stmt stmt_decl_from_ast(Decl * decl) {
	return (Stmt){
		.kind = STMT_DECL,
		.as.decl = decl,
	};
}

Stmt stmt_expr_from_ast(Expr expr) {
	return (Stmt){
		.kind = STMT_EXPR,
		.as.expr = expr,
	};
}

Stmt stmt_return_from_ast(Expr expr) {
	return (Stmt){
		.kind = STMT_RETURN,
		.as.return_ = expr,
	};
}

Stmt stmt_block_from_ast(StmtBlock block) {
	return (Stmt){
		.kind = STMT_BLOCK,
		.as.block = block,
	};
}

Fn fn_from_ast(SrcSpan span, bool is_const, ParamList params, TypeSig return_ty,
			   StmtBlock block) {
	return (Fn){
		.span = span,
		.pass = FN_PASS_PARSED,
		.proto =
			{
				.is_const = is_const,
				.return_ty = return_ty,
				.params = params,
			},
		.block = block,
	};
}

bool fn_is_const(const Fn * fn) { return fn->proto.is_const; }

void fn_set_pass_proto_checking(Fn * fn, VisitIndex idx) {
	fn->pass = FN_PASS_PROTO_CHECKING;
	fn->as.checking = idx;
}

void fn_set_pass_proto_checked(Fn * fn) {
	ASSERT(fn->pass == FN_PASS_PROTO_CHECKING);
	fn->pass = FN_PASS_PROTO_CHECKED;
}

void fn_set_pass_proto(Fn * fn, TypeHandle type) {
	ASSERT(fn->pass == FN_PASS_PROTO_CHECKED);
	fn->pass = FN_PASS_PROTO;
	fn->as.proto = type;
}

Fn fn_error(void) {
	return (Fn){
		.pass = FN_PASS_ERROR,
	};
}

void fn_set_error(Fn * fn) { fn->pass = FN_PASS_ERROR; }

bool fn_is_error(const Fn * fn) { return fn->pass == FN_PASS_ERROR; }

Var var_from_ast(SrcSpan span, TypeSig type, bool is_const, bool is_mut,
				 const Expr * opt_expr) {
	Var var;
	var.pass = VAR_PASS_PARSED;
	var.span = span;
	var.as.parsed.is_const = is_const;
	var.as.parsed.is_mut = is_mut;
	var.as.parsed.type = type;
	if (opt_expr) {
		var.as.parsed.has_expr = true;
		var.as.parsed.unwrap.expr = *opt_expr;
	} else {
		var.as.parsed.has_expr = false;
	}
	return var;
}

void var_set_checking(Var * var, VisitIndex index) {
	ASSERT(var->pass == VAR_PASS_PARSED);
	var->pass = VAR_PASS_CHECKING;
	var->as.checking.visit_index = index;
}

void var_set_checked(Var * var) {
	ASSERT(var->pass = VAR_PASS_CHECKING);
	var->pass = VAR_PASS_CHECKED;
}

TypeAlias type_alias_from_ast(SrcSpan span, TypeSig type) {
	return (TypeAlias){
		.span = span,
		.pass = TYPE_ALIAS_PASS_PARSED,
		.as.parsed = type,
	};
}

TypeAlias type_alias_error(void) {
	return (TypeAlias){.pass = TYPE_ALIAS_PASS_ERROR};
}

void type_alias_set_error(TypeAlias * alias) {
	alias->pass = TYPE_ALIAS_PASS_ERROR;
}

void type_alias_set_checking(TypeAlias * alias, VisitIndex visit_index) {
	ASSERT(alias->pass == TYPE_ALIAS_PASS_PARSED);
	alias->pass = TYPE_ALIAS_PASS_CHECKING;
	alias->as.checking.visit_index = visit_index;
}

void type_alias_set_checked(TypeAlias * alias) {
	ASSERT(alias->pass == TYPE_ALIAS_PASS_CHECKING);
	alias->pass = TYPE_ALIAS_PASS_CHECKED;
}

void type_alias_set_evalled(TypeAlias * alias, TypeHandle handle) {
	alias->pass = TYPE_ALIAS_PASS_EVALUATED;
	alias->as.evalled = handle;
}

bool type_alias_is_error(const TypeAlias * alias) {
	return alias->pass == TYPE_ALIAS_PASS_ERROR;
}

Var var_error(void) {
	return (Var){
		.pass = VAR_PASS_ERROR,
	};
}

void var_set_error(Var * var) { var->pass = VAR_PASS_ERROR; }

bool var_is_error(const Var * var) { return var->pass == VAR_PASS_ERROR; }

Decl decl_var_from_ast(Iden iden, Var var) {
	return (Decl){
		.kind = DECL_VAR,
		.iden = iden,
		.as.var = var,
	};
}

Decl decl_alias_from_ast(Iden iden, TypeAlias alias) {
	return (Decl){.kind = DECL_TYPE_ALIAS, .iden = iden, .as.alias = alias};
}

Decl decl_fn_from_ast(Iden iden, Fn fn) {
	return (Decl){.kind = DECL_FN, .iden = iden, .as.fn = fn};
}

Decl decl_error(void) {
	return (Decl){
		.kind = DECL_ERROR,
	};
}
void decl_set_error(Decl * decl) { decl->kind = DECL_ERROR; }

bool decl_is_error(const Decl * decl) { return decl->kind == DECL_ERROR; }
