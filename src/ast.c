#include "include/ast.h"

Type type_ptr_from_ast(Type * next) {
	return (Type){
		.pass = TYPE_PASS_PARSED,
		.kind = TYPE_PTR,
		.as.ptr = next,
	};
}

Type type_ref_from_ast(Type * next) {
	return (Type){
		.pass = TYPE_PASS_PARSED,
		.kind = TYPE_REF,
		.as.ref = next,
	};
}

Type type_iden_from_ast(Iden iden) {
	return (Type){
		.pass = TYPE_PASS_PARSED,
		.kind = TYPE_IDEN,
		.as.iden = iden,
	};
}

Type type_error(void) {
	return (Type){
		.pass = TYPE_PASS_ERROR,
	};
}

void type_set_error(Type * type) { type->pass = TYPE_PASS_ERROR; }

bool type_is_error(const Type * type) { return type->pass == TYPE_PASS_ERROR; }

Expr expr_int_from_ast(I128 i) {
	return (Expr){
		.pass = EXPR_PASS_PARSED,
		.kind = EXPR_INTEGER,
		.as.integer = i,
	};
}

Expr expr_plus_from_ast(Expr * a, Expr * b) {
	return (Expr){.pass = EXPR_PASS_PARSED,
				  .kind = EXPR_PLUS,
				  .as.plus = {.a = a, .b = b}};
}

Expr expr_iden_from_ast(Iden iden) {
	return (Expr){.pass = EXPR_PASS_PARSED, .kind = EXPR_IDEN, .as.iden = iden};
}

Expr expr_addr_from_ast(Expr * next) {
	return (Expr){
		.pass = EXPR_PASS_PARSED,
		.kind = EXPR_ADDR,
		.as.addr = next,
	};
}

Expr expr_error(void) {
	return (Expr){
		.pass = EXPR_PASS_ERROR,
	};
}

void expr_set_error(Expr * expr) { expr->pass = EXPR_PASS_ERROR; }

bool expr_is_error(const Expr * expr) { return expr->pass == EXPR_PASS_ERROR; }

Var var_from_ast(SrcSpan span, Type type, bool is_const, bool is_mut,
				 const Expr * opt_expr) {
	Var var;
	var.pass = VAR_PASS_PARSED;
	var.span = span;
	var.is_const = is_const;
	var.is_mut = is_mut;
	var.type = type;
	if (opt_expr) {
		var.has_expr = true;
		var.unwrap.expr = *opt_expr;
	} else {
		var.has_expr = false;
	}
	return var;
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

Decl decl_error(void) {
	return (Decl){
		.kind = DECL_ERROR,
	};
}
void decl_set_error(Decl * decl) { decl->kind = DECL_ERROR; }

bool decl_is_error(const Decl * decl) { return decl->kind == DECL_ERROR; }
