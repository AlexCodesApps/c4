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

Type type_error() {
	return (Type){
		.pass = TYPE_PASS_ERROR,
	};
}

void type_set_error(Type * type) { type->pass = TYPE_PASS_ERROR; }

bool type_is_error(const Type * type) { return type->pass == TYPE_PASS_ERROR; }

Var var_from_ast(SrcSpan span, Type type, bool is_const, bool is_mut) {
	return (Var){
		.pass = VAR_PASS_PARSED,
		.span = span,
		.is_const = is_const,
		.is_mut = is_mut,
		.type = type,
	};
}

Var var_error() {
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

Decl decl_error() {
	return (Decl){
		.kind = DECL_ERROR,
	};
}
void decl_set_error(Decl * decl) { decl->kind = DECL_ERROR; }

bool decl_is_error(const Decl * decl) { return decl->kind == DECL_ERROR; }
