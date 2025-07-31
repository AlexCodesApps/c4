#include "include/asm.h"

void lower_fns(FILE * file, const SemaDecl * decl) {
	switch (decl->type) {
	case SEMA_DECL_TYPE_ALIAS:
	case SEMA_DECL_VAR:
		return;
	case SEMA_DECL_FN:
		fprintf(file, "global %.*s\n", (int)decl->iden.size, decl->iden.data);
		break;
	}
}

void lower_vars(FILE * file, const SemaDecl * decl) {
	switch (decl->type) {
	case SEMA_DECL_TYPE_ALIAS:
	case SEMA_DECL_FN:
		return;
	case SEMA_DECL_VAR:
		if (decl->as.var.sema.type->type != SEMA_TYPE_I32) {
			return;
		}
		if (decl->as.var.sema.init_with_expr) {
			fprintf(file, "%.*s dw: %d\n", (int)decl->iden.size, decl->iden.data, decl->as.var.sema.unwrap.expr.as.i32);
		} else {
			fprintf(file, "%.*s dw: 0\n", (int)decl->iden.size, decl->iden.data);
		}
	}
}

void lower_to_asm(FILE * file, SemaDeclList list) {
	for (auto node = list.begin; node; node = node->next) {
		lower_fns(file, &node->decl);
	}
	fprintf(file, "section .data\n");
	for (auto node = list.begin; node; node = node->next) {
		lower_vars(file, &node->decl);
	}
	fprintf(file, "section .text\n");
}
