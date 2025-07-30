#include <stdio.h>
#include <inttypes.h>
#include "include/ast.h"
#include "include/lexer.h"

static void dump_token(const Lexer * lexer, const Token * token, Str token_type) {
	Str str = lexer_token_str(lexer, token);
	fprintf(stderr, "  %.*s '%.*s'\n",
			(int)token_type.size, token_type.data,
			(int)str.size, str.data);
}

void dump_tokens(Str src) {
	Lexer lexer = lexer_new(src);
	Token token;
	fputs("== TOKENS ==\n", stderr);
	do {
		token = lexer_next(&lexer);
		switch (token.type) {
			case TOKEN_LPAREN:
				dump_token(&lexer, &token, s("LPAREN")); break;
			case TOKEN_RPAREN:
				dump_token(&lexer, &token, s("RPAREN")); break;
			case TOKEN_LBRACE:
				dump_token(&lexer, &token, s("LBRACE")); break;
			case TOKEN_RBRACE:
				dump_token(&lexer, &token, s("RBRACE")); break;
			case TOKEN_COLON:
				dump_token(&lexer, &token, s("COLON")); break;
			case TOKEN_SEMICOLON:
				dump_token(&lexer, &token, s("SEMICOLON")); break;
			case TOKEN_PLUS:
				dump_token(&lexer, &token, s("PLUS")); break;
			case TOKEN_COMMA:
				dump_token(&lexer, &token, s("COMMA")); break;
			case TOKEN_EQ:
				dump_token(&lexer, &token, s("EQ")); break;
			case TOKEN_FN:
				dump_token(&lexer, &token, s("FN")); break;
			case TOKEN_LET:
				dump_token(&lexer, &token, s("LET")); break;
			case TOKEN_RETURN:
				dump_token(&lexer, &token, s("RETURN")); break;

			case TOKEN_TYPE:
				dump_token(&lexer, &token, s("TYPE")); break;
			case TOKEN_VOID:
				dump_token(&lexer, &token, s("VOID")); break;
			case TOKEN_IDEN:
				dump_token(&lexer, &token, s("IDEN")); break;
			case TOKEN_INT:
				dump_token(&lexer, &token, s("INT")); break;
			case TOKEN_EOF:
				dump_token(&lexer, &token, s("EOF")); break;
			case TOKEN_ERR:
				dump_token(&lexer, &token, s("ERR")); break;
		}
	} while (token.type != TOKEN_EOF);
}

static void pad_indent(u32 indent) {
	for (u32 i = 0; i < indent; ++i) {
		fputc(' ', stderr);
	}
}

static void dump_type(u32 indent, const Type * type) {
	pad_indent(indent);
	switch (type->type) {
	case TYPE_VOID:
		fputs("void\n", stderr);
		break;
	case TYPE_IDEN:
		fprintf(stderr, "iden %.*s\n", (int)type->as.iden.size, type->as.iden.data);
		break;
	case TYPE_FN:
		fprintf(stderr, "fn\n");
		pad_indent(indent + 1);
		fprintf(stderr, "parameters\n");
		for (auto node = type->as.fn.params.begin; node; node = node->next) {
			dump_type(indent + 2, &node->type);
		}
		pad_indent(indent + 1);
		fprintf(stderr, "returning\n");
		dump_type(indent + 2, type->as.fn.return_type);
	}
}

static void dump_expr(u32 indent, const Expr * expr) {
	pad_indent(indent);
	if (expr == &poisoned_expr) {
		fputs("<poisoned>\n", stderr);
		return;
	}
	switch (expr->type) {
		case EXPR_INT:
			fprintf(stderr, "%"PRIu64"\n", expr->as.int_);
			break;
		case EXPR_IDEN:
			fprintf(stderr, "iden %.*s\n", (int)expr->as.iden.size, expr->as.iden.data);
			break;
		case EXPR_FUNCALL:
			fputs("call\n", stderr);
			dump_expr(indent + 1, expr->as.funcall.fun);
			pad_indent(indent + 1);
			fputs("parameters\n", stderr);
			for (ExprNode * node = expr->as.funcall.args.begin; 
				node;
				node = node->next) {
				dump_expr(indent + 2, node->expr);
			}
			break;
		case EXPR_PLUS:
			fputs("+\n", stderr);
			dump_expr(indent + 1, expr->as.plus.a);
			dump_expr(indent + 1, expr->as.plus.b);
			break;
	}
}

static void dump_stmt(u32 indent, Stmt stmt) {
	switch (stmt.type) {
		case STMT_SEMICOLON:
			pad_indent(indent);
			fputs(";\n", stderr);
			break;
		case STMT_RETURN:
			pad_indent(indent);
			fputs("return\n", stderr);
			if (stmt.as.return_.has_expr) {
				dump_expr(indent + 1, stmt.as.return_.unwrap.expr);
			}
			break;
		case STMT_EXPR:
			pad_indent(indent);
			fputs("expr\n", stderr);
			dump_expr(indent + 1, stmt.as.expr);
			break;
		case STMT_BLOCK:
			pad_indent(indent);
			fprintf(stderr, "block\n");
			for (auto node = stmt.as.block.begin; node; node = node->next) {
				dump_stmt(indent + 1, node->stmt);
			}
			break;
	}
}

static void dump_fn(u32 indent, const Fn * fn) {
	pad_indent(indent);
	fprintf(stderr, "fn %.*s\n", (int)fn->iden.size, fn->iden.data);
	pad_indent(indent + 1);
	fprintf(stderr, "signature\n");
	if (fn->params != &poisoned_fn_param_list) {
		for (FnParamNode * node = fn->params->begin; node; node = node->next) {
			if (node->param.has_iden) {
				pad_indent(indent + 2);
				fprintf(stderr, "%.*s\n",
						(int)node->param.unwrap.iden.size, 
						node->param.unwrap.iden.data);
			}
			dump_type(indent + 3, &node->param.type);
		}
	} else {
		pad_indent(indent + 2);
		fprintf(stderr, "<poisoned>\n");
	}
	pad_indent(indent + 1);
	fprintf(stderr, "returning\n");
	dump_type(indent + 2, &fn->return_type);

	pad_indent(indent + 1);
	fprintf(stderr, "body\n");
	for (StmtNode * node = fn->body.begin; node; node = node->next) {
		dump_stmt(indent + 2, node->stmt);
	}
}

static void dump_var(u32 indent, const Var * var) {
	pad_indent(indent);
	fprintf(stderr, "var %.*s\n", (int)var->iden.size, var->iden.data);
	dump_type(indent + 1, &var->type);
	if (var->init_with_expr) {
		dump_expr(indent + 1, var->unwrap.expr);
	}
}

void dump_ast(Ast ast) {
	fprintf(stderr, "== AST ==\n");
	for (DeclNode * node = ast.begin; node; node = node->next) {
		switch (node->decl.type) {
			case DECL_POISONED:
				fprintf(stderr, "<poisoned>\n");
				break;
			case DECL_FN:
				dump_fn(0, &node->decl.as.fn);
				break;
			case DECL_TYPE_ALIAS:
				fprintf(stderr, "type %.*s\n", (int)node->decl.as.alias.iden.size,
											 node->decl.as.alias.iden.data);
				dump_type(1, &node->decl.as.alias.type);
				break;
			case DECL_VAR:
				dump_var(0, &node->decl.as.var);
		}
	}
}
