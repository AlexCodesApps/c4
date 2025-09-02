#include <stdio.h>
#include <inttypes.h>
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
			case TOKEN_STAR:
				dump_token(&lexer, &token, s("*")); break;
			case TOKEN_AMPERSAND:
				dump_token(&lexer, &token, s("&")); break;
			case TOKEN_CONST:
				dump_token(&lexer, &token, s("CONST")); break;
			case TOKEN_FN:
				dump_token(&lexer, &token, s("FN")); break;
			case TOKEN_LET:
				dump_token(&lexer, &token, s("LET")); break;
			case TOKEN_MUT:
				dump_token(&lexer, &token, s("MUT")); break;
			case TOKEN_NULLPTR:
				dump_token(&lexer, &token, s("NULLPTR")); break;
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
