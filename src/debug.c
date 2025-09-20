#include "include/debug.h"
#include "include/fmt.h"
#include "include/lexer.h"
#include "include/utility.h"
#include <inttypes.h>
#include <stdarg.h>

void va_debug(DebugLevel level, const char * filename, const char * function,
			  word line, const char * msg, va_list va) {
	const char * prefix[DEBUG_LEVEL_COUNT] = {
		[DEBUG_LOG] = "\x1b[33mLOG",
		[DEBUG_ERROR] = "\x1b[31mERROR",
	};
	c4printf(stderr, "%cs: in %cs[%uw, %cs]: ", prefix[level], filename, line,
			 function);
	c4vaprintf(stderr, msg, va);
	c4println(stderr, "\x1b[0m");
}

void debug(DebugLevel level, const char * filename, const char * function,
		   word line, const char * msg, ...) {
	va_list va;
	va_start(va, msg);
	va_debug(level, filename, function, line, msg, va);
	va_end(va);
}

void fail(const char * filename, const char * function, word line,
		  const char * msg, ...) {
	va_list va;
	va_start(va, msg);
	va_debug(DEBUG_ERROR, filename, function, line, msg, va);
	va_end(va);
	crash();
}

static void dump_token(const Lexer * lexer, const Token * token,
					   Str token_type) {
	Str str = lexer_token_str(lexer, token);
	c4printf(stderr, "%s '%s'\n", token_type, str);
}

void dump_tokens(Str src) {
	Lexer lexer = lexer_new(src);
	Token token;
	c4println(stderr, "== TOKENS ==\n");
	do {
		token = lexer_next(&lexer);
		switch (token.kind) {
		case TOKEN_LPAREN:
			dump_token(&lexer, &token, s("LPAREN"));
			break;
		case TOKEN_RPAREN:
			dump_token(&lexer, &token, s("RPAREN"));
			break;
		case TOKEN_LBRACE:
			dump_token(&lexer, &token, s("LBRACE"));
			break;
		case TOKEN_RBRACE:
			dump_token(&lexer, &token, s("RBRACE"));
			break;
		case TOKEN_COLON:
			dump_token(&lexer, &token, s("COLON"));
			break;
		case TOKEN_SEMICOLON:
			dump_token(&lexer, &token, s("SEMICOLON"));
			break;
		case TOKEN_PLUS:
			dump_token(&lexer, &token, s("PLUS"));
			break;
		case TOKEN_COMMA:
			dump_token(&lexer, &token, s("COMMA"));
			break;
		case TOKEN_EQ:
			dump_token(&lexer, &token, s("EQ"));
			break;
		case TOKEN_STAR:
			dump_token(&lexer, &token, s("*"));
			break;
		case TOKEN_AMPERSAND:
			dump_token(&lexer, &token, s("&"));
			break;
		case TOKEN_CONST:
			dump_token(&lexer, &token, s("CONST"));
			break;
		case TOKEN_FN:
			dump_token(&lexer, &token, s("FN"));
			break;
		case TOKEN_LET:
			dump_token(&lexer, &token, s("LET"));
			break;
		case TOKEN_MUT:
			dump_token(&lexer, &token, s("MUT"));
			break;
		case TOKEN_NULLPTR:
			dump_token(&lexer, &token, s("NULLPTR"));
			break;
		case TOKEN_RETURN:
			dump_token(&lexer, &token, s("RETURN"));
			break;
		case TOKEN_TYPE_:
			dump_token(&lexer, &token, s("TYPE"));
			break;
		case TOKEN_VOID:
			dump_token(&lexer, &token, s("VOID"));
			break;
		case TOKEN_IDEN:
			dump_token(&lexer, &token, s("IDEN"));
			break;
		case TOKEN_INT:
			dump_token(&lexer, &token, s("INT"));
			break;
		case TOKEN_EOF:
			dump_token(&lexer, &token, s("EOF"));
			break;
		case TOKEN_ERR:
			dump_token(&lexer, &token, s("ERR"));
			break;
		}
	} while (token.kind != TOKEN_EOF);
}
