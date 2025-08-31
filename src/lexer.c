#include "include/lexer.h"
#include <assert.h>

Lexer lexer_new(Str src) {
	Lexer lexer;
	lexer.src = src;
	lexer.index = 0;
	lexer.row = 0;
	lexer.col = 1;
	return lexer;
}

usize lexer_row(const Lexer * lexer) {
	return lexer->row;
}

usize lexer_col(const Lexer * lexer) {
	return lexer->col;
}

bool lexer_eof(const Lexer * lexer) {
	return lexer->index >= lexer->src.size;
}

Str lexer_token_str(const Lexer * lexer, const Token * token) {
	return str_new(lexer->src.data + token->start, token->end - token->start);
}

static char peek(Lexer * lexer) {
	if (lexer_eof(lexer)) {
		return '\0';
	}
	return lexer->src.data[lexer->index];
}

static char peek1(Lexer * lexer) {
	if (lexer->index + 1 >= lexer->src.size) {
		return '\0';
	}
	return lexer->src.data[lexer->index + 1];
}

static void advance(Lexer * lexer) {
	++lexer->index;
	++lexer->col;
}

static void advance2(Lexer * lexer) {
	lexer->index += 2;
	lexer->col += 2;
}

static char skip_ws(Lexer * lexer) {
	for (;;) {
		char c = peek(lexer);
		switch (c) {
			case '\n':
				lexer->col = 1;
				++lexer->row;
				[[fallthrough]];
			case ' ':
			case '\t':
			case '\r':
				advance(lexer);
				break;
			case '/':
				if (peek1(lexer) == '/') {
					advance2(lexer);
					while ((c = peek(lexer)) != '\0' && c != '\n') {
						advance(lexer);
					}
					break;
				}
				[[fallthrough]];
			default:
				return c;
		}
	}
}

static TokenIndex begin_token(Lexer * lexer) {
	assert(lexer->index <= TOKEN_INDEX_MAX);
	return (TokenIndex)lexer->index;
}

static Token make_token(Lexer * lexer, TokenIndex start, TokenType type) {
	Token token;
	token.type = type;
	token.start = start;
	assert(lexer->index <= TOKEN_INDEX_MAX);
	token.end = (TokenIndex)lexer->index;
	return token;
}

static inline bool is_digit(char c) {
	return '0' <= c && c <= '9';
}

static inline bool is_alpha(char c) {
	return ('a' <= c && c <= 'z')
		|| ('A' <= c && c <= 'Z');
}

static inline bool is_alnum(char c) {
	return is_digit(c) || is_alpha(c);
}

static inline bool is_start_of_iden(char c) {
	return c == '_'|| is_alnum(c);
}

static Token make_number(Lexer * lexer, TokenIndex start) {
	do {
		advance(lexer);
	} while (is_digit(peek(lexer)));
	return make_token(lexer, start, TOKEN_INT);
}

static Str span_lexer(Lexer * lexer, TokenIndex start) {
	return str_new(lexer->src.data + start, lexer->index - start);
}

static Token make_iden(Lexer * lexer, TokenIndex start) {
	do {
		advance(lexer);
	} while(is_alnum(peek(lexer)) || peek(lexer) == '_');
	Str iden = span_lexer(lexer, start);
	if (str_equal(iden, s("const"))) {
		return make_token(lexer, start, TOKEN_CONST);
	}
	if (str_equal(iden, s("fn"))) {
		return make_token(lexer, start, TOKEN_FN);
	}
	if (str_equal(iden, s("let"))) {
		return make_token(lexer, start, TOKEN_LET);
	}
	if (str_equal(iden, s("mut"))) {
		return make_token(lexer, start, TOKEN_MUT);
	}
	if (str_equal(iden, s("nullptr"))) {
		return make_token(lexer, start, TOKEN_NULLPTR);
	}
	if (str_equal(iden, s("return"))) {
		return make_token(lexer, start, TOKEN_RETURN);
	}
	if (str_equal(iden, s("type"))) {
		return make_token(lexer, start, TOKEN_TYPE);
	}
	if (str_equal(iden, s("void"))) {
		return make_token(lexer, start, TOKEN_VOID);
	}
	return make_token(lexer, start, TOKEN_IDEN);
}

Token lexer_next(Lexer * lexer) {
	char c = skip_ws(lexer);
	TokenIndex start = begin_token(lexer);
	switch (c) {
	case '\0':
		return make_token(lexer, start, TOKEN_EOF);
	case '(':
		advance(lexer);
		return make_token(lexer, start, TOKEN_LPAREN);
	case ')':
		advance(lexer);
		return make_token(lexer, start, TOKEN_RPAREN);
	case '{':
		advance(lexer);
		return make_token(lexer, start, TOKEN_LBRACE);
	case '}':
		advance(lexer);
		return make_token(lexer, start, TOKEN_RBRACE);
	case ':':
		advance(lexer);
		return make_token(lexer, start, TOKEN_COLON);
	case ';':
		advance(lexer);
		return make_token(lexer, start, TOKEN_SEMICOLON);
	case '+':
		advance(lexer);
		return make_token(lexer, start, TOKEN_PLUS);
	case ',':
		advance(lexer);
		return make_token(lexer, start, TOKEN_COMMA);
	case '=':
		advance(lexer);
		return make_token(lexer, start, TOKEN_EQ);
	case '*':
		advance(lexer);
		return make_token(lexer, start, TOKEN_STAR);
	case '&':
		advance(lexer);
		return make_token(lexer, start, TOKEN_AMPERSAND);
	default:
		if (is_digit(c)) {
			return make_number(lexer, start);
		}
		if (is_start_of_iden(c)) {
			return make_iden(lexer, start);
		}
	}
	advance(lexer);
	return make_token(lexer, start, TOKEN_ERR);
}
