#include "include/nlexer.h"
#include "include/checked_math.h"
#include "include/assert.h"
#include "include/utility.h"

NLexer nlexer_new(Str src) {
	return (NLexer) {
		.src = src,
		.pos = {
			.index = 0,
			.row = 1,
			.col = 1,
		}	
	};
}

bool nlexer_eof(const NLexer lexer[ref]) {
	return lexer->pos.index >= lexer->src.size;
}

struct _str_ttype_pair {
    Str str;
    TokenType ttype;
};

static const struct _str_ttype_pair keywords[] = {
    {s("fn"), TOKEN_TYPE_FN},         {s("as"), TOKEN_TYPE_AS},
    {s("let"), TOKEN_TYPE_LET},       {s("const"), TOKEN_TYPE_CONST},
    {s("return"), TOKEN_TYPE_RETURN}, {s("mod"), TOKEN_TYPE_MOD},
    {s("pub"), TOKEN_TYPE_PUB},       {s("struct"), TOKEN_TYPE_STRUCT},
};

static const struct _str_ttype_pair operators[] = {
    /* If ordering isn't done right, some operators can override others
     */
    {s(";"), TOKEN_TYPE_SEMICOLON}, {s(".*"), TOKEN_TYPE_DOTSTAR},
    {s("("), TOKEN_TYPE_LPAREN},    {s(")"), TOKEN_TYPE_RPAREN},
    {s(","), TOKEN_TYPE_COMMA},     {s("::"), TOKEN_TYPE_SCOPE},
    {s(":"), TOKEN_TYPE_COLON},     {s("{"), TOKEN_TYPE_LBRACE},
    {s("}"), TOKEN_TYPE_RBRACE},    {s("."), TOKEN_TYPE_DOT},
    {s("*"), TOKEN_TYPE_STAR},      {s("+"), TOKEN_TYPE_PLUS},
    {s("-"), TOKEN_TYPE_MINUS},     {s("="), TOKEN_TYPE_EQ},
    {s("&"), TOKEN_TYPE_AMPERSAND},
};

static char peek(NLexer * lexer) {
	if (nlexer_eof(lexer)) {
		return '\0';
	}
	return *span_at(&lexer->src, lexer->pos.index);
}

static char peek_by(NLexer * lexer, usize offset) {
	usize index;
	if (!ckd_add(lexer->pos.index, offset, &index)) {
		ASSERT(false, "overflow in lexer");
		return '\0';
	}	
	if (index >= lexer->src.size) {
		return '\0';
	}
	return *span_at(&lexer->src, index);
}

static void advance_to_nl(NLexer * lexer) {
	for (;;) {
		char c = peek(lexer);
		if (c == '\0') {
			return;	
		}
		++lexer->pos.index;
		if (c == '\n') {
			lexer->pos.col = 1;
			++lexer->pos.row;
			return;
		}
	}
}

static void skip_ws(NLexer * lexer) {
	for (;;) {
		switch (peek(lexer)) {
		case '\n':
			lexer->pos.col = 1;
			++lexer->pos.row;
		case ' ':
		case '\t':
		case '\r':
			++lexer->pos.index;	
			continue;
		case '/':
			if (peek_by(lexer, 1) != '/') {
				return;
			}
			lexer->pos.index += 2;
			advance_to_nl(lexer);
			break;
		default:
			return;
		}
	}
}

static SrcPos get_pos(NLexer * lexer) {
	return lexer->pos;
}

static usize get_index(NLexer * lexer) {
	return lexer->pos.index;
}

usize nlexer_index(const NLexer lexer[ref]) {
	return lexer->pos.index;
}

static void advance(NLexer lexer[ref], usize count) {
	while (count--) {
		char c = peek(lexer);
		if (c == '\0') {
			return;
		}
		if (c == '\n') {
			lexer->pos.col = 1;
			++lexer->pos.row;
		}
		++lexer->pos.index;
	}
}

static bool lexer_begins_with(const NLexer * lexer, Str str) {
	if (lexer->src.size - lexer->pos.index < str.size) {
		return false;
	}
	const char * current = lexer->src.data + lexer->pos.index;
	return memcmp(current, str.data, str.size) == 0;
}

static NLexerTokenResult tok_res_ok(Token token) {
	return (NLexerTokenResult) {
		.ok = true,
		.as.token = token,
	};
}

static NLexerError lex_err_new(SrcPos pos, char unexpected_char) {
	return (NLexerError){
		.pos = pos,
		.unexpected_char = unexpected_char,
	};
}

static NLexerTokenResult tok_res_error(NLexerError error) {
	return (NLexerTokenResult) {
		.ok = false,
		.as.error = error,
	};
}

NLexerTokenResult nlexer_next(NLexer lexer[ref]) {
	skip_ws(lexer);
	if (nlexer_eof(lexer)) {
		SrcSpan span = src_span_new(get_pos(lexer), 0);
		Token tok = token_new(span, TOKEN_TYPE_EOF);
		return tok_res_ok(tok);
	}
	for (usize i  = 0; i < ARRAY_SIZE(operators); ++i) {
		const struct _str_ttype_pair * pair = &operators[i];
		if (lexer_begins_with(lexer, pair->str)) {
			SrcSpan span = src_span_new(get_pos(lexer), pair->str.size); 
			advance(lexer, pair->str.size);
			TokenType ttype = pair->ttype;
			return tok_res_ok(token_new(span, ttype));
		}
	}
	char c = peek(lexer);
	if (char_is_alpha(c)) {
		SrcPos pos = get_pos(lexer);
		++lexer->pos.index;
		usize size = 1;	
		while (char_is_alnum(peek(lexer))) {
			++lexer->pos.index;
			++size;
		}
		SrcSpan span = src_span_new(pos, size);
		Str iden = str_slice(lexer->src, pos.index, size);
		for (usize i = 0; i < ARRAY_SIZE(keywords); ++i) {
			const struct _str_ttype_pair * pair = &keywords[i];
			if (str_eq(iden, pair->str)) {
				return tok_res_ok(token_new(span, pair->ttype));	
			}
		}
		return tok_res_ok(token_new(span, TOKEN_TYPE_IDENTIFIER));
	}
	if (char_is_digit(c)) {
		SrcPos pos = get_pos(lexer);
		++lexer->pos.index;
		usize size = 1;
		while (char_is_digit(c = peek(lexer))) {
			++lexer->pos.index;
			++size;
		}	
		if (char_is_alpha(c)) {
			return tok_res_error(lex_err_new(get_pos(lexer), c));
		}
		SrcSpan span = src_span_new(pos, size);
		return tok_res_ok(token_new(span, TOKEN_TYPE_INTEGER));
	}
	NLexerError error = lex_err_new(get_pos(lexer), c);
	++lexer->pos.index;
	return tok_res_error(error);	
}

