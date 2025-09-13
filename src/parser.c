#include "include/parser.h"
#include "include/utility.h"
#include <setjmp.h>
#include <stdbit.h>

typedef struct {
	Token token1;
	Token token2;
	Lexer lexer;
	usize row1, col1;
	usize row2, col2;
	VMemArena * arena;
	jmp_buf oom_handler;
	jmp_buf overflow_handler;
	Str path;
	bool had_error;
	bool panic_mode;
} Parser;

static Token next_valid_token(Parser * parser, usize * row, usize * col) {
	for (;;) {
		usize _row = lexer_row(&parser->lexer);
		usize _col = lexer_col(&parser->lexer);
		Token token = lexer_next(&parser->lexer);
		if (token.kind == TOKEN_ERR) {
			parser->had_error = true;
			fprintf(stderr, "in %.*s[%lu, %lu]: unexpected character '%c'\n",
					(int)parser->path.size, parser->path.data, _row, _col,
					*lexer_token_str(&parser->lexer, &token).data);
			continue;
		}
		*row = _row;
		*col = _col;
		return token;
	}
}

static bool eof(Parser * parser) { return parser->token1.kind == TOKEN_EOF; }

static Token * peek(Parser * parser) { return &parser->token1; }

static TokenKind peek_kind(Parser * parser) { return peek(parser)->kind; }

static void advance(Parser * parser) {
	parser->token1 = parser->token2;
	parser->row1 = parser->row2;
	parser->col1 = parser->col2;
	parser->token2 = next_valid_token(parser, &parser->row2, &parser->col2);
}

static bool match(Parser * parser, TokenKind type) {
	if (peek(parser)->kind == type) {
		advance(parser);
		return true;
	}
	return false;
}

static void expected_error(Parser * parser, const char * msg) {
	Token * token = peek(parser);
	parser->panic_mode = true;
	parser->had_error = true;
	Str src = lexer_token_str(&parser->lexer, token);
	fprintf(stderr, "in %.*s[%lu, %lu]: %s, found '%.*s'\n",
			(int)parser->path.size, parser->path.data, parser->row1,
			parser->col1, msg, (int)src.size, src.data);
}

static bool expect(Parser * parser, TokenKind type, const char * msg) {
	if (match(parser, type)) {
		return true;
	}
	expected_error(parser, msg);
	return false;
}

static TokenIndex src_span_begin(Parser * parser) {
	if (UNLIKELY(parser->lexer.index > TOKEN_INDEX_MAX)) {
		longjmp(parser->overflow_handler, 1);
	}
	return (TokenIndex)parser->lexer.index;
}

static SrcSpan src_span_end(Parser * parser, TokenIndex index) {
	return (SrcSpan){
		.begin = index,
		.end = src_span_begin(parser),
	};
}

static void * parser_alloc_bytes(Parser * parser, usize size, usize align) {
	void * ptr = vmem_arena_alloc_bytes(parser->arena, size, align);
	if (UNLIKELY(!ptr)) {
		longjmp(parser->oom_handler, 1);
	}
	return ptr;
}

static void * parser_alloc_bytes_n(Parser * parser, usize size, usize n,
								   usize align) {
	void * ptr = vmem_arena_alloc_bytes_n(parser->arena, size, n, align);
	if (UNLIKELY(!ptr)) {
		longjmp(parser->oom_handler, 1);
	}
	return ptr;
}

#define parser_alloc(parser, T)                                                \
	((T *)parser_alloc_bytes(parser, sizeof(T), alignof(T)))
#define parser_alloc_n(parser, T, n)                                           \
	((T *)parser_alloc_bytes_n(parser, sizeof(T), (n), alignof(T)))

static usize get_segmented_slot(usize size) {
	return stdc_bit_width(size + 1) - 1;
}

static usize get_segmented_slot_index(usize size, usize slot) {
	return size - (1U << slot) + 1;
}

static Decl * ast_add_decl(Parser * parser, Ast * ast, Decl decl) {
	usize slot = get_segmented_slot(ast->size);
	usize index = get_segmented_slot_index(ast->size, slot);
	if (index == 0) {
		size_t size = slot + 1;
		Decl ** data = parser_alloc_n(parser, Decl *, size);
		for (usize i = 0; i < slot; ++i) {
			data[i] = ast->data[i];
		}
		data[slot] = parser_alloc_n(parser, Decl, 1U << slot);
		ast->data = data;
	}
	++ast->size;
	Decl * loc = &ast->data[slot][index];
	*loc = decl;
	return loc;
}

Decl * ast_at(Ast * ast, usize index) {
	usize slot = get_segmented_slot(index);
	usize slot_index = get_segmented_slot_index(index, slot);
	return &ast->data[slot][slot_index];
}

static bool parse_type(Parser * parser, Type * out) {
	Type type;
	Type * next;
	switch (peek_kind(parser)) {
	case TOKEN_STAR:
		advance(parser);
		if (!parse_type(parser, &type)) {
			return false;
		}
		next = parser_alloc(parser, Type);
		*next = type;
		*out = type_ptr_from_ast(next);
		return true;
	case TOKEN_AMPERSAND:
		advance(parser);
		if (!parse_type(parser, &type)) {
			return false;
		}
		next = parser_alloc(parser, Type);
		*next = type;
		*out = type_ref_from_ast(next);
		return true;
	case TOKEN_IDEN: {
		Iden iden = lexer_token_str(&parser->lexer, peek(parser));
		*out = type_iden_from_ast(iden);
		advance(parser);
		return true;
	}
	default:
		expected_error(parser, "expected type");
		return false;
	}
}

typedef bool (*ExprPrefixFn)(Parser * parser, Expr * out);
typedef bool (*ExprPostfixFn)(Parser * parser, Expr prefix, Expr * out);

typedef enum {
	EXPR_PREC_NONE,
	EXPR_PREC_TERM,
	EXPR_PREC_PREFIX,
	EXPR_PREC_PRIMARY,
} ExprPrec;

typedef struct {
	ExprPrefixFn prefix;
	ExprPostfixFn postfix;
	ExprPrec prec;
} ExprRule;

static bool parse_expr_prec(Parser * parser, ExprPrec prec, Expr * out);
static bool parse_expr(Parser * parser, Expr * out);

static void recover_parse_expr_error_in_parens(Parser * parser) {
	if (!parser->panic_mode) {
		return;
	}
	parser->panic_mode = false;
	while (!eof(parser)) {
		switch (peek_kind(parser)) {
		case TOKEN_SEMICOLON:
		case TOKEN_RPAREN:
			return;
		default:
			advance(parser);
		}
	}
}

static bool expr_parens(Parser * parser, Expr * out) {
	advance(parser); // '('
	if (!parse_expr(parser, out)) {
		*out = expr_error();
	}
	recover_parse_expr_error_in_parens(parser);
	if (!expect(parser, TOKEN_RPAREN, "expected ')'")) {
		return false;
	}
	return true;
}

static bool expr_addr(Parser * parser, Expr * out) {
	advance(parser); // &
	Expr next;
	if (!parse_expr_prec(parser, EXPR_PREC_PREFIX, &next)) {
		return false;
	}
	Expr * pnext = parser_alloc(parser, Expr);
	*pnext = next;
	*out = expr_addr_from_ast(pnext);
	return true;
}

static bool expr_iden(Parser * parser, Expr * out) {
	Iden iden = lexer_token_str(&parser->lexer, peek(parser));
	advance(parser);
	*out = expr_iden_from_ast(iden);
	return true;
}

static bool expr_int(Parser * parser, Expr * out) {
	I128 i128 = i128_new(0, 0);
	Str src = lexer_token_str(&parser->lexer, peek(parser));
	// TODO: figure it out bc this aint it
	advance(parser); // integer
	for (usize i = 0; i < src.size; ++i) {
		i128.low *= 10;
		i128.low += (u64)(src.data[i] - '0');
	}
	*out = expr_int_from_ast(i128);
	return true;
}

static bool expr_plus(Parser * parser, Expr prefix, Expr * out) {
	advance(parser); // '+'
	Expr expr2;
	if (!parse_expr_prec(parser, EXPR_PREC_TERM, &expr2)) {
		return false;
	}
	Expr * a = parser_alloc(parser, Expr);
	Expr * b = parser_alloc(parser, Expr);
	*a = prefix;
	*b = expr2;
	*out = expr_plus_from_ast(a, b);
	return true;
}

ExprRule expr_rule_table[TOKEN_COUNT] = {
	[TOKEN_LPAREN] = {expr_parens, NULL, EXPR_PREC_NONE},
	[TOKEN_PLUS] = {NULL, expr_plus, EXPR_PREC_TERM},
	[TOKEN_AMPERSAND] = {expr_addr, NULL, EXPR_PREC_NONE},
	[TOKEN_INT] = {expr_int, NULL, EXPR_PREC_NONE},
	[TOKEN_IDEN] = {expr_iden, NULL, EXPR_PREC_NONE},
};

static bool parse_expr_prec(Parser * parser, ExprPrec prec, Expr * out) {
	ExprRule * rule = &expr_rule_table[peek_kind(parser)];
	if (!rule->prefix) {
		expected_error(parser, "expected expression");
		return false;
	}
	Expr expr;
	if (!rule->prefix(parser, &expr)) {
		return false;
	}
	for (;;) {
		ExprRule * rule = &expr_rule_table[peek_kind(parser)];
		if (rule->prec < prec)
			break;
		prec = rule->prec;
		if (!rule->postfix(parser, expr, &expr)) {
			return false;
		}
	}
	*out = expr;
	return true;
}

static bool parse_expr(Parser * parser, Expr * out) {
	return parse_expr_prec(parser, EXPR_PREC_TERM, out);
}

// *iden is guaranteed to be initialized
static Var parse_var(Parser * parser, bool is_const, TokenIndex begin,
					 Str * iden) {
	bool is_mut = match(parser, TOKEN_MUT);
	Token * token = peek(parser);
	*iden = lexer_token_str(&parser->lexer, token);
	if (!expect(parser, TOKEN_IDEN, "expected identifier")) {
		*iden = s("");
		goto error;
	}
	if (!expect(parser, TOKEN_COLON, "expected ':'")) {
		goto error;
	}
	Type type;
	if (!parse_type(parser, &type)) {
		goto error;
	}
	Expr expr;
	Expr * opt_expr = NULL;
	if (match(parser, TOKEN_EQ)) {
		opt_expr = &expr;
		if (!parse_expr(parser, opt_expr)) {
			goto error;
		}
	}
	if (!expect(parser, TOKEN_SEMICOLON, "expected ';'")) {
		goto error;
	}
	SrcSpan span = src_span_end(parser, begin);
	return var_from_ast(span, type, is_const, is_mut, opt_expr);
error:
	return var_error();
}

static Decl parse_decl(Parser * parser) {
	TokenIndex index = src_span_begin(parser);
	switch (peek_kind(parser)) {
	case TOKEN_CONST:
		advance(parser);
		switch (peek_kind(parser)) {
		case TOKEN_FN:
			TODO();
		case TOKEN_IDEN: {
			Iden iden;
			Var var = parse_var(parser, true, index, &iden);
			return decl_var_from_ast(iden, var);
		}
		default:
			expected_error(parser, "expected 'fn' or identifier");
			return decl_error();
		}
		break;
	case TOKEN_FN:
		TODO();
	case TOKEN_LET: {
		advance(parser);
		Iden iden;
		Var var = parse_var(parser, false, index, &iden);
		return decl_var_from_ast(iden, var);
	}
	case TOKEN_TYPE:
		TODO();
	default:
		expected_error(parser, "expected 'const', 'fn', 'let', or 'type'");
		return decl_error();
	}
}

static void recover_parse_decl_error(Parser * parser) {
	if (!parser->panic_mode)
		return;
	parser->panic_mode = false;
	while (!eof(parser)) {
		switch (peek_kind(parser)) {
		case TOKEN_CONST:
		case TOKEN_FN:
		case TOKEN_LET:
		case TOKEN_TYPE:
			return;
		default:
			advance(parser);
		}
	}
}

Ast parse_ast(Parser * parser) {
	Ast ast = {0};
	while (!eof(parser)) {
		ast_add_decl(parser, &ast, parse_decl(parser));
		recover_parse_decl_error(parser);
	}
	return ast;
}

ParseResult parse_src(VMemArena * arena, Str path, Str src, Ast * out) {
	Parser parser;
	parser.lexer = lexer_new(src);
	parser.arena = arena;
	parser.had_error = false;
	parser.panic_mode = false;
	parser.path = path;
	parser.token1 = next_valid_token(&parser, &parser.row1, &parser.col1);
	parser.token2 = next_valid_token(&parser, &parser.row2, &parser.col2);
	if (setjmp(parser.oom_handler)) {
		return PARSE_RESULT_OOM;
	}
	if (setjmp(parser.overflow_handler)) {
		return PARSE_RESULT_OVERFLOW;
	}
	*out = parse_ast(&parser);
	return parser.had_error ? PARSE_RESULT_ERROR : PARSE_RESULT_OK;
}
