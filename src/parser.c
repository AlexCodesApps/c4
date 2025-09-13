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
					(int)parser->path.size, parser->path.data, parser->row1, parser->col1,
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

static TokenKind peek_type(Parser * parser) { return peek(parser)->kind; }

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

static usize get_segmented_slot(usize size) { return stdc_bit_width(size); }

static usize get_segmented_slot_index(usize size, usize slot) {
	return size - (1U << slot) + 1;
}

static Decl * ast_add_decl(Parser * parser, Ast * ast, Decl decl) {
	usize slot = get_segmented_slot(ast->size);
	if (slot == ast->size) {
		size_t size = slot + 1;
		Decl ** data = parser_alloc_n(parser, Decl *, size);
		for (usize i = 0; i < slot; ++i) {
			data[i] = ast->data[i];
		}
		data[slot] = parser_alloc_n(parser, Decl, 1U << slot);
		ast->data = data;
	}
	usize index = get_segmented_slot_index(ast->size, slot);
	Decl * loc = &ast->data[slot][index];
	*loc = decl;
	++ast->size;
	return loc;
}

Decl * ast_at(Ast * ast, usize index) {
	usize slot = get_segmented_slot(index);
	usize slot_index = get_segmented_slot_index(index, slot);
	return &ast->data[slot][slot_index];
}

static Type parse_type(Parser * parser) {
	Type * next;
	switch (peek_type(parser)) {
	case TOKEN_STAR:
		advance(parser);
		next = parser_alloc(parser, Type);
		*next = parse_type(parser);
		return type_ptr_from_ast(next);
	case TOKEN_AMPERSAND:
		advance(parser);
		next = parser_alloc(parser, Type);
		*next = parse_type(parser);
		return type_ref_from_ast(next);
	case TOKEN_IDEN:
		advance(parser);
		return type_iden_from_ast(
			lexer_token_str(&parser->lexer, peek(parser)));
	default:
		expected_error(parser, "expected '*', '&' or identifier");
		return type_error();
	}
}

// *iden is garunteed to be initialized
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
	Type type = parse_type(parser);
	if (match(parser, TOKEN_EQ)) {
		TODO("parse expression");
	}
	if (!expect(parser, TOKEN_SEMICOLON, "expected ';'")) {
		goto error;
	}
	SrcSpan span = src_span_end(parser, begin);
	return var_from_ast(span, type, is_const, is_mut);
error:
	return var_error();
}

static Decl parse_decl(Parser * parser) {
	TokenIndex index = src_span_begin(parser);
	switch (peek_type(parser)) {
	case TOKEN_CONST:
		advance(parser);
		switch (peek_type(parser)) {
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
		switch (peek_type(parser)) {
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
