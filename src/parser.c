#include "include/parser.h"
#include "include/utility.h"
#include <stdbit.h>
#include <setjmp.h>

typedef struct {
	Token token1;
	Token token2;
	Lexer lexer;
	VMemArena * arena;
	jmp_buf oom_handler;
	jmp_buf overflow_handler;
	bool had_error;
	bool panic_mode;
} Parser;

static Token next_valid_token(Lexer * lexer, bool * had_error) {
	for(;;) {
		Token token = lexer_next(lexer);
		if (token.type == TOKEN_ERR) {
			*had_error = true;
			continue;
		}
		return token;
	}
}

static Token * peek(Parser * parser) {
	return &parser->token1;
}

static TokenType peek_type(Parser * parser) {
	return peek(parser)->type;
}

static void advance(Parser * parser) {
	parser->token1 = parser->token2;
	parser->token2 = next_valid_token(&parser->lexer, &parser->had_error);
}

static bool match(Parser * parser, TokenType type) {
	if (peek(parser)->type == type) {
		advance(parser);
		return true;
	}
	return false;
}

static void expected_error(Parser * parser, const char * msg) {
}

static bool expect(Parser * parser, TokenType type, const char * msg) {
	if (match(parser, type)) {
		return true;
	}
	parser->panic_mode = true;
	parser->had_error = true;
	return false;
}

static TokenIndex src_span_begin(Parser * parser) {
	if (UNLIKELY(parser->lexer.index > TOKEN_INDEX_MAX)) {
		longjmp(parser->overflow_handler, 1);
	}
	return (TokenIndex)parser->lexer.index;
}

static SrcSpan src_span_end(Parser * parser, TokenIndex index) {
	return (SrcSpan) {
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

static void * parser_alloc_bytes_n(Parser * parser, usize size, usize n, usize align) {
	void * ptr = vmem_arena_alloc_bytes_n(parser->arena, size, n, align);
	if (UNLIKELY(!ptr)) {
		longjmp(parser->oom_handler, 1);
	}
	return ptr;
}

#define parser_alloc(parser, T) ((T *)parser_alloc_bytes(parser, sizeof(T), alignof(T)))
#define parser_alloc_n(parser, T, n) ((T *)parser_alloc_bytes_n(parser, sizeof(T), (n), alignof(T)))

static usize get_segmented_slot(usize size) {
	return stdc_bit_width(size);
}

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
	Type type;
	Type * next;
	switch (peek_type(parser)) {
	case TOKEN_STAR:
		type.type = TYPE_PTR;
		next = parser_alloc(parser, Type);
		*next = parse_type(parser);
		type.as.ptr = next;
		break;
	case TOKEN_AMPERSAND:
		type.type = TYPE_REF;
		next = parser_alloc(parser, Type);
		*next = parse_type(parser);
		type.as.ref = next;
		break;
	case TOKEN_IDEN:
		type.type = TYPE_IDEN;
		type.as.iden = lexer_token_str(&parser->lexer, peek(parser));
		break;
	default:
		expected_error(parser, "expected '*', '&' or identifier");
		type.pass = TYPE_PASS_ERROR;
		return type;
	}
	type.pass = TYPE_PASS_PARSED;
	return type;
}

static Var parse_var(Parser * parser, bool is_const, TokenIndex begin, Str * iden) {
	Var var;
	var.is_const = is_const;
	var.is_mut = match(parser, TOKEN_MUT);
	Token * token = peek(parser);
	*iden = lexer_token_str(&parser->lexer, token);
	if (!expect(parser, TOKEN_IDEN, "expected identifier")) {
		goto error;
	}
	if (!expect(parser, TOKEN_COLON, "expected ':'")) {
		goto error;
	}

	var.type = parse_type(parser);
	if (match(parser, TOKEN_EQ)) {
	
	}
	var.span = src_span_end(parser, begin);
	var.pass = VAR_PASS_PARSED;
	return var;
error:
	var.pass = VAR_PASS_ERROR;
	return var;
}

static Decl parse_decl(Parser * parser) {
	Decl decl;
	TokenIndex index = src_span_begin(parser);
	switch (peek_type(parser)) {
	case TOKEN_CONST:
		advance(parser);
		switch (peek_type(parser)) {
		case TOKEN_FN:
		case TOKEN_IDEN:
			decl.type = DECL_VAR;
			decl.as.var = parse_var(parser, true, index, &decl.iden);
			break;
		default:
			expected_error(parser, "expected 'fn' or identifier");
			goto error;
		}
		break;
	case TOKEN_FN:
	case TOKEN_LET:
		advance(parser);
		decl.type = DECL_VAR;
		decl.as.var = parse_var(parser, false, index, &decl.iden);
		break;
	case TOKEN_TYPE:
	default:
		expected_error(parser, "expected 'const', 'fn', 'let', or 'type'");
		goto error;
	}
	return decl;
error:
	decl.type = DECL_ERROR;
	return decl;
}

Ast parse_ast(Parser * parser) {
	Ast ast = {0};
	while (!lexer_eof(&parser->lexer)) {
		ast_add_decl(parser, &ast, parse_decl(parser));
	}
	return ast;
}

ParseResult parse_src(VMemArena * arena, Str src, Ast * out) {
	Parser parser;
	parser.lexer = lexer_new(src);
	parser.arena = arena;
	parser.had_error = false;
	parser.panic_mode = false;
	parser.token1 = next_valid_token(&parser.lexer, &parser.had_error);
	parser.token2 = next_valid_token(&parser.lexer, &parser.had_error);
	if (setjmp(parser.oom_handler)) {
		return PARSE_RESULT_OOM;
	}
	if (setjmp(parser.overflow_handler)) {
		return PARSE_RESULT_OVERFLOW;
	}
	*out = parse_ast(&parser);
	return parser.had_error ? PARSE_RESULT_OK : PARSE_RESULT_ERROR;
}
