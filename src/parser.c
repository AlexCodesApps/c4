#include "include/parser.h"
#include "include/fmt.h"
#include "include/segment_list.h"
#include <setjmp.h>
#include <stdarg.h>

#define TOKEN_DECLS                                                            \
	TOKEN_FN:                                                                  \
	case TOKEN_LET:                                                            \
	case TOKEN_CONST:                                                          \
	case TOKEN_TYPE_

typedef struct {
	Token token1;
	Token token2;
	Lexer lexer;
	VMemArena * arena;
	jmp_buf oom_handler;
	jmp_buf overflow_handler;
	Str path;
	bool had_error;
	bool panic_mode;
} Parser;

static void _print_error_va(Str src, Str path, TokenIndex off, const char * msg,
							va_list va) {
	usize row, col;
	token_index_row_col(src, off, &row, &col);
	c4printf(stderr, "in %s[%uq, %uq]:\n", path, row, col);
	StrLineIter iter;
	str_line_iter_new(&iter, src, off);
	Str line = str_line_iter_current_line(&iter);
	{
		StrLineIter pre_iter = iter;
		Str pre;
		if (str_line_iter_last_line(&pre_iter, &pre)) {
			c4usr_print(stderr, pre);
			fputc('\n', stderr);
		}
	}
	c4usr_print(stderr, line);
	fputc('\n', stderr);
	Str pre, mid, post;
	str_split_at_idx(line, col - 1, &pre, &mid);
	str_split_at_idx(mid, 1, &mid, &post);
	c4print_space(stderr, c4cellwidth(pre));
	c4setcolor(stderr, C4FMT_COLOR_RED);
	fputc('^', stderr);
	c4resetcolor(stderr);
	if (mid.size && mid.data[0] == '\t') {
		c4print_space(stderr, TABWIDTH - 1);
	}
	c4print_space(stderr, c4cellwidth(post));
	fputc('\n', stderr);
	if (str_line_iter_next_line(&iter, &line)) {
		c4usr_print(stderr, line);
		fputc('\n', stderr);
	}
	c4setcolor(stderr, C4FMT_COLOR_RED);
	c4print(stderr, "error: ");
	c4vaprintf(stderr, msg, va);
	fputc('\n', stderr);
	c4resetcolor(stderr);
}

static void _print_error(Str src, Str path, TokenIndex off, const char * msg,
						 ...) {
	va_list va;
	va_start(va, msg);
	_print_error_va(src, path, off, msg, va);
	va_end(va);
}

static void print_error(Parser * parser, const char * msg, ...) {
	va_list va;
	va_start(va, msg);
	_print_error_va(parser->lexer.src, parser->path, parser->token1.start, msg,
					va);
	va_end(va);
	parser->had_error = true;
}

static Token next_valid_token(Parser * parser) {
	for (;;) {
		Token token = lexer_next(&parser->lexer);
		if (token.kind == TOKEN_ERR) {
			parser->had_error = true;
			_print_error(parser->lexer.src, parser->path, token.start,
						 "unexpected character '%ch'",
						 *lexer_token_str(&parser->lexer, &token).data);
			continue;
		}
		return token;
	}
}

static bool eof(Parser * parser) { return parser->token1.kind == TOKEN_EOF; }

static Token * peek(Parser * parser) { return &parser->token1; }

static TokenKind peek_kind(Parser * parser) { return peek(parser)->kind; }

static Str peek_str(Parser * parser) {
	return lexer_token_str(&parser->lexer, peek(parser));
}

static TokenKind peek_kind2(Parser * parser) { return parser->token2.kind; }

static void advance(Parser * parser) {
	parser->token1 = parser->token2;
	parser->token2 = next_valid_token(parser);
}

static bool match(Parser * parser, TokenKind kind) {
	if (peek_kind(parser) == kind) {
		advance(parser);
		return true;
	}
	return false;
}

static void expected_error(Parser * parser, const char * msg) {
	Token * token = peek(parser);
	parser->panic_mode = true;
	// parser->had_error = true; set by print_error() (for now)
	Str src = lexer_token_str(&parser->lexer, token);
	print_error(parser, "%cs, found '%s'", msg, src);
}

static bool expect(Parser * parser, TokenKind type, const char * msg) {
	if (match(parser, type)) {
		return true;
	}
	expected_error(parser, msg);
	return false;
}

static TokenIndex src_span_begin(Parser * parser) {
	TokenIndex start = peek(parser)->start;
	if (UNLIKELY(start > TOKEN_INDEX_MAX)) {
		// TODO: Lowkey hacky
		print_error(parser,
					"source file is longer than TOKEN_INDEX_MAX(%ti) bytes",
					TOKEN_INDEX_MAX);
		longjmp(parser->overflow_handler, 1);
	}
	return (TokenIndex)start;
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
	((T *)parser_alloc_bytes((parser), sizeof(T), ALIGNOF(T)))
#define parser_alloc_n(parser, T, n)                                           \
	((T *)parser_alloc_bytes_n((parser), sizeof(T), (n), ALIGNOF(T)))

TypeSig * type_sig_list_at(TypeSigList * list, usize index) {
	word slot = get_segmented_slot(index);
	usize slot_index = get_segmented_slot_index(index, slot);
	return &list->data[slot][slot_index];
}

static TypeSig * type_sig_list_add(Parser * parser, TypeSigList * list,
								   TypeSig sig) {
	word slot = get_segmented_slot(list->size);
	usize index = get_segmented_slot_index(list->size, slot);
	if (index == 0) {
		usize size = slot + 1;
		TypeSig ** data = parser_alloc_n(parser, TypeSig *, size);
		for (usize i = 0; i < slot; ++i) {
			data[i] = list->data[i];
		}
		data[slot] = parser_alloc_n(parser, TypeSig, (usize)1 << slot);
		list->data = data;
	}
	++list->size;
	TypeSig * loc = &list->data[slot][index];
	*loc = sig;
	return loc;
}

static Stmt * stmt_list_add(Parser * parser, StmtList * list, Stmt stmt) {
	word slot = get_segmented_slot(list->size);
	usize index = get_segmented_slot_index(list->size, slot);
	if (index == 0) {
		usize size = slot + 1;
		Stmt ** data = parser_alloc_n(parser, Stmt *, size);
		for (usize i = 0; i < slot; ++i) {
			data[i] = list->data[i];
		}
		data[slot] = parser_alloc_n(parser, Stmt, (usize)1 << slot);
		list->data = data;
	}
	++list->size;
	Stmt * loc = &list->data[slot][index];
	*loc = stmt;
	return loc;
}

static Expr * expr_list_add(Parser * parser, ExprList * list, Expr expr) {
	word slot = get_segmented_slot(list->size);
	usize index = get_segmented_slot_index(list->size, slot);
	if (index == 0) {
		usize size = slot + 1;
		Expr ** data = parser_alloc_n(parser, Expr *, size);
		for (usize i = 0; i < slot; ++i) {
			data[i] = list->data[i];
		}
		data[slot] = parser_alloc_n(parser, Expr, (usize)1 << slot);
		list->data = data;
	}
	++list->size;
	Expr * loc = &list->data[slot][index];
	*loc = expr;
	return loc;
}

Expr * expr_list_at(ExprList * list, usize index) {
	word slot = get_segmented_slot(index);
	usize slot_index = get_segmented_slot_index(index, slot);
	return &list->data[slot][slot_index];
}

Stmt * stmt_list_at(StmtList * list, usize index) {
	word slot = get_segmented_slot(index);
	usize slot_index = get_segmented_slot_index(index, slot);
	return &list->data[slot][slot_index];
}

static Param * param_list_add(Parser * parser, ParamList * list, Param param) {
	word slot = get_segmented_slot(list->size);
	usize index = get_segmented_slot_index(list->size, slot);
	if (index == 0) {
		usize size = slot + 1;
		Param ** data = parser_alloc_n(parser, Param *, size);
		for (usize i = 0; i < slot; ++i) {
			data[i] = list->data[i];
		}
		data[slot] = parser_alloc_n(parser, Param, (usize)1 << slot);
		list->data = data;
	}
	++list->size;
	Param * loc = &list->data[slot][index];
	*loc = param;
	return loc;
}

Param * param_list_at(ParamList * list, usize index) {
	word slot = get_segmented_slot(index);
	usize slot_index = get_segmented_slot_index(index, slot);
	return &list->data[slot][slot_index];
}

static Decl * ast_add_decl(Parser * parser, Ast * ast, Decl decl) {
	word slot = get_segmented_slot(ast->size);
	usize index = get_segmented_slot_index(ast->size, slot);
	if (index == 0) {
		usize size = slot + 1;
		Decl ** data = parser_alloc_n(parser, Decl *, size);
		for (usize i = 0; i < slot; ++i) {
			data[i] = ast->data[i];
		}
		data[slot] = parser_alloc_n(parser, Decl, (usize)1 << slot);
		ast->data = data;
	}
	++ast->size;
	Decl * loc = &ast->data[slot][index];
	*loc = decl;
	return loc;
}

Decl * ast_at(Ast * ast, usize index) {
	word slot = get_segmented_slot(index);
	usize slot_index = get_segmented_slot_index(index, slot);
	return &ast->data[slot][slot_index];
}

static void recover_param_list_error(Parser * parser);

static bool parse_type(Parser * parser, TypeSig * out) {
	TypeSig type;
	TypeSig * next;
	TokenIndex begin = src_span_begin(parser);
	SrcSpan span;
	switch (peek_kind(parser)) {
	case TOKEN_MUT:
		advance(parser);
		if (!parse_type(parser, out)) {
			return false;
		}
		type_sig_set_mut(out);
		return true;
	case TOKEN_STAR:
		advance(parser);
		if (!parse_type(parser, &type)) {
			return false;
		}
		span = src_span_end(parser, begin);
		next = parser_alloc(parser, TypeSig);
		*next = type;
		*out = type_sig_ptr_from_ast(span, next);
		return true;
	case TOKEN_AMPERSAND:
		advance(parser);
		if (!parse_type(parser, &type)) {
			return false;
		}
		span = src_span_end(parser, begin);
		next = parser_alloc(parser, TypeSig);
		*next = type;
		*out = type_sig_ref_from_ast(span, next);
		return true;
	case TOKEN_IDEN: {
		Iden iden = peek_str(parser);
		advance(parser);
		span = src_span_end(parser, begin);
		*out = type_sig_iden_from_ast(span, iden);
		return true;
	case TOKEN_VOID:
		advance(parser);
		span = src_span_end(parser, begin);
		*out = type_sig_void(span);
		return true;
	case TOKEN_FN: {
		advance(parser);
		if (!expect(parser, TOKEN_LPAREN, "expected '('"))
			return false;
		TypeSigList params = {0};
		if (!match(parser, TOKEN_RPAREN)) {
			do {
				TypeSig sig;
				if (peek_kind(parser) == TOKEN_IDEN &&
					peek_kind2(parser) == TOKEN_COLON) {
					advance(parser);
					advance(parser);
				}
				if (!parse_type(parser, &sig))
					break;
				type_sig_list_add(parser, &params, sig);
			} while (match(parser, TOKEN_COMMA));
			recover_param_list_error(parser);
			if (!expect(parser, TOKEN_RPAREN, "expected ')'"))
				return false;
		}
		TypeSig * return_ty = parser_alloc(parser, TypeSig);
		if (match(parser, TOKEN_COLON)) {
			if (!parse_type(parser, return_ty))
				return false;
		} else {
			*return_ty = type_sig_void(SRC_SPAN_VOID);
		}
		span = src_span_end(parser, begin);
		*out = type_sig_fn_from_ast(span, return_ty, params);
		return true;
	}
	}
	default:
		expected_error(parser, "expected type");
		return false;
	}
}

typedef bool (*ExprPrefixFn)(Parser * parser, Expr * out);
typedef bool (*ExprPostfixFn)(Parser * parser, Expr prefix, Expr * out,
							  TokenIndex begin);

typedef enum {
	EXPR_PREC_NONE,
	EXPR_PREC_TERM,
	EXPR_PREC_PREFIX,
	EXPR_PREC_POSTFIX,
	EXPR_PREC_PRIMARY,
} ExprPrec;

typedef struct {
	ExprPrefixFn prefix;
	ExprPostfixFn postfix;
	ExprPrec prec;
} ExprRule;

static bool parse_expr_prec(Parser * parser, ExprPrec prec, Expr * out);
static bool parse_expr(Parser * parser, Expr * out);

static Decl parse_decl(Parser * parser);

static bool parse_block(Parser * parser, StmtBlock * out);
static bool parse_stmt(Parser * parser, Stmt * out, bool allow_decls) {
	switch (peek_kind(parser)) {
	case TOKEN_SEMICOLON:
		advance(parser);
		*out = stmt_semicolon();
		return true;
	case TOKEN_RETURN: {
		advance(parser);
		if (match(parser, TOKEN_SEMICOLON)) {
			*out = stmt_return_from_ast(expr_void(INVALID_SRC_SPAN));
			return true;
		}
		Expr expr;
		if (!parse_expr(parser, &expr)) {
			return false;
		}
		if (!expect(parser, TOKEN_SEMICOLON, "expected ';'")) {
			return false;
		}
		*out = stmt_return_from_ast(expr);
		return true;
	}
	case TOKEN_LBRACE: {
		StmtBlock block;
		if (!parse_block(parser, &block)) {
			return false;
		}
		*out = stmt_block_from_ast(block);
		return true;
	}
	case TOKEN_DECLS: {
		if (peek_kind(parser) == TOKEN_FN &&
			peek_kind2(parser) == TOKEN_LPAREN) {
			goto _default;
		}
		if (!allow_decls && parser->panic_mode) {
			return false; // If this somehow happens the declaration was
						  // probably in an outer scope
		}
		Decl * decl = parser_alloc(parser, Decl);
		*decl = parse_decl(parser);
		if (!allow_decls) {
			print_error(parser,
						"declarations are not allowed in the current scope");
		}
		*out = stmt_decl_from_ast(decl);
		return true;
	}
	_default:
	default: {
		Expr expr;
		if (!parse_expr(parser, &expr)) {
			return false;
		}
		if (!expect(parser, TOKEN_SEMICOLON, "expected ';'")) {
			return false;
		}
		*out = stmt_expr_from_ast(expr);
		return true;
	}
	}
}

static void recover_stmt_block_error(Parser * parser) {
	if (!parser->panic_mode) {
		return;
	}
	parser->panic_mode = false;
	while (!eof(parser)) {
		switch (peek_kind(parser)) {
		case TOKEN_DECLS:
		case TOKEN_SEMICOLON:
		case TOKEN_RBRACE:
			return;
		default:
			advance(parser);
		}
	}
}

static bool parse_block(Parser * parser, StmtBlock * out) {
	if (!expect(parser, TOKEN_LBRACE, "expected '{'")) {
		return false;
	}
	StmtBlock block = {0};
	while (!match(parser, TOKEN_RBRACE)) {
		if (eof(parser)) { // perhaps this behavior could be improved?
			return false;
		}
		Stmt stmt;
		if (!parse_stmt(parser, &stmt, true)) {
			recover_stmt_block_error(parser);
			continue;
		}
		if (stmt.kind == STMT_SEMICOLON) {
			continue;
		}
		stmt_list_add(parser, &block, stmt);
	}
	*out = block;
	return true;
}

static void recover_parse_expr_error_in_parens(Parser * parser) {
	if (!parser->panic_mode) {
		return;
	}
	parser->panic_mode = false;
	while (!eof(parser)) {
		switch (peek_kind(parser)) {
		case TOKEN_DECLS:
		case TOKEN_SEMICOLON:
		case TOKEN_RPAREN:
			return;
		default:
			advance(parser);
		}
	}
}

static bool expr_parens(Parser * parser, Expr * out) {
	TokenIndex begin = src_span_begin(parser);
	advance(parser); // '('
	if (!parse_expr(parser, out)) {
		*out = expr_error();
	}
	recover_parse_expr_error_in_parens(parser);
	if (!expect(parser, TOKEN_RPAREN, "expected ')'")) {
		return false;
	}
	out->span = src_span_end(parser, begin);
	return true;
}

static bool expr_funcall(Parser * parser, Expr prefix, Expr * out,
						 TokenIndex begin) {
	advance(parser); // '('
	ExprList list = {0};
	if (!match(parser, TOKEN_RPAREN)) {
		do {
			Expr expr;
			if (!parse_expr(parser, &expr)) {
				recover_parse_expr_error_in_parens(parser);
				break;
			}
			expr_list_add(parser, &list, expr);
		} while (match(parser, TOKEN_COMMA));
		if (!expect(parser, TOKEN_RPAREN, "expected ')'")) {
			return false;
		}
	}
	SrcSpan span = src_span_end(parser, begin);
	Expr * fun = parser_alloc(parser, Expr);
	*fun = prefix;
	*out = expr_funcall_from_ast(span, fun, list);
	return true;
}

static bool expr_addr(Parser * parser, Expr * out) {
	TokenIndex index = src_span_begin(parser);
	advance(parser); // &
	Expr next;
	if (!parse_expr_prec(parser, EXPR_PREC_PREFIX, &next)) {
		return false;
	}
	Expr * pnext = parser_alloc(parser, Expr);
	*pnext = next;
	SrcSpan span = src_span_end(parser, index);
	*out = expr_addr_from_ast(span, pnext);
	return true;
}

static bool expr_deref(Parser * parser, Expr prefix, Expr * out,
					   TokenIndex begin) {
	advance(parser); // .*
	SrcSpan span = src_span_end(parser, begin);
	Expr * ptr = parser_alloc(parser, Expr);
	*ptr = prefix;
	*out = expr_deref_from_ast(span, ptr);
	return true;
}

static bool _expr_void(Parser * parser, Expr * out) {
	TokenIndex index = src_span_begin(parser);
	advance(parser); // 'void'
	SrcSpan span = src_span_end(parser, index);
	*out = expr_void(span);
	return true;
}

static bool expr_iden(Parser * parser, Expr * out) {
	TokenIndex index = src_span_begin(parser);
	Iden iden = peek_str(parser);
	advance(parser);
	SrcSpan span = src_span_end(parser, index);
	*out = expr_iden_from_ast(span, iden);
	return true;
}

static bool expr_int(Parser * parser, Expr * out) {
	TokenIndex index = src_span_begin(parser);
	I128 i128 = i128_new(0, 0);
	Str src = peek_str(parser);
	for (usize i = 0; i < src.size; ++i) {
		if (!i128_mul_by_10(&i128)) {
			print_error(parser, "integer overflow of '%s'", peek_str(parser));
			advance(parser);
			*out = expr_error();
			return true;
		}
		word digit = (word)(src.data[i] - '0');
		if (!i128_add_u64(i128, digit, &i128)) {
			print_error(parser, "integer overflow of '%s'", peek_str(parser));
			advance(parser);
			*out = expr_error();
			return true;
		}
	}
	advance(parser); // integer
	SrcSpan span = src_span_end(parser, index);
	*out = expr_int_from_ast(span, i128);
	return true;
}

static bool _expr_nullptr(Parser * parser, Expr * out) {
	TokenIndex index = src_span_begin(parser);
	advance(parser); // 'nullptr'
	SrcSpan span = src_span_end(parser, index);
	*out = expr_nullptr(span);
	return true;
}

static bool expr_plus(Parser * parser, Expr prefix, Expr * out,
					  TokenIndex begin) {
	advance(parser); // '+'
	Expr expr2;
	if (!parse_expr_prec(parser, EXPR_PREC_TERM, &expr2)) {
		return false;
	}
	Expr * a = parser_alloc(parser, Expr);
	Expr * b = parser_alloc(parser, Expr);
	*a = prefix;
	*b = expr2;
	SrcSpan span = src_span_end(parser, begin);
	*out = expr_plus_from_ast(span, a, b);
	return true;
}

ExprRule expr_rule_table[TOKEN_COUNT] = {
	[TOKEN_LPAREN] = {expr_parens, expr_funcall, EXPR_PREC_POSTFIX},
	[TOKEN_PLUS] = {NULL, expr_plus, EXPR_PREC_TERM},
	[TOKEN_AMPERSAND] = {expr_addr, NULL, EXPR_PREC_NONE},
	[TOKEN_DOT_STAR] = {NULL, expr_deref, EXPR_PREC_POSTFIX},
	[TOKEN_VOID] = {_expr_void, NULL, EXPR_PREC_NONE},
	[TOKEN_INT] = {expr_int, NULL, EXPR_PREC_NONE},
	[TOKEN_NULLPTR] = {_expr_nullptr, NULL, EXPR_PREC_NONE},
	[TOKEN_IDEN] = {expr_iden, NULL, EXPR_PREC_NONE},
};

static bool parse_expr_prec(Parser * parser, ExprPrec prec, Expr * out) {
	ExprRule * rule = &expr_rule_table[peek_kind(parser)];
	if (!rule->prefix) {
		expected_error(parser, "expected expression");
		return false;
	}
	Expr expr;
	TokenIndex begin = src_span_begin(parser);
	if (!rule->prefix(parser, &expr)) {
		return false;
	}
	for (;;) {
		ExprRule * rule = &expr_rule_table[peek_kind(parser)];
		if (rule->prec < prec) {
			break;
		}
		if (!rule->postfix(parser, expr, &expr, begin)) {
			return false;
		}
	}
	*out = expr;
	return true;
}

static bool parse_expr(Parser * parser, Expr * out) {
	return parse_expr_prec(parser, EXPR_PREC_TERM, out);
}

static void recover_param_list_error(Parser * parser) {
	if (!parser->panic_mode) {
		return;
	}
	parser->panic_mode = false;
	while (!eof(parser)) {
		switch (peek_kind(parser)) {
		case TOKEN_DECLS:
		case TOKEN_RPAREN:
			return;
		default:
			advance(parser);
		}
	}
}

static Fn parse_fn(Parser * parser, bool is_const, TokenIndex begin,
				   Str * iden) {
	advance(parser); // 'fn'
	*iden = peek_str(parser);
	if (!expect(parser, TOKEN_IDEN, "expected identifier")) {
		*iden = s("");
		goto error;
	}
	if (!expect(parser, TOKEN_LPAREN, "expected '('")) {
		goto error;
	}
	ParamList list = {0};
	if (!match(parser, TOKEN_RPAREN)) {
		do {
			Param param = {0};
			if (peek_kind(parser) == TOKEN_IDEN &&
				peek_kind2(parser) == TOKEN_COLON) {
				param.has_name = true;
				param.unwrap.name = peek_str(parser);
				advance(parser);
				advance(parser);
			} else {
				param.has_name = false;
			}
			if (!parse_type(parser, &param.type)) {
				break;
			}
			param_list_add(parser, &list, param);
		} while (match(parser, TOKEN_COMMA));
		recover_param_list_error(parser);
		if (!expect(parser, TOKEN_RPAREN, "expected ')'")) {
			goto error;
		}
	}
	TypeSig return_ty;
	if (match(parser, TOKEN_COLON)) {
		if (!parse_type(parser, &return_ty)) {
			goto error;
		}
	} else {
		return_ty = type_sig_void(SRC_SPAN_VOID);
	}
	StmtBlock block;
	if (!parse_block(parser, &block)) {
		goto error;
	}
	SrcSpan span = src_span_end(parser, begin);
	return fn_from_ast(span, is_const, list, return_ty, block);
error:
	return fn_error();
}

// *iden is guaranteed to be initialized
static Var parse_var(Parser * parser, bool is_const, TokenIndex begin,
					 Str * iden) {
	bool is_mut = match(parser, TOKEN_MUT);
	*iden = peek_str(parser);
	if (!expect(parser, TOKEN_IDEN, "expected identifier")) {
		*iden = s("");
		goto error;
	}
	if (!expect(parser, TOKEN_COLON, "expected ':'")) {
		goto error;
	}
	TypeSig type;
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

static TypeAlias parse_type_alias(Parser * parser, Str * iden) {
	TokenIndex index = src_span_begin(parser);
	advance(parser); // 'type'
	*iden = peek_str(parser);
	if (!expect(parser, TOKEN_IDEN, "expected identifier")) {
		*iden = s("");
		goto error;
	}
	if (!expect(parser, TOKEN_EQ, "expected '='")) {
		goto error;
	}
	TypeSig type;
	if (!parse_type(parser, &type)) {
		goto error;
	}
	if (!expect(parser, TOKEN_SEMICOLON, "expected ';'")) {
		goto error;
	}
	SrcSpan span = src_span_end(parser, index);
	return type_alias_from_ast(span, type);
error:
	return type_alias_error();
}

static Decl parse_decl(Parser * parser) {
	TokenIndex index = src_span_begin(parser);
	switch (peek_kind(parser)) {
	case TOKEN_CONST:
		advance(parser);
		switch (peek_kind(parser)) {
		case TOKEN_FN: {
			Iden iden;
			Fn fn = parse_fn(parser, true, index, &iden);
			return decl_fn_from_ast(iden, fn);
		}
		case TOKEN_MUT: // illegal but parsed anyways
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
	case TOKEN_FN: {
		Iden iden;
		Fn fn = parse_fn(parser, false, index, &iden);
		return decl_fn_from_ast(iden, fn);
	}
	case TOKEN_LET: {
		advance(parser);
		Iden iden;
		Var var = parse_var(parser, false, index, &iden);
		return decl_var_from_ast(iden, var);
	}
	case TOKEN_TYPE_: {
		Iden iden;
		TypeAlias alias = parse_type_alias(parser, &iden);
		return decl_alias_from_ast(iden, alias);
	}
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
		case TOKEN_TYPE_:
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
		LOG("parsed top level decl");
		recover_parse_decl_error(parser);
	}
	return ast;
}

ParseResult parse_src(VMemArena * arena, Str path, Str src, Ast * out) {
	LOG("compiling file : %s", path);
	Parser parser;
	parser.lexer = lexer_new(src);
	parser.arena = arena;
	parser.had_error = false;
	parser.panic_mode = false;
	parser.path = path;
	parser.token1 = next_valid_token(&parser);
	parser.token2 = next_valid_token(&parser);
	if (setjmp(parser.oom_handler)) {
		return PARSE_RESULT_OOM;
	}
	if (setjmp(parser.overflow_handler)) {
		return PARSE_RESULT_OVERFLOW;
	}
	LOG("initialized parser : %s", path);
	*out = parse_ast(&parser);
	LOG("finished parsing");
	return parser.had_error ? PARSE_RESULT_ERROR : PARSE_RESULT_OK;
}
