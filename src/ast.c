#include <inttypes.h>
#include <stdio.h>
#include "include/ast.h"
#include "include/utility.h"

#define DECL_TOKENS \
TOKEN_FN: \
case TOKEN_TYPE: \
case TOKEN_LET: \
case TOKEN_CONST

const Expr poisoned_expr = { .type = EXPR_POISONED };
const FnParamList poisoned_fn_param_list;

_Noreturn static void parser_oom(Parser * parser) {
	longjmp(parser->oom_handler, 1);
}

static bool parse_block(Parser * parser, StmtList * out);
static bool parse_decl(Parser * parser, Decl * out);

static void print_unsanitized_char(char c) {
	if (c >= 0x20 && c <= 0x7E) {
		fprintf(stderr, "'%c'", c);
		return;
	}
	fprintf(stderr, "%x", (unsigned)c);
}

static void print_token(const Parser * parser, const Token * token) {
	Str str = lexer_token_str(&parser->lexer, token);
	fprintf(stderr, "'%.*s'", (int)str.size, str.data);
}

static void print_error_header(const Parser * parser) {
	fprintf(stderr, "in [%"PRIu64", %"PRIu64"] error: ",
			lexer_row(&parser->lexer),
			lexer_col(&parser->lexer));
}

static void parser_declare_error(Parser * parser) {
	parser->panic_mode = true;
	parser->had_error = true;
}

static Token next_token(Parser * parser) {
	for (;;) {
		Token token = lexer_next(&parser->lexer);
		if (token.type == TOKEN_ERR) {
			if (parser->panic_mode) {
				continue;
			}
			Str str = lexer_token_str(&parser->lexer, &token);
			print_error_header(parser);
			fputs("unexpected char ", stderr);
			print_unsanitized_char(*str.data);
			fputs("\n", stderr);
			parser->had_error = true;
			continue;
		}
		return token;
	}
}

static const Token * peek(const Parser * parser) {
	return &parser->current;
}

static const Token * peek1(const Parser * parser) {
	return &parser->next;
}

static void advance(Parser * parser) {
	parser->current = parser->next;
	parser->next = next_token(parser);
}

static bool match(Parser * parser, TokenType type) {
	if (peek(parser)->type == type) {
		advance(parser);
		return true;
	}
	return false;
}

static bool match_out(Parser * parser, TokenType type, Token * out) {
	if (peek(parser)->type == type) {
		*out = *peek(parser);
		advance(parser);
		return true;
	}
	return false;
}

static bool eof(const Parser * parser) {
	return peek(parser)->type == TOKEN_EOF;
}

static void expect_error(Parser * parser, const char * msg) {
	if (parser->panic_mode) {
		return;
	}
	parser_declare_error(parser);
	print_error_header(parser);
	fputs(msg, stderr);
	fputs(", found ", stderr);
	print_token(parser, peek(parser));
	fputc('\n', stderr);
}

static bool expect(Parser * parser, TokenType type, const char * msg) {
	if (match(parser, type)) {
		return true;
	}
	expect_error(parser, msg);
	return false;
}

static TokenIndex src_span_start(const Parser * parser) {
	return peek(parser)->start;
}

static SrcSpan src_span_end(const Parser * parser, TokenIndex start) {
	TokenIndex end = peek(parser)->end;
	return (SrcSpan) {
		.start = start,
		.end = end,
	};
}

void parser_init(Parser * parser, Str src, VMemArena * arena) {
	parser->arena = arena;
	parser->lexer = lexer_new(src);
	parser->panic_mode = false;
	parser->had_error = false;

	parser->current = next_token(parser);
	parser->next = next_token(parser);
}

typedef enum {
	EXPR_PREC_NONE = 0,
	EXPR_PREC_TERM,
	EXPR_PREC_PREFIX,
	EXPR_PREC_FUNCALL,
	EXPR_PREC_PRIMARY,
} ExprPrecedence;

typedef Expr (* PrefixRule)(Parser *);
typedef Expr (* InfixRule)(Parser *, Expr);

typedef struct {
	PrefixRule prefix;
	InfixRule infix;
	ExprPrecedence prec;
} ExprParseRule;

static Expr parse_expr_precedence(Parser * parser, ExprPrecedence prec);
static Expr parse_expr(Parser * parser);

static bool expr_is_poisoned(const Expr * expr) {
	return expr->type == EXPR_POISONED;
}

static Expr expr_int(Parser * parser) {
	Str str = lexer_token_str(&parser->lexer, peek(parser));
	usize accum = 0;
	for (usize i = 0; i < str.size; ++i) {
		// TODO: guard against overflow sanely
		usize digit = (usize)(str.data[i] - '0');
		bool ok = ckd_mul(accum, 10, &accum);
		ok &= ckd_add(accum, digit, &accum);
		if (!ok) {
			print_error_header(parser);
			fprintf(stderr, "integer overflow, ");
			print_token(parser, peek(parser));
			fputc('\n', stderr);
			return poisoned_expr;
		}
	}
	advance(parser);
	Expr expr;
	expr.type = EXPR_INT;
	expr.as.int_ = accum;
	return expr;
}

static Expr expr_nullptr(Parser * parser) {
	advance(parser); // 'nullptr'
	Expr expr;
	expr.type = EXPR_NULLPTR;
	return expr;
}

static Expr expr_iden(Parser * parser) {
	Str str = lexer_token_str(&parser->lexer, peek(parser));
	advance(parser);
	Expr expr;
	expr.type = EXPR_IDEN;
	expr.as.iden = str;
	return expr;
}

static Expr expr_addr(Parser * parser) {
	advance(parser); // '&'
	Expr * next = vmem_arena_alloc(parser->arena, Expr);
	if (!next) {
		parser_oom(parser);
	}
	*next = parse_expr_precedence(parser, EXPR_PREC_PREFIX);
	Expr expr;
	expr.type = EXPR_ADDR;
	expr.as.addr = next;
	return expr;
}

static void synchronize_expr_in_parens(Parser * parser) {
	if (!parser->panic_mode) {
		return;
	}
	while (!eof(parser)) {
		switch (peek(parser)->type) {
			case TOKEN_RPAREN:
				parser->panic_mode = false;
				[[fallthrough]];
			case TOKEN_FN:
			case TOKEN_TYPE:
			case TOKEN_LET:
			case TOKEN_RBRACE:
			case TOKEN_SEMICOLON:
				return;
			default:
				advance(parser);
				break;
		}
	}
}

static Expr expr_grouping(Parser * parser) {
	advance(parser); // '('
	Expr expr = parse_expr(parser);
	synchronize_expr_in_parens(parser);
	if (!expect(parser, TOKEN_RPAREN, "expected ')'")) {
		return poisoned_expr;
	}
	return expr;
}

static Expr expr_funcall(Parser * parser, Expr prefix) {
	advance(parser); // '('
	ExprList expr_list;
	expr_list_init(&expr_list);
	if (peek(parser)->type != TOKEN_RPAREN) {
		do {
			Expr expr = parse_expr(parser);
			synchronize_expr_in_parens(parser);
			if (!expr_list_push(parser->arena, &expr_list, expr)) {
				parser_oom(parser);
			}
		} while (match(parser, TOKEN_COMMA));
	}
	if (!expect(parser, TOKEN_RPAREN, "expected ')'")) {
		return poisoned_expr;
	}
	Expr new_expr;
	Expr * fun = vmem_arena_alloc(parser->arena, Expr);
	if (!fun) {
		parser_oom(parser);
	}
	*fun = prefix;
	new_expr.type = EXPR_FUNCALL;
	new_expr.as.funcall.fun = fun;
	new_expr.as.funcall.args = expr_list;
	return new_expr;
}

static Expr expr_plus(Parser * parser, Expr prefix) {
	advance(parser); // '+'
	Expr * a = vmem_arena_alloc(parser->arena, Expr);
	Expr * b = vmem_arena_alloc(parser->arena, Expr);
	if (!a || !b) {
		parser_oom(parser);
	}
	*a = prefix;
	*b = parse_expr_precedence(parser, EXPR_PREC_FUNCALL);
	Expr new_expr;
	new_expr.type = EXPR_PLUS;
	new_expr.as.plus.a = a;
	new_expr.as.plus.b = b;
	return new_expr;
}

static ExprParseRule expr_parse_rules[TOKEN_EOF + 1] = {
	[TOKEN_LPAREN]    = {expr_grouping, expr_funcall,    EXPR_PREC_FUNCALL},
	[TOKEN_PLUS]      = {nullptr,       expr_plus,       EXPR_PREC_TERM   },
	[TOKEN_AMPERSAND] = {expr_addr,     nullptr,         EXPR_PREC_NONE   },
	[TOKEN_INT]       = {expr_int,      nullptr,         EXPR_PREC_NONE   },
	[TOKEN_NULLPTR]   = {expr_nullptr,  nullptr,         EXPR_PREC_NONE   },
	[TOKEN_IDEN]      = {expr_iden,     nullptr,         EXPR_PREC_NONE   },
};

static Expr parse_expr_precedence(Parser * parser, ExprPrecedence prec) {
	ExprParseRule * rule = expr_parse_rules + peek(parser)->type;
	if (!rule->prefix) {
		expect_error(parser, "expected expression");
		return poisoned_expr;
	}
	TokenIndex begin = src_span_start(parser);
	Expr expr = rule->prefix(parser);
	if (expr_is_poisoned(&expr)) {
		return expr;
	}
	expr.span = src_span_end(parser, begin);
	for (;;) {
		ExprParseRule * rule = expr_parse_rules + peek(parser)->type;
		if (prec > rule->prec) {
			break;
		}
		TokenIndex begin = src_span_start(parser);
		expr = rule->infix(parser, expr);
		expr.span = src_span_end(parser, begin);
		if (expr_is_poisoned(&expr)) {
			return expr;
		}
	}
	return expr;
}

static Expr parse_expr(Parser * parser) {
	return parse_expr_precedence(parser, EXPR_PREC_TERM);
}

static bool parse_type(Parser * parser, Type * out) {
	TokenIndex begin = src_span_start(parser);
	switch (peek(parser)->type) {
		case TOKEN_VOID:
			advance(parser);
			out->type = TYPE_VOID;
			break;
		case TOKEN_IDEN:
			out->type = TYPE_IDEN;
			out->as.iden = lexer_token_str(&parser->lexer, peek(parser));
			advance(parser);
			break;
		case TOKEN_FN:
			advance(parser);
			if (!expect(parser, TOKEN_LPAREN, "expected '('")) {
				return false;
			}
			TypeList params;
			type_list_init(&params);
			if (peek(parser)->type != TOKEN_RPAREN) {

				if (peek(parser)->type == TOKEN_IDEN
					&& peek1(parser)->type == TOKEN_COLON) {
					advance(parser);
					advance(parser);
				}
				do {
					Type type;
					if (!parse_type(parser, &type)) {
						return false;
					}
					if (!type_list_push(parser->arena, &params, type)) {
						parser_oom(parser);
					}
					if (!match(parser, TOKEN_COMMA)) {
						break;
					}
				} while (peek(parser)->type != TOKEN_RPAREN);
			}
			if (!expect(parser, TOKEN_RPAREN, "expected ')'")) {
				return false;
			}
			if (!expect(parser, TOKEN_COLON, "expected ':'")) {
				if (peek(parser)->type == TOKEN_LBRACE) {
					fprintf(stderr, "hint : functions returning void always have ': void'\n");
				}
				return false;
			}
			Type * return_type = vmem_arena_alloc(parser->arena, Type);
			if (!return_type) {
				parser_oom(parser);
			}
			if (!parse_type(parser, return_type)) {
				return false;
			}
			out->type = TYPE_FN;
			out->as.fn.return_type = return_type;
			out->as.fn.params = params;
			break;
		case TOKEN_MUT:
			advance(parser);
			Type * mut = vmem_arena_alloc(parser->arena, Type);
			if (!mut) {
				parser_oom(parser);
			}
			if (!parse_type(parser, mut)) {
				return false;
			}
			out->type = TYPE_MUT;
			out->as.mut = mut;
			break;
		case TOKEN_STAR:
			advance(parser);
			Type * ptr = vmem_arena_alloc(parser->arena, Type);
			if (!ptr) {
				parser_oom(parser);
			}
			if (!parse_type(parser, ptr)) {
				return false;
			}
			out->type = TYPE_PTR;
			out->as.ptr = ptr;
			break;
		case TOKEN_AMPERSAND:
			advance(parser);
			ptr = vmem_arena_alloc(parser->arena, Type);
			if (!ptr) {
				parser_oom(parser);
			}
			if (!parse_type(parser, ptr)) {
				return false;
			}
			out->type = TYPE_REF;
			out->as.ref = ptr;
			break;
		default:
			expect_error(parser, "expected type");
			return false;
	}
	out->span = src_span_end(parser, begin);
	return true;
}

static bool parse_stmt(Parser * parser, Stmt * out, bool allow_decls) {
	switch (peek(parser)->type) {
	case TOKEN_SEMICOLON:
		advance(parser);
		out->type = STMT_SEMICOLON;
		return true;
	case TOKEN_RETURN:
		advance(parser);
		StmtReturn return_stmt;
		return_stmt.has_expr = false;
		if (peek(parser)->type != TOKEN_SEMICOLON) {
			Expr expr = parse_expr(parser);
			if (parser->panic_mode) {
				return false;
			}
			return_stmt.has_expr = true;
			return_stmt.unwrap.expr = expr;
		}
		if (!expect(parser, TOKEN_SEMICOLON, "expected ';'")) {
			return false;
		}
		out->type = STMT_RETURN;
		out->as.return_ = return_stmt;
		return true;
	case TOKEN_LBRACE:
		if (!parse_block(parser, &out->as.block)) {
			return false;
		}
		out->type = STMT_BLOCK;
		return true;
	case DECL_TOKENS:
		// second clause is to make space for anonymous fn's
	    if (!allow_decls || (peek(parser)->type == TOKEN_FN &&
				peek1(parser)->type != TOKEN_IDEN)) {
			goto default_;
	    }
		Decl * decl = vmem_arena_alloc(parser->arena, Decl);
		if (!decl) {
			parser_oom(parser);
		}
		if (!parse_decl(parser, decl)) {
			return false;
		}
		out->type = STMT_DECL;
		out->as.decl = decl;
		return true;
	default_:
	default:
		Expr expr = parse_expr(parser);
		if (parser->panic_mode) {
			return false;
		}
		if (!expect(parser, TOKEN_SEMICOLON, "expected ';'")) {
			return false;
		}
		out->type = STMT_EXPR;
		out->as.expr = expr;
		return true;
	}
}

static void synchronize_stmt(Parser * parser, bool allow_decls) {
	if (!parser->panic_mode) {
		return;
	}
	while (!eof(parser)) {
		switch (peek(parser)->type) {
		case TOKEN_RBRACE:
		case TOKEN_SEMICOLON:
			parser->panic_mode = false;
			return;
		case DECL_TOKENS:
			if (allow_decls) {
				parser->panic_mode = false;
			}
			return;
		default:
			advance(parser);
			break;
		}
	}
}

static bool parse_block(Parser * parser, StmtList * out) {
	if (!expect(parser, TOKEN_LBRACE, "expected '{'")) {
		return false;
	}
	stmt_list_init(out);
	while (!match(parser, TOKEN_RBRACE)) {
		Stmt stmt;
		if (!parse_stmt(parser, &stmt, true)) {
			synchronize_stmt(parser, true);
			continue;
		}
		if (stmt.type == STMT_SEMICOLON) {
			continue;
		}
		if (!stmt_list_push(parser->arena, out, stmt)) {
			parser_oom(parser);
		}
	}
	return true;
}

static void synchronize_fn_param_list(Parser * parser) {
	if (!parser->panic_mode) {
		return;
	}
	while (!eof(parser)) {
		switch (peek(parser)->type) {
		case TOKEN_RPAREN:
			parser->panic_mode = false;
			[[fallthrough]];
		case TOKEN_FN:
		case TOKEN_TYPE:
		case TOKEN_LET:
			return;
		default:
			advance(parser);
			break;
		}
	}
}

static bool parse_fn(Parser * parser, Fn * out, bool is_const) {
	advance(parser); // 'fn'
	Token iden_token;
	if (!match_out(parser, TOKEN_IDEN, &iden_token)) {
		expect_error(parser, "expected identifier");
		return false;
	}
	if (!expect(parser, TOKEN_LPAREN, "expected '('")) {
		return false;
	}
	auto param_list_alloc = vmem_arena_alloc(parser->arena, FnParamList);
	if (!param_list_alloc) {
		parser_oom(parser);
	}
	fn_param_list_init(param_list_alloc);
	const FnParamList * param_list = param_list_alloc;
	
	if (peek(parser)->type != TOKEN_RPAREN) {
		do {
			FnParam param;
			if (peek(parser)->type == TOKEN_IDEN 
				&& peek1(parser)->type == TOKEN_COLON) {
				Token iden_token = *peek(parser);
				advance(parser);
				advance(parser);
				Str iden = lexer_token_str(&parser->lexer, &iden_token);
				param.has_iden = true;
				param.unwrap.iden = iden;
			}
			if (!parse_type(parser, &param.type)) {
				param_list = &poisoned_fn_param_list;
				break;
			}
			if (!fn_param_list_push(parser->arena, param_list_alloc, param)) {
				parser_oom(parser);
			}
		} while (match(parser, TOKEN_COMMA));
	}

	synchronize_fn_param_list(parser);

	if (!expect(parser, TOKEN_RPAREN, "expected ')'")) {
		return false;
	}
	
	if (!expect(parser, TOKEN_COLON, "expected ':'")) {
		if (peek(parser)->type == TOKEN_LBRACE) {
			fprintf(stderr, "hint : functions returning void always have ': void'\n");
		}
		return false;
	}

	Type return_type;
	if (!parse_type(parser, &return_type)) {
		return false;
	}

	StmtList body;
	if (!parse_block(parser, &body)) {
		return false;
	}

	out->iden = lexer_token_str(&parser->lexer, &iden_token);
	out->return_type = return_type;
	out->params = param_list;
	out->body = body;
	out->is_const = is_const;
	return true;
}

static bool parse_type_alias(Parser * parser, TypeAlias * out) {
	advance(parser); // 'type'
	if (peek(parser)->type != TOKEN_IDEN) {
		expect_error(parser, "expected identifier");
		return false;
	}
	Token iden_token = *peek(parser);
	advance(parser);
	if (!expect(parser, TOKEN_EQ, "expected '='")) {
		return false;
	}
	if (!parse_type(parser, &out->type)) {
		return false;
	}
	if (!expect(parser, TOKEN_SEMICOLON, "expected ';'")) {
		return false;
	}
	out->iden = lexer_token_str(&parser->lexer, &iden_token);
	return true;
}

// 'let' or 'const' is preconsumed!
static bool parse_var(Parser * parser, Var * out, bool is_const) {
	out->is_mut = false;
	out->is_const = is_const;
	if (match(parser, TOKEN_MUT)) {
		out->is_mut = true;
	}
	Token iden_token;
	if (!match_out(parser, TOKEN_IDEN, &iden_token)) {
		expect_error(parser, "expected identifier");
		return false;
	}
	if (!expect(parser, TOKEN_COLON, "expected ':'")) {
		return false;
	}
	if (!parse_type(parser, &out->type)) {
		return false;
	}
	out->init_with_expr = false;
	if (match(parser, TOKEN_EQ)) {
		Expr expr = parse_expr(parser);
		out->unwrap.expr = expr;
		out->init_with_expr = true;
	}
	if (!expect(parser, TOKEN_SEMICOLON, "expected ';'")) {
		return false;
	}
	out->iden = lexer_token_str(&parser->lexer, &iden_token);
	return true;
}

static void synchronize_decl(Parser * parser) {
	if (!parser->panic_mode) {
		return;
	}
	parser->panic_mode = false;
	while (!eof(parser)) {
		switch (peek(parser)->type) {
		case TOKEN_TYPE:
		case TOKEN_FN:
		case TOKEN_LET:
			return;
		default:
			advance(parser);
			break;
		}
	}
}

bool parse_decl(Parser * parser, Decl * out) {
	Fn fn;
	Var var;
	TypeAlias alias;
	switch (peek(parser)->type) {
		case TOKEN_FN:
			if (!parse_fn(parser, &fn, false)) {
				return false;
			}
			out->type = DECL_FN;
			out->as.fn = fn;
			break;
		case TOKEN_TYPE:
			if (!parse_type_alias(parser, &alias)) {
				return false;
			}
			out->type = DECL_TYPE_ALIAS;
			out->as.alias = alias;
			break;
		case TOKEN_LET:
			advance(parser);
			if (!parse_var(parser, &var, false)) {
				return false;
			}
			out->type = DECL_VAR;
			out->as.var = var;
			break;
		case TOKEN_CONST:
			advance(parser);
			switch (peek(parser)->type) {
				case TOKEN_FN:
					if (!parse_fn(parser, &fn, true)) {
						return false;
					}
					out->type = DECL_FN;
					out->as.fn = fn;
					break;
				case TOKEN_MUT:
				case TOKEN_IDEN:
					if (!parse_var(parser, &var, true)) {
						return false;
					}
					out->type = DECL_VAR;
					out->as.var = var;
					break;
				default:
					// doesn't account for mut but that is an error in semantic analysis
					expect_error(parser, "expected 'fn' or identifier");
					return false;
			}
			break;
		default:
			expect_error(parser, "expected 'fn','type' or 'let'");
			return false;
	}
	return true;
}

DeclList parser_run(Parser * parser) {
	Decl decl;
	DeclList list;
	decl_list_init(&list);
	if (setjmp(parser->oom_handler) != 0) {
		fprintf(stderr, "fatal error: OOM\n");
		parser_declare_error(parser);
		return list;
	}
	while (!eof(parser)) {
		if (parse_decl(parser, &decl)) {
			if (!decl_list_push(parser->arena, &list, decl)) {
				parser_oom(parser);
			}
		}
		synchronize_decl(parser);
	}
	return list;
}

void type_list_init(TypeList * list) {
	ZERO(list);
}

bool type_list_push(VMemArena * arena, TypeList * list, Type type) {
	auto node = vmem_arena_alloc(arena, TypeNode);
	if (!node) {
		return false;
	}
	node->type = type;
	node->next = nullptr;
	if (!list->begin) {
		list->begin = node;
	}
	if (list->end) {
		list->end->next = node;
	}
	list->end = node;
	return true;
}

void expr_list_init(ExprList * list) {
	ZERO(list);
}

bool expr_list_push(VMemArena * arena, ExprList * list, Expr expr) {
	auto node = vmem_arena_alloc(arena, ExprNode);
	if (!node) {
		return false;
	}
	node->expr = expr;
	node->next = nullptr;
	if (!list->begin) {
		list->begin = node;
	}
	if (list->end) {
		list->end->next = node;
	}
	list->end = node;
	++list->count;
	return true;
}

void stmt_list_init(StmtList * list) {
	ZERO(list);
}

bool stmt_list_push(VMemArena * arena, StmtList * list, Stmt stmt) {
	auto node = vmem_arena_alloc(arena, StmtNode);
	if (!node) {
		return false;
	}
	node->stmt = stmt;
	node->next = nullptr;
	if (!list->begin) {
		list->begin = node;
	}
	if (list->end) {
		list->end->next = node;
	}
	list->end = node;
	return true;
}

void fn_param_list_init(FnParamList * list) {
	ZERO(list);
}

bool fn_param_list_push(VMemArena * arena, FnParamList * list, FnParam param) {
	auto node = vmem_arena_alloc(arena, FnParamNode);
	if (!node) {
		return false;
	}
	node->param = param;
	node->next = nullptr;
	if (!list->begin) {
		list->begin = node;
	}
	if (list->end) {
		list->end->next = node;
	}
	list->end = node;
	++list->count;
	return true;
}

void decl_list_init(DeclList * list) {
	ZERO(list);
}

bool decl_list_push(VMemArena * arena, DeclList * list, Decl decl) {
	auto node = vmem_arena_alloc(arena, DeclNode);
	if (!node) {
		return false;
	}
	node->decl = decl;
	node->next = nullptr;
	if (!list->begin) {
		list->begin = node;
	}
	if (list->end) {
		list->end->next = node;
	}
	list->end = node;
	return true;
}
