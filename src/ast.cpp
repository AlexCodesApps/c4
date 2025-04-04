#include "include/ast.hpp"
#include "include/lexer.hpp"
#include "include/token_parser.hpp"
#include "include/try.hpp"
#include "include/utils.hpp"

namespace {
    auto parse_comma = [](TokenParser& parser) { return parser.expect(TokenType::COMMA); };
}

namespace ast {

auto parse_identifier(TokenParser& parser) -> std::optional<Identifier> {
    auto& iden = parser.peek_advance();
    if (iden.type != TokenType::IDENTIFIER) {
        return std::nullopt;
    }
    return iden.source_string;
}

auto parse_expression_primary(TokenParser& parser) -> std::optional<Expression> {
    if (parser.advance_if_match(TokenType::LPAREN)) {
        auto expr = TRY(parse_expression(parser));
        parser.expect(TokenType::RPAREN);
        return std::move(expr);
    } else if (parser.match(TokenType::INTEGER)) {
        auto& tok = parser.peek_advance();
        return Expression {
            .variant = expr::Literal {
                .variant = lit::Integer {
                    .value = tok.integer
                }
            }
        };
    } else if (parser.advance_if_match(TokenType::TRUE)) {
        return Expression {
            .variant = expr::Literal {
                .variant = lit::True{}
            }
        };
    } else if (parser.advance_if_match(TokenType::FALSE)) {
        return Expression {
            .variant = expr::Literal {
                .variant = lit::False{}
            }
        };
    } else if (parser.advance_if_match(TokenType::NULLPTR)) {
        return Expression {
            .variant = expr::Literal {
                .variant = lit::Nullptr{}
            }
        };
    } else if (parser.match(TokenType::IDENTIFIER)) {
        auto& tok = parser.peek_advance();
        return Expression {
            .variant = expr::Identifier {
                tok.source_string
            }
        };
    }
    return std::nullopt;
}

auto parse_expression_funcall(Expression& expr, TokenParser& parser) -> bool {
    if (parser.advance_if_match(TokenType::LPAREN)) {
        auto args = TRY(parse_with_sep(parser, parse_expression, parse_comma, false));
        TRY(parser.expect(TokenType::RPAREN));
        expr = Expression {
            .variant = expr::FunctionCall {
                .fun = unique_ptr_wrap(std::move(expr)),
                .args = std::move(args),
            }
        };
    }
    return false;
}

auto parse_expression_deref(Expression& expr, TokenParser& parser) -> bool {
    if (parser.match(TokenType::DOT) && parser.match(TokenType::STAR, 1)) {
        parser.advance(2);
        expr = Expression {
            .variant = expr::Deref {
                .next = unique_ptr_wrap(std::move(expr))
            }
        };
        return true;
    }
    return false;
}

auto parse_expression_postfix(TokenParser& parser) -> std::optional<Expression> {
    auto expr = TRY(parse_expression_primary(parser));
    auto helper = [&](auto fun) {
        auto pos = parser.get_position();
        if (!fun(expr, parser)) {
            parser.set_position(pos);
            return false;
        }
        return true;
    };
    while (helper(parse_expression_funcall) || helper(parse_expression_deref)) {
        // keep iterating until no more postfix expressions are recognized
    }
    return expr;
}

auto parse_expression_unary(TokenParser& parser) -> std::optional<Expression> {
    if (parser.advance_if_match(TokenType::AMPERSAND)) {
        return Expression {
            .variant = expr::AddrOf {
                .next = unique_ptr_wrap(TRY(parse_expression_unary(parser)))
            }
        };
    } else if (parser.advance_if_match(TokenType::MINUS)) {
        return Expression {
            .variant = expr::Unary {
                .next = unique_ptr_wrap(TRY(parse_expression_unary(parser))),
                .type = expr::Unary::MINUS
            }
        };
    } else {
        return parse_expression_postfix(parser);
    }
}

auto parse_expression_term(TokenParser& parser) -> std::optional<Expression> {
    auto expr = TRY(parse_expression_unary(parser));
    while (parser.match(TokenType::MINUS) || parser.match(TokenType::PLUS)) {
        auto& tok = parser.peek_advance();
        auto bin_type =
            tok.type == TokenType::PLUS ?
            expr::Binary::ADD : expr::Binary::SUB;
        expr = Expression {
            .variant = expr::Binary {
                .a = unique_ptr_wrap(std::move(expr)),
                .b = unique_ptr_wrap(TRY(parse_expression_unary(parser))),
                .type = bin_type
            }
        };
    }

    return expr;
}

auto parse_expression_as(TokenParser& parser) -> std::optional<Expression> {
    auto expr = TRY(parse_expression_term(parser));
    while (parser.advance_if_match(TokenType::AS)) {
        expr = Expression {
            .variant = expr::As {
                .next = unique_ptr_wrap(std::move(expr)),
                .type = TRY(parse_type(parser))
            }
        };
    }
    return std::move(expr);
}

auto parse_expression(TokenParser& parser) -> std::optional<Expression> {
    return parse_expression_as(parser);
}

auto parse_type(TokenParser& parser) -> std::optional<Type> {
    if (parser.advance_if_match(TokenType::AMPERSAND)) {
        return Type {
            .variant = type::Reference {
                .next = unique_ptr_wrap(TRY(parse_type(parser)))
            }
        };
    } else if (parser.advance_if_match(TokenType::STAR)) {
        return Type {
            .variant = type::Pointer {
                .next = unique_ptr_wrap(TRY(parse_type(parser)))
            }
        };
    } else if (parser.advance_if_match(TokenType::FUNCTION)) {
        TRY(parser.expect(TokenType::LPAREN));
        auto params = TRY(parse_with_sep(parser, parse_type, parse_comma, false));
        TRY(parser.expect(TokenType::RPAREN));
        TRY(parser.expect(TokenType::COLON));
        auto ret_type = TRY(parse_type(parser));
        return Type {
            .variant = type::Function {
                .parameter_types = std::move(params),
                .return_type = unique_ptr_wrap(std::move(ret_type)),
            }
        };
    } else {
        return Type {
            .variant = type::Identifier {
                TRY(parse_identifier(parser))
            }
        };
    }
}

auto parse_variable_declaration(TokenParser& parser) -> std::optional<Variable> {
    auto iden = TRY(parse_identifier(parser));
    TRY(parser.expect(TokenType::COLON));
    auto type = TRY(parse_type(parser));
    std::optional<Expression> expr;
    if (parser.advance_if_match(TokenType::EQ)) {
        expr = TRY(parse_expression(parser));
    }
    return Variable {
        .identifier = std::move(iden),
        .type = std::move(type),
        .value = std::move(expr),
    };
}

auto parse_function_param(TokenParser& parser) -> std::optional<FunctionParameter> {
    auto decl = parse_maybe(parser, parse_variable_declaration);
    if (decl) {
        if (decl->value) {
            std::println(stderr, "doesn't support default function args ");
            return std::nullopt;
        }
        return FunctionParameter {
            .iden = std::move(decl->identifier),
            .type = std::move(decl->type)
        };
    }
    auto type = TRY(parse_type(parser));
    return FunctionParameter {
        .iden = std::nullopt,
        .type = std::move(type)
    };
}

auto parse_statement(TokenParser& parser) -> std::optional<Statement> {
    if (parser.advance_if_match(TokenType::LBRACE)) {
        return Statement {
            .variant = TRY(parse_until(parser, parse_statement, [](auto& parser) {
                return parser.advance_if_match(TokenType::RBRACE);
            }))
        };
    } else if (parser.advance_if_match(TokenType::RETURN)) {
        auto statement = Statement {
            .variant = stmt::Return {
                .value = parse_maybe(parser, parse_expression)
            }
        };
        TRY(parser.expect(TokenType::SEMICOLON));
        return std::move(statement);
    } else if (parser.advance_if_match(TokenType::LET)) {
        auto stmt = Statement {
            .variant = TRY(parse_variable_declaration(parser))
        };
        TRY(parser.expect(TokenType::SEMICOLON));
        return std::move(stmt);
    } else {
        auto expr = TRY(parse_expression(parser));
        if (parser.advance_if_match(TokenType::EQ)) {
            auto expr2 = TRY(parse_expression(parser));
            TRY(parser.expect(TokenType::SEMICOLON));
            return Statement {
                .variant = stmt::Assignment {
                    .target = std::move(expr),
                    .value = std::move(expr2)
                }
            };
        }
        TRY(parser.expect(TokenType::SEMICOLON));
        return Statement {
            .variant = std::move(expr)
        };
    }
    return std::nullopt;
}

auto parse_function(TokenParser& parser) -> std::optional<Function> {
    TRY(parser.expect(TokenType::FUNCTION));
    auto iden = TRY(parse_identifier(parser));
    TRY(parser.expect(TokenType::LPAREN));
    auto args = TRY(parse_with_sep(parser, parse_function_param, parse_comma, false));
    TRY(parser.expect(TokenType::RPAREN));
    TRY(parser.expect(TokenType::COLON));
    auto return_type = TRY(parse_type(parser));
    TRY(parser.expect(TokenType::LBRACE));
    auto body = parse_many(parser, parse_statement);
    TRY(parser.expect(TokenType::RBRACE));
    return Function {
        .iden = std::move(iden),
        .args = std::move(args),
        .return_type = std::move(return_type),
        .body = std::move(body)
    };
}

auto parse_program(TokenParser& parser) -> std::optional<Program> {
    auto eof = [](TokenParser& parser) {
        return parser.eof();
    };
    return parse_until(parser, parse_function, eof);
}

auto parse(std::span<Token> src) -> std::optional<Program> {
    TokenParser parser(src);
    return parse_program(parser);
}

}
