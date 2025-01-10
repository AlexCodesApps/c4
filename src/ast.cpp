#include "include/ast.hpp"

namespace ast {

auto parse_identifier(TokenParser& parser) -> std::optional<Identifier> {
    auto& iden = parser.peek_advance();
    if (iden.type != TokenType::IDENTIFIER) {
        return std::nullopt;
    }
    return iden.source_string;
}

auto parse_expresison(TokenParser& parser) -> std::optional<Expression> {
    if (parser.match(TokenType::INTEGER)) {
        auto& tok = parser.peek_advance();
        return Expression {
            .variant = expr::Literal {
                .type = expr::Literal::INTEGER,
                .integer = tok.integer,
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

auto parse_type(TokenParser& parser) -> std::optional<Type> {
    if (parser.advance_if_match(TokenType::STAR)) {
        return Type {
            .variant = type::Pointer {
                .next = std::make_unique<Type>(TRY(parse_type(parser)))
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
        expr = TRY(parse_expresison(parser));
    }
    return Variable {
        .iden = std::move(iden),
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
            .iden = std::move(decl->iden),
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
    if (parser.advance_if_match(TokenType::RETURN)) {
        auto statement = Statement {
            .type = Statement::RETURN,
            .value = parse_maybe(parser, parse_expresison)
        };
        TRY(parser.expect(TokenType::SEMICOLON));
        return std::move(statement);
    } else {
        auto iden = TRY(parse_identifier(parser));
        TRY(parser.expect(TokenType::EQ));
        auto expr = TRY(parse_expresison(parser));
    }
    return std::nullopt;
}

auto parse_function(TokenParser& parser) -> std::optional<Function> {
    TRY(parser.expect(TokenType::FUNCTION));
    auto iden = TRY(parse_identifier(parser));
    TRY(parser.expect(TokenType::LPAREN));
    auto parse_comma = [](TokenParser& parser) { return parser.expect(TokenType::COMMA); };
    auto args = TRY(parse_with_sep(parser, parse_function_param, parse_comma, false));
    try_impl_collapse_lvalue(({
      auto &&_opt_ = parser.expect(TokenType ::RPAREN);
      using type = decltype(_opt_);
      if (!_opt_) {
        return try_impl_castable_error<type>{std ::forward<type>(_opt_)};
      }
      try_impl_propagate_lvalue<type>(*_opt_);
    }));
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
