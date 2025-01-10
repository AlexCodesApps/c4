#pragma once
#include <memory>
#include <print>
#include "lexer.hpp"
#include "try.hpp"
#include "token_parser.hpp"

namespace ast {
    using Identifier = std::string_view;
    struct Type;
    namespace type {
        using Identifier = ast::Identifier;
        struct Pointer {
            std::unique_ptr<Type> next;
        };
    }
    struct Type {
        std::variant<type::Identifier, type::Pointer> variant;
        bool has_identifier() const {
            return std::holds_alternative<type::Identifier>(variant);
        }
        bool has_pointer() const {
            return std::holds_alternative<type::Pointer>(variant);
        }
        type::Identifier& get_identifier() {
            return std::get<type::Identifier>(variant);
        }
        const type::Identifier& get_identifier() const {
            return std::get<type::Identifier>(variant);
        }
        type::Pointer& get_pointer() {
            return std::get<type::Pointer>(variant);
        }
        const type::Pointer& get_pointer() const {
            return std::get<type::Pointer>(variant);
        }
    };
    struct Expression;
    namespace expr {
        struct Literal {
            enum { INTEGER, NULLPTR } type;
            usize integer;
        };
        struct AddrOf {
            std::unique_ptr<Expression> next;
        };
        using Identifier = ast::Identifier;
    }
    struct Expression {
        std::variant<expr::Literal, expr::Identifier, expr::AddrOf> variant;
        bool has_literal() const {
            return std::holds_alternative<expr::Literal>(variant);
        }
        bool has_identifier() const {
            return std::holds_alternative<expr::Identifier>(variant);
        }
        bool has_addr_of() const {
            return std::holds_alternative<expr::AddrOf>(variant);
        }
        expr::Literal& get_literal() {
            return std::get<expr::Literal>(variant);
        }
        const expr::Literal& get_literal() const {
            return std::get<expr::Literal>(variant);
        }
        expr::Identifier& get_identifier() {
            return std::get<Identifier>(variant);
        }
        const expr::Identifier& get_identifier() const {
            return std::get<Identifier>(variant);
        }
        expr::AddrOf& get_addr_of() {
            return std::get<expr::AddrOf>(variant);
        }
        const expr::AddrOf& get_addr_of() const {
            return std::get<expr::AddrOf>(variant);
        }
    };
    namespace stmt {
        struct Return {
            std::optional<Expression> value;
        };
    }
    struct Statement {
        enum { RETURN } type;
        std::optional<Expression> value;
    };
    struct Variable {
        Identifier iden;
        Type type;
        std::optional<Expression> value;
    };
    struct FunctionParameter {
        std::optional<Identifier> iden;
        Type type;
    };
    struct Function {
        Identifier iden;
        std::vector<FunctionParameter> args;
        Type return_type;
        std::vector<Statement> body;
    };
    using Program = std::vector<Function>;
    template <typename F>
    auto parse_maybe(TokenParser& parser, F functor)
    -> std::optional<typename decltype(functor(parser))::value_type> {
        auto pos = parser.get_position();
        auto opt = functor(parser);
        if (!opt) {
            parser.set_position(pos);
        }
        return opt;
    }
    template <typename F>
    auto parse_many(TokenParser& parser, F functor) {
        using type = typename decltype(functor(parser))::value_type;
        std::vector<type> output;
        for (;;) {
            usize pos = parser.get_position();
            auto value = ({
                auto opt = functor(parser);
                if (!opt) {
                    parser.set_position(pos);
                    return output;
                }
                std::move(*opt);
            });
            output.push_back(std::move(value));
        }
    }
    template <typename F, typename S>
    auto parse_with_sep(TokenParser& parser, F functor, S sep_functor, bool allow_trailing)
    -> std::optional<std::vector<typename decltype(functor(parser))::value_type>>
    {
        enum {
            NONE,
            EXPECT_SEP_OR_END,
            EXPECT_FUN_OR_TRAIL,
        } state = NONE;
        using type = typename decltype(functor(parser))::value_type;
        std::vector<type> output;
        for (;;) {
            switch (state) {
            case NONE:
                output.push_back(({
                    auto pos = parser.get_position();
                    auto opt = functor(parser);
                    if (!opt) {
                        parser.set_position(pos);
                        return output;
                    }
                    std::move(*opt);
                }));
                state = EXPECT_SEP_OR_END;
                break;
            case EXPECT_SEP_OR_END: {
                    auto pos = parser.get_position();
                    if (!sep_functor(parser)) {
                        parser.set_position(pos);
                        return output;
                    }
                }
                state = EXPECT_FUN_OR_TRAIL;
                break;
            case EXPECT_FUN_OR_TRAIL:
                output.push_back(({
                    auto pos = parser.get_position();
                    auto opt = functor(parser);
                    if (!opt) {
                        if (!allow_trailing) {
                            return std::nullopt;
                        }
                        parser.set_position(pos);
                        return output;
                    }
                    std::move(*opt);
                }));
                state = EXPECT_SEP_OR_END;
                break;
            }
        }
    }
    template <typename F, typename T>
    auto parse_until(TokenParser& parser, F functor, T terminal_functor)
    -> std::optional<
        std::vector<typename decltype(functor(parser))::value_type>>
    {
        using type = decltype(functor(parser))::value_type;
        std::vector<type> output;
        while (!terminal_functor(parser)) {
            output.push_back(TRY(functor(parser)));
        }
        return std::optional(std::move(output));
    }
    std::optional<Identifier> parse_identifier(TokenParser& parser);
    std::optional<Expression> parse_expresison(TokenParser& parser);
    std::optional<Type> parse_type(TokenParser& parser);
    std::optional<Variable> parse_variable_declaration(TokenParser& parser);
    std::optional<FunctionParameter> parse_function_param(TokenParser& parser);
    std::optional<Statement> parse_statement(TokenParser& parser);
    std::optional<Function> parse_function(TokenParser& parser);
    std::optional<Program> parse_program(TokenParser& parser);
    std::optional<Program> parse(std::span<Token> src);
}
