#pragma once
#include <memory>
#include <print>
#include <variant>
#include <vector>
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
        struct Reference {
            std::unique_ptr<Type> next;
        };
    }
    struct Type {
        std::variant<type::Identifier, type::Pointer, type::Reference> variant;
        bool is_identifier() const {
            return std::holds_alternative<type::Identifier>(variant);
        }
        bool is_pointer() const {
            return std::holds_alternative<type::Pointer>(variant);
        }
        bool is_reference() const {
            return std::holds_alternative<type::Reference>(variant);
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
        type::Reference& get_reference() {
            return std::get<type::Reference>(variant);
        }
        const type::Reference& get_reference() const {
            return std::get<type::Reference>(variant);
        }
    };
    struct Expression;
    namespace lit {
        struct Nullptr {};
        struct Integer {
            usize value;
        };
        struct True {};
        struct False {};
    }
    struct Literal {
        std::variant<lit::Nullptr, lit::Integer, lit::True, lit::False> variant;
        bool is_nullptr() const {
            return std::holds_alternative<lit::Nullptr>(variant);
        }
        bool is_integer() const {
            return std::holds_alternative<lit::Integer>(variant);
        }
        bool is_true() const {
            return std::holds_alternative<lit::True>(variant);
        }
        bool is_false() const {
            return std::holds_alternative<lit::False>(variant);
        }
        lit::Integer& get_integer() {
            return std::get<lit::Integer>(variant);
        }
        const lit::Integer& get_integer() const {
            return std::get<lit::Integer>(variant);
        }
    };
    namespace expr {
        using Literal = ast::Literal;
        struct AddrOf {
            std::unique_ptr<Expression> next;
        };
        struct Deref {
            std::unique_ptr<Expression> next;
        };
        struct As {
            std::unique_ptr<Expression> next;
            Type type;
        };
        struct Unary {
            std::unique_ptr<Expression> next;
            enum { MINUS } type;
        };
        struct Binary {
            std::unique_ptr<Expression> a;
            std::unique_ptr<Expression> b;
            enum { ADD, SUB } type;
        };
        struct FunctionCall {
            std::unique_ptr<Expression> fun;
            std::vector<Expression> args;
        };
        using Identifier = ast::Identifier;
    }
    struct Expression {
        std::variant<
            expr::Literal, expr::Identifier, expr::AddrOf, expr::Deref,
            expr::As, expr::Unary, expr::Binary, expr::FunctionCall> variant;
        bool is_literal() const {
            return std::holds_alternative<expr::Literal>(variant);
        }
        bool is_identifier() const {
            return std::holds_alternative<expr::Identifier>(variant);
        }
        bool is_addr_of() const {
            return std::holds_alternative<expr::AddrOf>(variant);
        }
        bool is_deref() const {
            return std::holds_alternative<expr::Deref>(variant);
        }
        bool is_as() const {
            return std::holds_alternative<expr::As>(variant);
        }
        bool is_unary() const {
            return std::holds_alternative<expr::Unary>(variant);
        }
        bool is_binary() const {
            return std::holds_alternative<expr::Binary>(variant);
        }
        bool is_funcall() const {
            return std::holds_alternative<expr::FunctionCall>(variant);
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
        expr::Deref& get_deref() {
            return std::get<expr::Deref>(variant);
        }
        const expr::Deref& get_deref() const {
            return std::get<expr::Deref>(variant);
        }
        expr::As& get_as() {
            return std::get<expr::As>(variant);
        }
        const expr::As& get_as() const {
            return std::get<expr::As>(variant);
        }
        expr::Unary& get_unary() {
            return std::get<expr::Unary>(variant);
        }
        const expr::Unary& get_unary() const {
            return std::get<expr::Unary>(variant);
        }
        expr::Binary& get_binary() {
            return std::get<expr::Binary>(variant);
        }
        const expr::Binary& get_binary() const {
            return std::get<expr::Binary>(variant);
        }
        expr::FunctionCall& get_funcall() {
            return std::get<expr::FunctionCall>(variant);
        }
        const expr::FunctionCall& get_funcall() const {
            return std::get<expr::FunctionCall>(variant);
        }
    };
    struct Variable {
        Identifier iden;
        Type type;
        std::optional<Expression> value;
    };
    struct Statement;
    namespace stmt {
        using VariableDecl = ast::Variable;
        struct Return {
            std::optional<Expression> value;
        };
        struct Assignment {
            Expression target;
            Expression value;
        };
        using Expression = ast::Expression;
        using Block = std::vector<Statement>;
    }
    struct Statement {
        std::variant<stmt::Return, stmt::VariableDecl, stmt::Assignment, stmt::Block, stmt::Expression> variant;
        bool is_return() const {
            return std::holds_alternative<stmt::Return>(variant);
        }
        bool is_variable_decl() const {
            return std::holds_alternative<stmt::VariableDecl>(variant);
        }
        bool is_assignment() const {
            return std::holds_alternative<stmt::Assignment>(variant);
        }
        bool is_block() const {
            return std::holds_alternative<stmt::Block>(variant);
        }
        bool is_expr() const {
            return std::holds_alternative<stmt::Expression>(variant);
        }
        stmt::Return& get_return() {
            return std::get<stmt::Return>(variant);
        }
        const stmt::Return& get_return() const {
            return std::get<stmt::Return>(variant);
        }
        stmt::VariableDecl& get_variable_decl() {
            return std::get<stmt::VariableDecl>(variant);
        }
        const stmt::VariableDecl& get_variable_decl() const {
            return std::get<stmt::VariableDecl>(variant);
        }
        stmt::Assignment& get_assignment() {
            return std::get<stmt::Assignment>(variant);
        }
        const stmt::Assignment& get_assignment() const {
            return std::get<stmt::Assignment>(variant);
        }
        stmt::Block& get_block() {
            return std::get<stmt::Block>(variant);
        }
        const stmt::Block& get_block() const {
            return std::get<stmt::Block>(variant);
        }
        stmt::Expression& get_expr() {
            return std::get<stmt::Expression>(variant);
        }
        const stmt::Expression& get_expr() const {
            return std::get<stmt::Expression>(variant);
        }
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
    std::optional<Expression> parse_expression(TokenParser& parser);
    std::optional<Type> parse_type(TokenParser& parser);
    std::optional<Variable> parse_variable_declaration(TokenParser& parser);
    std::optional<FunctionParameter> parse_function_param(TokenParser& parser);
    std::optional<Statement> parse_statement(TokenParser& parser);
    std::optional<Function> parse_function(TokenParser& parser);
    std::optional<Program> parse_program(TokenParser& parser);
    std::optional<Program> parse(std::span<Token> src);
}
