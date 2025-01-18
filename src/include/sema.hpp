#pragma once
#include "ast.hpp"
#include "utils.hpp"
#include <cassert>
#include <cmath>
#include <memory>
#include <variant>
#include <vector>

namespace sema {
    struct Type;
    namespace type {
        struct Void {};
        struct Integer {};
        struct Pointer {
            ref<Type> next;
        };
        struct Reference {
            ref<Type> next;
        };
        struct LValue {
            ref<Type> next;
        };
    }
    struct Type {
        std::variant<type::Void, type::Integer, type::Pointer, type::Reference, type::LValue> variant;
        bool is_void() const {
            return std::holds_alternative<type::Void>(variant);
        }
        bool is_integer() const {
            return std::holds_alternative<type::Integer>(variant);
        }
        bool is_pointer() const {
            return std::holds_alternative<type::Pointer>(variant);
        }
        bool is_reference() const {
            return std::holds_alternative<type::Reference>(variant);
        }
        bool is_lvalue() const {
            return std::holds_alternative<type::LValue>(variant);
        }
        bool can_be_deref() const {
            return is_pointer() || is_reference();
        }
        Type& deref() const {
            return is_pointer() ?
            *get_pointer().next
            : *get_reference().next;
        }
        Type& deref_lvalue() {
            return is_lvalue() ?
                *get_lvalue().next
                : *this;
        }
        const Type& deref_lvalue() const {
            return is_lvalue() ?
                *get_lvalue().next
                : *this;
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
        type::LValue& get_lvalue() {
            return std::get<type::LValue>(variant);
        }
        const type::LValue& get_lvalue() const {
            return std::get<type::LValue>(variant);
        }
        usize size() const {
            return std::visit(Overload{
                [](const type::Void&) { return 0UL; },
                [](const type::Pointer&) { return sizeof(void *); },
                [](const type::Reference&) { return sizeof(void *); },
                [](const type::LValue& lvalue) -> usize { assert(false && "invalid operation"); },
                [](const type::Integer&) { return sizeof(int); },
            }, variant);
        }
        usize alignment() const {
            return std::visit(Overload{
                [](const type::Void&) { return 0UL; },
                [](const type::Pointer&) { return alignof(void *); },
                [](const type::Reference&) { return alignof(void *); },
                [](const type::LValue& lvalue) -> usize { assert(false && "invalid operation"); },
                [](const type::Integer&) { return alignof(int); },
            }, variant);
        }
        static bool equal(const Type& a, const Type& b) {
            return &a == &b;
        }
    };
    struct TypeTable {
        using pair = std::pair<std::vector<ast::Identifier>, std::unique_ptr<Type>>;
        std::vector<pair> types_database;
        TypeTable() {
            types_database.emplace_back(
                std::vector<std::string_view>({"int", "i32"}), std::make_unique<Type>(Type{
                    .variant = type::Integer{}
                })
            );
            types_database.emplace_back(
                std::vector<std::string_view>({"void"}), std::make_unique<Type>(Type{
                    .variant = type::Void{}
                })
            );
        }
        Type * lookup(const ast::Type& type);
        Type * lookup_identifier(const ast::Identifier& iden);
        Type& get_pointer_to(Type& type);
        Type& get_reference_to(Type& type);
        Type& get_lvalue_to(Type& type);
        Type& get_integer();
        Type& get_void_pointer();
        Type& get_void();
    };
    struct FunctionType {
        std::vector<ref<Type>> parameters;
        ref<Type> return_type;
    };
    struct Variable {
        ast::Identifier iden;
        ref<Type> type;
    };
    struct Expression;
    namespace expr {
        struct Literal {
            enum { INTEGER, NULLPTR } type;
            usize integer;
        };
        struct Variable {
            ref<sema::Variable> var;
        };
        struct Deref {
            std::unique_ptr<Expression> next;
        };
        struct AddrOf {
            std::unique_ptr<Expression> next;
        };
    }
    struct Expression {
        std::variant<expr::Literal, expr::Variable, expr::AddrOf, expr::Deref> variant;
        ref<Type> type;
        bool is_literal() const {
            return std::holds_alternative<expr::Literal>(variant);
        }
        bool is_variable() const {
            return std::holds_alternative<expr::Variable>(variant);
        }
        bool is_addr_of() const {
            return std::holds_alternative<expr::AddrOf>(variant);
        }
        bool is_deref() const {
            return std::holds_alternative<expr::Deref>(variant);
        }
        expr::Literal& get_literal() {
            return std::get<expr::Literal>(variant);
        }
        const expr::Literal& get_literal() const {
            return std::get<expr::Literal>(variant);
        }
        expr::Variable& get_variable() {
            return std::get<expr::Variable>(variant);
        }
        const expr::Variable& get_variable() const {
            return std::get<expr::Variable>(variant);
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
    };
    struct Statement;
    struct Function;
    struct Frame {
        std::vector<std::unique_ptr<Variable>> parameters;
        std::vector<std::unique_ptr<Variable>> variables;
        std::vector<Statement> statements;
        enum { GLOBAL, FUNCTION_BASE, SCOPED } type;
        Frame * parent;
        Variable * lookup(const ast::Identifier& iden);
        Variable& push_variable(Variable new_var, TypeTable& table);
        Frame new_child();
        void push_function_args(const FunctionType& function, const ast::Function& ast, TypeTable& table);
    };

    namespace stmt {
        struct Return {
            std::optional<Expression> value;
        };
        struct Assignment {
            Expression target;
            Expression value;
        };
    }
    struct Statement {
        std::variant<stmt::Return, stmt::Assignment> variant;
        bool is_return() const {
            return std::holds_alternative<stmt::Return>(variant);
        }
        bool is_assignment() const {
            return std::holds_alternative<stmt::Assignment>(variant);
        }
        stmt::Return& get_return() {
            return std::get<stmt::Return>(variant);
        }
        const stmt::Return& get_return() const {
            return std::get<stmt::Return>(variant);
        }
        stmt::Assignment& get_assignment() {
            return std::get<stmt::Assignment>(variant);
        }
        const stmt::Assignment& get_assignment() const {
            return std::get<stmt::Assignment>(variant);
        }
    };

    struct Function {
        FunctionType type;
        ast::Identifier identifier;
        Frame frame;
    };

    struct SymbolTable {
        TypeTable types;
        std::vector<Function> functions;
    };

    std::optional<Expression>
    parse_expression(ast::Expression& expr, TypeTable& table, Frame& frame);

    std::optional<Statement>
    parse_statement(ast::Statement& statement, TypeTable& type_table, Frame& frame);

    std::optional<std::vector<Statement>>
    parse_statements(
        std::span<ast::Statement> statements, TypeTable& type_table, FunctionType& type, Frame& frame);

    std::optional<Function>
    parse_function(ast::Function& function, TypeTable& type_table);

    std::optional<SymbolTable>
    parse(ast::Program& program);
}
