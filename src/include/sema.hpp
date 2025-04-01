#pragma once
#include "arena.hpp"
#include "arena_chunk_list.hpp"
#include "ast.hpp"
#include "debug.hpp"
#include "numbers.hpp"
#include "small_vector.hpp"
#include "utils.hpp"
#include <cassert>
#include <cmath>
#include <span>
#include <utility>
#include <variant>

namespace sema {
    class LexerState;
    enum class IntegerKind {
        U8 = 0, U16 = 1, U32 = 2, U64 = 3, I8 = 4, I16 = 5, I32 = 6, I64 = 7, BOOL = U8,
    };
    struct Type;
    namespace type {
        struct Void {};
        struct Integer {
            IntegerKind type;
            bool is_signed() const {
                return std::to_underlying(type) >= 4;
            }
            bool is_unsigned() const {
                return std::to_underlying(type) < 4;
            }
            usize size() const {
                return std::pow<usize>(2, std::to_underlying(type) % 4);
            }
            usize align() const {
                return size();
            }
        };
        struct Function {
            std::span<ref<Type>> parameters;
            ref<Type> return_type;
        };
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
        std::variant<type::Void, type::Integer,
            type::Pointer, type::Reference, type::Function> variant;
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
        bool is_function() const {
            return std::holds_alternative<type::Function>(variant);
        }
        bool can_be_deref() const {
            return is_pointer() || is_reference();
        }
        bool is_tangible() const {
            return !(is_function() || is_void());
        }
        bool is_integer_like() const {
            return is_integer() || can_be_deref();
        }
        Type& deref() const {
            return is_pointer() ?
            *get_pointer().next
            : *get_reference().next;
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
        type::Function& get_function() {
            return std::get<type::Function>(variant);
        }
        const type::Function& get_function() const {
            return std::get<type::Function>(variant);
        }
        type::Integer& get_integer() {
            return std::get<type::Integer>(variant);
        }
        const type::Integer& get_integer() const {
            return std::get<type::Integer>(variant);
        }
        usize size() const {
            return std::visit(Overload{
                [](const type::Void&) { return 0UL; },
                [](const type::Pointer&) { return sizeof(void *); },
                [](const type::Reference&) { return sizeof(void *); },
                [](const type::Function&) -> usize { DEBUG_ERROR("invalid operation on incomplete type"); },
                [](const type::Integer& integer) { return integer.size(); },
            }, variant);
        }
        usize alignment() const {
            return std::visit(Overload{
                [](const type::Void&) { return 0UL; },
                [](const type::Pointer&) { return alignof(void *); },
                [](const type::Reference&) { return alignof(void *); },
                [](const type::Function&) -> usize { DEBUG_ERROR("invalid operation on incomplete type"); },
                [](const type::Integer& integer) { return integer.align(); },
            }, variant);
        }
        static bool equal(const Type& a, const Type& b) {
            return &a == &b;
        }
    };
    class TypeTable {
        using pair = std::pair<ArenaChunkList<ast::Identifier, 4>, Type>;
        ArenaChunkList<pair, 8> types_database;
    public:
        TypeTable(Arena& arena);
        Type * lookup(const ast::Type& type, Arena& arena);
        Type * lookup_identifier(const ast::Identifier& iden);
        Type& get_pointer_to(Type& type, Arena& arena);
        Type& get_reference_to(Type& type, Arena& arena);
        Type& get_function_to(Type& ret, std::span<ref<Type>> types, Arena& arena);
        Type& get_integer(IntegerKind);
        Type& get_void();
    };
    struct Conversion {
        enum {
            BITCAST, // same representation in memory
            SIGN_EXTEND, // signed extension of smaller integer
            ZERO_EXTEND, // unsigned extension of smaller integer
            TRUNCATE // truncation of larger integer
        } type;
        bool implicit; // whether the conversion has to be done with the 'as' keyword
        bool(*validate)(Type& from, Type& to); // virtual polymorphic check for compatability
    };
    struct ConversionTable {
        std::span<Conversion> conversions;
        Conversion * validate(Type& a, Type& b, bool implicit);
        Conversion * validate_explicit(Type& a, Type& b) {
            return validate(a, b, false);
        }
        Conversion * validate_implicit(Type& a, Type& b) {
            return validate(a, b, true);
        }
    };
    extern ConversionTable conversion_table;
    using FunctionType = type::Function;
    struct Expression;
    struct Symbol;
    struct Statement;

    struct Frame {
        SmallVector<Frame> children;
        SmallVector<Symbol> symbols;
        SmallVector<Statement> statements;
        enum Type { GLOBAL, FUNCTION_BASE, SCOPED } type;
        Frame * parent;
        usize scope_level;
        Symbol * lookup(const ast::Identifier& iden);
        Symbol& push_symbol(Symbol symbol);
        Frame& new_child(Arena& arena, usize children_cap, usize symbol_cap, usize statement_cap);
        void push_function_args(const type::Function& function, const ast::expr::Function& ast);
    };

    namespace lit {
        struct Nullptr {};
        struct Integer {
            union {
                usize uvalue;
                isize ivalue;
            };
            IntegerKind type;
            bool is_signed() const {
                return std::to_underlying(type) >= 4;
            }
            bool is_unsigned() const {
                return std::to_underlying(type) < 4;
            }
            usize size() const {
                return std::pow<usize>(2, std::to_underlying(type) % 4);
            }
            usize align() const {
                return size();
            }
        };
        struct Function {
            ref<Type> type;
            Frame frame;
        };
    }
    struct Literal {
        std::variant<lit::Nullptr, lit::Integer, lit::Function> variant;
        bool is_nullptr() const {
            return std::holds_alternative<lit::Nullptr>(variant);
        }
        bool is_integer() const {
            return std::holds_alternative<lit::Integer>(variant);
        }
        bool is_function() const {
            return std::holds_alternative<lit::Function>(variant);
        }
        lit::Integer& get_integer() {
            return std::get<lit::Integer>(variant);
        }
        const lit::Integer& get_integer() const {
            return std::get<lit::Integer>(variant);
        }
        lit::Function& get_function() {
            return std::get<lit::Function>(variant);
        }
        const lit::Function& get_function() const {
            return std::get<lit::Function>(variant);
        }
    };
    namespace expr {
        using Literal = sema::Literal;
        struct Symbol {
            ref<sema::Symbol> var;
        };
        struct Deref {
            ref<Expression> next;
        };
        struct AddrOf {
            ref<Expression> next;
        };
        struct Conversion {
            ref<Expression> next;
            ref<sema::Conversion> conversion_type;
        };
        struct Unary {
            ref<Expression> next;
            enum { MINUS } type;
        };
        struct Binary {
            ref<Expression> a;
            ref<Expression> b;
            enum Type { ADD, SUB } type;
        };
        struct FunctionCall {
            ref<Expression> function;
            std::span<Expression> args;
        };
    }

    struct Expression {
        std::variant<
            expr::Literal, expr::Symbol, expr::AddrOf, expr::Deref,
            expr::Conversion, expr::Unary, expr::Binary, expr::FunctionCall> variant;
        ref<Type> type;
        bool is_lvalue;
        bool is_literal() const {
            return std::holds_alternative<expr::Literal>(variant);
        }
        bool is_symbol() const {
            return std::holds_alternative<expr::Symbol>(variant);
        }
        bool is_addr_of() const {
            return std::holds_alternative<expr::AddrOf>(variant);
        }
        bool is_deref() const {
            return std::holds_alternative<expr::Deref>(variant);
        }
        bool is_conversion() const {
            return std::holds_alternative<expr::Conversion>(variant);
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
        expr::Symbol& get_symbol() {
            return std::get<expr::Symbol>(variant);
        }
        const expr::Symbol& get_symbol() const {
            return std::get<expr::Symbol>(variant);
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
        expr::Conversion& get_conversion() {
            return std::get<expr::Conversion>(variant);
        }
        const expr::Conversion& get_conversion() const {
            return std::get<expr::Conversion>(variant);
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

    struct Statement;
    struct Symbol;

    namespace symb {
        struct Base {
            ref<Type> type;
            ast::Identifier identifier;
            Base(ref<Type> type, ast::Identifier identifier)
            : type(type), identifier(std::move(identifier)) {}
            struct Init {
                ref<Type> type;
                ast::Identifier identifier;
            };
            Base(Init init)
            : type(init.type), identifier(std::move(init.identifier)) {}
        };
        struct Variable : Base {
            struct Init {
                ref<Type> type;
                ast::Identifier identifier;
                usize offset;
            };
            usize offset;
            Variable(Init init)
            : Base(init.type, init.identifier), offset(init.offset)
            {}
        };
        struct Parameter : Base {
            using Base::Base;
        };
        namespace cnst {
            struct Literal : Base {
                struct Init {
                    ref<Type> type;
                    ast::Identifier identifier;
                    sema::Literal literal;
                };
                sema::Literal literal;
                Literal(Init init)
                : Base(init.type, std::move(init.identifier)), literal(std::move(init.literal)) {}
            };
            struct UnImplemented : Base {
                using Base::Base;
            };
        }
        class Constant : public poly_variant<Base, cnst::Literal, cnst::UnImplemented> {
            using BaseType = poly_variant<Base, cnst::Literal, cnst::UnImplemented>;
        public:
            using BaseType::BaseType;
            bool is_literal() const {
                return std::holds_alternative<cnst::Literal>(*this);
            }
            bool is_unimplemented() const {
                return std::holds_alternative<cnst::UnImplemented>(*this);
            }
            cnst::Literal& get_literal() {
                return std::get<cnst::Literal>(*this);
            }
            const cnst::Literal& get_literal() const {
                return std::get<cnst::Literal>(*this);
            }
        };
    }

    struct Symbol {
        poly_variant<symb::Base, symb::Variable, symb::Constant, symb::Parameter> variant;
        bool is_variable() const {
            return std::holds_alternative<symb::Variable>(variant);
        }
        bool is_constant() const {
            return std::holds_alternative<symb::Constant>(variant);
        }
        bool is_parameter() const {
            return std::holds_alternative<symb::Parameter>(variant);
        }
        symb::Variable& get_variable() {
            return std::get<symb::Variable>(variant);
        }
        const symb::Variable& get_variable() const {
            return std::get<symb::Variable>(variant);
        }
        symb::Constant& get_constant() {
            return std::get<symb::Constant>(variant);
        }
        const symb::Constant& get_constant() const {
            return std::get<symb::Constant>(variant);
        }
        Type& get_type() {
            return *variant->type;
        }
        const Type& get_type() const {
            return *variant->type;
        }
        ast::Identifier& get_identifier() {
            return variant->identifier;
        }
        const ast::Identifier& get_identifier() const {
            return variant->identifier;
        }
    };

    namespace stmt {
        struct Return {
            std::optional<Expression> value;
        };
        struct Assignment {
            Expression target;
            Expression value;
        };
        using Expression = sema::Expression;
        using Block = std::span<Statement>;
    }
    struct Statement {
        std::variant<stmt::Return, stmt::Assignment, stmt::Block, stmt::Expression> variant;
        bool is_return() const {
            return std::holds_alternative<stmt::Return>(variant);
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

    struct SymbolTable {
        Frame global_frame;
        TypeTable types;
    };

    class LexerState {
        ref<Arena> m_arena;
        ref<TypeTable> m_types;
        ref<Frame> m_frame;
    public:
        LexerState(Arena& arena, SymbolTable& table);
        LexerState(Arena&, TypeTable&, Frame&);
        Arena& arena() {
            return m_arena.get();
        }
        const Arena& arena() const {
            return m_arena.get();
        }
        TypeTable& type_table() {
            return m_types.get();
        }
        const TypeTable& type_table() const {
            return m_types.get();
        }
        Frame& frame() {
            return m_frame.get();
        }
        const Frame& frame() const {
            return m_frame.get();
        }
        LexerState construct_new_state(Frame& frame) {
            return LexerState(arena(), type_table(), frame);
        }
    };

    std::optional<Empty>
    parse_statements(SmallVector<Statement>& output,
        std::span<const ast::Statement> statements, type::Function& type, LexerState& state);

    std::optional<SymbolTable>
    parse(ast::Program& program, Arena& arena);
}
