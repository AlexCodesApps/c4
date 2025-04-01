#include "include/sema.hpp"
#include "include/arena.hpp"
#include "include/ast.hpp"
#include "include/small_vector.hpp"
#include "include/utils.hpp"
#include <algorithm>
#include <array>
#include <cassert>
#include <numeric>
#include <optional>
#include <ranges>
#include <string_view>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

namespace {
    sema::Frame& produce_frame(sema::Frame& parent, const ast::stmt::Block& block, Arena& arena) {
        usize children_cap =
            std::accumulate(block.begin(), block.end(), 0Ul,
                [](usize n, auto& s) -> usize { return n + s.is_block(); });
        usize symbol_cap =
            std::accumulate(block.begin(), block.end(), 0Ul,
                [](usize n, auto& s) -> usize { return n + s.is_variable_decl(); });
        usize statement_cap = block.size() + symbol_cap;
        return parent.new_child(arena, children_cap, symbol_cap, statement_cap);
    }
    template <typename T, typename F>
    std::optional<std::span<T>> simultaneous_initialize(usize n, F functor, Arena& arena) {
        auto span = arena.allocate_n_uninit<T>(n);
        for (auto& slot : span) {
            slot.construct(TRY(functor(n)));
        }
        return std::span(span[0].get(), n);
    };
}

namespace sema {
    LexerState::LexerState(Arena& arena, SymbolTable& table)
    : m_arena(ref(arena)), m_types(ref(table.types)), m_frame(ref(table.global_frame)) {}
    LexerState::LexerState(Arena& arena, TypeTable& types, Frame& frame)
    : m_arena(ref(arena)), m_types(ref(types)), m_frame(ref(frame)) {}

    auto conversion_array = std::to_array({
        Conversion {
            .type = Conversion::BITCAST,
            .implicit = true,
            /* A cast to itself... */
            .validate = [](Type& from, Type& to) {
                return Type::equal(from, to);
            }
        },
        Conversion {
            .type = Conversion::BITCAST,
            .implicit = true,
            /*
                references can safely be implicitly casted to pointer,
                but pointers have an invariant in the nullptr, so they must be
                explicitly cast to references
            */
            .validate = [](Type& from, Type& to) {
                return from.is_reference() && to.is_pointer()
                    && Type::equal(from.deref(), to.deref());
            }
        },
        Conversion {
            .type = Conversion::BITCAST,
            .implicit = false, // not implicit because of unsafe pointer cast
            .validate = [](Type& from, Type& to) {
                return from.can_be_deref() && to.can_be_deref();
            }
        },
        Conversion {
            .type = Conversion::BITCAST,
            .implicit = false, // unsigned to signed cast of same size and vice versa
            .validate = [](Type& from, Type& to) {
                if (!from.is_integer_like() || !to.is_integer_like()) { // support pointers and references too
                    return false;
                }
                return from.size() == to.size();
            }
        },
        Conversion {
            .type = Conversion::ZERO_EXTEND,
            .implicit = true,
            .validate = [](Type& from, Type& to) {
                if (!from.is_integer() || !to.is_integer()) {
                    return false;
                }
                auto& ifrom = from.get_integer();
                auto& ito = to.get_integer();
                if (!ito.is_unsigned() || !ifrom.is_unsigned()) {
                    return false;
                }
                if (ito.size() < ifrom.size()) {
                    return false;
                }
                return true;
            }
        },
        Conversion {
            .type = Conversion::ZERO_EXTEND, // lossy signed to bigger unsigned conv
            .implicit = false, // for obvious reasons
            .validate = [](Type& from, Type& to) {
                if (!from.is_integer() || !to.is_integer()) {
                    return false;
                }
                auto& ifrom = from.get_integer();
                auto& ito = to.get_integer();
                if (!ifrom.is_signed() || !ito.is_unsigned()) {
                    return false;
                }
                return ito.size() > ifrom.size();
            }
        },
        Conversion {
            .type = Conversion::SIGN_EXTEND,
            .implicit = true,
            .validate = [](Type& from, Type& to) {
                if (!from.is_integer() || !to.is_integer()) {
                    return false;
                }
                auto& ito = to.get_integer();
                auto& ifrom = from.get_integer();
                if (!ito.is_signed()) {
                    return false;
                }
                if (ito.size() <= ifrom.size()) {
                    return false;
                }
                return true;
            }
        },
        Conversion {
            .type = Conversion::TRUNCATE,
            .implicit = false, // lossy cast
            .validate = [](Type& from, Type& to) {
                return from.is_integer_like() && to.is_integer_like();
                // the above cases should handle casts to larger integers
                // pointer is 64 bit so doesn't need a zero / sign extend cast
            }
        },
    });
    ConversionTable conversion_table = {
        .conversions = conversion_array
    };

    Conversion * ConversionTable::validate(Type& a, Type& b, bool implicit) {
        for (auto [index, conversion] : std::views::enumerate(conversions)) {
            if (implicit) {
                /* When in implicit mode,
                    only implicit conversions are allowed.
                    when in explicit mode,
                    all conversions are allowed.
                */
                if (!conversion.implicit) {
                    std::println(stderr, "skipped {}", index);
                    continue;
                }
            }
            if (conversion.validate(a, b)) {
                std::println(stderr, "passed {}", index);
                return &conversion;
            } else {
                std::println(stderr, "failed {}", index);
            }
        }
        return nullptr;
    }

    TypeTable::TypeTable(Arena& arena) {
        assert(IntegerKind::U8 == IntegerKind::BOOL);
        types_database.emplace_back(arena,
            ArenaChunkList<std::string_view, 4>(arena, {"void"}), Type{
                .variant = type::Void{}
            }
        );
        types_database.emplace_back(arena,
            ArenaChunkList<std::string_view, 4>(arena, {"i8"}), Type{
                type::Integer { IntegerKind::I8 }
            }
        );
        types_database.emplace_back(arena,
            ArenaChunkList<std::string_view, 4>(arena, {"i16"}), Type{
                type::Integer { IntegerKind::I16 }
            }
        );
        types_database.emplace_back(arena,
            ArenaChunkList<std::string_view, 4>(arena, {"int", "i32"}), Type{
                type::Integer { IntegerKind::I32 }
            }
        );
        types_database.emplace_back(arena,
            ArenaChunkList<std::string_view, 4>(arena, {"isize, i64"}), Type{
                type::Integer{ IntegerKind::I64 }
            }
        );
        types_database.emplace_back(arena,
            ArenaChunkList<std::string_view, 4>(arena, {"u8", "bool"}), Type{
                type::Integer{ IntegerKind::U8 }
            }
        );
        types_database.emplace_back(arena,
            ArenaChunkList<std::string_view, 4>(arena, {"u32"}), Type{
                type::Integer{ IntegerKind::U32 }
            }
        );
        types_database.emplace_back(arena,
            ArenaChunkList<std::string_view, 4>(arena, {"usize, u64"}), Type{
                type::Integer{ IntegerKind::U64 }
            }
        );
    }

    Type * TypeTable::lookup(const ast::Type& type, Arena& arena) {
        if (type.is_identifier()) {
            return lookup_identifier(type.get_identifier());
        } else if (type.is_pointer()) {
            return &get_pointer_to(TRY(lookup(*type.get_pointer().next, arena)), arena);
        } else if (type.is_reference()) {
            return &get_reference_to(TRY(lookup(*type.get_reference().next, arena)), arena);
        } else if (type.is_function()) {
            auto& fun = type.get_function();
            auto& ret_type = TRY(lookup(*fun.return_type, arena));
            auto params =
                TRY(simultaneous_initialize<ref<Type>>(fun.parameter_types.size(),
                    [&](usize n) -> std::optional<ref<Type>>{
                        return ref(TRY(lookup(fun.parameter_types[n], arena)));
                    }, arena));
            return &get_function_to(ret_type, params, arena);
        } else {
            std::unreachable();
        }
    }

    Type * TypeTable::lookup_identifier(const ast::Identifier& iden) {
        for (auto& [idens, otype] : types_database) {
            for (auto& oiden : idens) {
                if (iden == oiden) {
                    return &otype;
                }
            }
        }
        return nullptr;
    }

    Type& TypeTable::get_pointer_to(Type& type, Arena& arena) {
        for (auto& [_, otype] : types_database) {
            if (otype.is_pointer() && Type::equal(*otype.get_pointer().next, type)) {
                return otype;
            }
        }
        return types_database.emplace_back(arena, pair{
            {},
            Type {
                .variant = type::Pointer {
                    .next = ref(type)
                }
            }
        }).second;
    }

    Type& TypeTable::get_reference_to(Type& type, Arena& arena) {
        for (auto& [_, otype] : types_database) {
            if (otype.is_reference() && Type::equal(*otype.get_reference().next, type)) {
                return otype;
            }
        }
        return types_database.emplace_back(arena, pair{
            {},
            Type {
                .variant = type::Reference {
                    .next = ref(type)
                }
            }
        }).second;
    }



    Type& TypeTable::get_function_to(Type& ret, std::span<ref<Type>> types, Arena& arena) {
        for (auto& [_, otype] : types_database) {
            if (!otype.is_function()) {
                continue;
            }
            auto& fun = otype.get_function();
            if (!Type::equal(*fun.return_type, ret) || fun.parameters.size() != types.size()) {
                continue;
            }
            for (auto [a, b] : std::views::zip(types, fun.parameters)) {
                if (!Type::equal(*a, *b)) {
                    continue;
                }
            }
            return otype;
        }
        return types_database.emplace_back(arena, pair{
            {},
            Type {
            .variant = type::Function {
                    .parameters = types,
                    .return_type = ref(ret),
                }
            }
        }).second;
    }

    Type& TypeTable::get_integer(IntegerKind type) {
        std::array<char, 3> buffer;
        auto n = std::to_underlying(type);
        buffer[0] = n < 4 ? 'i' : 'u';
        u8 l;
        if (n % 4 == 3) {
            buffer[1] = '6';
            buffer[2] = '4';
            l = 3;
        } else if (n % 4 == 2) {
            buffer[1] = '3';
            buffer[2] = '2';
            l = 3;
        } else if (n % 4 == 1) {
            buffer[1] = '1';
            buffer[2] = '6';
            l = 3;
        } else {
            buffer[1] = '8';
            l = 2;
        }
        Type * t = lookup_identifier(std::string_view(buffer.data(), l));
        assert(t);
        return *t;
    }

    Type& TypeTable::get_void() {
        Type * t = lookup_identifier("void");
        assert(t);
        return *t;
    }

    Symbol * Frame::lookup(const ast::Identifier& iden) {
        for (auto& var : std::views::reverse(symbols)) {
            if (var.get_identifier() == iden) {
                return &var;
            }
        }
        if (type == SCOPED || type == FUNCTION_BASE) {
            return parent->lookup(iden);
        }
        return nullptr;
    }

    Symbol& Frame::push_symbol(Symbol symbol) {
        if (symbol.is_variable()) {
            symbol.get_variable().offset = scope_level;
        }
        return symbols.emplace_back(std::move(symbol));
    }

    Frame& Frame::new_child(Arena& arena, usize children_cap, usize symbol_cap, usize statement_cap) {
        auto new_frame = Frame {
            .children = {arena, children_cap},
            .symbols = {arena, symbol_cap},
            .statements = {arena, statement_cap},
            .type = SCOPED,
            .parent = this,
            .scope_level = scope_level + 1,
        };
        return children.emplace_back(std::move(new_frame));
    }

    // fn(i32): i32
    // | ~~~~~~~~~~~~~~|
    // | i32 : size 4  |
    // | ~~~~~~~~~~~~~ |
    // | i32 : size 4  |
    // |~~~~~~~~~~~~~~~|
    // |               |
    // | ret : size 8  |
    // |               |
    // |~~~~~~~~~~~~~~~|
    // |               |
    // | rbp : size 8  |
    // |               |
    // |~~~~~~~~~~~~~~~|

    void Frame::push_function_args(const FunctionType& function, const ast::expr::Function& ast) {
        for (auto [type, ast] : std::views::zip(function.parameters, ast.args)) {
            push_symbol(Symbol {
                .variant = symb::Parameter({
                    .type = ref(*type),
                    .identifier = ast.identifier.value_or(""),
                }),
            });
        }
    }

    auto type_coerce(Expression target, Type& type, Arena& arena)
    -> std::optional<Expression> {
        auto& target_type = *target.type;
        if (Type::equal(target_type, type)) {
            return std::optional{ std::move(target) };
        }
        auto& conversion = TRY(conversion_table.validate_implicit(target_type, type));
        return Expression {
            .variant = expr::Conversion {
                .next = arena.wrap(std::move(target)),
                .conversion_type = ref(conversion),
            },
            .type = ref(type),
            .is_lvalue = false,
        };
    }

    auto type_coerce_binary(Expression a, Expression b, ast::expr::Binary::Type type, Arena& arena)
    -> std::optional<Expression> {
        if (!a.type->is_integer_like() || !b.type->is_integer_like()) {
            return std::nullopt;
        }
        auto impl = [&arena](Expression& a, Expression& b, ast::expr::Binary::Type type)
        -> std::optional<Expression>
        {
            auto helper = [&]{
                return Expression {
                    .variant = expr::Binary {
                        .a = arena.wrap(std::move(a)),
                        .b = arena.wrap(std::move(b)),
                        .type = (expr::Binary::Type)type
                    },
                    .type = a.type,
                    .is_lvalue = false,
                };
            };
            if (a.type->can_be_deref() && b.type->can_be_deref()) {
                return std::nullopt;
            }
            if (!Type::equal(*a.type, *b.type)) {
                return std::nullopt;
            }
            return helper();
        };
        if (auto value = impl(a, b, type)) {
            return value;
        } else {
            return impl(b, a, type);
        }
    }

    auto parse_expression(const ast::Expression& expr, LexerState& state) -> std::optional<Expression> {
        auto& type_table = state.type_table();
        auto& frame = state.frame();
        auto& arena = state.arena();
        if (expr.is_literal()) {
            auto& lit = expr.get_literal();
            if (lit.is_integer()) {
                return Expression {
                    .variant = expr::Literal {
                        .variant = lit::Integer {
                            .uvalue = lit.get_integer().value,
                            .type = IntegerKind::I32,
                        }
                    },
                    .type = ref(type_table.get_integer(IntegerKind::I32)),
                    .is_lvalue = false,
                };
            } else if (lit.is_nullptr()) {
                return Expression {
                    .variant = expr::Literal {
                        .variant = lit::Nullptr {}
                    },
                    .type = ref(type_table.get_pointer_to(type_table.get_void(), arena)),
                    .is_lvalue = false,
                };
            } else if (lit.is_true()) {
                return Expression {
                    .variant = expr::Literal {
                        .variant = lit::Integer {
                            .uvalue = true,
                            .type = IntegerKind::BOOL,
                        }
                    },
                    .type = ref(type_table.get_integer(IntegerKind::BOOL)),
                    .is_lvalue = false,
                };
            } else if (lit.is_false()) {
                return Expression {
                    .variant = expr::Literal {
                        .variant = lit::Integer {
                            .uvalue = false,
                            .type = IntegerKind::BOOL,
                        }
                    },
                    .type = ref(type_table.get_integer(IntegerKind::BOOL)),
                    .is_lvalue = false,
                };
            } else {
                std::unreachable();
            }
        } else if (expr.is_identifier()) {
            auto& var = TRY(frame.lookup(expr.get_identifier()));
            return Expression {
                .variant = expr::Symbol {
                    .var = ref(var)
                },
                .type = ref(var.get_type()),
                .is_lvalue = true,
            };
        } else if (expr.is_addr_of()) {
            auto& next_ast = *expr.get_addr_of().next;
            auto next = TRY(parse_expression(next_ast, state));
            if (!next.is_lvalue) {
                std::println(stderr, "invalid addr of");
                return std::nullopt;
            }
            return Expression {
                .variant = expr::AddrOf {
                    .next = arena.wrap(std::move(next))
                },
                .type = ref(type_table.get_reference_to(*next.type, arena)),
                .is_lvalue = false,
            };
        } else if (expr.is_deref()) {
            auto next = TRY(parse_expression(*expr.get_deref().next, state));
            if (!next.type->can_be_deref()) {
                std::println(stderr, "tried to deref a non-pointer type");
                return std::nullopt;
            }
            return Expression {
                .variant = expr::Deref {
                    .next = arena.wrap(std::move(next)),
                },
                .type = ref(next.type->deref()),
                .is_lvalue = true,
            };
        } else if (expr.is_as()) {
            auto& as_ast = expr.get_as();
            auto expr = TRY(parse_expression(*as_ast.next, state));
            auto& to = TRY(type_table.lookup(as_ast.type, arena));
            auto& conversion = TRY(conversion_table.validate_explicit(*expr.type, to));
            return Expression {
                .variant = expr::Conversion {
                    .next = arena.wrap(std::move(expr)),
                    .conversion_type = ref(conversion),
                },
                .type = ref(to),
                .is_lvalue = false,
            };
        } else if (expr.is_unary()) {
            auto& unary = expr.get_unary();
            auto next = TRY(parse_expression(*unary.next, state));
            if (!next.type->is_integer()) {
                std::println(stderr, "invalid type in unary operation");
                return std::nullopt;
            }
            auto type = next.type;
            return Expression {
                .variant = expr::Unary {
                    .next = arena.wrap(std::move(next)),
                    .type = expr::Unary::MINUS,
                },
                .type = type,
                .is_lvalue = false,
            };
        } else if (expr.is_binary()) {
            auto& binary = expr.get_binary();
            auto a = TRY(parse_expression(*binary.a, state));
            auto b = TRY(parse_expression(*binary.b, state));
            return type_coerce_binary(std::move(a), std::move(b), binary.type, arena);
        } else if (expr.is_funcall()) {
            auto& funcall = expr.get_funcall();
            auto fun = TRY(parse_expression(*funcall.fun, state));
            auto& type = fun.type->get_function();
            if (funcall.args.size() != type.parameters.size()) {
                return std::nullopt;
            }
            auto args = TRY(simultaneous_initialize<Expression>(funcall.args.size(),
                [&](usize n) {
                    auto& arg = funcall.args[n];
                    auto& atype = type.parameters[n].get();
                    return parse_expression(arg, state)
                        .and_then([&](auto t) { return type_coerce(std::move(t), atype, arena); });
                }, arena));
            return Expression {
                .variant = expr::FunctionCall {
                    .function = arena.wrap(std::move(fun)),
                    .args = args,
                },
                .type = type.return_type,
                .is_lvalue = false,
            };
        } else if (expr.is_function()) {
            auto& function = expr.get_function();
            auto& return_type = TRY(type_table.lookup(function.return_type, arena));

            auto args = TRY(simultaneous_initialize<ref<Type>>(function.args.size(),
                [&](usize n) -> std::optional<ref<Type>> {
                    auto& arg = function.args[n];
                    return ref(TRY(type_table.lookup(arg.type, arena)));
                }, arena));

            auto& function_type = type_table.get_function_to(return_type, args, arena);
            usize children_cap =
                std::accumulate(function.body.begin(), function.body.end(), 0UL,
                    [](usize size, auto& statement) -> usize { return size + statement.is_block(); });
            usize symbol_cap
                = std::accumulate(function.body.begin(), function.body.end(), 0UL,
                    [](usize size, auto& statement) -> usize { return size + statement.is_variable_decl(); });
            usize statement_cap = function.body.size() + symbol_cap;
            Frame new_frame = {
                .children = {arena, children_cap},
                .symbols = {arena, symbol_cap},
                .statements = {arena, statement_cap},
                .type = Frame::FUNCTION_BASE,
                .parent = &frame,
                .scope_level = 0,
            };
            frame.push_function_args(function_type.get_function(), function);
            auto nested_state = state.construct_new_state(new_frame);
            TRY(parse_statements(new_frame.statements, function.body, function_type.get_function(), nested_state));
        }
        std::unreachable();
    }

    auto
    parse_statement(SmallVector<Statement>& output,
        const ast::Statement& statement, FunctionType& function_type,
        LexerState& state)
    -> std::optional<std::monostate>
    {
        auto& frame = state.frame();
        auto& table = state.type_table();
        auto& arena = state.arena();
        auto parse_assignment = [&](const ast::Expression& target, const ast::Expression& value) -> std::optional<std::monostate> {
            auto expr1 = TRY(parse_expression(target, state));
            auto expr2 = TRY(parse_expression(value, state));
            if (!expr1.is_lvalue) {
                std::println(stderr, "invalid assignment");
                return std::nullopt;
            }
            output.push_back(Statement {
                .variant = stmt::Assignment {
                    .target = std::move(expr1),
                    .value = TRY(type_coerce(std::move(expr2), *expr1.type, arena)),
                }
            });
            return std::monostate{};
        };

        if (statement.is_return()) {
            auto& return_stmt = statement.get_return();
            if (return_stmt.value) {
                output.push_back(Statement {
                    .variant = stmt::Return {
                        .value =
                        TRY(parse_expression(*return_stmt.value, state)
                            .and_then([&](Expression expr) {
                                return type_coerce(std::move(expr), *function_type.return_type, arena);
                            }))
                    },
                });
                return std::monostate{};
            }
            output.push_back(Statement {
                .variant = stmt::Return {
                    .value = std::nullopt
                }
            });
            return std::monostate{};
        } else if (statement.is_assignment()) {
            auto& assignment = statement.get_assignment();
            return parse_assignment(assignment.target, assignment.value);
        } else if (statement.is_variable_decl()) {
            auto& var_decl = statement.get_variable_decl();
            auto& var = frame.push_symbol(Symbol{
                .variant = symb::Variable({
                    .type = ref(TRY(table.lookup(var_decl.type, arena))),
                    .identifier = var_decl.identifier,
                    .offset = 0,
                }),
            });
            if (var_decl.value) {
                output.push_back(Statement {
                        .variant = stmt::Assignment {
                            .target = Expression {
                                .variant = expr::Symbol {
                                .var = ref(var)
                            },
                            .type = ref(var.get_type()),
                            .is_lvalue = true,
                        },
                        .value = TRY(parse_expression(*var_decl.value, state)
                            .and_then([&](Expression expr) {
                                return type_coerce(std::move(expr), var.get_type(), arena);
                        }))
                    }
                });
            }
            return std::monostate{};
        } else if (statement.is_block()) {
            auto& sub_frame = produce_frame(frame, statement.get_block(), arena);
            auto sub_state = state.construct_new_state(sub_frame);
            TRY(parse_statements(sub_frame.statements, statement.get_block(), function_type, sub_state));
            output.push_back(Statement {
                .variant = std::span(sub_frame.statements),
            });
            return std::monostate{};
        } else if (statement.is_expr()) {
            auto& expr = statement.get_expr();
            output.push_back(Statement {
                .variant = TRY(parse_expression(expr, state))
            });
            return std::monostate{};
        }
        std::unreachable();
    }

    auto parse_statements(SmallVector<Statement>& output, std::span<const ast::Statement> statements,
        FunctionType& function_type, LexerState& state)
    -> std::optional<Empty> {
        for (auto& statement : statements) {
            TRY(parse_statement(output, statement, function_type, state));
        }
        return empty;
    }

    auto parse_constant_declaration(const ast::Variable& variable, LexerState& state) -> std::optional<Symbol> {
        return Symbol {
            .variant = symb::Constant {
                symb::cnst::UnImplemented ({
                    .type = ref(TRY(state.type_table().lookup(variable.type, state.arena()))),
                    .identifier = variable.identifier,
                })
            }
        };
    }

    std::optional<Literal> evaluate_constant_expression(const Expression& expr) {
        auto& type = expr.type.get();
        if (!type.is_integer()) {
            return std::nullopt;
        }
        auto& itype = type.get_integer();
        struct IntegerHelper {
            union {
                usize u;
                isize i;
            };
            enum Tag : u8 { U, I } tag;
        };
        auto helper = [](const Literal& literal) {
            if (literal.is_nullptr()) {
                return IntegerHelper { .u = 0, .tag = IntegerHelper::U };
            } else if (literal.is_integer()) {
                auto& integer = literal.get_integer();
                return IntegerHelper {
                    .u = integer.uvalue,
                    .tag = (IntegerHelper::Tag)integer.is_signed()
                };
            }
            std::unreachable();
        };
        auto value = TRY(std::visit(Overload {
            [&](const expr::Literal& literal) -> std::optional<IntegerHelper> {
                return helper(literal);
            },
            [&](const expr::Symbol& esymbol) -> std::optional<IntegerHelper> {
                auto& symbol = esymbol.var.get();
                if (!symbol.get_type().is_integer()) {
                    return std::nullopt;
                }
                auto& lit = symbol.get_constant().get_literal();
                return helper(lit.literal);
            },
            [](const expr::AddrOf&) -> std::optional<IntegerHelper> {
                return std::nullopt;
            },
            [](const expr::Deref&) -> std::optional<IntegerHelper> {
                return std::nullopt;
            },
            [&](const expr::Conversion& conversion) -> std::optional<IntegerHelper> {
                if (!expr.type->is_integer() || !conversion.next->type->is_integer()) {
                    return std::nullopt;
                }
                return helper(TRY(evaluate_constant_expression(*conversion.next)));
            },
            [&](const expr::Unary& unary) -> std::optional<IntegerHelper> {
                switch (unary.type) {
                case expr::Unary::MINUS:
                    auto integer = helper(TRY(evaluate_constant_expression(*unary.next)));
                    integer.u = -integer.u;
                    return integer;
                    break;
                }
                std::unreachable();
            },
            [&](const expr::Binary& binary) -> std::optional<IntegerHelper> {
                auto a = helper(TRY(evaluate_constant_expression(*binary.a)));
                auto b = helper(TRY(evaluate_constant_expression(*binary.b)));
                switch (binary.type) {
                case expr::Binary::ADD:
                    return IntegerHelper {
                        .u = a.u + b.u,
                        .tag = a.tag,
                    };
                    break;
                case expr::Binary::SUB:
                    return IntegerHelper {
                        .u = a.u + b.u,
                        .tag = a.tag,
                    };
                    break;
                }
                std::unreachable();
            },
            [](const expr::FunctionCall&) -> std::optional<IntegerHelper> {
                return std::nullopt;
            },
        }, expr.variant));
        return Literal {
            .variant = lit::Integer {
                .uvalue = value.u,
                .type = itype.type,
            }
        };
    }

    auto parse_constant_implementation(symb::Constant& constant, const ast::Variable& variable,
                                        LexerState& state)
    -> std::optional<std::monostate> {
        (void)constant;
        auto& ast_expr = TRY(variable.value);
        auto expr = TRY(parse_expression(ast_expr, state));
        auto value = TRY(evaluate_constant_expression(expr));
        constant = symb::cnst::Literal({
            .type = constant->type,
            .identifier = constant->identifier,
            .literal = std::move(value),
        });
        return std::monostate{};
    }

    auto parse(ast::Program& program, Arena& arena) -> std::optional<SymbolTable> {
        SymbolTable table = {
            .global_frame = {
                .children = {std::span<Uninitialized<Frame>>{}},
                .symbols = {arena, program.variables.size()},
                .statements = {std::span<Uninitialized<Statement>>{}},
                .type = Frame::GLOBAL,
                .parent = nullptr,
                .scope_level = 0
            },
            .types = TypeTable(arena),
        };
        LexerState state(arena, table);
        for (auto& variable : program.variables) {
            auto new_symbol = TRY(parse_constant_declaration(variable, state));
            table.global_frame.push_symbol(std::move(new_symbol));
        }
        for (auto& variable : program.variables) {
            auto& symbol = TRY(table.global_frame.lookup(variable.identifier));
            parse_constant_implementation(symbol.get_constant(), variable, state);
        }
        return table;
    }


}
