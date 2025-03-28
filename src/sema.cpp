#include "include/sema.hpp"
#include "include/ast.hpp"
#include "include/debug.hpp"
#include "include/utils.hpp"
#include <algorithm>
#include <array>
#include <cassert>
#include <memory>
#include <optional>
#include <ranges>
#include <string_view>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

namespace sema {
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
                if (!from.is_integer() || !to.is_integer()) {
                    return false;
                }
                auto& ifrom = from.get_integer();
                auto& ito = to.get_integer();
                return ifrom.size() == ito.size();
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
                return from.is_integer() && to.is_integer();
                // the above cases should handle casts to larger integers
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

    TypeTable::TypeTable() {
        assert(IntegerKind::U8 == IntegerKind::BOOL);
        types_database.resize(4);
        types_database.emplace_back(
            std::vector<std::string_view>({"void"}), unique_ptr_wrap(Type{
                .variant = type::Void{}
            })
        );
        types_database.emplace_back(
            std::vector<std::string_view>({"i8"}), unique_ptr_wrap(Type{
                type::Integer { IntegerKind::I8 }
            })
        );
        types_database.emplace_back(
            std::vector<std::string_view>({"i16"}), unique_ptr_wrap(Type{
                type::Integer { IntegerKind::I16 }
            })
        );
        types_database.emplace_back(
            std::vector<std::string_view>({"int", "i32"}), unique_ptr_wrap(Type{
                type::Integer { IntegerKind::I32 }
            })
        );
        types_database.emplace_back(
            std::vector<std::string_view>({"isize, i64"}), unique_ptr_wrap(Type{
                type::Integer{ IntegerKind::I64 }
            })
        );
        types_database.emplace_back(
            std::vector<std::string_view>({"u8", "bool"}), unique_ptr_wrap(Type{
                type::Integer{ IntegerKind::U8 }
            })
        );
        types_database.emplace_back(
            std::vector<std::string_view>({"u32"}), unique_ptr_wrap(Type{
                type::Integer{ IntegerKind::U32 }
            })
        );
        types_database.emplace_back(
            std::vector<std::string_view>({"usize, u64"}), unique_ptr_wrap(Type{
                type::Integer{ IntegerKind::U64 }
            })
        );
    }

    Type * TypeTable::lookup(const ast::Type& type) {
        if (type.is_identifier()) {
            return lookup_identifier(type.get_identifier());
        } else if (type.is_pointer()) {
            return &get_pointer_to(TRY(lookup(*type.get_pointer().next)));
        } else if (type.is_reference()) {
            return &get_reference_to(TRY(lookup(*type.get_reference().next)));
        } else if (type.is_function()) {
            auto& fun = type.get_function();
            auto& ret_type = TRY(lookup(*fun.return_type));
            std::vector<ref<Type>> params{};
            for (auto& type : fun.parameter_types) {
                params.push_back(ref(TRY(lookup(type))));
            }
            return &get_function_to(ret_type, params);
        } else {
            std::unreachable();
        }
    }

    Type * TypeTable::lookup_identifier(const ast::Identifier& iden) {
        for (auto& [idens, otype] : types_database) {
            if (std::find(idens.begin(), idens.end(), iden) != idens.end()) {
                return otype.get();
            }
        }
        return nullptr;
    }

    Type& TypeTable::get_pointer_to(Type& type) {
        if (type.is_lvalue()) {
            return get_pointer_to(*type.get_lvalue().next);
        }
        for (auto& [_, otype] : types_database) {
            if (otype->is_pointer() && Type::equal(*otype->get_pointer().next, type)) {
                return *otype;
            }
        }
        return *types_database.emplace_back(pair{
            {},
            unique_ptr_wrap(Type {
                .variant = type::Pointer {
                    .next = ref(type)
                }
            })
        }).second;
    }

    Type& TypeTable::get_reference_to(Type& type) {
        if (type.is_lvalue()) {
            return get_reference_to(*type.get_lvalue().next);
        }
        for (auto& [_, otype] : types_database) {
            if (otype->is_reference() && Type::equal(*otype->get_reference().next, type)) {
                return *otype;
            }
        }
        return *types_database.emplace_back(pair{
            {},
            unique_ptr_wrap(Type {
                .variant = type::Reference {
                    .next = ref(type)
                }
            })
        }).second;
    }

    Type& TypeTable::get_lvalue_to(Type& type) {
        if (type.is_lvalue()) {
            return type;
        }
        for (auto& [_, otype] : types_database) {
            if (otype->is_lvalue() && Type::equal(*otype->get_lvalue().next, type)) {
                return *otype;
            }
        }
        return *types_database.emplace_back(pair{
            {},
            unique_ptr_wrap(Type {
                .variant = type::LValue {
                    .next = ref(type)
                }
            })
        }).second;
    }

    Type& TypeTable::get_function_to(Type& ret, std::span<ref<Type>> types) {
        for (auto& [_, otype] : types_database) {
            if (!otype->is_function()) {
                continue;
            }
            auto& fun = otype->get_function();
            if (!Type::equal(*fun.return_type, ret) || fun.parameters.size() != types.size()) {
                continue;
            }
            for (auto [a, b] : std::views::zip(types, fun.parameters)) {
                assert(!a->is_lvalue());
                if (!Type::equal(*a, *b)) {
                    continue;
                }
            }
            return *otype;
        }
        DEBUG(for (auto& type : types) {
            assert(!type->is_lvalue());
        });
        return *types_database.emplace_back(pair{
            {},
            unique_ptr_wrap(Type {
            .variant = type::Function {
                    .parameters = types | std::ranges::to<std::vector<ref<Type>>>(),
                    .return_type = ref(ret),
                }
            })
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

    Type& TypeTable::get_void_pointer() {
        return get_pointer_to(get_void());
    }

    Symbol * Frame::lookup(const ast::Identifier& iden) {
        for (auto& var : std::views::reverse(symbols)) {
            if (var->get_identifier() == iden) {
                return var.get();
            }
        }
        if (type == SCOPED || type == FUNCTION_BASE) {
            return parent->lookup(iden);
        }
        return nullptr;
    }

    Symbol& Frame::push_symbol(Symbol symbol, TypeTable& table) {
        if (symbol.is_variable()) {
            symbol.get_variable().offset = scope_level;
        }
        symbol.get_type() = table.get_lvalue_to(symbol.get_type());
        return *symbols.emplace_back(unique_ptr_wrap(std::move(symbol)));
    }

    Frame& Frame::new_child() {
        auto new_frame = unique_ptr_wrap(Frame {
            .children = {},
            .symbols = {},
            .statements = {},
            .type = SCOPED,
            .parent = this,
            .scope_level = scope_level + 1,
        });
        return *children.emplace_back(std::move(new_frame));
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

    void Frame::push_function_args(const FunctionType& function, const ast::Function& ast, TypeTable& table) {
        for (auto [type, ast] : std::views::zip(function.parameters, ast.args)) {
            push_symbol(Symbol {
                .variant = symb::Parameter({
                    .type = ref(table.get_lvalue_to(*type)),
                    .identifier = ast.iden.value_or(""),
                }),
            }, table);
        }
    }

    auto type_coerce(Expression target, Type& type)
    -> std::optional<Expression> {
        auto& target_type_deref = target.type->deref_lvalue();
        auto& type_deref = type.deref_lvalue();
        if (Type::equal(target_type_deref, type_deref)) {
            return std::optional{ std::move(target) };
        }
        auto& conversion = TRY(conversion_table.validate_implicit(target_type_deref, type_deref));
        return Expression {
            .variant = expr::Conversion {
                .next = unique_ptr_wrap(std::move(target)),
                .conversion_type = ref(conversion),
            },
            .type = ref(type_deref)
        };
    }

    auto parse_expression(const ast::Expression& expr, TypeTable& table, Frame& frame) -> std::optional<Expression> {
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
                    .type = ref(table.get_integer(IntegerKind::I32))
                };
            } else if (lit.is_nullptr()) {
                return Expression {
                    .variant = expr::Literal {
                        .variant = lit::Nullptr {}
                    },
                    .type = ref(table.get_pointer_to(table.get_void()))
                };
            } else if (lit.is_true()) {
                return Expression {
                    .variant = expr::Literal {
                        .variant = lit::Integer {
                            .uvalue = true,
                            .type = IntegerKind::BOOL,
                        }
                    },
                    .type = ref(table.get_integer(IntegerKind::BOOL))
                };
            } else if (lit.is_false()) {
                return Expression {
                    .variant = expr::Literal {
                        .variant = lit::Integer {
                            .uvalue = false,
                            .type = IntegerKind::BOOL,
                        }
                    },
                    .type = ref(table.get_integer(IntegerKind::BOOL))
                };
            } else {
                std::unreachable();
            }
        }
        if (expr.is_identifier()) {
            auto& var = TRY(frame.lookup(expr.get_identifier()));
            return Expression {
                .variant = expr::Symbol {
                    .var = ref(var)
                },
                .type = ref(var.get_type()),
            };
        }
        if (expr.is_addr_of()) {
            auto& next_ast = *expr.get_addr_of().next;
            auto next = TRY(parse_expression(next_ast, table, frame));
            if (!next.type->is_lvalue()) {
                std::println(stderr, "invalid addr of");
                return std::nullopt;
            }
            return Expression {
                .variant = expr::AddrOf {
                    .next = unique_ptr_wrap(std::move(next))
                },
                .type = ref(table.get_reference_to(*next.type))
            };
        }
        if (expr.is_deref()) {
            auto next = TRY(parse_expression(*expr.get_deref().next, table, frame));
            if (!next.type->deref_lvalue().can_be_deref()) {
                std::println(stderr, "tried to deref a non-pointer type");
                return std::nullopt;
            }
            return Expression {
                .variant = expr::Deref {
                    .next = unique_ptr_wrap(std::move(next)),
                },
                .type = ref(next.type->deref_lvalue().deref())
            };
        }
        if (expr.is_as()) {
            auto& as_ast = expr.get_as();
            auto expr = TRY(parse_expression(*as_ast.next, table, frame));
            auto& to = TRY(table.lookup(as_ast.type));
            auto& conversion = TRY(conversion_table.validate_explicit(expr.type->deref_lvalue(), to));
            return Expression {
                .variant = expr::Conversion {
                    .next = unique_ptr_wrap(std::move(expr)),
                    .conversion_type = ref(conversion),
                },
                .type = ref(to),
            };
        }
        if (expr.is_unary()) {
            auto& unary = expr.get_unary();
            auto next = TRY(parse_expression(*unary.next, table, frame));
            if (!next.type->is_integer()) {
                std::println(stderr, "invalid type in unary operation");
                return std::nullopt;
            }
            auto type = ref(next.type->deref_lvalue());
            return Expression {
                .variant = expr::Unary {
                    .next = unique_ptr_wrap(std::move(next)),
                    .type = expr::Unary::MINUS,
                },
                .type = type
            };
        }
        if (expr.is_binary()) {
            auto& binary = expr.get_binary();
            auto a = TRY(parse_expression(*binary.a, table, frame));
            auto b = TRY(parse_expression(*binary.b, table, frame));
            if (!Type::equal(a.type->deref_lvalue(), b.type->deref_lvalue())) {
                std::println(stderr, "mismatched types in binary operation");
                return std::nullopt;
            }
            if (a.type->deref_lvalue().is_void()) {
                std::println(stderr, "invalid type in unary operation");
                return std::nullopt;
            }
            return Expression {
                .variant = expr::Binary {
                    .a = unique_ptr_wrap(std::move(a)),
                    .b = unique_ptr_wrap(std::move(b)),
                    .type = binary.type == ast::expr::Binary::ADD ? expr::Binary::ADD : expr::Binary::SUB
                },
                .type = ref(a.type->deref_lvalue())
            };
        }
        if (expr.is_funcall()) {
            auto& funcall = expr.get_funcall();
            auto fun = TRY(parse_expression(*funcall.fun, table, frame));
            auto& type = fun.type->get_function();
            if (funcall.args.size() != type.parameters.size()) {
                return std::nullopt;
            }
            std::vector<std::unique_ptr<Expression>> out{};
            for (usize i = 0; i < funcall.args.size(); ++i) {
                auto& arg = funcall.args[i];
                auto& atype = type.parameters[i].get();
                out.push_back(
                    unique_ptr_wrap(
                        TRY(type_coerce(
                            TRY(parse_expression(arg, table, frame)), atype))));
            }
            return Expression {
                .variant = expr::FunctionCall {
                    .function = unique_ptr_wrap(std::move(fun)),
                    .args = std::move(out),
                },
                .type = type.return_type,
            };
        }
        std::unreachable();
    }

    auto
    parse_statement(std::vector<Statement>& output,
        ast::Statement& statement, TypeTable& table,
        FunctionType& function_type, Frame& frame)
    -> std::optional<std::monostate>
    {
        auto parse_assignment = [&](ast::Expression& target, ast::Expression& value) -> std::optional<std::monostate> {
            auto expr1 = TRY(parse_expression(target, table, frame));
            auto expr2 = TRY(parse_expression(value, table, frame));
            if (!expr1.type->is_lvalue()) {
                std::println(stderr, "invalid assignment");
                return std::nullopt;
            }
            output.push_back(Statement {
                .variant = stmt::Assignment {
                    .target = std::move(expr1),
                    .value = TRY(type_coerce(std::move(expr2), *expr1.type)),
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
                        TRY(parse_expression(*return_stmt.value, table, frame)
                            .and_then([&](Expression expr) {
                                return type_coerce(std::move(expr), *function_type.return_type);
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
                    .type = ref(TRY(table.lookup(var_decl.type))),
                    .identifier = var_decl.identifier,
                    .offset = 0,
                }),
            }, table);
            if (var_decl.value) {
                output.push_back(Statement {
                    .variant = stmt::Assignment {
                            .target = Expression {
                                .variant = expr::Symbol {
                                .var = ref(var)
                            },
                            .type = ref(var.get_type()),
                        },
                        .value = TRY(parse_expression(*var_decl.value, table, frame)
                            .and_then([&](Expression expr) {
                                return type_coerce(std::move(expr), var.get_type().deref_lvalue());
                            }))
                    }
                });
            }
            return std::monostate{};
        } else if (statement.is_block()) {
            auto& sub_frame = frame.new_child();
            auto block = TRY(parse_statements(statement.get_block(), table, function_type, sub_frame));
            output.push_back(Statement {
                .variant = std::move(block)
            });
            return std::monostate{};
        } else if (statement.is_expr()) {
            auto& expr = statement.get_expr();
            output.push_back(Statement {
                .variant = TRY(parse_expression(expr, table, frame))
            });
            return std::monostate{};
        }
        std::unreachable();
    }

    auto parse_statements(std::span<ast::Statement> statements, TypeTable& type_table, FunctionType& function_type, Frame& frame)
    -> std::optional<std::vector<Statement>> {
        std::vector<Statement> output;
        for (auto& statement : statements) {
            TRY(parse_statement(output, statement, type_table, function_type, frame));
        }
        return output;
    }

    auto parse_function_declaration(const ast::Function& function, SymbolTable& table) -> std::optional<Symbol> {
        auto& return_type = TRY(table.types.lookup(function.return_type));
        std::vector<ref<Type>> parameters;
        for (auto& arg : function.args) {
            parameters.push_back(ref(TRY(table.types.lookup(arg.type))));
        }
        auto& type = table.types.get_function_to(return_type, parameters);
        return Symbol {
            .variant = symb::Constant {
                symb::cnst::UnImplemented({
                    .type = ref(type),
                    .identifier = function.iden,
                })
            }
        };
    }

    auto parse_constant_declaration(const ast::Variable& variable, SymbolTable& table) -> std::optional<Symbol> {
        return Symbol {
            .variant = symb::Constant {
                symb::cnst::UnImplemented ({
                    .type = ref(TRY(table.types.lookup(variable.type))),
                    .identifier = variable.identifier,
                })
            }
        };
    }

    auto parse_function_implementation(symb::cnst::Function& function, ast::Function& ast_fun, SymbolTable& table)
    -> std::optional<std::monostate> {
        auto& type = function.type->get_function();
        Frame new_frame {
            .children = {},
            .symbols = {},
            .statements = {},
            .type = Frame::FUNCTION_BASE,
            .parent = &table.global_frame,
            .scope_level = 1,
        };
        new_frame.push_function_args(type, ast_fun, table.types);
        new_frame.statements = TRY(parse_statements(ast_fun.body, table.types, type, new_frame));
        function = symb::cnst::Function ({
            .type = function.type,
            .identifier = std::move(function.identifier),
            .frame = std::move(new_frame),
        });
        return std::monostate{};
    }

    std::optional<Literal> evaluate_constant_expression(const Expression& expr, SymbolTable& table) {
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
                return helper(TRY(evaluate_constant_expression(*conversion.next, table)));
            },
            [&](const expr::Unary& unary) -> std::optional<IntegerHelper> {
                switch (unary.type) {
                case expr::Unary::MINUS:
                    auto integer = helper(TRY(evaluate_constant_expression(*unary.next, table)));
                    integer.u = -integer.u;
                    return integer;
                    break;
                }
                std::unreachable();
            },
            [&](const expr::Binary& binary) -> std::optional<IntegerHelper> {
                auto a = helper(TRY(evaluate_constant_expression(*binary.a, table)));
                auto b = helper(TRY(evaluate_constant_expression(*binary.b, table)));
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
                                        SymbolTable& table)
    -> std::optional<std::monostate> {
        (void)constant;
        auto& ast_expr = TRY(variable.value);
        auto expr = TRY(parse_expression(ast_expr, table.types, table.global_frame));
        auto value = TRY(evaluate_constant_expression(expr, table));
        constant = symb::cnst::Literal({
            .type = constant->type,
            .identifier = constant->identifier,
            .literal = std::move(value),
        });
        return std::monostate{};
    }

    auto parse(ast::Program& program) -> std::optional<SymbolTable> {
        SymbolTable table = {
            .global_frame = {
                .children = {},
                .symbols = {},
                .statements = {},
                .type = Frame::GLOBAL,
                .parent = nullptr,
                .scope_level = 0
            },
            .types = {},
        };
        for (auto& function : program.functions) {
            auto new_symbol = TRY(parse_function_declaration(function, table));
            table.global_frame.push_symbol(std::move(new_symbol), table.types);
        }
        for (auto& variable : program.variables) {
            auto& symbol = TRY(table.global_frame.lookup(variable.identifier));
            parse_constant_implementation(symbol.get_constant(), variable, table);
        }
        for (auto& function : program.functions) {
            auto& symbol = TRY(table.global_frame.lookup(function.iden));
            parse_function_implementation(symbol.get_constant().get_function(), function, table);
        }
        return table;
    }

    symb::cnst::Function::Function(Init init)
    : Base(init.type, std::move(init.identifier)), frame(std::move(init.frame))
    {}
}
