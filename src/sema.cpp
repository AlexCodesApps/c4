#include "include/sema.hpp"
#include "include/ast.hpp"
#include <algorithm>
#include <array>
#include <cassert>
#include <memory>
#include <ranges>
#include <utility>
#include <variant>

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

    Type * TypeTable::lookup(const ast::Type& type) {
        if (type.is_identifier()) {
            return lookup_identifier(type.get_identifier());
        } else if (type.is_pointer()) {
            return &get_pointer_to(TRY(lookup(*type.get_pointer().next)));
        } else if (type.is_reference()) {
            return &get_reference_to(TRY(lookup(*type.get_reference().next)));
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
            std::make_unique<Type>(Type {
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
            std::make_unique<Type>(Type {
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
            std::make_unique<Type>(Type {
                .variant = type::LValue {
                    .next = ref(type)
                }
            })
        }).second;
    }

    Type& TypeTable::get_integer() {
        Type * t = lookup_identifier("int");
        assert(t);
        return *t;
    }

    Type& TypeTable::get_void() {
        Type * t = lookup_identifier("void");
        assert(t);
        return *t;
    }

    Type& TypeTable::get_bool() {
        Type * t = lookup_identifier("bool");
        assert(t);
        return *t;
    }

    Type& TypeTable::get_void_pointer() {
        return get_pointer_to(get_void());
    }

    Variable * Frame::lookup(const ast::Identifier& iden) {
        for (auto& var : parameters) {
            if (var->iden == iden) {
                return var.get();
            }
        }
        for (auto& var : variables) {
            if (var->iden == iden) {
                return var.get();
            }
        }
        if (type == SCOPED) {
            return parent->lookup(iden);
        }
        if (type == FUNCTION_BASE) {
            std::println(stderr, "global variables not implemented");
        }
        return nullptr;
    }

    Variable& Frame::push_variable(Variable new_var, TypeTable& table) {
        new_var.type = ref(table.get_lvalue_to(*new_var.type));
        new_var.scope_level = scope_level;
        return *variables.emplace_back(std::make_unique<Variable>(std::move(new_var)));
    }

    Frame& Frame::new_child() {
        auto new_frame = std::make_unique<Frame>(Frame {
            .type = SCOPED,
            .parent = this,
            .scope_level = scope_level + 1,
        });
        return *frames.emplace_back(std::move(new_frame));
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
            parameters.push_back(std::make_unique<Variable>(Variable {
                .iden = ast.iden.value_or(""),
                .type = ref(table.get_lvalue_to(*type)),
            }));
        }
    }

    auto parse_expression(ast::Expression& expr, TypeTable& table, Frame& frame) -> std::optional<Expression> {
        if (expr.is_literal()) {
            auto& lit = expr.get_literal();
            if (lit.is_integer()) {
                return Expression {
                    .variant = expr::Literal {
                        .variant = lit::Integer {
                            .value = lit.get_integer().value
                        }
                    },
                    .type = ref(table.get_integer())
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
                        .variant = lit::Bool {
                            .value = true
                        }
                    },
                    .type = ref(table.get_bool())
                };
            } else if (lit.is_false()) {
                return Expression {
                    .variant = expr::Literal {
                        .variant = lit::Bool {
                            .value = false
                        }
                    },
                    .type = ref(table.get_bool())
                };
            } else {
                std::unreachable();
            }
        }
        if (expr.is_identifier()) {
            auto& var = TRY(frame.lookup(expr.get_identifier()));
            return Expression {
                .variant = expr::Variable {
                    .var = ref(var)
                },
                .type = var.type,
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
                    .next = std::make_unique<Expression>(std::move(next))
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
                    .next = std::make_unique<Expression>(std::move(next)),
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
                    .next = std::make_unique<Expression>(std::move(expr)),
                    .conversion_type = ref(conversion),
                },
                .type = ref(to),
            };
        }
        if (expr.is_unary()) {
            auto& unary = expr.get_unary();
            auto next = TRY(parse_expression(*unary.next, table, frame));
            if (next.type->is_void()) {
                std::println(stderr, "invalid type in unary operation");
                return std::nullopt;
            }
            auto type = ref(next.type->deref_lvalue());
            return Expression {
                .variant = expr::Unary {
                    .next = std::make_unique<Expression>(std::move(next)),
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
                    .a = std::make_unique<Expression>(std::move(a)),
                    .b = std::make_unique<Expression>(std::move(b)),
                    .type = binary.type == ast::expr::Binary::ADD ? expr::Binary::ADD : expr::Binary::SUB
                },
                .type = ref(a.type->deref_lvalue())
            };
        }
        std::unreachable();
    }

    auto type_coerce(Expression target, Type& type)
    -> std::optional<Expression> {
        auto& target_type_deref = target.type->deref_lvalue();
        auto& type_deref = type.deref_lvalue();
        if (Type::equal(target_type_deref, type_deref)) {
            return std::move(target);
        }
        auto& conversion = TRY(conversion_table.validate_implicit(target_type_deref, type_deref));
        return Expression {
            .variant = expr::Conversion {
                .next = std::make_unique<Expression>(std::move(target)),
                .conversion_type = ref(conversion),
            },
            .type = ref(type_deref)
        };
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
            auto& type1_deref = expr1.type->deref_lvalue();
            auto& type2_deref = expr2.type->deref_lvalue();
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
            auto& var = frame.push_variable(Variable{
                .iden = var_decl.iden,
                .type = ref(TRY(table.lookup(var_decl.type)))
            }, table);
            if (var_decl.value) {
                output.push_back(Statement {
                    .variant = stmt::Assignment {
                            .target = Expression {
                                .variant = expr::Variable {
                                .var = ref(var)
                            },
                            .type = var.type,
                        },
                        .value = TRY(parse_expression(*var_decl.value, table, frame)
                            .and_then([&](Expression expr) {
                                return type_coerce(std::move(expr), var.type->deref_lvalue());
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
        }
        std::unreachable();
    }

    auto parse_statements(std::span<ast::Statement> statements, TypeTable& type_table, FunctionType& function_type, Frame& frame)
    -> std::optional<std::vector<Statement>> {
        std::vector<Statement> output;
        for (auto& statement : statements) {
            usize size = output.size();
            TRY(parse_statement(output, statement, type_table, function_type, frame));
        }
        return output;
    }

    auto parse_function(ast::Function& function, TypeTable& type_table) -> std::optional<Function> {
        FunctionType type {
            .return_type = ref(TRY(type_table.lookup(function.return_type)))
        };
        for (auto& arg : function.args) {
            type.parameters.push_back(ref(TRY(type_table.lookup(arg.type))));
        }
        Frame new_frame {
            .type = Frame::FUNCTION_BASE,
            .parent = nullptr,
            .scope_level = 1,
        };
        new_frame.push_function_args(type, function, type_table);
        new_frame.statements = TRY(parse_statements(function.body, type_table, type, new_frame));
        return Function {
            .type = std::move(type),
            .identifier = function.iden,
            .frame = std::move(new_frame),
        };
    }

    auto parse(ast::Program& program) -> std::optional<SymbolTable> {
        SymbolTable table;
        for (auto& function : program) {
            auto new_function = TRY(parse_function(function, table.types));
            table.functions.push_back(std::move(new_function));
        }
        return table;
    }
}
