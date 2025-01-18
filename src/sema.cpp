#include "include/sema.hpp"
#include "include/ast.hpp"
#include <algorithm>
#include <memory>
#include <ranges>
#include <utility>
#include <variant>

namespace sema {

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
        return *variables.emplace_back(std::make_unique<Variable>(std::move(new_var)));
    }

    Frame Frame::new_child() {
        return Frame {
            .type = SCOPED,
            .parent = this,
        };
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
            return Expression {
                .variant = expr::Literal {
                    .type = expr.get_literal().type == ast::expr::Literal::NULLPTR ?
                    expr::Literal::NULLPTR : expr::Literal::INTEGER,
                    .integer = expr.get_literal().integer,
                },
                .type = ref(expr.get_literal().type == ast::expr::Literal::INTEGER ?
                            table.get_integer() : table.get_void_pointer())
            };
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
        std::unreachable();
    }

    auto parse_statement(std::vector<Statement>& output, ast::Statement& statement, TypeTable& table, Frame& frame)
    -> std::optional<std::monostate>
    {
        auto parse_assignment = [&](ast::Expression& target, ast::Expression& value) -> std::optional<std::monostate> {
            auto expr1 = TRY(parse_expression(target, table, frame));
            auto expr2 = TRY(parse_expression(value, table, frame));
            if (!expr1.type->is_lvalue() || !Type::equal(expr1.type->deref_lvalue(), expr2.type->deref_lvalue())) {
                std::println(stderr, "invalid assignment");
                return std::nullopt;
            }
            output.push_back(Statement {
                .variant = stmt::Assignment {
                    .target = std::move(expr1),
                    .value = std::move(expr2),
                }
            });
            return std::monostate{};
        };

        if (statement.is_return()) {
            auto& return_stmt = statement.get_return();
            if (return_stmt.value) {
                output.push_back(Statement {
                    .variant = stmt::Return {
                        .value = TRY(parse_expression(*return_stmt.value, table, frame))
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
                        .value = TRY(parse_expression(*var_decl.value, table, frame))
                    }
                });
            }
            return std::monostate{};
        }
        std::unreachable();
    }

    auto parse_statements(std::span<ast::Statement> statements, TypeTable& type_table, FunctionType& function_type, Frame& frame)
    -> std::optional<std::vector<Statement>> {
        std::vector<Statement> output;
        for (auto& statement : statements) {
            usize size = output.size();
            TRY(parse_statement(output, statement, type_table, frame));
            if (size == output.size()) {
                continue;
            }
            auto& new_statement = output.back();
            if (new_statement.is_return()) {

                auto& stmt_type = *new_statement.get_return().value
                    .transform([](Expression& ex) { return ex.type; })
                    .value_or(ref(type_table.get_void()));

                if (!Type::equal(stmt_type.deref_lvalue(), *function_type.return_type)) {
                    std::println(stderr, "mismatched types");
                    return std::nullopt;
                }
            }
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
            .parent = nullptr
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
