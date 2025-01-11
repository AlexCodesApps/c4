#include "include/sema.hpp"
#include "include/ast.hpp"
#include <algorithm>
#include <memory>
#include <ranges>
#include <utility>

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
            if (otype->is_pointer() && *otype->get_pointer().next == type) {
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
            if (otype->is_reference() && *otype->get_reference().next == type) {
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
            if (otype->is_lvalue() && *otype->get_lvalue().next == type) {
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
        for (auto& var : variables) {
            if (var.iden == iden) {
                return &var;
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
        isize align = new_var.type->alignment();
        isize size = new_var.type->size();
        new_var.type = ref(table.get_lvalue_to(*new_var.type));
        isize base =  align_mul_of_two(offset + base_offset, align);
        offset = base + size - base_offset;
        new_var.offset = base;
        return variables.emplace_back(std::move(new_var));
    }

    Frame Frame::new_child() {
        return Frame {
            .base_offset = offset,
            .offset = 0,
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
    void Frame::push_function_stack_frame(const FunctionType& function, const ast::Function& ast, TypeTable& table) {
        for (auto [type, ast] : std::views::zip(function.parameters, ast.args)) {
            push_variable(Variable {
                .iden = ast.iden.value_or(""),
                .type = type,
            }, table);
        }
        push_variable(Variable {
            .iden = "return",
            .type = function.return_type
        }, table);
        align_offset(8);
        offset += 16; // simulate return address and rbp saved state
        align_offset(16); // maximum needed alignment in x86 i think
        for (auto& var : variables) {
            var.offset -= offset; // all of this is below the rbp value
        }
        offset = 0;
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
            if (next_ast.is_deref()) {
                return TRY(parse_expression(*next_ast.get_deref().next, table, frame));
            }
            auto next = TRY(parse_expression(*expr.get_addr_of().next, table, frame));
            if (!next.type->is_lvalue()) {
                std::println(stderr, "invalid addr of");
                return std::nullopt;
            }
            return Expression {
                .variant = expr::AddrOf {
                    .next = std::make_unique<Expression>(std::move(next))
                },
                .type = ref(table.get_reference_to(next.type.get()))
            };
        }
        if (expr.is_deref()) {
            auto next = TRY(parse_expression(*expr.get_deref().next, table, frame));
            if (!next.type->can_be_deref()) {
                std::println(stderr, "tried to deref a non-pointer type");
                return std::nullopt;
            }
            return Expression {
                .variant = expr::Deref {
                    .next = std::make_unique<Expression>(std::move(next)),
                },
                .type = ref(next.type->deref())
            };
        }
        std::unreachable();
    }

    auto parse_statement(ast::Statement& statement, TypeTable& table, Frame& frame) -> std::optional<Statement> {
        if (statement.is_return()) {
            auto& return_stmt = statement.get_return();
            if (return_stmt.value) {
                return Statement {
                    .type = Statement::RETURN,
                    .value = TRY(parse_expression(*return_stmt.value, table, frame))
                };
            }
            return Statement {
                .type = Statement::RETURN,
                .value = std::nullopt
            };
        } else if (statement.is_variable_decl()) {
            auto& var_decl = statement.get_variable_decl();
            frame.push_variable(Variable{
                .iden = var_decl.iden,
                .type = ref(TRY(table.lookup(var_decl.type)))
            }, table);
        }
        std::unreachable();
    }

    auto parse_statements(std::span<ast::Statement> statements, TypeTable& type_table, FunctionType& function_type, Frame& frame)
    -> std::optional<std::vector<Statement>> {
        std::vector<Statement> output;
        for (auto& statement : statements) {
            auto new_statement = TRY(parse_statement(statement, type_table, frame));
            if (*new_statement.value
                    .transform([](Expression& ex) { return ex.type; })
                    .value_or(ref(type_table.get_void())) != *function_type.return_type) {
                std::println(stderr, "mismatched types");
                return std::nullopt;
            }
            output.push_back(std::move(new_statement));
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
            .base_offset = 0,
            .offset = 0,
            .type = Frame::FUNCTION_BASE,
            .parent = nullptr
        };
        new_frame.push_function_stack_frame(type, function, type_table);
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
