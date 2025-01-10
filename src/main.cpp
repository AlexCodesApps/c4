#include <algorithm>
#include <cassert>
#include <climits>
#include <cwchar>
#include <fstream>
#include <memory>
#include <optional>
#include <print>
#include <span>
#include <sstream>
#include <string_view>
#include <utility>
#include <variant>
#include <vector>
#include <expected>
#include <ranges>
#include "include/try.hpp"
#include "include/numbers.hpp"
#include "include/lexer.hpp"
#include "include/utils.hpp"
#include "include/ast.hpp"

namespace Sema {
    struct Type;
    namespace type {
        struct Void {};
        struct Integer {};
        struct Pointer {
            Type * next;
        };
    }
    struct Type {
        std::variant<type::Void, type::Integer, type::Pointer> variant;
        bool is_void() const {
            return std::holds_alternative<type::Void>(variant);
        }
        bool is_integer() const {
            return std::holds_alternative<type::Integer>(variant);
        }
        bool is_pointer() const {
            return std::holds_alternative<type::Pointer>(variant);
        }
        type::Pointer& get_pointer() {
            return std::get<type::Pointer>(variant);
        }
        const type::Pointer& get_pointer() const {
            return std::get<type::Pointer>(variant);
        }
        usize size() const {
            return std::visit(Overload{
                [](const type::Void&) { return 0UL; },
                [](const type::Pointer&) { return sizeof(void *); },
                [](const type::Integer&) { return sizeof(int); }
            }, variant);
        }
        usize alignment() const {
            return std::visit(Overload{
                [](const type::Void&) { return 0UL; },
                [](const type::Pointer&) { return alignof(void *); },
                [](const type::Integer&) { return alignof(int); }
            }, variant);
        }
    };
    struct TypeTable {
        using pair = std::pair<std::vector<ast::Identifier>, Type>;
        std::vector<pair> types_database = {
            pair({"int", "i32"}, Type{
                .variant = type::Integer{}
            }),
            pair({"void"}, Type{
                .variant = type::Void{}
            })
        };
        Type * lookup(const ast::Type& type) {
            if (type.has_identifier()) {
                return lookup_identifier(type.get_identifier());
            } else if (type.has_pointer()) {
                auto& next = TRY(lookup(*type.get_pointer().next));
                for (auto& [_, otype] : types_database) {
                    if (otype.is_pointer() && otype.get_pointer().next == &next) {
                        return &otype;
                    }
                }
                return &types_database.emplace_back(pair{
                    {},
                    Type {
                        .variant = type::Pointer {
                            .next = &next
                        }
                    }
                }).second;
            } else {
                std::unreachable();
            }
        }
        Type * lookup_identifier(const ast::Identifier& iden) {
            for (auto& [idens, otype] : types_database) {
                if (std::find(idens.begin(), idens.end(), iden) != idens.end()) {
                    return &otype;
                }
            }
            return nullptr;
        }
    };
    struct FunctionType {
        std::vector<ref<Type>> parameters;
        ref<Type> return_type;
    };
    struct Variable {
        ast::Identifier iden;
        isize offset;
        ref<Type> type;
    };
    struct Expression {
        enum { LITERAL, VARIABLE } expr_type;
        ref<ast::Expression> ast;
        ref<Type> type;
        Variable * var;
    };
    struct Statement;
    struct Function;
    struct Frame {
        isize base_offset = 0;
        isize offset = 0;
        std::vector<Variable> variables;
        std::vector<Statement> statements;
        enum { GLOBAL, FUNCTION_BASE, SCOPED } type;
        Frame * parent;

        Variable * lookup(const ast::Identifier& iden) {
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
        Variable& push_variable(Variable new_var) {
            isize align = new_var.type->alignment();
            isize size = new_var.type->size();
            isize base =  align_mul_of_two(offset + base_offset, align);
            offset = base + size - base_offset;
            new_var.offset = base;
            return variables.emplace_back(std::move(new_var));
        }
        Frame new_child();
        void push_function_stack_frame(const FunctionType& function, const ast::Function& ast);
        void align_offset(isize alignment) {
            offset = align_mul_of_two(offset, alignment);
        }
    };

    struct Statement {
        enum { RETURN } type;
        std::optional<Expression> value;
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
    void Frame::push_function_stack_frame(const FunctionType& function, const ast::Function& ast) {
        for (auto [type, ast] : std::views::zip(function.parameters, ast.args)) {
            push_variable(Variable {
                .iden = ast.iden.value_or(""),
                .type = type,
            });
        }
        push_variable(Variable {
            .iden = "return",
            .type = function.return_type
        });
        align_offset(8);
        offset += 16; // simulate return and rbp save
        align_offset(16); // maximum needed alignment in x86 i think
        for (auto& var : variables) {
            var.offset -= offset; // all of this is below the rbp value
        }
        offset = 0;
    }

    auto parse_expression(ast::Expression& expr, TypeTable& table, Frame& frame) -> std::optional<Expression> {
        if (expr.has_literal()) {
            return Expression {
                .expr_type = Expression::LITERAL,
                .ast = ref(expr),
                .type = ref(TRY(table.lookup_identifier("int")))
            };
        }
        if (expr.has_identifier()) {
            auto& var = TRY(frame.lookup(expr.get_identifier()));
            return Expression {
                .expr_type = Expression::VARIABLE,
                .ast = ref(expr),
                .type = var.type,
                .var = &var,
            };
        }
        return std::nullopt;
    }
    auto parse_statement(ast::Statement& statement, TypeTable& type_table, Frame& frame) -> std::optional<Statement> {
        if (statement.value) {
            return Statement {
                .type = Statement::RETURN,
                .value = TRY(parse_expression(*statement.value, type_table, frame))
            };
        }
        return Statement {
            .type = Statement::RETURN,
            .value = std::nullopt
        };
    }
    auto parse_statements(std::span<ast::Statement> statements, TypeTable& type_table, FunctionType& type, Frame& frame)
    -> std::optional<std::vector<Statement>> {
        std::vector<Statement> output;
        for (auto& statement : statements) {
            auto new_statement = TRY(parse_statement(statement, type_table, frame));
            if (!new_statement.value) {
                if (!type.return_type->is_void()) {
                    std::println(stderr, "expected value in return");
                    return std::nullopt;
                }
            } else  {
                if (new_statement.value->type != type.return_type) {
                    std::println(stderr, "mismatched types");
                    return std::nullopt;
                }
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
        new_frame.push_function_stack_frame(type, function);
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

namespace Gen {
    void gen_offset(std::stringstream& output, isize offset) {
        if (offset > 0) {
            output << "+ " << offset;
        } else if (offset < 0) {
            output << "- " << -offset;
        }
    }
    void gen_expression(std::stringstream& output, Sema::Expression& expr, isize dest_offset) {
        if (expr.expr_type == Sema::Expression::LITERAL) {
            output << "mov DWORD[rbp ";
            gen_offset(output, dest_offset);
            output << "], " << expr.ast->get_literal().integer;
        } else if (expr.expr_type == Sema::Expression::VARIABLE) {
            output << "mov edi, DWORD[rbp ";
            gen_offset(output, expr.var->offset);
            output << "]\n";
            output << "mov DWORD[rbp ";
            gen_offset(output, dest_offset);
            output << "], edi";
        }
        output << "\n";
    }
    void gen_statement(std::stringstream& output, Sema::Statement& statement, Sema::Frame& frame) {
        if (statement.type == Sema::Statement::RETURN) {
            if (statement.value) {
                auto dest = frame.lookup("return")->offset;
                auto& value = *statement.value;
                gen_expression(output, value, dest);
            }
            output << "add rsp, " << frame.offset << "\n"
                      "pop rbp\n"
                      "ret\n";
        }
    }
    void gen_frame(std::stringstream& output, Sema::Frame& frame) {
        output << "sub rsp, " << frame.offset << "\n";
        for (auto& statement : frame.statements) {
            gen_statement(output, statement, frame);
        }
    }
    void gen_function(std::stringstream& output, Sema::Function& function) {
        output << function.identifier << ":\n"
        "push rbp\n"
        "mov rbp, rsp\n";
        gen_frame(output, function.frame);
    }
    std::string gen(Sema::SymbolTable& table) {
        std::stringstream output;
        for (auto& fun : table.functions) {
            output << "global " << fun.identifier << "\n";
        }
        output << "section .text\n";
        output <<
        "init:\n"
        "call main\n"
        "mov rdi, rax\n"
        "mov rax, 60\n"
        "syscall\n";
        for (auto& fun : table.functions) {
            gen_function(output, fun);
        }
        return std::move(output).str();
    }
}

int main(int argc, char ** argv) {
    if (argc != 2) {
        std::println(stderr, "usage : {} <filename>", argv[0]);
        return -1;
    }
    std::ifstream file(argv[1]);
    if (!file) {
        std::println(stderr, "error opening file : {}", argv[1]);
        return -2;
    }
    std::string contents = (std::stringstream() << file.rdbuf()).str();
    auto tokens = ({
        auto result = lex(contents);
        if (!result) {
            return -3;
        }
        std::move(*result);
    });
    for (auto& tok : tokens) {
        std::println(stderr, "tok {{ {}, source: \"{}\", loc: {} {}, int: {} }}", token_type_to_string(tok.type),
            tok.source_string, tok.source_location.first, tok.source_location.second, tok.integer);
    }
    auto ast = ({
        auto result = ast::parse(tokens);
        if (!result) {
            std::println(stderr, "parsing error");
            return -4;
        }
        std::move(*result);
    });
    std::println(stderr, "success!");
    auto symbol_table = ({
        auto result = Sema::parse(ast);
        if (!result) {
            std::println(stderr, "semantic error");
            return -5;
        }
        std::move(*result);
    });
    std::println("{}", Gen::gen(symbol_table));
}
