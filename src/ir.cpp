#include "include/ir.hpp"
#include "include/sema.hpp"
#include "include/utils.hpp"
#include <cassert>
#include <format>
#include <ostream>
#include <print>
#include <string>
#include <string_view>
#include <utility>

namespace ir {

/*

    Generating QBE intermediate language
    for the time being.

*/

struct Context {
    usize label_counter = 0;
    usize tmp_counter = 0;
    std::string generate_label() {
        return std::format("@.l{}", label_counter++);
    }
    std::string generate_temp_name() {
        return std::format("%.r{}", tmp_counter++);
    }
};

struct Target {
    enum { DEREFED_POINTER, REGISTER } type;
    std::string_view name;
    ref<sema::Type> type_ref;
};

std::string sema_symbol_to_string(const sema::Symbol& symbol) {
    if (symbol.is_constant()) {
        return std::format("${}", symbol.get_identifier());
    } else if (symbol.is_parameter()) {
        return std::format("%.v_{}", symbol.get_identifier());
    } else if (symbol.is_variable()) {
        auto& var = symbol.get_variable();
        return std::format("%.v{}_{}", var.offset, symbol.get_identifier());
    }
    std::unreachable();
}

enum class ExpressionIntent {
    ADDRESS,
    VALUE
};

void gen_expression(std::ostream& output, sema::Expression& expr, Context& context, Target target, ExpressionIntent intent) {
    (void)output;
    (void)expr;
    (void)context;
    (void)target;
    (void)intent;
    std::unreachable();
}

void gen_statement(std::ostream& output, sema::Statement& statement, Context& context) {
    if (statement.is_return()) {
        auto& return_stmt = statement.get_return();
        if (!return_stmt.value) {
            std::println(output, "ret");
        } else {
            auto type = return_stmt.value->type;
            auto var = context.generate_temp_name();
            gen_expression(output, *return_stmt.value, context, Target{
                .type = Target::REGISTER,
                .name = var,
                .type_ref = type }, ExpressionIntent::VALUE);
            std::println(output, "ret {}", var);
        }
    } else if (statement.is_assignment()) {
        auto& assign_stmt = statement.get_assignment();
        auto type = assign_stmt.target.type;
        auto var = context.generate_temp_name();
        gen_expression(output, assign_stmt.target, context, Target{
            .type = Target::REGISTER,
            .name = var,
            .type_ref = type
        }, ExpressionIntent::ADDRESS);
        gen_expression(output, assign_stmt.value, context, Target{
            .type = Target::DEREFED_POINTER,
            .name = var,
            .type_ref = type,
        }, ExpressionIntent::VALUE);
    } else if (statement.is_block()) {
        for (auto& statement : statement.get_block()) {
            gen_statement(output, statement, context);
        }
    } else if (statement.is_expr()) {
        auto& expr = statement.get_expr();
        auto placeholder = context.generate_temp_name();
        auto type = expr.type;
        gen_expression(output, expr, context, Target{
            .type = Target::REGISTER,
            .name = placeholder,
            .type_ref = type,
        }, ExpressionIntent::VALUE);
    } else {
        std::unreachable();
    }
}

void gen_function(std::ostream& output, sema::symb::Constant& symbol) {
    assert(symbol.is_function());
    auto& function = symbol.get_function();
    auto& type = symbol->type->get_function();
    std::print(output, "export function");
    if (!type.return_type->is_void()) {
        // std::print(output, " {}", value_type_double(sema_type_to_type(*type.return_type)));
    }
    std::print(output, " ${} (", symbol->identifier);
    for (auto& symbol : function.frame.symbols) {
        if (!symbol->is_parameter()) break;
        // std::print(output, "{} %.p{}, ", value_type_double(sema_type_to_type(symbol->get_type().deref_lvalue())), symbol->get_identifier());
    }
    std::println(output, ") {{\n"
                       "@start");
    for (auto& symbol : function.frame.symbols) {
        if (symbol->get_identifier().empty()) {
            continue;
        }
        // auto& type = symbol->get_type().deref_lvalue();
        // assign(output, sema_symbol_to_string(*symbol), std::format("alloc{} {}", type.alignment(), type.size()), ValueType::LONG);
        // if (symbol->is_parameter()) {
        //     store(output, sema_symbol_to_string(*symbol), std::format("%.p{}", symbol->get_identifier()), sema_type_to_type(type));
        // }
    }
    Context context;
    for (auto& statement : function.frame.statements) {
        gen_statement(output, statement, context);
        if (statement.is_return()) {
            break;
        }
    }
    std::println(output, "}}");
}

void gen(std::ostream& output, sema::SymbolTable& table) {
    for (auto& symbol : table.global_frame.symbols) {
        gen_function(output, symbol->get_constant());
    }
}

}
