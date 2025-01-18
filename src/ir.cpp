#include "include/ir.hpp"
#include "include/sema.hpp"
#include "include/utils.hpp"
#include <ostream>
#include <string>
#include <string_view>
#include <utility>
namespace ir {

/*

    generating QBE Intermediate Language
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

std::string get_type_letter(sema::Type& type) {
    if (type.can_be_deref()) {
        return "l";
    } else if (type.is_void()) {
        return  "";
    } else if (type.is_integer()) {
        return "w";
    } else {
        std::unreachable();
    }
}


enum class ExpressionIntent {
    ADDRESS,
    VALUE
};

void gen_expression(std::ostream& output, sema::Expression& expr, Context& context, Target target, ExpressionIntent intent) {
    auto& type = *target.type_ref;
    auto store = [&](auto&& callback){
        if (target.type == Target::DEREFED_POINTER) {
            auto var = context.generate_temp_name();
            callback(var);
            std::println(output, "store{} {}, {}", get_type_letter(type), var, target.name);
        } else  if (target.type == Target::REGISTER) {
            callback(target.name);
        } else {
            std::unreachable();
        }
    };
    if (expr.is_addr_of()) {
        auto& addr = *expr.get_addr_of().next;
        auto var = context.generate_temp_name();
        store([&](std::string_view var) {
            gen_expression(output, addr, context, Target{
                .type = Target::REGISTER,
                .name = var,
                .type_ref = addr.type
            }, ExpressionIntent::ADDRESS);
        });
    } else if (expr.is_deref()) {
        auto& derefed = *expr.get_deref().next;
        if (intent == ExpressionIntent::VALUE) {
            store([&](std::string_view var) {
                auto letter = get_type_letter(*expr.type);
                auto var2 = context.generate_temp_name();
                gen_expression(output, derefed, context, Target{
                    .type = Target::REGISTER,
                    .name = var2,
                    .type_ref = derefed.type
                }, ExpressionIntent::VALUE);
                std::println(output, "{} ={} load{} {}", var, letter, letter, var2);
            });
        } else if (intent == ExpressionIntent::ADDRESS) {
            // take address
            store([&](std::string_view var) {
                gen_expression(output, derefed, context, Target{
                    .type = Target::REGISTER,
                    .name = var,
                    .type_ref = derefed.type
                }, ExpressionIntent::ADDRESS);
            });
        } else {
            std::unreachable();
        }
    } else if (expr.is_literal()) {
        auto& literal = expr.get_literal();
        store([&](std::string_view var) {
            if (literal.type == sema::expr::Literal::INTEGER) {
                std::println(output, "{} =w copy {}", var, literal.integer);
            } else if (literal.type == sema::expr::Literal::NULLPTR) {
                std::println(output, "{} =l copy 0", var);
            } else {
                std::unreachable();
            }
        });
    } else if (expr.is_variable()) {
        auto& sema_var = *expr.get_variable().var;
        store([&](std::string_view var) {
            if (intent == ExpressionIntent::ADDRESS) {
                std::println("{} =l copy %{}", var, sema_var.iden);
            } else if (intent == ExpressionIntent::VALUE) {
                auto letter = get_type_letter(sema_var.type->deref_lvalue());
                std::println(output, "{} ={} load{} %{}", var, letter, letter, sema_var.iden);
            } else {
                std::unreachable();
            }
        });
    } else {
        std::unreachable();
    }
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
        auto type = ref(assign_stmt.target.type->deref_lvalue());
        auto var = context.generate_temp_name();
        gen_expression(output, assign_stmt.target, context, Target{
            .type = Target::REGISTER,
            .name = var,
            .type_ref = type }, ExpressionIntent::ADDRESS);
        gen_expression(output, assign_stmt.value, context, Target{
            .type = Target::DEREFED_POINTER,
            .name = var,
            .type_ref = type,
        }, ExpressionIntent::VALUE);
    } else {
        std::unreachable();
    }
}

void gen_function(std::ostream& output, sema::Function& function) {
    std::print(output, "export function {} ${} (", get_type_letter(*function.type.return_type), function.identifier);
    for (auto& param : function.frame.parameters) {
        std::print(output, "{} %.p{}, ", get_type_letter(param->type->deref_lvalue()), param->iden);
    }
    std::println(output, ") {{\n"
                       "@start");
    for (auto& var : function.frame.parameters) {
        if (var->iden.empty()) {
            continue;
        }
        auto& type = var->type->deref_lvalue();
        auto letter = get_type_letter(type);
        std::println(output, "%{} =l alloc{} {}", var->iden, type.alignment(), type.size());
        std::println(output, "store{} %.p{}, %{}", letter, var->iden, var->iden);
    }
    for (auto& var : function.frame.variables) {
        if (var->iden.empty()) {
            continue;
        }
        auto& type = var->type->deref_lvalue();
        std::println(output, "%{} =l alloc{} {}", var->iden, type.alignment(), type.size());
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

void gen(std::ostream& output, std::span<sema::Function> functions) {
    for (auto& function : functions) {
        gen_function(output, function);
    }
}

}
