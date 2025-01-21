#include "include/ir.hpp"
#include "include/sema.hpp"
#include "include/utils.hpp"
#include <cassert>
#include <ostream>
#include <string>
#include <string_view>
#include <utility>

int foo() {
    return 0;
}

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

enum class ValueType {
    UNSIGNED_BYTE,
    SIGNED_BYTE,
    UNSIGNED_SHORT,
    SIGNED_SHORT,
    WORD,
    LONG,
};

enum class VariableType {
    WORD,
    LONG,
};

ValueType get_type(sema::Type& type) {
    if (type.is_lvalue()) {
        return get_type(type.get_lvalue().next.get());
    }
    assert(!type.is_void());
    if (type.can_be_deref()) {
        return ValueType::LONG;
    } else if (type.is_integer()) {
        return ValueType::WORD;
    } else if (type.is_bool()) {
        return ValueType::UNSIGNED_BYTE;
    } else {
        std::unreachable();
    }
}

VariableType get_var_type(sema::Type& type) {
    if (type.is_lvalue()) {
        return get_var_type(type.get_lvalue().next.get());
    }
    assert(!type.is_void());
    if (type.can_be_deref()) {
        return VariableType::LONG;
    } else {
        return VariableType::WORD;
    }
}

std::string_view to_string(ValueType type) {
    switch (type) {
    case ValueType::UNSIGNED_BYTE:
        return "b";
    case ValueType::SIGNED_BYTE:
        return "b";
    case ValueType::UNSIGNED_SHORT:
        return "h";
    case ValueType::SIGNED_SHORT:
        return "h";
    case ValueType::WORD:
        return "w";
    case ValueType::LONG:
        return "l";
    }
}

std::string_view to_string(VariableType type) {
    switch (type) {
    case VariableType::WORD:
        return "w";
    case VariableType::LONG:
        return "l";
    }
}


enum class ExpressionIntent {
    ADDRESS,
    VALUE
};

void gen_load_literal(std::ostream& output, Target target, sema::expr::Literal& literal, sema::Type& type, Context& context) {
    auto v_type = get_type(type);
    auto store = [&](auto&& callback){
        if (target.type == Target::DEREFED_POINTER) {
            auto var = context.generate_temp_name();
            callback(var);
            std::println(output, "store{} {}, {}", to_string(v_type), var, target.name);
        } else  if (target.type == Target::REGISTER) {
            callback(target.name);
        } else {
            std::unreachable();
        }
    };
    if (literal.is_bool()) {
        store([&](std::string_view var) {
            std::println("{} =w copy {}", var, (u8)literal.get_bool().value);
        });
    } else if (literal.is_integer()) {
        store([&](std::string_view var) {
            std::println("{} =w copy {}", var, literal.get_integer().value);
        });
    } else if (literal.is_nullptr()) {
        store([&](std::string_view var) {
            std::println("{} =l copy 0", var);
        });
    } else {
        std::unreachable();
    }
}

void gen_load(std::ostream& output, Target target, Target src, ExpressionIntent intent, Context& context) {
    auto inter_reg = context;
}

void gen_expression(std::ostream& output, sema::Expression& expr, Context& context, Target target, ExpressionIntent intent) {
    auto& type = *target.type_ref;
    auto v_type = get_type(type);
    auto store = [&](auto&& callback){
        if (target.type == Target::DEREFED_POINTER) {
            auto var = context.generate_temp_name();
            callback(var);
            std::println(output, "store{} {}, {}", to_string(v_type), var, target.name);
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
                auto var_letter = to_string(get_var_type(*expr.type));
                auto letter = to_string(get_type(*expr.type));
                auto var2 = context.generate_temp_name();
                gen_expression(output, derefed, context, Target{
                    .type = Target::REGISTER,
                    .name = var2,
                    .type_ref = derefed.type
                }, ExpressionIntent::VALUE);
                std::println(output, "{} ={} load{} {}", var, var_letter, letter, var2);
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
        return gen_load_literal(output, target, expr.get_literal(), *expr.type, context);
    } else if (expr.is_variable()) {
        auto& sema_var = *expr.get_variable().var;
        store([&](std::string_view var) {
            if (intent == ExpressionIntent::ADDRESS) {
                std::println(output, "{} =l copy %.v{}{}", var, sema_var.scope_level, sema_var.iden);
            } else if (intent == ExpressionIntent::VALUE) {
                auto& type = sema_var.type->deref_lvalue();
                std::println(output, "{} ={} load{} %.v{}{}", var, to_string(get_type(type)), to_string(get_var_type(type)), sema_var.scope_level, sema_var.iden);
            } else {
                std::unreachable();
            }
        });
    } else if (expr.is_conversion()) {
        auto& conv_expr = expr.get_conversion();
        if (conv_expr.conversion_type->type == sema::Conversion::BITCAST) {
            return gen_expression(output, *conv_expr.next, context, target, intent);
        } else {
            std::unreachable();
        }
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
    } else {
        std::unreachable();
    }
}

void gen_function(std::ostream& output, sema::Function& function) {
    std::print(output, "export function");
    if (!function.type.return_type->is_void()) {
        std::print(output, " {}", to_string(get_var_type(*function.type.return_type)));
    }
    std::print(output, " ${} (", function.identifier);
    for (auto& param : function.frame.parameters) {
        std::print(output, "{} %.p{}, ", to_string(get_var_type(param->type->deref_lvalue())), param->iden);
    }
    std::println(output, ") {{\n"
                       "@start");
    for (auto& var : function.frame.parameters) {
        if (var->iden.empty()) {
            continue;
        }
        auto& type = var->type->deref_lvalue();
        auto letter = to_string(get_var_type(type));
        std::println(output, "%.v{}{} =l alloc{} {}", var->scope_level, var->iden, type.alignment(), type.size());
        std::println(output, "store{} %.p{}, %.v{}{}", letter, var->iden, var->scope_level, var->iden);
    }
    for (auto& var : function.frame.variables) {
        if (var->iden.empty()) {
            continue;
        }
        auto& type = var->type->deref_lvalue();
        std::println(output, "%.v{}{} =l alloc{} {}", var->scope_level, var->iden, type.alignment(), type.size());
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
