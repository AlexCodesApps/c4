#include "include/ir.hpp"
#include "include/sema.hpp"
#include "include/utils.hpp"
#include <cassert>
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

enum class ValueType {
    UNSIGNED_BYTE,
    SIGNED_BYTE,
    BYTE,
    UNSIGNED_SHORT,
    SIGNED_SHORT,
    SHORT,
    SIGNED_WORD,
    UNSIGNED_WORD,
    WORD,
    LONG,
};

std::string_view value_type_double(ValueType type) {
    switch (type) {
    using enum ValueType;
    case UNSIGNED_BYTE:  return  "ub";
    case SIGNED_BYTE:    return  "sb";
    case BYTE:           return  "ub";
    case UNSIGNED_SHORT: return  "uh";
    case SIGNED_SHORT:   return  "sh";
    case SHORT:          return   "h";
    case SIGNED_WORD:    return  "sw";
    case UNSIGNED_WORD:  return  "uw";
    case WORD:           return   "w";
    case LONG:           return   "l";
    }
}

std::string_view value_type_word(ValueType type) {
    switch (type) {
    case ValueType::LONG:
        return "l";
    default:
        return "w";
    }
}

std::string_view value_type_single(ValueType type) {
    auto str = value_type_double(type);
    return std::string_view(str.end() - 1, str.end());
}

std::string sema_variable_to_string(const sema::Variable& variable) {
    return std::format("%.v{}_{}", variable.scope_level, variable.iden);
}

ValueType sema_type_to_type(sema::Type& type) {
    if (type.can_be_deref()) {
        return ValueType::LONG;
    } else if (type.is_bool()) {
        return ValueType::BYTE;
    } else if (type.is_integer()) {
        return ValueType::WORD;
    } else {
        std::unreachable();
    }
}

enum class ExpressionIntent {
    ADDRESS,
    VALUE
};

void load(std::ostream& output, std::string_view target, std::string_view src, ValueType type) {
    std::println(output, "{} ={} load{} {}", target, value_type_word(type), value_type_double(type), src);
}

void store(std::ostream& output, std::string_view target_ptr, std::string_view src, ValueType type) {
    std::println(output, "store{} {}, {}", value_type_single(type), src, target_ptr);
}

void assign(std::ostream& output, std::string_view target, std::string_view src, ValueType type) {
    std::println(output, "{} ={} {}", target, value_type_word(type), src);
}

void gen_load_literal(std::ostream& output, Target target, sema::expr::Literal& literal, sema::Type& type, Context& context) {
    auto store = [&](auto&& callback){
        if (target.type == Target::DEREFED_POINTER) {
            auto var = context.generate_temp_name();
            callback(var);
            ir::store(output, target.name, var, sema_type_to_type(type));
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
    auto store = [&](auto&& callback){
        if (target.type == Target::DEREFED_POINTER) {
            auto var = context.generate_temp_name();
            callback(var);
            ir::store(output, target.name, var, sema_type_to_type(type));
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
                auto var2 = context.generate_temp_name();
                gen_expression(output, derefed, context, Target{
                    .type = Target::REGISTER,
                    .name = var2,
                    .type_ref = derefed.type
                }, ExpressionIntent::ADDRESS);
                load(output, var, var2, sema_type_to_type(*expr.type));
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
                auto str = std::format("copy {}", sema_variable_to_string(sema_var));
                assign(output, target.name, str, ValueType::LONG);
            } else if (intent == ExpressionIntent::VALUE) {
                auto& type = sema_var.type->deref_lvalue();
                load(output, var, sema_variable_to_string(sema_var), sema_type_to_type(type));
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
    } else if (expr.is_unary()) {
        auto& unary_expr = expr.get_unary();
        store([&](std::string_view var) {
            auto var2 = context.generate_temp_name();
            gen_expression(output, *unary_expr.next, context, Target {
                .type = Target::REGISTER,
                .name = var2,
                .type_ref = unary_expr.next->type
            }, ExpressionIntent::VALUE);
            assign(output, var, std::format("neg {}", var2), sema_type_to_type(*expr.type));
        });
    } else if (expr.is_binary()) {
        auto& binary_expr = expr.get_binary();
        store([&](std::string_view var) {
            auto a = context.generate_temp_name();
            auto b = context.generate_temp_name();
            gen_expression(output, *binary_expr.a, context, Target {
                .type = Target::REGISTER,
                .name = a,
                .type_ref = binary_expr.a->type
            }, ExpressionIntent::VALUE);
            gen_expression(output, *binary_expr.b, context, Target {
                .type = Target::REGISTER,
                .name = b,
                .type_ref = binary_expr.b->type
            }, ExpressionIntent::VALUE);
            assign(output, var,
                std::format("{} {}, {}", binary_expr.type == sema::expr::Binary::ADD ? "add" : "sub", a, b),
                sema_type_to_type(*expr.type));
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
        auto type = ref(expr.type->deref_lvalue());
        gen_expression(output, expr, context, Target{
            .type = Target::REGISTER,
            .name = placeholder,
            .type_ref = type,
        }, ExpressionIntent::VALUE);
    } else {
        std::unreachable();
    }
}

void gen_function(std::ostream& output, sema::Function& function) {
    std::print(output, "export function");
    if (!function.type.return_type->is_void()) {
        std::print(output, " {}", value_type_double(sema_type_to_type(*function.type.return_type)));
    }
    std::print(output, " ${} (", function.identifier);
    for (auto& param : function.frame.parameters) {
        std::print(output, "{} %.p{}, ", value_type_double(sema_type_to_type(param->type->deref_lvalue())), param->iden);
    }
    std::println(output, ") {{\n"
                       "@start");
    for (auto& var : function.frame.parameters) {
        if (var->iden.empty()) {
            continue;
        }
        auto& type = var->type->deref_lvalue();
        assign(output, sema_variable_to_string(*var), std::format("alloc{} {}", type.alignment(), type.size()), ValueType::LONG);
        store(output, sema_variable_to_string(*var), std::format("%.p{}", var->iden), sema_type_to_type(type));
    }
    for (auto& var : function.frame.variables) {
        if (var->iden.empty()) {
            continue;
        }
        auto& type = var->type->deref_lvalue();
        assign(output, sema_variable_to_string(*var), std::format("alloc{} {}", type.alignment(), type.size()), ValueType::LONG);
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
