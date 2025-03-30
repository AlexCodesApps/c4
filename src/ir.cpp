#include "include/ir.hpp"
#include "include/sema.hpp"
#include "include/utils.hpp"
#include <cassert>
#include <format>
#include <ostream>
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

void gen([[maybe_unused]]std::ostream& output, [[maybe_unused]]sema::SymbolTable& symbols) {

}


}
