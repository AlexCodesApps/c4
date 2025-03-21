#pragma once
#include "sema.hpp"
#include <ostream>
namespace ir {
    void gen(std::ostream&, sema::SymbolTable& table);
}
