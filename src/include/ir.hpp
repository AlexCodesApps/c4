#pragma once
#include "sema.hpp"
#include <ostream>
namespace ir {
    void gen(std::ostream&, std::span<sema::Function> functions);
}
