#pragma once
#include "numbers.hpp"
#include "sema.hpp"
#include <sstream>

namespace gen {
    void gen_offset(std::stringstream& output, isize offset);
    void gen_expression(std::stringstream& output, sema::Expression& expr, isize total_offset, isize dest_offset);
    void gen_statement(std::stringstream& output, sema::Statement& statement, sema::Frame& frame);
    void gen_frame(std::stringstream& output, sema::Frame& frame);
    void gen_function(std::stringstream& output, sema::Function& function);
    std::string generate(sema::SymbolTable& table);
}
