#include "include/gen.hpp"
#include "include/utils.hpp"
#include <utility>

namespace gen {
    void gen_offset(std::stringstream& output, isize offset) {
        if (offset > 0) {
            output << "+ " << offset;
        } else if (offset < 0) {
            output << "- " << -offset;
        }
    }

    void gen_expression(std::stringstream& output, sema::Expression& expr, isize total_offset, isize dest_offset) {
        if (expr.is_deref()) {
            auto& next = *expr.get_deref().next;
            output << "sub rsp, 8\n";
            isize new_offset = align_mul_of_two<isize>(total_offset, 8);
            gen_expression(output, *expr.get_deref().next, new_offset + 8, new_offset);
            assert(next.type->can_be_deref());
            auto& type = next.type->deref();
            // copy
            if (type.is_integer()) {
                output << "mov edi, DWORD[rbp ";
                gen_offset(output, new_offset);
                output << "]\n"
                          "mov DWORD[rbp ";
                gen_offset(output, dest_offset);
                output << "], edi";
            } else if (type.is_pointer()) {
                output << "mov rdi, QWORD[rbp ";
                gen_offset(output, new_offset);
                output << "]\n"
                          "mov QWORD[rbp ";
                gen_offset(output, dest_offset);
                output << "], rdi\n";
            } else  {
                std::unreachable();
            }
            output << "add rsp, 8";
        } else if (expr.is_literal()) {
            output << "mov DWORD[rbp ";
            gen_offset(output, dest_offset);
            output << "], ";
        } else if (expr.is_variable()) {
            output << "mov edi, DWORD[rbp ";
            gen_offset(output, expr.get_variable().var->offset);
            output << "]\n";
            output << "mov DWORD[rbp ";
            gen_offset(output, dest_offset);
            output << "], edi";
        } else if (expr.is_addr_of()) {
            auto& var = expr.get_addr_of().next->get_variable().var.get();
            output << "lea rdi, [rbp ";
            gen_offset(output, var.offset);
            output << "]\n"
                      "mov QWORD[rbp ";
            gen_offset(output, dest_offset);
            output << "], rdi";
        } else {
            std::unreachable();
        }
        output << "\n";
    }

    void gen_statement(std::stringstream& output, sema::Statement& statement, sema::Frame& frame) {
        if (statement.type == sema::Statement::RETURN) {
            if (statement.value) {
                auto dest = frame.lookup("return")->offset;
                auto& value = *statement.value;
                gen_expression(output, value, frame.offset + frame.base_offset, dest);
            }
            output << "add rsp, " << frame.offset << "\n"
                      "pop rbp\n"
                      "ret\n";
        }
    }

    void gen_frame(std::stringstream& output, sema::Frame& frame) {
        output << "sub rsp, " << frame.offset << "\n";
        for (auto& statement : frame.statements) {
            gen_statement(output, statement, frame);
        }
    }

    void gen_function(std::stringstream& output, sema::Function& function) {
        output << function.identifier << ":\n"
        "push rbp\n"
        "mov rbp, rsp\n";
        gen_frame(output, function.frame);
    }

    std::string generate(sema::SymbolTable& table) {
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
