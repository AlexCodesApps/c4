#include <fstream>
#include <optional>
#include <print>
#include "include/lexer.hpp"
#include "include/ast.hpp"
#include "include/sema.hpp"
#include "include/gen.hpp"

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
    auto symbol_table = ({
        auto result = sema::parse(ast);
        if (!result) {
            std::println(stderr, "semantic error");
            return -5;
        }
        std::move(*result);
    });
    std::println("{}", gen::generate(symbol_table));
}
