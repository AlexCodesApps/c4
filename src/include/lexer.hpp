#pragma once
#include <optional>
#include <string_view>
#include <vector>
#include "numbers.hpp"

enum class TokenType {
    FUNCTION,
    RETURN,
    INTEGER,
    LPAREN,
    RPAREN,
    COLON,
    COMMA,
    SEMICOLON,
    LBRACE,
    RBRACE,
    IDENTIFIER,
    AMPERSAND,
    STAR,
    DOT,
    EQ,
    _EOF,
};

struct Token {
    TokenType type;
    std::pair<usize, usize> source_location;
    std::string_view source_string;
    union {
        usize integer;
    };
};

std::string_view token_type_to_string(TokenType type);
std::optional<std::vector<Token>> lex(std::string_view str);
