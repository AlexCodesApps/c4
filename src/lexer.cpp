#include "include/lexer.hpp"
#include "include/utils.hpp"
#include <print>
#include <string_view>
#include <sys/types.h>
#include <utility>

std::string_view token_type_to_string(TokenType type) {
    switch (type) {
    using enum TokenType;
    case FUNCTION:
        return "FUNCTION";
    case RETURN:
        return "RETURN";
    case LET:
        return "LET";
    case AS:
        return "AS";
    case TRUE:
        return "TRUE";
    case FALSE:
        return "FALSE";
    case NULLPTR:
        return "NULLPTR";
    case INTEGER:
        return "INTEGER";
    case LPAREN:
        return "LPAREN";
    case RPAREN:
        return "RPAREN";
    case COLON:
        return "COLON";
    case LBRACE:
        return "LBRACE";
    case RBRACE:
        return "RBRACE";
    case IDENTIFIER:
        return "IDENTIFIER";
    case COMMA:
        return "COMMA";
    case PLUS:
        return "PLUS";
    case MINUS:
        return "MINUS";
    case SEMICOLON:
        return "SEMICOLON";
    case AMPERSAND:
        return "AMPERSAND";
    case EQ:
        return "EQ";
    case STAR:
        return "STAR";
    case DOT:
        return "DOT";
    case _EOF:
        return "EOF";
    }
    std::unreachable();
}

auto lex(std::string_view str) -> std::optional<std::vector<Token>> {
    usize index = 0;
    usize row = 1, col = 1;
    std::vector<Token> output{};
    auto eof = [&](usize offset = 0) {
        return index + offset >= str.size();
    };
    auto peek = [&](usize offset = 0) {
        if (eof(offset)) {
            return '\0';
        }
        return str[index + offset];
    };
    auto advance = [&](){
        if (peek() == '\n') {
            ++row;
            col = 1;
        } else {
            ++col;
        }
        ++index;
    };
    auto iden = [&](std::string_view iden) {
        if (!str.substr(index).starts_with(iden)) {
            return false;
        }
        char c = peek(iden.size());
        if (part_of_iden(c)) {
            return false;
        }
        for (usize i = 0; i < iden.size(); ++i) {
            advance();
        }
        return true;
    };
    auto push_token = [&](TokenType type, std::string_view source_string) {
        output.push_back(Token{
            .type = type,
            .source_location = {row, col},
            .source_string = source_string,
            .integer = 0,
        });
    };
    while (!eof()) {
        char c = peek();
        switch (c) {
        case '(':
            push_token(TokenType::LPAREN, "(");
            advance();
            break;
        case ')':
            push_token(TokenType::RPAREN, ")");
            advance();
            break;
        case '{':
            push_token(TokenType::LBRACE, "{");
            advance();
            break;
        case '}':
            push_token(TokenType::RBRACE, "}");
            advance();
            break;
        case ',':
            push_token(TokenType::COMMA, ",");
            advance();
            break;
        case ';':
            push_token(TokenType::SEMICOLON, ";");
            advance();
            break;
        case ':':
            push_token(TokenType::COLON, ":");
            advance();
            break;
        case '=':
            push_token(TokenType::EQ, "=");
            advance();
            break;
        case '&':
            push_token(TokenType::AMPERSAND, "&");
            advance();
            break;
        case '*':
            push_token(TokenType::STAR, "*");
            advance();
            break;
        case '.':
            push_token(TokenType::DOT, ".");
            advance();
            break;
        case '+':
            push_token(TokenType::PLUS, "+");
            advance();
            break;
        case '-':
            push_token(TokenType::MINUS, "-");
            advance();
            break;
        case ' ':
        case '\n':
        case '\t':
        case '\r':
            advance();
            break;
        default:
            usize srow = row;
            usize scol = col;
            if (iden("fn")) {
                push_token(TokenType::FUNCTION, "fn");
            } else if (iden("return")) {
                push_token(TokenType::RETURN, "return");
            } else if (iden("let")) {
                push_token(TokenType::LET, "let");
            } else if (iden("as")) {
                push_token(TokenType::AS, "as");
            } else if (iden("true")) {
                push_token(TokenType::TRUE, "true");
            } else if (iden("false")) {
                push_token(TokenType::FALSE, "false");
            } else if (iden("nullptr")) {
                push_token(TokenType::NULLPTR, "nullptr");
            } else if (is_digit(c)) {
                usize start = index;
                usize count = 0;
                usize value = 0;
                char c;
                while (is_digit(c = peek())) {
                    value *= 10;
                    value += c - '0';
                    ++count;
                    advance();
                }
                output.push_back(Token{
                    .type = TokenType::INTEGER,
                    .source_location = {srow, scol},
                    .source_string = str.substr(start, count),
                    .integer = value,
                });
            } else if (is_alpha(c) || c == '_') {
                usize start = index;
                usize count = 0;
                while (part_of_iden(peek())) {
                    advance();
                    ++count;
                }
                output.push_back(Token{
                    .type = TokenType::IDENTIFIER,
                    .source_location = {srow, scol},
                    .source_string = str.substr(start, count),
                    .integer = 0,
                });
            } else {
                std::print(stderr, "unexpected token '");
                if (is_printable_char(c)) {
                    std::print(stderr, "{}", c);
                } else {
                    std::print(stderr, "{}", (u16)c);
                }
                std::println(stderr, "' ({}, {})", srow, scol);
                return std::nullopt;
            }
        }
    }
    output.push_back(Token {
        .type = TokenType::_EOF,
        .source_location = {row, col},
        .source_string = "",
        .integer = 0,
    });
    return std::optional(std::move(output));
}
