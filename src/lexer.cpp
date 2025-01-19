#include "include/lexer.hpp"
#include "include/utils.hpp"
#include <print>
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
    auto match = [&](char c) {
        if (peek() == c) {
            advance();
            return true;
        }
        return false;
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
    while (!eof()) {
        char c = peek();
        switch (c) {
        case '(':
            output.push_back(Token{
                .type = TokenType::LPAREN,
                .source_location = {row, col},
                .source_string = "("
            });
            advance();
            break;
        case ')':
            output.push_back(Token{
                .type = TokenType::RPAREN,
                .source_location = {row, col},
                .source_string = ")"
            });
            advance();
            break;
        case '{':
            output.push_back(Token{
                .type = TokenType::LBRACE,
                .source_location = {row, col},
                .source_string = "{"
            });
            advance();
            break;
        case '}':
            output.push_back(Token{
                .type = TokenType::RBRACE,
                .source_location = {row, col},
                .source_string = "}"
            });
            advance();
            break;
        case ',':
            output.push_back(Token{
                .type = TokenType::COMMA,
                .source_location = {row, col},
                .source_string = ","
            });
            advance();
            break;
        case ';':
            output.push_back(Token{
                .type = TokenType::SEMICOLON,
                .source_location = {row, col},
                .source_string = ";"
            });
            advance();
            break;
        case ':':
            output.push_back(Token{
                .type = TokenType::COLON,
                .source_location = {row, col},
                .source_string = ":"
            });
            advance();
            break;
        case '=':
            output.push_back(Token{
                .type = TokenType::EQ,
                .source_location = {row, col},
                .source_string = "="
            });
            advance();
            break;
        case '&':
            output.push_back(Token{
                .type = TokenType::AMPERSAND,
                .source_location = {row, col},
                .source_string = "&"
            });
            advance();
            break;
        case '*':
            output.push_back(Token{
                .type = TokenType::STAR,
                .source_location = {row, col},
                .source_string = "*"
            });
            advance();
            break;
        case '.':
            output.push_back(Token{
                .type = TokenType::DOT,
                .source_location = {row, col},
                .source_string = "."
            });
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
                output.push_back(Token{
                    .type = TokenType::FUNCTION,
                    .source_location = {srow, scol},
                    .source_string = "fn",
                });
            } else if (iden("return")) {
                output.push_back(Token{
                    .type = TokenType::RETURN,
                    .source_location = {srow, scol},
                    .source_string = "return",
                });
            } else if (iden("let")) {
                output.push_back(Token{
                    .type = TokenType::LET,
                    .source_location = {srow, scol},
                    .source_string = "let",
                });
            } else if (iden("as")) {
                output.push_back(Token{
                    .type = TokenType::AS,
                    .source_location = {srow, scol},
                    .source_string = "as",
                });
            } else if (iden("true")) {
                output.push_back(Token{
                    .type = TokenType::TRUE,
                    .source_location = {srow, scol},
                    .source_string = "true",
                });
            } else if (iden("false")) {
                output.push_back(Token{
                    .type = TokenType::FALSE,
                    .source_location = {srow, scol},
                    .source_string = "false",
                });
            } else if (iden("nullptr")) {
                output.push_back(Token{
                    .type = TokenType::TRUE,
                    .source_location = {srow, scol},
                    .source_string = "nullptr",
                });
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
    });
    return std::optional(std::move(output));
}
