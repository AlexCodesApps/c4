#pragma once
#include "lexer.hpp"
#include <span>
#include <cassert>
#include <optional>
#include <variant>

class TokenParser {
    std::span<Token> src;
    usize index;
public:
    TokenParser(std::span<Token> src)
    : src(src), index(0) {
        assert(src.size() > 0 && src.back().type == TokenType::_EOF);
    }
    bool eof(usize offset = 0) const {
        return index + offset >= src.size() - 1;
    }
    const Token& peek(usize offset = 0) const {
        if (eof(offset)) {
            return src.back();
        }
        return src.at(index + offset);
    }
    const Token& peek_advance() {
        auto& token = peek();
        advance();
        return token;
    }
    bool match(TokenType type, usize offset = 0) const {
        return peek(offset).type == type;
    }
    void advance(usize offset = 1) {
        index += offset;
    }
    bool advance_if_match(TokenType type) {
        if (match(type)) {
            advance();
            return true;
        }
        return false;
    }
    std::optional<std::monostate> expect(TokenType type) {
        if (match(type)) {
            advance();
            return std::monostate{};
        }
        return std::nullopt;
    }
    usize get_position() const {
        return index;
    }
    void set_position(usize saved) {
        index = saved;
    }
};
