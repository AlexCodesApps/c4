#pragma once
#include "lexer.hpp"
#include "arena.hpp"
#include <span>
#include <cassert>
#include <optional>
#include <variant>

class TokenParser {
    std::span<Token> src;
    usize index;
    ref<Arena> m_arena;
public:
    TokenParser(std::span<Token> src, Arena& arena)
    : src(src), index(0), m_arena(arena) {
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
    class State {
        friend TokenParser;
        usize index;
        void * arena_ptr;
        State(usize index, void * arena_ptr)
        : index(index), arena_ptr(arena_ptr) {}
    };
    State get_state() const {
        return State(index, m_arena->get_current_ptr());
    }
    void set_state(State saved) {
        index = saved.index;
        m_arena->unsafe_set_current_ptr(saved.arena_ptr);
    }
    Arena& arena() {
        return m_arena.get();
    }
    const Arena& arena() const {
        return m_arena.get();
    }
};
