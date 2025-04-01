#pragma once

#include "arena.hpp"
#include "numbers.hpp"
#include "uninitialized.hpp"
#include "utils.hpp"
#include <cassert>
#include <new>

template <typename T>
class SmallVector {
    Uninitialized<T> * m_memory;
    usize m_size;
    usize m_capacity;
public:
    SmallVector(Empty)
    : m_memory(nullptr), m_size(0), m_capacity(0) {
        static_assert(std::is_trivially_destructible_v<T>);
    }
    SmallVector(std::span<Uninitialized<T>> memory)
    : m_memory(memory.data()), m_size(0), m_capacity(memory.size()) {
        static_assert(std::is_trivially_destructible_v<T>);
    }
    SmallVector(Arena& arena, usize capacity)
    : SmallVector(arena.allocate_n_uninit<T>(capacity)) {}
    usize size() const { return m_size; }
    template <typename ...Args>
    T * try_emplace_back(Args&&... args) {
        if (m_size == m_capacity) {
            return nullptr;
        }
        Uninitialized<T> * slot = m_memory + m_size++;
        return slot->construct(std::forward<Args>(args)...);
    }
    template <typename ...Args>
    T& emplace_back(Args&&... args) {
        T * ptr = try_emplace_back(std::forward<Args>(args)...);
        if (!ptr) {
            throw std::bad_alloc();
        }
        return *ptr;
    }
    T * try_push_back(T&& t) {
        return try_emplace_back(std::move(t));
    }
    T * try_push_back(const T& t) {
        return try_emplace_back(t);
    }
    T& push_back(T&& t) {
        return emplace_back(t);
    }
    T& push_back(const T& t) {
        return emplace_back(t);
    }
    T * begin() { return m_memory->get(); }
    T * end() { return m_memory->get() + m_size; }
    const T * begin() const { return m_memory->get(); }
    const T * end() const { return m_memory->get() + m_size; }
    const T * cbegin() const { return m_memory->get(); }
    const T * cend() const { return m_memory->get() + m_size; }
    T& operator[](usize index) {
        assert(index < m_size);
        return m_memory[index].get();
    }
    const T& operator[](usize index) const {
        assert(index < m_size);
        return m_memory[index].get();
    }
};
