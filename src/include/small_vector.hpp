#pragma once

#include "numbers.hpp"
#include "uninitialized.hpp"
#include <cassert>
#include <new>
template <typename T>
class SmallVector {
    T * m_memory;
    usize m_size;
    usize m_capacity;
public:
    SmallVector(std::span<Uninitialized<T>> memory)
    : m_memory(memory.data()), m_size(0), m_capacity(memory.size()) {}
    usize size() const { return m_size; }
    template <typename ...Args>
    T * try_emplace_back(Args&&... args) {
        if (m_size > m_capacity) {
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
    T * begin() { return m_memory; }
    T * end() { return m_memory + m_size; }
    const T * cbegin() const { return m_memory; }
    const T * cend() const { return m_memory + m_size; }
    T& operator[](usize index) {
        assert(index < m_size);
        return m_memory[index].get();
    }
    const T& operator[](usize index) const {
        assert(index < m_size);
        return m_memory[index].get();
    }
};
