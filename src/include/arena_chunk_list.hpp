#pragma once

#include "arena.hpp"
#include "numbers.hpp"
#include "uninitialized.hpp"
#include <cassert>
#include <initializer_list>
#include <type_traits>
#include <utility>

template <typename T, usize ChunkSize>
class ArenaChunkList {
    struct Chunk {
        Uninitialized<T> array[ChunkSize];
        Chunk * next;
    };
    Chunk * m_first;
    Chunk * m_end;
    usize m_size;
public:
    ArenaChunkList()
    : m_first(nullptr), m_end(nullptr), m_size(0) {
        static_assert(std::is_trivially_destructible_v<T>,
            "maybe cheap but removes expensive deallocation routine");
    }
    ArenaChunkList(Arena& arena, std::initializer_list<T> list)
    : ArenaChunkList() {
        for (auto& elem : list) {
            push_back(arena, std::move(elem));
        }
    }
    template <typename ...Args>
    T& emplace_back(Arena& arena, Args&&... args) {
        [[unlikely]]if (!m_first) {
            m_first = m_end = arena.allocate<Chunk>().get_ptr();
            m_size = 1;
            return *m_first->array[0].construct(std::forward<Args>(args)...);
        }
        usize used_chunk_size = m_size % ChunkSize;
        if (used_chunk_size == ChunkSize) {
            Chunk * new_chunk = arena.allocate<Chunk>().get_ptr();
            m_end->next = new_chunk;
            m_end = new_chunk;
            used_chunk_size = 0;
        }
        ++m_size;
        return *m_end->array[used_chunk_size].construct(std::forward<Args>(args)...);
    }
    T& push_back(Arena& arena, T&& t) {
        return emplace_back(arena, std::move(t));
    }
    T& push_back(Arena& arena, const T& t) {
        return emplace_back(arena, t);
    }
    usize size() const {
        return m_size;
    }
    T& operator[](usize index) {
        assert(index < m_size);
        usize chunk_index = index / ChunkSize;
        usize real_index = index % ChunkSize;
        Chunk * current = m_first;
        for (usize i = 0; i < chunk_index; ++i) {
            current = current->next;
        }
        return current[real_index];
    }
    const T& operator[](usize index) const {
        assert(index < m_size);
        usize chunk_index = index / ChunkSize;
        usize real_index = index % ChunkSize;
        Chunk * current = m_first;
        for (usize i = 0; i < chunk_index; ++i) {
            current = current->next;
        }
        return current[real_index];
    }
    T& front() {
        assert(m_size > 0);
        return m_first->array[0].get();
    }
    const T& front() const {
        assert(m_size > 0);
        return m_first->array[0].get();
    }
    T& back() {
        assert(m_size > 0);
        usize index = m_size % ChunkSize;
        return m_end->array[index].get();
    }
    const T& back() const {
        assert(m_size > 0);
        usize index = m_size % ChunkSize;
        return m_end->array[index].get();
    }
private:
    template <typename U>
    struct IteratorMixin {
        U& get() {
            return *static_cast<U *>(this);
        }
        const U& get() const {
            return *static_cast<const U *>(this);
        }
        bool operator==(U other) const {
            return get().current == other.current && get().current_chunk_index == other.current_chunk_index;
        }
        bool operator!=(U other) const {
            return !(*this == other);
        }
        const T& operator*() const {
            return *get().current->array[get().current_chunk_index].get();
        }
        U& operator++() {
            ++get().current_chunk_index;
            if (get().current_chunk_index == ChunkSize) {
                get().current = get().current->next;
                get().current_chunk_index = 0;
            }
            return get();
        }
    };
public:
    class Iterator : public IteratorMixin<Iterator> {
        friend ArenaChunkList;
        Chunk * current;
        usize current_chunk_index;
        Iterator(Chunk * current, usize current_chunk_index)
        : current(current), current_chunk_index(current_chunk_index)
        {}
    public:
        T& operator*() {
            return *current->array[current_chunk_index].get();
        }
    };
    class ConstIterator : public IteratorMixin<ConstIterator> {
        friend ArenaChunkList;
        const Chunk * current;
        usize current_chunk_index;
        ConstIterator(const Chunk * current, usize current_chunk_index)
        : current(current), current_chunk_index(current_chunk_index)
        {}
    };
    friend Iterator;
    friend ConstIterator;
    Iterator begin() {
        return Iterator(m_first, 0);
    }
    Iterator end() {
        return Iterator(m_end, m_size % ChunkSize);
    }
    ConstIterator begin() const {
        return ConstIterator(m_first, 0);
    }
    ConstIterator end() const {
        return ConstIterator(m_end, m_size % ChunkSize);
    }
    ConstIterator cbegin() const {
        return ConstIterator(m_first, 0);
    }
    ConstIterator cend() const {
        return ConstIterator(m_end, m_size % ChunkSize);
    }
};
