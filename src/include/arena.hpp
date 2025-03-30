#pragma once
#include "numbers.hpp"
#include <new>
#include <span>
#include <type_traits>
#include <utility>
#include "uninitialized.hpp"
#include "utils.hpp"

class Arena {
    void * start;
    void * current;
    void * commited;
    void * end;
public:
    Arena(usize size);
    ~Arena();
    Arena(const Arena&) = delete;
    Arena(Arena&&) = delete;
    Arena& operator=(const Arena&) = delete;
    Arena& operator=(Arena&&) = delete;
    void * allocate_bytes(usize size, usize alignment);
    void reset_pointer();
    template <typename T, typename ...Args>
    ref<T> allocate(Args&&... args) {
        void * allocation = allocate_bytes(sizeof(T), alignof(T));
        [[unlikely]]if (!allocation) {
            throw std::bad_alloc();
        }
        return ref(*(new (allocation) T(std::forward<Args>(args)...)));
    }
    template <typename T>
    std::span<Uninitialized<T>> allocate_n_uninit(usize n) {
        void * ptr = allocate_bytes(sizeof(T) * n, alignof(T));
        return std::span(static_cast<Uninitialized<T>>(ptr), n);
    }
    template <typename U>
    auto wrap(U&& value) {
        using R = std::remove_cvref_t<U>;
        return allocate<R>(std::forward<U>(value));
    }
    void * get_current_ptr() const {
        return current;
    }
    void unsafe_set_current_ptr(void * new_current) {
        current = new_current;
    }
};
