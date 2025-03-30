#pragma once
#include <memory>
#include <utility>

template <typename T>
class Uninitialized {
    struct Placeholder {
    };
    union {
        T storage;
        Placeholder _;
    };
public:
    constexpr Uninitialized()
    : _(Placeholder{}) {}
    constexpr ~Uninitialized() {}
    template <typename ...Args>
    constexpr T * construct(Args&&... args) {
        return std::construct_at(&storage, std::forward<Args>(args)...);
    }
    constexpr void destroy() {
        std::destroy_at(&storage);
    }
    constexpr T * get() {
        return &storage;
    }
};
