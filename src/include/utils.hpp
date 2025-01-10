#include "numbers.hpp"
#include <concepts>

inline bool is_alpha(char c) {
    return ('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z');
}

inline bool is_digit(char c) {
    return '0' <= c && c <= '9';
}

inline bool is_alphanumeric(char c) {
    return is_digit(c) || is_alpha(c);
}

inline bool part_of_iden(char c) {
    return is_alphanumeric(c) || c == '_';
}

inline bool is_printable_char(char c) {
    return (u16)c-0x20 < 0x5f;
}

template <std::integral I>
bool is_multiple_of_two(I i) {
    return !(i & (i - 1));
}

template <std::integral I>
I align_mul_of_two(I i, I align) {
    assert(is_multiple_of_two(align));
    return (i + (align - 1)) & ~(align - 1);
}


template <typename ...Args>
struct Overload : Args... {
    using Args::operator()...;
};

template <typename T>
class ref {
    T * m_ptr;
public:
    explicit ref(T& value)
    : m_ptr(&value) {}
    T& get() const {
        assert(m_ptr);
        return *m_ptr;
    }
    T* get_ptr() const {
        assert(m_ptr);
        return m_ptr;
    }
    T& operator*() const {
        assert(m_ptr);
        return *m_ptr;
    }
    T* operator->() const {
        assert(m_ptr);
        return m_ptr;
    }
    operator ref<const T>() const {
        return ref(*m_ptr);
    }
    auto operator<=>(const ref& other) const = default;
    auto operator<=>(const T * other) const {
        return m_ptr <=> other;
    }
};
