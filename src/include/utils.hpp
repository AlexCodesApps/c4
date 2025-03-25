#pragma once
#include "numbers.hpp"
#include <concepts>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

constexpr inline bool is_alpha(char c) {
    return ('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z');
}

constexpr inline bool is_digit(char c) {
    return '0' <= c && c <= '9';
}

constexpr inline bool is_alphanumeric(char c) {
    return is_digit(c) || is_alpha(c);
}

constexpr inline bool part_of_iden(char c) {
    return is_alphanumeric(c) || c == '_';
}

constexpr inline bool is_printable_char(char c) {
    return (u16)c-0x20 < 0x5f;
}

template <std::integral I>
constexpr bool is_multiple_of_two(I i) {
    return !(i & (i - 1)) && i != 0;
}

template <std::integral I>
constexpr I align_mul_of_two(I i, I align) {
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
    // auto operator<=>(const ref& other) const = default;
    // auto operator<=>(const T * other) const {
    //     return m_ptr <=> other;
    // }
};


template <typename T>
auto unique_ptr_wrap(T&& v) {
    using RT = std::remove_cvref_t<T>;
    return std::make_unique<RT>(std::forward<T>(v));
}

template <bool Value, template <typename> typename MetaClass, typename T>
struct apply_metaclass_if {
    using type = std::conditional_t<Value, MetaClass<T>, T>;
};

template <bool Value, template <typename> typename MetaClass, typename T>
using apply_metaclass_if_t = apply_metaclass_if<Value, MetaClass, T>::type;

template <typename From, typename To>
struct propogate_qualifiers
{
    using FromWithoutRef = std::remove_reference_t<From>;
    using type = apply_metaclass_if_t<std::is_rvalue_reference_v<From>, std::add_rvalue_reference_t,
                    apply_metaclass_if_t<std::is_lvalue_reference_v<From>, std::add_lvalue_reference_t,
                        apply_metaclass_if_t<std::is_const_v<FromWithoutRef>, std::add_const_t,
                            apply_metaclass_if_t<std::is_volatile_v<FromWithoutRef>, std::add_volatile_t,
                                std::remove_cvref_t<To>>>>>;
};
template <typename From, typename To>
using propogate_qualifiers_t = propogate_qualifiers<From, To>::type;

template <typename T, typename Base>
concept poly_variant_of = requires { typename T::poly_variant_tag; } && std::is_same_v<Base, typename T::base_type>;

template <typename Parent, typename ...Children>
class poly_variant : public std::variant<Children...> {
    using Base__ = std::variant<Children...>;
    struct Visitor__ {
        template <poly_variant_of<Parent> T>
        constexpr auto& operator()(T& value) const noexcept {
            return value.get_base();
        }
        template <poly_variant_of<Parent> T>
        constexpr auto&& operator()(T&& value) const noexcept {
            return std::move(value.get_base());
        }
        template <poly_variant_of<Parent> T>
        constexpr const auto& operator()(const T& value) const noexcept {
            return value.get_base();
        }
        template <typename T>
        constexpr decltype(auto) operator()(T&& value) const noexcept {
            return static_cast<propogate_qualifiers_t<T, Parent>>(value);
        }
    };
public:
    using Base__::Base__;
    using base_type = Parent;
    struct poly_variant_tag {};
    Parent& get_base() & noexcept {
        return std::visit(Visitor__{}, *this);
    }
    Parent&& get_base() && noexcept {
        return std::visit(Visitor__{}, std::move(*this));
    }
    const Parent& get_base() const& noexcept {
        return std::visit(Visitor__{}, *this);
    }
    Parent& operator*() & noexcept {
        return get_base();
    }
    Parent&& operator*() && noexcept {
        return std::move(get_base());
    }
    const Parent& operator*() const& noexcept {
        return std::visit(get_base());
    }
    Parent* operator->() noexcept {
        return &get_base();
    }
    const Parent* operator->() const noexcept {
        return &get_base();
    }
};
