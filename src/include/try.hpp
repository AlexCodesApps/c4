#ifndef LIB_TRY_MACRO_HPP
#define LIB_TRY_MACRO_HPP
#include <type_traits>
#include <utility>
#ifdef __cpp_lib_optional
#include <optional>
#endif

struct try_impl_lvalue_base {};
template <typename T>
struct try_impl_lvalue : try_impl_lvalue_base { T * value; };
template <typename T, typename U>
auto try_impl_propagate_lvalue(U&& value) -> decltype(auto) {
    if constexpr (std::is_rvalue_reference_v<T> && !std::is_pointer_v<std::remove_reference_t<T>>) {
        return std::move(value);
    } else {
        return try_impl_lvalue<std::remove_reference_t<U>> { .value = &value };
    }
}

template <typename T>
auto try_impl_collapse_lvalue(T&& value) -> decltype(auto) {
    if constexpr (std::is_base_of_v<try_impl_lvalue_base, std::remove_reference_t<T>>) {
        return *value.value;
    } else {
        return std::forward<T>(value);
    }
}

template <typename T>
struct try_impl_castable_error {
    T&& value;
    template <typename U>
    operator U*() {
        return nullptr;
    }
    operator bool() {
        return false;
    }
#ifdef __cpp_lib_optional
    template <typename U>
    operator std::optional<U>() {
        return std::nullopt;
    }
#endif
};

#define TRY(value) try_impl_collapse_lvalue(({ \
    auto&& _opt_ = value; \
    using type = decltype(_opt_); \
    if (!_opt_) { \
        return try_impl_castable_error<type>{ std::forward<type>(_opt_) }; \
    } \
    try_impl_propagate_lvalue<type>(*_opt_); \
}))
#endif
