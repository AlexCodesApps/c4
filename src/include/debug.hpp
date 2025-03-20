#pragma once

#ifdef _GLIBCXX_DEBUG
#include <print>
#include <source_location>
#define DEBUG(...) __VA_ARGS__
#else
#define DEBUG(...)
#endif
DEBUG (
    namespace _detail {
        enum debug_log_type {
            NORMAL,
            WARNING,
            ERROR,
        };
        template <typename ...Args>
        void
        base_debug(debug_log_type type, std::source_location location,
                    std::format_string<Args...> string, Args&&... args) {
            std::string_view name;
            std::string_view color;
            switch (type) {
            case debug_log_type::NORMAL:
                name = "NORMAL";
                color = "\x1b[32m";
                break;
            case debug_log_type::WARNING:
                name = "WARNING";
                color = "\x1b[33m";
                break;
            case debug_log_type::ERROR:
                name = "ERROR";
                color = "\x1b[31m";
                break;
            }
            std::print(stderr, "{}DEBUG LOG [TYPE : {}, LINE : {}, FILE : {}, FUNCTION : {}]\nMSG : ",
                color, name, location.line(), location.file_name(), location.function_name());
            std::println(stderr, string, std::forward<Args>(args)...);
            std::print(stderr, "\x1b[0m");
            if (type == debug_log_type::ERROR) {
                abort();
            }
        }
    }
)
#define DEBUG_LOG_BASE(type, msg, ...) do { DEBUG( \
    _detail::base_debug(type, std::source_location::current(), msg __VA_OPT__(, __VA_ARGS__))); } while(0)
#define DEBUG_LOG(msg, ...) DEBUG_LOG_BASE(_detail::debug_log_type::NORMAL, msg, __VA_ARGS__)
#define DEBUG_WARN(msg, ...) DEBUG_LOG_BASE(_detail::debug_log_type::WARNING, msg, __VA_ARGS__)
#define DEBUG_ERROR(msg, ...) do { \
    DEBUG_LOG_BASE(_detail::debug_log_type::ERROR, msg, __VA_ARGS__); \
    std::unreachable(); \
} while (0)
