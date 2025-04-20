#pragma once
#define _CONCAT_(a, b) a##b
#define CONCAT(a, b) _CONCAT_(a, b)
#define MACRO_VAR(a) CONCAT(_macro_var_, CONCAT(__LINE__, a))
