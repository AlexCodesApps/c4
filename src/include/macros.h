#pragma once
#define CONCAT_(a, b) a##b
#define CONCAT(a, b) CONCAT_(a, b)
#define MACRO_VAR(a) CONCAT(_macro_var_, CONCAT(__LINE__, a))
#define FST(a, ...) a
#define SND(a, b, ...) b
