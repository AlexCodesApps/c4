#include <stdint.h>

#define FILLREGS uint64_t __a, uint64_t __b, uint64_t __c, uint64_t __d, uint64_t __e, uint64_t __f, \
				double _a, double _b, double _c, double _d, double _e, double _f, double _g, double _h

struct __attribute__((aligned(16))) bar {
	uint64_t a;
};

// uint64_t foo(FILLREGS, uint64_t a, uint64_t b, __float128 c) {
// 	return a + b + c;
// }
//
struct wol {
	uint64_t a;
	double b;
};

struct wol wool(void) {
	return (struct wol) {
		.a = 10,
		.b = 23.0f
	};
}
