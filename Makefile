.PHONY: clean, make, all, fmt, release

RM=cmake -E rm -rf

FMT=find src '(' -name '*.c' -o -name '*.h' ')' -exec clang-format -i {} +

all: build fmt make

make: build
	cmake --build build

release: clean
	cmake -S . -B build -DCMAKE_BUILD_TYPE=Release
	cmake --build build --clean-first

build: CMakeLists.txt Makefile
	cmake -S . -B build -DCMAKE_BUILD_TYPE=Debug

fmt:
	$(FMT)

clean:
	$(RM) build
