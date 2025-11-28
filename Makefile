.PHONY: clean, make, all, fmt, release

CC=clang
RM=rm -rf
CP=cp

FMT=echo $(find src -name '*.c' -o -name '*.h') main.c | xargs clang-format -i

all: build fmt make

make: build
	cmake --build build

release: clean
	cmake -S . -B build -DCMAKE_C_COMPILER=$(CC) -DCMAKE_BUILD_TYPE=Release
	cmake --build build

build: CMakeLists.txt Makefile
	cmake -S . -B build -DCMAKE_C_COMPILER=$(CC) -DCMAKE_BUILD_TYPE=Debug

fmt:
	$(FMT)

clean:
	$(RM) build
