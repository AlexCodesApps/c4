.PHONY: clean, make, all, fmt, lsp, release

all: build fmt make

make: build
	cmake --build build

lsp: compile_commands.json

compile_commands.json: build
	cp build/compile_commands.json .

release:
	CC=clang CXX=clang++ cmake -S . -B build && cmake --build build

build: CMakeLists.txt Makefile
	CC=clang CXX=clang++ cmake -S . -B build -DCMAKE_BUILD_TYPE=Debug

fmt:
	find src -name '*.c' -o -name '*.h' | xargs clang-format -i

clean:
	rm -r build
