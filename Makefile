.PHONY: clean, make, all, fmt

all: build fmt compile_commands.json make

make: build
	cmake --build build

compile_commands.json: build
	cp build/compile_commands.json .

build: CMakeLists.txt Makefile
	CC=clang CXX=clang++ cmake -S . -B build -DCMAKE_BUILD_TYPE=Debug

fmt:
	find src -name '*.c' -o -name '*.h' | xargs clang-format -i

clean:
	rm -r build
