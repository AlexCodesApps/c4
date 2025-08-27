.PHONY: clean, make, all

all: make compile_commands.json

make: build
	cmake --build build

compile_commands.json: build
	cp build/compile_commands.json .

build: CMakeLists.txt Makefile
	CC=clang CXX=clang++ cmake -S . -B build -DCMAKE_BUILD_TYPE=Debug

clean:
	rm -r build
