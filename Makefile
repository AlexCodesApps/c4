.PHONY: clean, make

make: build
	cmake --build build

build: CMakeLists.txt Makefile
	cmake -S . -B build -DCMAKE_BUILD_TYPE=Debug

clean:
	rm -r build
