.PHONY: clean, make, all, fmt, lsp, release

CC=clang
RM=rm -rf
CP=cp

ifeq (, $(shell which clang-format))
	FMT=find src -name '*.c' -o -name '*.h' | xargs clang-format -i
else
	FMT=echo 'Install clang-format to format code'
endif

all: build fmt make

make: build
	cmake --build build

lsp: compile_commands.json

compile_commands.json: build
	$(COPY) build/compile_commands.json .

release: clean
	cmake -S . -B build -DCMAKE_C_COMPILER=$(CC)
	cmake --build build

build: CMakeLists.txt Makefile
	cmake -S . -B build -DCMAKE_C_COMPILER=$(CC) -DCMAKE_BUILD_TYPE=Debug

fmt:
	$(FMT)

clean:
	$(RM) build
