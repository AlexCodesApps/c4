BIN_DIR=build
OBJ_DIR=$(BIN_DIR)/obj
SRC_DIR=src
TARGET=main
CFLAGS=-std=c23 -g -Wimplicit-fallthrough
BUILD_OBJS = $(patsubst $(SRC_DIR)/%.c, $(OBJ_DIR)/%.o, $(wildcard $(SRC_DIR)/*.c)) $(OBJ_DIR)/main.o
BUILD_OBJ_COMMAND=$(CC) -MMD -c $< -o $@ $(CFLAGS)

$(BIN_DIR)/$(TARGET): $(BUILD_OBJS)
	$(CC) $(BUILD_OBJS) -o $@

$(OBJ_DIR)/main.o: main.c
	$(BUILD_OBJ_COMMAND)

$(OBJ_DIR)/%.o: $(SRC_DIR)/%.c | $(OBJ_DIR)
	$(BUILD_OBJ_COMMAND)

$(OBJ_DIR):
	mkdir -p build/obj

.PHONY: format
format:
	find -name *.c -o -name *.h | xargs clang-format -i

-include $(BUILD_OBJS:.o=.d)
