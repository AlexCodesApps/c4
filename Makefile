BIN_DIR=build
OBJ_DIR=$(BIN_DIR)/obj
SRC_DIR=src
TARGET_FILE=main
TARGET=$(BIN_DIR)/$(TARGET_FILE)
BUILD_OBJS=$(patsubst $(SRC_DIR)/%.c, $(OBJ_DIR)/%.o, $(wildcard $(SRC_DIR)/*.c)) $(OBJ_DIR)/main.o
MODE ?= DEBUG
WARNINGS=-Wimplicit-fallthrough -Wall
CFLAGS_DEBUG=-g -fsanitize=address
CFLAGS_RELEASE=-O2 -flto -DNDEBUG
CFLAGS= $(CFLAGS_$(MODE)) $(WARNINGS) -std=c23
BUILD_OBJ_COMMAND=$(CC) -MMD -c $< -o $@ $(CFLAGS)

all: $(TARGET)

debug:
	$(MAKE) MODE=DEBUG

release:
	$(MAKE) MODE=RELEASE

$(TARGET): $(BUILD_OBJS)
	$(CC) $(BUILD_OBJS) -o $@ $(CFLAGS)

$(OBJ_DIR)/main.o: main.c
	$(BUILD_OBJ_COMMAND)

$(OBJ_DIR)/%.o: $(SRC_DIR)/%.c | $(OBJ_DIR)
	$(BUILD_OBJ_COMMAND)

$(OBJ_DIR):
	mkdir -p build/obj

format:
	find -name *.c -o -name *.h | xargs clang-format -i

clean:
	rm -r build

-include $(BUILD_OBJS:.o=.d)

.PHONY: format, clean
