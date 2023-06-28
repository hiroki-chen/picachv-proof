MODULE_PATH := $(CURDIR)/../executor_lib

.phony: build run

build:
	@cargo build -r --manifest-path=$(MODULE_PATH)/Cargo.toml
	@cargo build -r

run: build
	@cargo run -r
