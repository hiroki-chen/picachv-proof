MODULE_PATH		:= $(CURDIR)/../executor_lib

DEBUG			?= 1
CARGO_BUILD_FLAGS	= +nightly build
CARGO_RUN_FLAGS		= +nightly run

ifeq ($(DEBUG), 0)
	CARGO_BUILD_FLAGS	+= -r
	CARGO_RUN_FLAGS		+= -r 
endif

.phony: build run

build:
	@cargo $(CARGO_BUILD_FLAGS) --manifest-path=$(MODULE_PATH)/Cargo.toml
	@cargo $(CARGO_BUILD_FLAGS)

run: build
	@cargo $(CARGO_RUN_FLAGS)
