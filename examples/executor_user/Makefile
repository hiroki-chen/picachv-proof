MODULE_PATH		:= $(CURDIR)/../executor_lib
NIGHTLY			?= 0
DEBUG			?= 1
CARGO_BUILD_FLAGS	= build
CARGO_RUN_FLAGS		= run

ifeq ($(NIGHTLY), 1)
	CARGO_BUILD_FLAGS	= +nightly build
	CARGO_RUN_FLAGS		= +nightly run
else
	CARGO_BUILD_FLAGS	= build
	CARGO_RUN_FLAGS		= run
endif

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
