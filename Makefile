SHELL := /bin/sh

WRAPPER_SOURCE := scripts/exe.sh
WRAPPER_TARGET := anvil
BUILT_BIN := _build/default/bin/main.exe
INSTALL_TARGET := /usr/local/bin/anvil

.DEFAULT_GOAL := anvil

.PHONY: all anvil install build clean

all: anvil

anvil: build $(WRAPPER_SOURCE)
	cp "$(WRAPPER_SOURCE)" "$(WRAPPER_TARGET)"
	chmod +x "$(WRAPPER_TARGET)"

install: build
	install -m 755 "$(BUILT_BIN)" "$(INSTALL_TARGET)"

build:
	dune build ./bin/main.exe

clean:
	dune clean
	rm -f "$(WRAPPER_TARGET)"
