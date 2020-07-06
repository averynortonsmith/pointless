
SHELL:=/bin/bash

.PHONY: all
all: check bin/pointless

.PHONY: pub
pub:
	pub get

.PHONY: check
check: pub
	-dartanalyzer lib/pointless.dart

.PHONY: dev
dev: check bin/pointless

.PHONY: test
test: check bin/debug
	-tests/runTests.sh --test -tokenize tests/tokenizer/*.test
	-tests/runTests.sh --test -parse tests/parser/*.test
	-tests/runTests.sh --test -eval tests/interpreter/*.test
	
bin/pointless: makefile lib/*/*.dart
	dart2native lib/pointless.dart -o bin/pointless

bin/debug: makefile lib/*/*.dart
	dart2native lib/src/debug.dart -o bin/debug
