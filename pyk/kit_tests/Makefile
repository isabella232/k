K_ROOT := $(abspath ../..)
K_BIN  := $(K_ROOT)/k-distribution/target/release/k/bin

KOMPILE = $(K_BIN)/kompile
KAST    = $(K_BIN)/kast
KRUN    = $(K_BIN)/krun
KPROVE  = $(K_BIN)/kprove
KPROVEX = $(K_BIN)/kprovex
KPYK    = $(K_BIN)/kpyk
KIT     = kit

export PATH := $(K_BIN):$(PATH)


.PHONY: all clean test test-kit

all: test

clean:
	rm -rf verification-kompiled
	rm -f looping-spec.json
	rm -rf .kit
	rm -rf .kprove-*

test: test-kit

test-kit: .kit/config.json
	$(KIT) expand 4e1cef5a8d1cf4291f6cca7f05e6f9dc915622be845a6d25b09608bac7d5514e
	$(KIT) expand ca5c0c94e496932c34fadda9b7e13477f892b72749d5373e2e78338214043b87
	$(KIT) expand 9172179ec48f4b95c05f773f343d94078cff918a2f7899a0c7cfcea99cbb9d81
	$(KIT) expand 9635cb3ed192f730fb8b95a3859b77c672fd5d5035cf477d7fb37cf01e1c0e02
	$(KIT) cover  deff9a41dd9634ece272d7c0ecac0750b9402a41714bf9fec60b73630ac0ce3d \
	         --by 9172179ec48f4b95c05f773f343d94078cff918a2f7899a0c7cfcea99cbb9d81 \
			 --semantic

.kit/config.json: looping-spec.json
	$(KIT) init --force verification-kompiled verification.k $<

verification-kompiled/timestamp: verification.k control-flow.k
	$(KOMPILE) $< --backend haskell --emit-json

looping-spec.json: looping-spec.k verification-kompiled/timestamp
	$(KPROVEX) $< --backend haskell --directory . --emit-json-spec $@ --dry-run
