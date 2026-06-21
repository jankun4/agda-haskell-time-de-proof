# Sanctum — convenience targets.
.PHONY: all check extract build test demo clean

all: check build test

# Type-check every Agda thesis and module.
check:
	./scripts/check.sh

# Generate Haskell from the Agda kernel and run its self-test.
extract:
	./scripts/extract.sh

# Build the Haskell node.
build:
	cd haskell && cabal build all

# Run the node test-suite.
test:
	cd haskell && cabal run sanctum-test

# Run the hospital-network demo.
demo:
	cd haskell && cabal run sanctum-node

clean:
	rm -rf haskell/dist-newstyle haskell/gen
	find agda -name '*.agdai' -delete
