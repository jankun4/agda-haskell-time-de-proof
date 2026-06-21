#!/usr/bin/env bash
# Generate Haskell from the verified Agda kernel (GHC/MAlonzo backend) and
# build a native binary that runs the kernel's self-test.  This is the
# literal "Haskell generated from Agda" path: the produced sources land in
# haskell/gen/ and the proven core (quorum rule, median time, total
# contract evaluator) runs unchanged.
set -euo pipefail

export LC_ALL="${LC_ALL:-C.UTF-8}"
export LANG="${LANG:-C.UTF-8}"

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT/agda"

OUT="$ROOT/haskell/gen"
mkdir -p "$OUT"

echo "Extracting Haskell from agda/src/Sanctum/Kernel.agda ..."
agda -i src --compile --compile-dir="$OUT" src/Sanctum/Kernel.agda

echo
echo "Generated Haskell under: haskell/gen/MAlonzo/Code/Sanctum/Kernel.hs"
echo "Running the extracted kernel self-test:"
echo "------------------------------------------------------------"
"$OUT/Kernel"
echo "------------------------------------------------------------"
echo "OK — the verified core was generated and executed."
