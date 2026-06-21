#!/usr/bin/env bash
# Type-check every Agda module: the seven principles, the theses, and the
# extractable kernel.  Requires `agda` and the standard library.
set -euo pipefail

# Agda needs a UTF-8 locale.
export LC_ALL="${LC_ALL:-C.UTF-8}"
export LANG="${LANG:-C.UTF-8}"

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT/agda"

echo "Type-checking Sanctum (Agda) ..."
agda -i src src/Everything.agda
echo "OK — all theses and modules type-check."
