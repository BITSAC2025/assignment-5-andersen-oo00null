#!/usr/bin/env bash
set -euo pipefail
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
REPO_ROOT="$SCRIPT_DIR/.."
cd "$REPO_ROOT"
CLANG="${LLVM_DIR:-}/bin/clang"
if [ ! -x "$CLANG" ]; then
  CLANG="clang"
fi
bash build.sh Assignment-5-Andersen
for f in Assignment-5-Andersen/Test-Cases/*.c; do
  bc="${f%.c}.bc"
  "$CLANG" -O0 -g -emit-llvm -c "$f" -o "$bc"
  Assignment-5-Andersen/andersen "$bc"
done
ls -1 Assignment-5-Andersen/Test-Cases/*.res.txt