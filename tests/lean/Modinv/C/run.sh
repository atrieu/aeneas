#!/bin/sh
# The modular inversion example: print the C of its deep terms with `#deep_c`, compile it
# with harness.c, run it. Usage (from tests/lean, after `lake build Modinv`):
#   sh Modinv/C/run.sh [output directory]
set -e
here=$(cd "$(dirname "$0")" && pwd)
out=${1:-$(mktemp -d)}
printf 'import Aeneas.Deep.CDriver\nimport Modinv.Modinv\n#deep_c "%s/modinv.c" modinv\n' "$out" > "$out/GenModinv.lean"
lake env lean "$out/GenModinv.lean"
cc -std=c11 -Wall -Wno-parentheses-equality -Wno-unused-but-set-variable -Wno-unused-variable \
  -I"$out" -o "$out/harness" "$here/harness.c"
"$out/harness"
