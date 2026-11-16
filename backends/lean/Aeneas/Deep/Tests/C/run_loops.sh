#!/bin/sh
# Differential test of the C printer on the generated `loops` crate (tests/lean/Loops.lean):
# generate its C with `#deep_c` from the tests project, compile it with harness_loops.c, run.
# Usage (from tests/lean, after `lake build Loops`): sh ../../backends/lean/Aeneas/Deep/Tests/C/run_loops.sh [output directory]
set -e
here=$(cd "$(dirname "$0")" && pwd)
out=${1:-$(mktemp -d)}
printf 'import Aeneas.Deep.CDriver\nimport Loops\n#deep_c "%s/loops.c" loops\n' "$out" > "$out/GenLoops.lean"
lake env lean "$out/GenLoops.lean"
cc -std=c11 -Wall -Wno-parentheses-equality -Wno-unused-but-set-variable -Wno-unused-variable \
  -I"$out" -o "$out/harness_loops" "$here/harness_loops.c"
"$out/harness_loops"
