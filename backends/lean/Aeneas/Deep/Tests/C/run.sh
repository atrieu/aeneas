#!/bin/sh
# Differential test of the C printer on the hand-written deep terms of
# Aeneas/Deep/Tests.lean: generate the C with `#deep_c`, compile it with harness.c, run it.
# Usage (from backends/lean): sh Aeneas/Deep/Tests/C/run.sh [output directory]
set -e
here=$(cd "$(dirname "$0")" && pwd)
out=${1:-$(mktemp -d)}
printf 'import Aeneas.Deep\n#deep_c "%s/tests.c"\n' "$out" > "$out/GenTests.lean"
lake env lean "$out/GenTests.lean"
cc -std=c11 -Wall -Wno-parentheses-equality -Wno-unused-but-set-variable -Wno-unused-variable \
  -I"$out" -o "$out/harness" "$here/harness.c"
"$out/harness"
