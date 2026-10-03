#!/bin/bash
# soq on the run of Section 5 of the paper (n = 300, m = 5, rho = 1.3, window [0.35, 14]): writes the grid file and
# the tables table-T.txt into TABLES (option emitall), and prints its output in the form of
# out/soq-m5-n300-r1.3-w0.35-14.txt (the times removed). From the root of the package:
#   code/soq/run.sh TABLES > soq.txt && cmp soq.txt code/soq/out/soq-m5-n300-r1.3-w0.35-14.txt
# The grid file of out/ is the header line of that file followed by TABLES/grid.txt.
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd)
[ $# -eq 1 ] || { sed -n '2,6p' "$0" >&2; exit 2; }
mkdir -p "$1"
(cd "$here" && cargo build --release -q) || exit 1
bin=${CARGO_TARGET_DIR:-$here/target}/release/soq
echo "# args 300 5 1.3 1 0.35 14"
"$bin" 300 5 1.3 1 0.35 14 "emitall=$1" 2>&1 | grep -v '^t=' | grep -vE '^time |^wall '
echo "# exit status ${PIPESTATUS[0]}"
