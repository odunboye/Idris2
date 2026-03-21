#!/usr/bin/env bash
# Benchmark RefC incremental vs full build times.
# Run from the repo root: ./scripts/bench-build.sh
#
# Baseline (2026-03-21, Apple M2, idris2 0.8.0):
#   full build (tailrec-libs):        ~4.2s
#   incremental rebuild (no changes): ~0.8s
#   incremental rebuild (touch lib):  ~1.6s

set -euo pipefail

IDRIS2=${IDRIS2:-idris2}
TESTDIR=${TMPDIR:-/tmp}/refc-bench-$$
SRCDIR=$(cd "$(dirname "$0")/.." && pwd)
TESTCASE=$SRCDIR/tests/refc/tailrec-libs/tailrec.idr

echo "=== RefC build benchmark ==="
echo "Compiler: $($IDRIS2 --version 2>/dev/null || echo 'not found')"
echo "Test:     $TESTCASE"
echo

mkdir -p "$TESTDIR"
cp "$TESTCASE" "$TESTDIR/tailrec.idr"
cd "$TESTDIR"

ms_now() {
    # Portable millisecond timer: python3 fallback for macOS where
    # date +%s%3N is not supported.
    if date +%s%3N 2>/dev/null | grep -qE '^[0-9]+$'; then
        date +%s%3N
    else
        python3 -c 'import time; print(int(time.time()*1000))'
    fi
}

time_cmd() {
    local label=$1
    shift
    printf "%-40s" "$label"
    local start end elapsed
    start=$(ms_now)
    "$@" >/dev/null 2>&1
    end=$(ms_now)
    elapsed=$((end - start))
    printf "%d ms\n" "$elapsed"
}

# Full build
time_cmd "Full build:" \
    "$IDRIS2" --cg refc -o bench_out tailrec.idr

# Incremental rebuild — no source changes
time_cmd "Incremental (no changes):" \
    "$IDRIS2" --cg refc -o bench_out tailrec.idr

# Incremental rebuild — touch one source file
touch tailrec.idr
time_cmd "Incremental (source touched):" \
    "$IDRIS2" --cg refc -o bench_out tailrec.idr

echo
echo "Done. Temp dir: $TESTDIR"
