#!/usr/bin/env bash
# Copyright © 2026 François G. Dorais. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Usage: scripts/bench_ab.sh BASE [PAIRS] [THRESHOLD]
#
# Times this checkout against the revision BASE on this machine: builds both with this checkout's
# benchmarks, runs `bench --tsv` PAIRS times (default 10) for each, alternately, and prints
# `bench_compare.py`'s table, which marks the rows whose median ratio is above THRESHOLD
# (default 1.05). On Linux, set CPU to a core number to pin the runs to that core, with the
# frequency governor on `performance`. The worktree of BASE is removed at the end.
set -euo pipefail
base=$1
pairs=${2:-10}
threshold=${3:-1.05}
tmp=$(mktemp -d)
trap 'git worktree remove --force "$tmp/base" 2>/dev/null || true; rm -rf "$tmp"' EXIT
pin=()
if [ -n "${CPU:-}" ]; then pin=(taskset -c "$CPU"); fi

lake build bench
cp .lake/build/bin/bench "$tmp/bench-head"
scripts/bench_base.sh "$base" "$tmp/base"
(cd "$tmp/base" && lake build bench)
cp "$tmp/base/.lake/build/bin/bench" "$tmp/bench-base"

for i in $(seq "$pairs"); do
  echo "pair $i of $pairs" >&2
  ${pin[@]+"${pin[@]}"} "$tmp/bench-base" --tsv >> "$tmp/base.tsv"
  ${pin[@]+"${pin[@]}"} "$tmp/bench-head" --tsv >> "$tmp/head.tsv"
done
python3 scripts/bench_compare.py --threshold "$threshold" "$tmp/base.tsv" "$tmp/head.tsv"
