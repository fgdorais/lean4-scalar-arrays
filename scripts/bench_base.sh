#!/usr/bin/env bash
# Copyright © 2026 François G. Dorais. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Usage: scripts/bench_base.sh REV DIR
#
# Checks out REV in a new worktree at DIR, with this checkout's benchmark sources
# (`ScalarArrayBench.lean` and `ScalarArrayBench/`), so that both builds run the same benchmarks
# and probes. The lakefile of REV gets the benchmark targets if it doesn't have them.
set -euo pipefail
rev=$1
dir=$2
git worktree add --detach "$dir" "$rev"
cp ScalarArrayBench.lean "$dir/"
rm -rf "$dir/ScalarArrayBench"
cp -r ScalarArrayBench "$dir/"
lakefile="$dir/lakefile.toml"
if ! grep -q '^name = "ScalarArrayProbes"' "$lakefile"; then
  printf '\n[[lean_lib]]\nname = "ScalarArrayProbes"\nroots = ["ScalarArrayBench.Probes"]\n' \
    >> "$lakefile"
  printf 'moreLeancArgs = ["-falign-loops=64"]\n' >> "$lakefile"
fi
if ! grep -q '^name = "bench"' "$lakefile"; then
  printf '\n[[lean_exe]]\nname = "bench"\nroot = "ScalarArrayBench"\n' >> "$lakefile"
  printf 'moreLeancArgs = ["-falign-loops=64"]\n' >> "$lakefile"
fi
if ! grep -q '^name = "probes"' "$lakefile"; then
  printf '\n[[lean_exe]]\nname = "probes"\nroot = "ScalarArrayBench.Driver"\n' >> "$lakefile"
  printf 'moreLeancArgs = ["-falign-loops=64"]\n' >> "$lakefile"
fi
