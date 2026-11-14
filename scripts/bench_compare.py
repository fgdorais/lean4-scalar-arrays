#!/usr/bin/env python3
# Copyright © 2026 François G. Dorais. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
"""Compare benchmark results of two builds.

Usage: bench_compare.py [--threshold T] BASE.tsv HEAD.tsv

Each file holds the `lake exe bench --tsv` output of one or more runs, and the k-th run in one file
is paired with the k-th run in the other: run them alternately (base, head, base, head, ...), so
that drift in the machine's speed affects both alike. For each benchmark, the table shows the
fastest time of each build and the median of the paired ratios head / base, with their range.

Medians above the threshold are marked. The default, 1.25, suits GitHub's runners; on a quiet
machine with the benchmark pinned to one core, 1.05 is about right.
"""

import statistics
import sys


def load(path):
    runs = {}
    order = []
    with open(path) as f:
        for line in f:
            name, _, ms = line.rstrip("\n").partition("\t")
            if not ms:
                continue
            if name not in runs:
                order.append(name)
                runs[name] = []
            runs[name].append(float(ms))
    return order, runs


def main():
    args = sys.argv[1:]
    threshold = 1.25
    if len(args) == 4 and args[0] == "--threshold":
        threshold = float(args[1])
        args = args[2:]
    if len(args) != 2:
        sys.exit(__doc__)
    _, base = load(args[0])
    order, head = load(args[1])
    print("| Benchmark | Base | Head | Head / base (median) | Range |")
    print("|---|--:|--:|--:|--:|")
    for name in order:
        h = head[name]
        if name not in base:
            print(f"| {name} | — | {min(h):.3f} | — | — |")
            continue
        b = base[name]
        ratios = [y / x if x > 0 else float("inf") for x, y in zip(b, h)]
        med = statistics.median(ratios)
        mark = " ⚠️" if med > threshold else ""
        print(f"| {name} | {min(b):.3f} | {min(h):.3f} | {med:.2f}{mark} | "
              f"{min(ratios):.2f}–{max(ratios):.2f} |")


if __name__ == "__main__":
    main()
