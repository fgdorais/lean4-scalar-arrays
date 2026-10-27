#!/usr/bin/env python3
"""Compare benchmark results of two builds.

Usage: bench_compare.py BASE.tsv HEAD.tsv

Each file holds the `lake exe bench --tsv` output of one or more runs. For each benchmark the
fastest time is kept, and the table shows the ratio head / base. Ratios above 1.25 are marked,
since GitHub's runners vary by about that much between runs.
"""

import sys

THRESHOLD = 1.25


def load(path):
    times = {}
    order = []
    with open(path) as f:
        for line in f:
            name, _, ms = line.rstrip("\n").partition("\t")
            if not ms:
                continue
            if name not in times:
                order.append(name)
                times[name] = float(ms)
            else:
                times[name] = min(times[name], float(ms))
    return order, times


def main():
    if len(sys.argv) != 3:
        sys.exit(__doc__)
    _, base = load(sys.argv[1])
    order, head = load(sys.argv[2])
    print("| Benchmark | Base | Head | Head / base |")
    print("|---|--:|--:|--:|")
    for name in order:
        h = head[name]
        if name not in base:
            print(f"| {name} | — | {h:.3f} | — |")
            continue
        b = base[name]
        ratio = h / b if b > 0 else float("inf")
        mark = " ⚠️" if ratio > THRESHOLD else ""
        print(f"| {name} | {b:.3f} | {h:.3f} | {ratio:.2f}{mark} |")


if __name__ == "__main__":
    main()
