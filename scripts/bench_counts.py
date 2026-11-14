#!/usr/bin/env python3
# Copyright © 2026 François G. Dorais. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
"""Count the instructions and allocations of each probe call, and compare two builds.

Usage:
  bench_counts.py run [--sizes 0,4,137] [--calls 1000] [--jobs N] PROBES_EXE > counts.tsv
  bench_counts.py compare BASE.tsv HEAD.tsv

`run` calls each probe of `ScalarArrayBench.Probes` CALLS times (through `lake exe probes`, whose
binary is `PROBES_EXE`) under valgrind's callgrind, counting only inside the loop that makes the
calls (`repeatProbe`), so without the startup and the input. The counts are the same on every run
of the same binary. Each line of the output is
`probe<TAB>size<TAB>instructions<TAB>allocations<TAB>object allocations`, per call. Allocations
count the calls to the runtime's two allocators: `lean_alloc_small_object_core` for constructors
and boxed scalars, and `lean_alloc_object` for arrays and closures, which is the second count.

`compare` prints a Markdown table of the probes whose counts changed, and exits with status 1 if
a probe makes more allocations per call, or more than `FAIL` more instructions (and at least
`MIN_FAIL`), than in the base.
Changes of more than `WARN` are marked. The counts don't see the cache, branch prediction or code
alignment: they catch work and allocations, and `lake exe bench` measures time.
"""

import concurrent.futures
import os
import subprocess
import sys
import tempfile

WARN = 0.01
FAIL = 0.05
# A change of fewer instructions than this per call only warns: on the smallest probes, which run
# about 150 instructions, a register spill or a moved branch is already a few percent.
MIN_FAIL = 16

# The runtime's allocators: `lean_alloc_ctor` and the boxes call the first one (inlined fast paths
# aside, which the runtime doesn't have), and arrays and closures call the second.
SMALL = "lean_alloc_small_object_core"
LARGE = "lean_alloc_object"


def callgrind(exe, probe, size, calls):
    """Total instructions and allocator calls of one run."""
    with tempfile.TemporaryDirectory() as tmp:
        out = os.path.join(tmp, "cg.out")
        subprocess.run(
            ["valgrind", "--tool=callgrind", "--compress-strings=no", "--compress-pos=no",
             "--toggle-collect=*repeatProbe*",
             f"--callgrind-out-file={out}", exe, probe, str(size), str(calls)],
            check=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        total = 0
        counts = {SMALL: 0, LARGE: 0}
        callee = None
        with open(out) as f:
            for line in f:
                if line.startswith("summary:"):
                    total = int(line.split()[1])
                elif line.startswith("cfn="):
                    callee = line[4:].strip()
                elif line.startswith("calls=") and callee is not None:
                    if callee in counts:
                        counts[callee] += int(line.split()[0][6:])
                    callee = None
        return total, counts[SMALL] + counts[LARGE], counts[LARGE]


def measure(exe, probe, size, calls):
    return probe, size, *(x / calls for x in callgrind(exe, probe, size, calls))


def run(args):
    sizes = [0, 4, 137]
    calls = 1000
    jobs = os.cpu_count() or 1
    rest = []
    while args:
        a = args.pop(0)
        if a == "--sizes":
            sizes = [int(s) for s in args.pop(0).split(",")]
        elif a == "--calls":
            calls = int(args.pop(0))
        elif a == "--jobs":
            jobs = int(args.pop(0))
        else:
            rest.append(a)
    if len(rest) != 1:
        sys.exit(__doc__)
    exe = rest[0]
    probes = subprocess.run([exe, "--list"], check=True, capture_output=True,
                            text=True).stdout.split()
    with concurrent.futures.ThreadPoolExecutor(jobs) as pool:
        futures = [pool.submit(measure, exe, p, n, calls) for p in probes for n in sizes]
        for fut in futures:
            probe, size, ir, allocs, large = fut.result()
            print(f"{probe}\t{size}\t{ir:.1f}\t{allocs:.2f}\t{large:.2f}")


def load(path):
    rows = {}
    order = []
    with open(path) as f:
        for line in f:
            parts = line.split()
            if len(parts) != 5:
                continue
            key = (parts[0], int(parts[1]))
            order.append(key)
            rows[key] = tuple(float(x) for x in parts[2:])
    return order, rows


def compare(args):
    if len(args) != 2:
        sys.exit(__doc__)
    _, base = load(args[0])
    order, head = load(args[1])
    failed = []
    lines = []
    for key in order:
        h = head[key]
        b = base.get(key)
        name = f"{key[0]} ({key[1]})"
        if b is None:
            lines.append(f"| {name} | — | {h[0]:.0f} | — | — | {h[1]:.2f} | new |")
            continue
        ratio = h[0] / b[0] if b[0] > 0 else 1.0
        more_allocs = h[1] > b[1] + 0.05
        if abs(ratio - 1) <= WARN / 10 and abs(h[1] - b[1]) <= 0.05:
            continue
        mark = ""
        if more_allocs or (ratio > 1 + FAIL and h[0] - b[0] >= MIN_FAIL):
            mark = "❌"
            failed.append(name)
        elif abs(ratio - 1) > WARN:
            mark = "⚠️" if ratio > 1 else "✅"
        lines.append(f"| {name} | {b[0]:.0f} | {h[0]:.0f} | {ratio:.3f} | {b[1]:.2f} | "
                     f"{h[1]:.2f} | {mark} |")
    if lines:
        print("| Probe (size) | Base instr. | Head instr. | Head / base | Base allocs | "
              "Head allocs | |")
        print("|---|--:|--:|--:|--:|--:|---|")
        print("\n".join(lines))
    else:
        print("No probe changed.")
    if failed:
        print(f"\n{len(failed)} probe(s) got slower: more allocations per call, or more than "
              f"{FAIL:.0%} more instructions.")
        sys.exit(1)


def main():
    if len(sys.argv) < 2 or sys.argv[1] not in ("run", "compare"):
        sys.exit(__doc__)
    {"run": run, "compare": compare}[sys.argv[1]](sys.argv[2:])


if __name__ == "__main__":
    main()
