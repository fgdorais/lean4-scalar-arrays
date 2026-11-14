#!/usr/bin/env python3
# Copyright © 2026 François G. Dorais. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
"""Compare the C code of the probes in two builds.

Usage: codegen_check.py BASE_DIR [HEAD_DIR]

Reads the C code that Lean generated for `ScalarArrayBench/Probes.lean` in two checkouts (run
`lake build probes` in each first; HEAD_DIR defaults to this one) and counts, in each probe and in
the helpers the compiler made for it (its `_spec` and `_lam` functions), the closures built, the
constructors allocated, the calls of closures, and the calls of functions of the library that
weren't specialized for the probe. The rest of the module, such as instances, counts as
`(shared)`. It prints a Markdown table of the counts that differ, and marks the increases.

The counts don't say whether code runs: a closure in a fallback branch that never runs costs
nothing. So a change here is a prompt to look at the C code, and at `bench_counts.py`, which counts
what runs. The C code also changes with the Lean toolchain.
"""

import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SOURCE = os.path.join(ROOT, "ScalarArrayBench", "Probes.lean")
C_FILE = os.path.join(".lake", "build", "ir", "ScalarArrayBench", "Probes.c")

PREFIX = "lp_lean4_x2dscalar_x2darrays_"
# The code that no single probe owns, such as instances and the driver's loops.
OTHER = "(shared)"
COLUMNS = ["closures", "ctors", "applies", "library calls"]
FUNCTION = re.compile(r"^LEAN_EXPORT [^\n;(]*?\b(" + PREFIX + r"\w+)\([^)]*\) ?\{\n(.*?)^\}",
                      re.S | re.M)
# A call of a function of the library, other than a copy specialized in this module.
LIBRARY_CALL = re.compile(r"\b" + PREFIX + r"(?:___private_)?ScalarArray_(\w+)\(")


def probes():
    with open(SOURCE) as f:
        return re.findall(r'\("(\w+)", run \w+\)', f.read())


def counts(directory):
    path = os.path.join(directory, C_FILE)
    if not os.path.exists(path):
        sys.exit(f"{path} doesn't exist: run `lake build probes` there first.")
    with open(path) as f:
        src = f.read()
    names = probes()
    pattern = re.compile(r"ScalarArrayBench_Probes_(" + "|".join(names) + r")(?=_|$)")
    names.append(OTHER)
    result = {p: [0] * len(COLUMNS) for p in names}
    for m in FUNCTION.finditer(src):
        name, body = m.group(1), m.group(2)
        if name.endswith("___boxed"):
            continue
        # The probe is the last one named: a specialization is named after the function it
        # specializes, then the probe it was made for.
        owners = pattern.findall(name)
        c = result[owners[-1] if owners else OTHER]
        c[0] += body.count("lean_alloc_closure(")
        c[1] += body.count("lean_alloc_ctor(")
        c[2] += len(re.findall(r"\blean_apply_\w+\(", body))
        c[3] += sum(1 for x in LIBRARY_CALL.findall(body) if "_at___00ScalarArrayBench" not in x)
    return names, result


def main():
    if len(sys.argv) not in (2, 3):
        sys.exit(__doc__)
    _, base = counts(sys.argv[1])
    names, head = counts(sys.argv[2] if len(sys.argv) == 3 else ROOT)
    lines = []
    for p in names:
        b = base.get(p)
        h = head[p]
        if b == h:
            continue
        if b is None:
            lines.append(f"| {p} | " + " | ".join(f"— → {y}" for y in h) + " | new |")
            continue
        cells = [f"{x}" if x == y else f"{x} → {y}" for x, y in zip(b, h)]
        mark = "⚠️" if any(y > x for x, y in zip(b, h)) else "✅"
        lines.append(f"| {p} | " + " | ".join(cells) + f" | {mark} |")
    if not lines:
        print(f"The C code of the {len(names)} probes has the same counts.")
        return
    print("| Probe | " + " | ".join(COLUMNS) + " | |")
    print("|---|" + "--:|" * len(COLUMNS) + "---|")
    print("\n".join(lines))


if __name__ == "__main__":
    main()
