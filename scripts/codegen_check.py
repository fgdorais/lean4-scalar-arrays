#!/usr/bin/env python3
# Copyright © 2026 François G. Dorais. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
"""Check the C code of the probes against a snapshot.

Usage: codegen_check.py [--update]

Reads the C code that Lean generated for `ScalarArrayBench/Probes.lean` (run `lake build probes`
first) and counts, in each probe and in the helpers the compiler made for it (its `_spec` and
`_lam` functions), the closures built, the constructors allocated, the calls of closures, and the
calls of functions of the library that weren't specialized for the probe. The rest of the module,
such as instances, counts as `(shared)`. It compares the counts with `ScalarArrayBench/codegen.tsv`
and fails if any differs. With `--update`, it writes the new counts there instead.

The counts don't say whether code runs: a closure in a fallback branch that never runs costs
nothing. So a change here is a prompt to look at the C code and at `bench_counts.py`, which counts
what runs, before updating the snapshot. The C code also changes with the Lean toolchain, so a
toolchain update usually updates the snapshot too.
"""

import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SOURCE = os.path.join(ROOT, "ScalarArrayBench", "Probes.lean")
C_FILE = os.path.join(ROOT, ".lake", "build", "ir", "ScalarArrayBench", "Probes.c")
SNAPSHOT = os.path.join(ROOT, "ScalarArrayBench", "codegen.tsv")

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


def counts():
    with open(C_FILE) as f:
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
    update = sys.argv[1:] == ["--update"]
    if sys.argv[1:] and not update:
        sys.exit(__doc__)
    if not os.path.exists(C_FILE):
        sys.exit(f"{C_FILE} doesn't exist: run `lake build probes` first.")
    names, result = counts()
    if update:
        with open(SNAPSHOT, "w") as f:
            f.write("probe\t" + "\t".join(COLUMNS) + "\n")
            for p in names:
                f.write(p + "\t" + "\t".join(map(str, result[p])) + "\n")
        print(f"Wrote {os.path.relpath(SNAPSHOT, ROOT)}.")
        return
    old = {}
    with open(SNAPSHOT) as f:
        next(f)
        for line in f:
            p, *vals = line.split()
            old[p] = [int(v) for v in vals]
    diffs = []
    for p in names:
        if p not in old:
            diffs.append(f"{p}: new probe")
            continue
        for col, a, b in zip(COLUMNS, old[p], result[p]):
            if a != b:
                diffs.append(f"{p}: {col} {a} -> {b}")
    diffs += [f"{p}: probe removed" for p in old if p not in result]
    if diffs:
        print("The C code of the probes changed:")
        print("\n".join("  " + d for d in diffs))
        print("If the change is intended, run `python3 scripts/codegen_check.py --update`.")
        sys.exit(1)
    print(f"The C code of the {len(names)} probes matches the snapshot.")


if __name__ == "__main__":
    main()
