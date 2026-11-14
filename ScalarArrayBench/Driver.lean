/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import ScalarArrayBench.Probes

/-!
# Probe driver

Usage: `lake exe probes --list`, or `lake exe probes NAME SIZE CALLS`, which calls the probe
`NAME` `CALLS` times on an input of `SIZE` elements and prints a checksum.
`scripts/bench_counts.py` runs it under callgrind at two numbers of calls, so that the difference
is the cost of the calls alone.
-/

/-- Runs one probe, or lists them. -/
public def main (args : List String) : IO UInt32 := do
  match args with
  | ["--list"] =>
    for (name, _) in ScalarArrayBench.Probes.all do IO.println name
    return 0
  | [name, size, calls] =>
    let some (_, f) := ScalarArrayBench.Probes.all.find? (·.1 == name)
      | IO.eprintln s!"unknown probe {name}"; return 1
    let some n := size.toNat? | IO.eprintln "bad size"; return 1
    let some reps := calls.toNat? | IO.eprintln "bad number of calls"; return 1
    IO.println (f n reps)
    return 0
  | _ =>
    IO.eprintln "usage: probes --list | probes NAME SIZE CALLS"
    return 1
