/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import ScalarArray
import ScalarArray.Bytes

/-!
# Benchmarks

Times the main operations of `UInt8Array`, `UInt32Array`, `UInt64Array` and `Float64Array`, which
cover 1-, 4- and 8-byte elements, and compares each with the same operation on core's `ByteArray`,
`Array UInt32`, `Array UInt64` and `FloatArray`. The ratios are more meaningful than the times,
since both sides run on the same machine at the same moment.

Usage: `lake exe bench [--tsv] [size] [rounds]`. Each benchmark runs `rounds` times and reports
the fastest run. `--tsv` prints `name<TAB>milliseconds` lines, which
`scripts/bench_compare.py` uses to compare two builds.
-/

open ScalarArray

namespace ScalarArrayBench

/--
The operations that are timed, for an array type `A` with elements `X`. The benchmarks are
specialized to each instance, so they compile to the same code as direct calls.
-/
class Ops (A : Type) (X : outParam Type) where
  /-- An element computed from an index. -/
  ofNat : Nat → X
  /-- An element as a checksum contribution. -/
  toUInt64 : X → UInt64
  /-- An empty array with room for the given number of elements. -/
  emptyWithCapacity : Nat → A
  /-- Appends an element. -/
  push : A → X → A
  /-- The number of elements. -/
  size : A → Nat
  /-- The element at an index, or a default. -/
  get! : A → Nat → X
  /-- Replaces the element at an index. -/
  set! : A → Nat → X → A
  /-- Folds over the elements. -/
  foldl : (UInt64 → X → UInt64) → UInt64 → A → UInt64
  /-- Concatenation, if the type has it. -/
  append : Option (A → A → A)
  /-- The elements between two indices, if the type has it. -/
  extract : Option (A → Nat → Nat → A)

/-- A fast conversion for the small indices used here; `Float.ofNat` is much slower. -/
@[inline] def natToFloat (n : Nat) : Float := n.toUInt64.toFloat

/-- An `Ops` instance for one of this library's arrays. -/
local macro "scalar_ops" A:ident X:ident empty:ident ofNat:ident toU64:term:max : command =>
  `(instance : Ops $A $X where
      ofNat := $ofNat
      toUInt64 := $toU64
      emptyWithCapacity := $empty
      push a x := a.push x
      size a := a.size
      get! a i := a.get! i
      set! a i x := a.set! i x
      foldl f init a := a.foldl f init
      append := some (· ++ ·)
      extract := some fun a i j => a.extract i j)

scalar_ops UInt8Array UInt8 UInt8Array.emptyWithCapacity Nat.toUInt8 UInt8.toUInt64
scalar_ops UInt32Array UInt32 UInt32Array.emptyWithCapacity Nat.toUInt32 UInt32.toUInt64
scalar_ops UInt64Array UInt64 UInt64Array.emptyWithCapacity Nat.toUInt64 id
scalar_ops Float64Array Float Float64Array.emptyWithCapacity natToFloat Float.toUInt64

instance : Ops ByteArray UInt8 where
  ofNat := Nat.toUInt8
  toUInt64 := UInt8.toUInt64
  emptyWithCapacity := ByteArray.emptyWithCapacity
  push := ByteArray.push
  size := ByteArray.size
  get! := ByteArray.get!
  set! := ByteArray.set!
  foldl f init a := a.foldl f init
  append := some (· ++ ·)
  extract := some ByteArray.extract

instance : Ops FloatArray Float where
  ofNat := natToFloat
  toUInt64 := Float.toUInt64
  emptyWithCapacity := FloatArray.emptyWithCapacity
  push := FloatArray.push
  size := FloatArray.size
  get! := FloatArray.get!
  set! := FloatArray.set!
  foldl f init a := a.foldl f init
  append := none
  extract := none

/-- An `Ops` instance for core's `Array`. -/
@[inline, instance_reducible] def arrayOps {X : Type} [Inhabited X] (ofNat : Nat → X) (toU64 : X → UInt64) :
    Ops (Array X) X where
  ofNat := ofNat
  toUInt64 := toU64
  emptyWithCapacity := Array.emptyWithCapacity
  push := Array.push
  size := Array.size
  get! a i := a[i]!
  set! := Array.set!
  foldl f init a := a.foldl f init
  append := some (· ++ ·)
  extract := some fun a i j => a.extract i j

instance : Ops (Array UInt32) UInt32 := arrayOps Nat.toUInt32 UInt32.toUInt64
instance : Ops (Array UInt64) UInt64 := arrayOps Nat.toUInt64 id

/-- Builds an array of `n` elements with `push`. -/
@[specialize] def build {A X : Type} [Ops A X] (n : Nat) : A := Id.run do
  let mut a := Ops.emptyWithCapacity (A := A) 0
  for i in [0:n] do
    a := Ops.push a (Ops.ofNat (A := A) i)
  return a

/-- The kernels: each takes an input array and a size, and returns a checksum. -/
@[specialize] def kernels {A X : Type} [Ops A X] : List (String × Option (A → Nat → UInt64)) := [
  ("push", some fun _ n => (Ops.size (build (A := A) n)).toUInt64),
  ("foldl", some fun a _ => Ops.foldl (fun s x => s + Ops.toUInt64 (A := A) x) 0 a),
  ("get!", some fun a _ => Id.run do
    let mut s : UInt64 := 0
    for i in [0:Ops.size a] do
      s := s + Ops.toUInt64 (A := A) (Ops.get! a i)
    return s),
  ("set!", some fun a _ => Id.run do
    let mut a := a
    for i in [0:Ops.size a] do
      a := Ops.set! a i (Ops.ofNat (A := A) (i + 1))
    return Ops.toUInt64 (A := A) (Ops.get! a 0)),
  ("append", (Ops.append (A := A)).map fun app a _ => (Ops.size (app a a)).toUInt64),
  ("extract", (Ops.extract (A := A)).map fun ext a _ =>
    (Ops.size (ext a 1 (Ops.size a - 1))).toUInt64)]

/--
Runs `f` and returns its result. It is not inlined, so `f` runs exactly when this action does,
between the clock readings around it.
-/
@[noinline] def run (f : Nat → UInt64) (n : Nat) : IO UInt64 := pure (f n)

/-- The fastest of `rounds` runs of `f n`, in milliseconds. -/
def time (rounds n : Nat) (f : Nat → UInt64) : IO Float := do
  let mut best := (0 : UInt64) - 1
  let mut sink : UInt64 := 0
  for _ in [0:rounds] do
    let t₀ ← IO.monoNanosNow
    sink := sink + (← run f n)
    let t₁ ← IO.monoNanosNow
    best := min best (t₁ - t₀).toUInt64
  -- Keeps the results live.
  if sink == 0xdeadbeef then IO.eprintln ""
  return best.toFloat / 1e6

/-- One row of results: a name, a time for this library and maybe a time for core. -/
structure Row where
  /-- The benchmark's name. -/
  name : String
  /-- The time for this library, in milliseconds. -/
  time : Float
  /-- The time for core's array, in milliseconds, if there is a comparable operation. -/
  core : Option Float

/-- Times the kernels for the array `A` and the core array `B`. -/
@[specialize] def compare (A : Type) {X : Type} [Ops A X] (B : Type) {Y : Type} [Ops B Y]
    (label : String) (rounds n : Nat) : IO (List Row) := do
  let a : A := build n
  let b : B := build n
  let mut rows := []
  for ((name, f), (_, g)) in (kernels (A := A)).zip (kernels (A := B)) do
    let some f := f | continue
    let t ← time rounds n (f a)
    let c ← g.mapM fun g => time rounds n (g b)
    rows := rows ++ [{ name := s!"{label} {name}", time := t, core := c }]
  return rows

/--
Times the operations that have no counterpart in core, on `UInt32Array`. Each kernel takes its
input as an argument, so that the compiler can't compute its result once, outside the timing.
-/
def extras (rounds n : Nat) : IO (List Row) := do
  let a : UInt32Array := build n
  let bytes := a.toBytesLE
  let one {α : Type} (name : String) (x : α) (f : α → Nat → UInt64) : IO Row := do
    return { name, time := ← time rounds n (f x), core := none }
  return [
    ← one "UInt32 toArray" a fun a _ => a.toArray.size.toUInt64,
    ← one "UInt32 ofFn" () fun _ n =>
      (UInt32Array.ofFn (n := n) fun i => i.val.toUInt32).size.toUInt64,
    ← one "UInt32 Slice.foldlInPlace" a fun a _ =>
      (a.toSlice.foldlInPlace (0 : UInt64) fun _ _ x s => (x + 1, s + x.toUInt64)).2,
    ← one "UInt32 Slice.reverse" a fun a _ => a.toSlice.reverse.array.size.toUInt64,
    ← one "UInt32 toBytesLE" a fun a _ => a.toBytesLE.size.toUInt64,
    ← one "UInt32 toBytesBE" a fun a _ => a.toBytesBE.size.toUInt64,
    ← one "UInt32 ofBytesLE!" bytes fun b _ => (UInt32Array.ofBytesLE! b).size.toUInt64,
    ← one "UInt32 ofBytesBE!" bytes fun b _ => (UInt32Array.ofBytesBE! b).size.toUInt64]

/-- Formats milliseconds with three decimals. -/
def fmt (t : Float) : String :=
  let s := toString ((t * 1000).round / 1000)
  match s.splitOn "." with
  | [i, f] => i ++ "." ++ (f ++ "000").take 3
  | _ => s

end ScalarArrayBench

open ScalarArrayBench in
/-- Runs the benchmarks and prints a Markdown table, or TSV with `--tsv`. -/
public def main (args : List String) : IO Unit := do
  let tsv := args.contains "--tsv"
  let nums := (args.filter (· != "--tsv")).filterMap String.toNat?
  let n := nums[0]?.getD 1_000_000
  let rounds := nums[1]?.getD 10
  let rows :=
    (← compare UInt8Array ByteArray "UInt8" rounds n) ++
    (← compare UInt32Array (Array UInt32) "UInt32" rounds n) ++
    (← compare UInt64Array (Array UInt64) "UInt64" rounds n) ++
    (← compare Float64Array FloatArray "Float64" rounds n) ++
    (← extras rounds n)
  if tsv then
    for r in rows do
      IO.println s!"{r.name}\t{fmt r.time}"
  else
    IO.println s!"{n} elements, fastest of {rounds} runs, in milliseconds.\n"
    IO.println "| Benchmark | ScalarArray | Core | Ratio |"
    IO.println "|---|--:|--:|--:|"
    for r in rows do
      let (c, ratio) := match r.core with
        | some c => (fmt c, fmt (r.time / c))
        | none => ("—", "—")
      IO.println s!"| {r.name} | {fmt r.time} | {c} | {ratio} |"
