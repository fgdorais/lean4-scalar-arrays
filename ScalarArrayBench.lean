/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import ScalarArray
import ScalarArray.Notation
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

/-- The carry of `x + y + c`, for a carry `c ≤ 1`, with `s := x + y + c` already computed. -/
@[inline] def carry (x s c : UInt64) : UInt64 :=
  (decide (s < x)).toUInt64 ||| ((decide (s == x)).toUInt64 &&& c)

/-- The borrow of `x - y - b`, for a borrow `b ≤ 1`. -/
@[inline] def borrow (x y b : UInt64) : UInt64 :=
  (decide (x < y)).toUInt64 ||| ((decide (x == y)).toUInt64 &&& b)

/--
A butterfly on the windows of `len` limbs at `0`, `len` and `2 * len` of `a`, the way lean4-mpn's
FFT does one: `x, t := x + y, x - y`, carrying the carry and the borrow apart. This one makes two
passes, one `foldlInPlace2Then` for each result.
-/
@[noinline] def butterflyTwoPass (a : UInt64Array) (len : USize) : UInt64Array × UInt64 :=
  if h : 3 * len.toNat ≤ a.size ∧ (2 * len).toNat = 2 * len.toNat ∧ len.toNat ≤ a.size then
    have hx : (0 : USize).toNat + len.toNat ≤ a.size := by simp; lia
    have hy : len.toNat + len.toNat ≤ a.size := by lia
    have ht : (2 * len).toNat + len.toNat ≤ a.size := by lia
    a.foldlInPlace2Then 0 len (2 * len) len hx hy ht (0 : UInt64)
      (fun _ _ x y b => (x - y - b, borrow x y b)) fun a ha b =>
        a.foldlInPlace2Then 0 len 0 len (ha ▸ hx) (ha ▸ hy) (ha ▸ hx) (0 : UInt64)
          (fun _ _ x y c => let s := x + y + c; (s, carry x s c)) fun a _ c => (a, b + c)
  else (a, 0)

/-- The same butterfly in one pass, as an `InPlace` program with `forIn2`. -/
@[noinline] def butterflyInPlace (a : UInt64Array) (len : USize) : UInt64Array × UInt64 :=
  if h : 3 * len.toNat ≤ a.size ∧ (2 * len).toNat = 2 * len.toNat ∧ len.toNat ≤ a.size then
    have hx : (0 : USize).toNat + len.toNat ≤ a.size := by simp; lia
    have hy : len.toNat + len.toNat ≤ a.size := by lia
    have ht : (2 * len).toNat + len.toNat ≤ a.size := by lia
    let r := a.runInPlace <| UInt64Array.InPlace.forIn2 0 len (0 : UInt64) (0 : UInt64)
      fun j _ hj c b => do
        let x ← UInt64Array.InPlace.read (0 + j) (UInt64Array.InPlace.toNat_add_lt_of_window hx hj)
        let y ← UInt64Array.InPlace.read (len + j) (UInt64Array.InPlace.toNat_add_lt_of_window hy hj)
        let s := x + y + c
        UInt64Array.InPlace.write (0 + j) (UInt64Array.InPlace.toNat_add_lt_of_window hx hj) s
        UInt64Array.InPlace.write (2 * len + j) (UInt64Array.InPlace.toNat_add_lt_of_window ht hj)
          (x - y - b)
        pure (carry x s c, borrow x y b)
    (r.2, r.1.1 + r.1.2)
  else (a, 0)

/-- The same one-pass butterfly, written with the `inplace` notation. -/
@[noinline] def butterflySyntax (a : UInt64Array) (len : USize) : UInt64Array × UInt64 :=
  if h : 3 * len.toNat ≤ a.size ∧ (2 * len).toNat = 2 * len.toNat ∧ len.toNat ≤ a.size then
    have hx : (0 : USize).toNat + len.toNat ≤ a.size := by simp; lia
    have hy : len.toNat + len.toNat ≤ a.size := by lia
    have ht : (2 * len).toNat + len.toNat ≤ a.size := by lia
    let r := inplace a do
      for j in 0...len with (c := 0) (b := 0) do
        let x := a[0 + j]
        let y := a[len + j]
        let s := x + y + c
        a[0 + j] := s
        a[2 * len + j] := x - y - b
        c := carry x s c
        b := borrow x y b
      return (c, b)
    (r.2, r.1.1 + r.1.2)
  else (a, 0)

/-- The same one-pass butterfly in the notation, with the carries handed to `then`. -/
@[noinline] def butterflySyntaxThen (a : UInt64Array) (len : USize) : UInt64Array × UInt64 :=
  if h : 3 * len.toNat ≤ a.size ∧ (2 * len).toNat = 2 * len.toNat ∧ len.toNat ≤ a.size then
    have hx : (0 : USize).toNat + len.toNat ≤ a.size := by simp; lia
    have hy : len.toNat + len.toNat ≤ a.size := by lia
    have ht : (2 * len).toNat + len.toNat ≤ a.size := by lia
    inplace a do
      for j in 0...len with (c := 0) (b := 0) do
        let x := a[0 + j]
        let y := a[len + j]
        let s := x + y + c
        a[0 + j] := s
        a[2 * len + j] := x - y - b
        c := carry x s c
        b := borrow x y b
      return (c, b)
    then fun (c, b) a _ => (a, c + b)
  else (a, 0)

/-- `t := x + y` with a carry, on the same windows as the butterflies, with `foldlInPlace2`. -/
@[noinline] def addFold2 (a : UInt64Array) (len : USize) : UInt64Array × UInt64 :=
  if h : 3 * len.toNat ≤ a.size ∧ (2 * len).toNat = 2 * len.toNat ∧ len.toNat ≤ a.size then
    have hx : (0 : USize).toNat + len.toNat ≤ a.size := by simp; lia
    have hy : len.toNat + len.toNat ≤ a.size := by lia
    have ht : (2 * len).toNat + len.toNat ≤ a.size := by lia
    a.foldlInPlace2 0 len (2 * len) len hx hy ht (0 : UInt64)
      fun _ _ x y c => let s := x + y + c; (s, carry x s c)
  else (a, 0)

/-- Doubles the elements at the first `m` steps of the stride `s`, with the `inplace` notation. -/
@[noinline] def doubleStride (a : Float64Array) (s : Stride) (m : USize) : Float64Array :=
  if h : s.Fits m.toNat a.size ∧ a.size < USize.size then
    let o := s.off.toUSize
    let c := s.inc.toUSize
    (inplace a do
      for k in 0...m do
        have hk : (o + c * k).toNat < a.size := s.toNat_idx_toUSize_lt h.1 h.2 (by assumption)
        a[o + c * k] := 2 * a[o + c * k]).2
  else a

/-- `doubleStride` on all the elements, as a contiguous loop. -/
@[noinline] def doubleAll (a : Float64Array) : Float64Array :=
  have := a.toNat_usize_le
  (inplace a do
    for k in 0...a.usize do
      a[k] := 2 * a[k]).2

/-- Runs a butterfly on windows of `len` limbs `reps` times, and returns a checksum. -/
@[inline] def butterflies (k : UInt64Array → USize → UInt64Array × UInt64) (a : UInt64Array)
    (len : USize) (reps : Nat) : UInt64 := Id.run do
  let mut a := a
  let mut s : UInt64 := 0
  for _ in [0:reps] do
    let r := k a len
    a := r.1
    s := s + r.2
  return s + a[0]!

/--
Times the operations that have no counterpart in core, on `UInt32Array`. Each kernel takes its
input as an argument, so that the compiler can't compute its result once, outside the timing.
-/
def extras (rounds n : Nat) : IO (List Row) := do
  let a : UInt32Array := build n
  let bytes := a.toBytesLE
  let w : UInt64Array := build n
  let f : Float64Array := build n
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
    ← one "UInt32 ofBytesBE!" bytes fun b _ => (UInt32Array.ofBytesBE! b).size.toUInt64,
    ← one "UInt64 foldlInPlaceRange, pair" w fun a _ =>
      let r := a.foldlInPlaceRange 0 a.usize (by simpa using a.toNat_usize_le)
        ((0 : UInt64), (0 : UInt64)) fun _ _ x c =>
          let lo := x * 3 + c.1
          (lo, (c.2 + x * 5, lo >>> 7))
      r.2.1 + r.2.2,
    ← one "UInt64 foldlInPlaceRangeWith2Acc" w fun a _ =>
      let r := a.foldlInPlaceRangeWith2Acc 0 a.usize (by simpa using a.toNat_usize_le)
        (0 : UInt64) (0 : UInt64) fun _ _ x c₁ c₂ =>
          let lo := x * 3 + c₁
          (lo, c₂ + x * 5, lo >>> 7)
      r.2.1 + r.2.2,
    ← one "UInt64 clamp, foldlInPlaceRange" w fun a _ =>
      let m : UInt64 := (1 : UInt64) <<< 63
      let r := a.foldlInPlaceRange 0 a.usize (by simpa using a.toNat_usize_le) (0 : UInt64)
        fun _ _ x k => if x > m then (m, k + 1) else (x, k)
      r.2,
    ← one "UInt64 clamp, inplace notation" w fun a _ =>
      let m : UInt64 := (1 : UInt64) <<< 63
      have := a.toNat_usize_le
      let r := inplace a do
        for j in 0...a.usize with (k := (0 : UInt64)) do
          if a[j] > m then
            a[j] := m
            k := k + 1
        return k
      r.1,
    ← one "UInt64 rows of 4, nested inplace loops" w fun a _ =>
      have := a.toNat_usize_le
      let rows := a.usize / 4
      have : 4 * rows.toNat ≤ a.size ∧ 4 * rows.toNat < USize.size := by
        have := USize.toNat_lt_size a.usize
        simp only [rows, USize.toNat_div]; lia
      let r := inplace a do
        for r in 0...rows with (tot := (0 : UInt64)) do
          for c in 0...4 with (acc := (0 : UInt64)) (t := tot) do
            have hc : (4 * r + c).toNat < a.size := by inplace_bound
            let x := a[4 * r + c]
            acc := acc + x
            a[4 * r + c] := acc
            t := t + x
          tot := t
        return tot
      r.1,
    -- Ten passes over one array, so that only the first copies it.
    ← one "Float64 double ×10, contiguous inplace loop" f fun a _ =>
      (Nat.fold 10 (fun _ _ a => doubleAll a) a).size.toUInt64,
    ← one "Float64 double ×10, stride 1" f fun a n =>
      (Nat.fold 10 (fun _ _ a => doubleStride a ⟨0, 1⟩ n.toUSize) a).size.toUInt64,
    ← one "Float64 double ×10, stride 2" f fun a n =>
      (Nat.fold 10 (fun _ _ a => doubleStride a ⟨0, 2⟩ (n / 2).toUSize) a).size.toUInt64,
    ← one "Float64 double ×10, stride 8" f fun a n =>
      (Nat.fold 10 (fun _ _ a => doubleStride a ⟨0, 8⟩ (n / 8).toUSize) a).size.toUInt64,
    -- lean4-mpn's FFT residues are windows of about 137 limbs.
    ← one "UInt64 add 137, foldlInPlace2" (w.extract 0 411) fun a n =>
      butterflies addFold2 a 137 (n / 137),
    ← one "UInt64 add n/3, foldlInPlace2" w fun a n => butterflies addFold2 a (n / 3).toUSize 3,
    ← one "UInt64 butterfly 137, 2× foldlInPlace2Then" (w.extract 0 411) fun a n =>
      butterflies butterflyTwoPass a 137 (n / 137),
    ← one "UInt64 butterfly 137, InPlace.forIn2" (w.extract 0 411) fun a n =>
      butterflies butterflyInPlace a 137 (n / 137),
    ← one "UInt64 butterfly 137, inplace notation" (w.extract 0 411) fun a n =>
      butterflies butterflySyntax a 137 (n / 137),
    ← one "UInt64 butterfly 137, inplace then" (w.extract 0 411) fun a n =>
      butterflies butterflySyntaxThen a 137 (n / 137),
    ← one "UInt64 butterfly 16, InPlace.forIn2" (w.extract 0 48) fun a n =>
      butterflies butterflyInPlace a 16 (n / 16),
    ← one "UInt64 butterfly 16, inplace notation" (w.extract 0 48) fun a n =>
      butterflies butterflySyntax a 16 (n / 16),
    ← one "UInt64 butterfly 16, inplace then" (w.extract 0 48) fun a n =>
      butterflies butterflySyntaxThen a 16 (n / 16),
    ← one "UInt64 butterfly n/3, 2× foldlInPlace2Then" w fun a n =>
      butterflies butterflyTwoPass a (n / 3).toUSize 3,
    ← one "UInt64 butterfly n/3, InPlace.forIn2" w fun a n =>
      butterflies butterflyInPlace a (n / 3).toUSize 3,
    ← one "UInt64 butterfly n/3, inplace notation" w fun a n =>
      butterflies butterflySyntax a (n / 3).toUSize 3]

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
