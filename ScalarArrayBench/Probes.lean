/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ScalarArray
public import ScalarArray.Bytes
import ScalarArray.Notation

/-!
# Probes

Call sites for measuring what one call of an operation costs, apart from its loop: the probes
catch a fixed charge per call, such as a closure built or a test made on every call, which large
inputs hide.

This module is compiled on its own, as a downstream package would compile its calls, and each
probe is `@[noinline]`, so the driver can't merge it with its own code. A probe takes its input and
a word `w`, and returns its output and a checksum. The driver feeds each output back in and changes
`w` on every call, so that in-place operations stay in place and a step that captures `w` captures
a runtime value.

Probe names end in the call shape:

* `K`: a step function that captures nothing, which the compiler can make a constant;
* `W`: a step function that captures `w`, as most downstream steps do;
* `G`: through a downstream-style class and a `@[specialize]` generic function;
* `H`: with an unknown step function, passed into a `@[noinline]` higher-order function.

`scripts/codegen_check.py` reads the C code of this module, and `scripts/bench_counts.py` counts
the instructions and allocations of each probe through the `probes` driver. `lake exe bench`
times them.
-/

open ScalarArray

namespace ScalarArrayBench.Probes

/-! ## Inputs -/

/-- Inputs of a given size, for the probes. -/
public class Input (X : Type) where
  /-- An input of size `n`. -/
  make : Nat → X

public instance : Input UInt64Array where
  make n := UInt64Array.ofFn (n := n) fun i => i.val.toUInt64 * 0x9e3779b97f4a7c15

public instance : Input UInt8Array where
  make n := UInt8Array.ofFn (n := n) fun i => i.val.toUInt8

public instance : Input Float64Array where
  make n := Float64Array.ofFn (n := n) fun i => i.val.toUInt64.toFloat

public instance : Input ByteArray where
  make n := (UInt64Array.ofFn (n := n) fun i => i.val.toUInt64).toBytesLE

public instance {X Y : Type} [Input X] [Input Y] : Input (X × Y) where
  make n := (Input.make n, Input.make n)

/-- Calls `p` `reps` times, feeding each output back in. -/
@[specialize] public def repeatProbe {X : Type} (p : X → UInt64 → X × UInt64) (x : X) (w : UInt64) :
    Nat → UInt64
  | 0 => w
  | reps + 1 => let r := p x w; repeatProbe p r.1 (w + r.2 + 1) reps

/-- Runs a probe `reps` times on an input of size `n`, and returns a checksum. -/
@[inline] public def run {X : Type} [Input X] (p : X → UInt64 → X × UInt64) (n reps : Nat) :
    UInt64 :=
  repeatProbe p (Input.make n) 1 reps

/-! ## Array folds -/

/-- `foldl`, constant step. -/
@[noinline] public def foldlK (a : UInt64Array) (_w : UInt64) : UInt64Array × UInt64 :=
  (a, a.foldl (· + ·) 0)

/-- `foldl`, capturing step. -/
@[noinline] public def foldlW (a : UInt64Array) (w : UInt64) : UInt64Array × UInt64 :=
  (a, a.foldl (fun s x => s + x * w) 0)

/-- `foldr`, capturing step. -/
@[noinline] public def foldrW (a : UInt64Array) (w : UInt64) : UInt64Array × UInt64 :=
  (a, a.foldr (fun x s => s + x * w) 0)

/-- `any`, capturing predicate. -/
@[noinline] public def anyW (a : UInt64Array) (w : UInt64) : UInt64Array × UInt64 :=
  (a, (a.any (· == w)).toUInt64)

/-- `contains`. -/
@[noinline] public def containsW (a : UInt64Array) (w : UInt64) : UInt64Array × UInt64 :=
  (a, (a.contains w).toUInt64)

/-- A `for … in` loop, capturing. -/
@[noinline] public def forInW (a : UInt64Array) (w : UInt64) : UInt64Array × UInt64 := Id.run do
  let mut s : UInt64 := 0
  for x in a do
    s := s + x * w
  return (a, s)

/-- `Slice.foldl`, capturing step. -/
@[noinline] public def sliceFoldlW (a : UInt64Array) (w : UInt64) : UInt64Array × UInt64 :=
  (a, a.toSlice.foldl (fun s x => s + x * w) 0)

/-- `foldl` on `UInt8Array`, capturing step. -/
@[noinline] public def u8FoldlW (a : UInt8Array) (w : UInt64) : UInt8Array × UInt64 :=
  (a, a.foldl (fun s x => s + x.toUInt64 * w) 0)

/-! ## In-place folds -/

/-- The step of a multiplication by a word, as in an `mpn` `mul_1`. -/
@[inline] public def mulStep (w x c : UInt64) : UInt64 × UInt64 :=
  (x * w + c, (x >>> 32) * w)

/-- `Slice.foldlInPlace`, constant step. -/
@[noinline] public def foldlInPlaceK (a : UInt64Array) (_w : UInt64) : UInt64Array × UInt64 :=
  let r := a.toSlice.foldlInPlace (0 : UInt64) fun _ _ x c => mulStep 3 x c
  (r.1.array, r.2)

/-- `Slice.foldlInPlace`, capturing step. -/
@[noinline] public def foldlInPlaceW (a : UInt64Array) (w : UInt64) : UInt64Array × UInt64 :=
  let r := a.toSlice.foldlInPlace (0 : UInt64) fun _ _ x c => mulStep w x c
  (r.1.array, r.2)

/-- `Slice.foldrInPlace`, capturing step. -/
@[noinline] public def foldrInPlaceW (a : UInt64Array) (w : UInt64) : UInt64Array × UInt64 :=
  let r := a.toSlice.foldrInPlace (0 : UInt64) fun _ _ x c => mulStep w x c
  (r.1.array, r.2)

/-- `Slice.foldlInPlaceThen`, capturing step. -/
@[noinline] public def foldlInPlaceThenW (a : UInt64Array) (w : UInt64) : UInt64Array × UInt64 :=
  a.toSlice.foldlInPlaceThen (0 : UInt64) (fun _ _ x c => mulStep w x c) fun s c => (s.array, c)

/-- `foldlInPlaceRange` on the whole array, capturing step. -/
@[noinline] public def foldlInPlaceRangeW (a : UInt64Array) (w : UInt64) :
    UInt64Array × UInt64 :=
  a.foldlInPlaceRange 0 a.usize (by simpa using a.toNat_usize_le) (0 : UInt64)
    fun _ _ x c => mulStep w x c

/-- `foldrInPlaceRange` on the whole array, capturing step. -/
@[noinline] public def foldrInPlaceRangeW (a : UInt64Array) (w : UInt64) :
    UInt64Array × UInt64 :=
  a.foldrInPlaceRange 0 a.usize (by simpa using a.toNat_usize_le) (0 : UInt64)
    fun _ _ x c => mulStep w x c

/-- `foldlInPlaceRangeThen` on the whole array, capturing step. -/
@[noinline] public def foldlInPlaceRangeThenW (a : UInt64Array) (w : UInt64) :
    UInt64Array × UInt64 :=
  a.foldlInPlaceRangeThen 0 a.usize (by simpa using a.toNat_usize_le) (0 : UInt64)
    (fun _ _ x c => mulStep w x c) fun a _ c => (a, c)

/-- `foldlInPlaceRangeWith2Acc` on the whole array, capturing step. -/
@[noinline] public def foldlInPlaceRangeWith2AccW (a : UInt64Array) (w : UInt64) :
    UInt64Array × UInt64 :=
  let r := a.foldlInPlaceRangeWith2Acc 0 a.usize (by simpa using a.toNat_usize_le)
    (0 : UInt64) (0 : UInt64) fun _ _ x c s => let p := mulStep w x c; (p.1, p.2, s + x)
  (r.1, r.2.1 + r.2.2)

/-- The carry of `x + y + c`, with `s := x + y + c`. -/
@[inline] public def carry (x s c : UInt64) : UInt64 :=
  (decide (s < x)).toUInt64 ||| ((decide (s == x)).toUInt64 &&& c)

/-- `foldlInPlace2`: adds the second third of the array to the first, into the last. -/
@[noinline] public def foldlInPlace2W (a : UInt64Array) (w : UInt64) : UInt64Array × UInt64 :=
  let len := a.usize / 3
  if h : 3 * len.toNat ≤ a.size ∧ (2 * len).toNat = 2 * len.toNat then
    have hx : (0 : USize).toNat + len.toNat ≤ a.size := by simp; lia
    have hy : len.toNat + len.toNat ≤ a.size := by lia
    have hr : (2 * len).toNat + len.toNat ≤ a.size := by lia
    a.foldlInPlace2 0 len (2 * len) len hx hy hr w
      fun _ _ x y c => let s := x + y + c; (s, carry x s c)
  else (a, 0)

/-- `foldlInPlace2Then`, as `foldlInPlace2W`. -/
@[noinline] public def foldlInPlace2ThenW (a : UInt64Array) (w : UInt64) :
    UInt64Array × UInt64 :=
  let len := a.usize / 3
  if h : 3 * len.toNat ≤ a.size ∧ (2 * len).toNat = 2 * len.toNat then
    have hx : (0 : USize).toNat + len.toNat ≤ a.size := by simp; lia
    have hy : len.toNat + len.toNat ≤ a.size := by lia
    have hr : (2 * len).toNat + len.toNat ≤ a.size := by lia
    a.foldlInPlace2Then 0 len (2 * len) len hx hy hr w
      (fun _ _ x y c => let s := x + y + c; (s, carry x s c)) fun a _ c => (a, c)
  else (a, 0)

/-- `Slice.foldlInPlace` on `UInt8Array`, capturing step. -/
@[noinline] public def u8FoldlInPlaceW (a : UInt8Array) (w : UInt64) : UInt8Array × UInt64 :=
  let r := a.toSlice.foldlInPlace w fun _ _ x c => (x + c.toUInt8, c + x.toUInt64)
  (r.1.array, r.2)

/-- `Slice.foldlInPlace` on `Float64Array`, capturing step. -/
@[noinline] public def f64FoldlInPlaceW (a : Float64Array) (w : UInt64) :
    Float64Array × UInt64 :=
  let t := w.toFloat
  let r := a.toSlice.foldlInPlace (0 : Float) fun _ _ x s => (x * 0.5 + t, s + x)
  (r.1.array, r.2.toUInt64)

/-- A downstream-style class for limb vectors. -/
public class Limbs (A : Type) where
  /-- Multiplies by a word in place, and returns the carry. -/
  mul1 : A → UInt64 → A × UInt64

public instance : Limbs UInt64Array where
  mul1 a w :=
    let r := a.toSlice.foldlInPlace (0 : UInt64) fun _ _ x c => mulStep w x c
    (r.1.array, r.2)

/-- Generic code over `Limbs`, specialized at each use. -/
@[specialize] public def genericMul1 {A : Type} [Limbs A] (a : A) (w : UInt64) : A × UInt64 :=
  Limbs.mul1 a w

/-- `Slice.foldlInPlace` through `Limbs` and `genericMul1`. -/
@[noinline] public def foldlInPlaceG (a : UInt64Array) (w : UInt64) : UInt64Array × UInt64 :=
  genericMul1 a w

/-- A higher-order wrapper whose step function is unknown. -/
@[noinline] public def mapCarry (f : UInt64 → UInt64 → UInt64 × UInt64) (a : UInt64Array) :
    UInt64Array × UInt64 :=
  let r := a.toSlice.foldlInPlace (0 : UInt64) fun _ _ x c => f x c
  (r.1.array, r.2)

/-- `Slice.foldlInPlace` with an unknown step function. -/
@[noinline] public def foldlInPlaceH (a : UInt64Array) (w : UInt64) : UInt64Array × UInt64 :=
  mapCarry (mulStep w) a

/-! ## `InPlace` programs and the notation -/

/-- An `inplace` loop over the whole array. -/
@[noinline] public def inplaceForW (a : UInt64Array) (w : UInt64) : UInt64Array × UInt64 :=
  have := a.toNat_usize_le
  let r := inplace a do
    for j in 0...a.usize with (c := (0 : UInt64)) do
      let p := mulStep w a[j] c
      a[j] := p.1
      c := p.2
    return c
  (r.2, r.1)

/-- An `inplace` loop handing its result to `then`. -/
@[noinline] public def inplaceThenW (a : UInt64Array) (w : UInt64) : UInt64Array × UInt64 :=
  have := a.toNat_usize_le
  inplace a do
    for j in 0...a.usize with (c := (0 : UInt64)) do
      let p := mulStep w a[j] c
      a[j] := p.1
      c := p.2
    return c
  then fun c a _ => (a, c)

/-- An `inplace` loop that stops at the first element equal to `w`. -/
@[noinline] public def inplaceBreakW (a : UInt64Array) (w : UInt64) : UInt64Array × UInt64 :=
  have := a.toNat_usize_le
  let r := inplace a do
    for j in 0...a.usize with (k := (0 : UInt64)) do
      if a[j] = w then break
      a[j] := a[j] + 1
      k := k + 1
    return k
  (r.2, r.1)

/-- Nested `inplace` loops over rows of 4. -/
@[noinline] public def inplaceNestedW (a : UInt64Array) (w : UInt64) : UInt64Array × UInt64 :=
  have := a.toNat_usize_le
  let rows := a.usize / 4
  have : 4 * rows.toNat ≤ a.size ∧ 4 * rows.toNat < USize.size := by
    have := USize.toNat_lt_size a.usize
    simp only [rows, USize.toNat_div]; lia
  let r := inplace a do
    for r in 0...rows with (tot := w) do
      for c in 0...4 with (acc := (0 : UInt64)) (t := tot) do
        have hc : (4 * r + c).toNat < a.size := by inplace_bound
        let x := a[4 * r + c]
        acc := acc + x
        a[4 * r + c] := acc
        t := t + x
      tot := t
    return tot
  (r.2, r.1)

/-- An `inplace` loop on a slice of all but the first element. -/
@[noinline] public def inplaceSliceW (a : UInt64Array) (w : UInt64) : UInt64Array × UInt64 :=
  let s := a.toSlice 1
  have := s.toNat_usize_le
  let r := inplace s do
    for j in 0...s.usize do
      s[j] := s[j] * w
  (r.2.array, 0)

/-! ## Strides and two-array loops -/

/-- `modifyAt` on the whole array. -/
@[noinline] public def modifyAtW (a : UInt64Array) (w : UInt64) : UInt64Array × UInt64 :=
  (a.modifyAt id 0 a.size fun _ x => x * w, 0)

/-- `modifyStride` with stride 1. -/
@[noinline] public def modifyStrideW (a : UInt64Array) (w : UInt64) : UInt64Array × UInt64 :=
  if h : Stride.Fits ⟨0, 1⟩ a.size a.size then (a.modifyStride ⟨0, 1⟩ a.size (· * w) h, 0)
  else (a, 0)

/-- `modifyStride2` on the even and the odd elements. -/
@[noinline] public def modifyStride2W (a : UInt64Array) (w : UInt64) : UInt64Array × UInt64 :=
  let m := a.size / 2
  if h : Stride.Fits ⟨0, 2⟩ m a.size ∧ Stride.Fits ⟨1, 2⟩ m a.size then
    (a.modifyStride2 ⟨0, 2⟩ ⟨1, 2⟩ m (fun x y => x * w + y) (fun x y => y * w - x) h.1 h.2, 0)
  else (a, 0)

/-- `zipModifyStride` on two arrays. -/
@[noinline] public def zipModifyStrideW (p : UInt64Array × UInt64Array) (w : UInt64) :
    (UInt64Array × UInt64Array) × UInt64 :=
  let (a, b) := p
  if h : Stride.Fits ⟨0, 1⟩ a.size a.size ∧ Stride.Fits ⟨0, 1⟩ a.size b.size then
    (UInt64Array.zipModifyStride a b ⟨0, 1⟩ ⟨0, 1⟩ a.size (fun x y => x * w + y)
      (fun x y => y * w - x) h.1 h.2, 0)
  else ((a, b), 0)

/-! ## Basic operations -/

/-- `push` then `pop`, which never grows the array after the first call. -/
@[noinline] public def pushPopW (a : UInt64Array) (w : UInt64) : UInt64Array × UInt64 :=
  ((a.push w).pop, 0)

/-- Builds a new array of the same size with `push`, from an empty one. -/
@[noinline] public def pushBuildW (a : UInt64Array) (w : UInt64) : UInt64Array × UInt64 :=
  let b := Nat.fold a.size (fun i _ b => b.push (i.toUInt64 + w)) (UInt64Array.emptyWithCapacity 0)
  (a, b.size.toUInt64)

/-- `set!` of the first element. -/
@[noinline] public def setW (a : UInt64Array) (w : UInt64) : UInt64Array × UInt64 :=
  (a.set! 0 w, 0)

/-- `uset` of the first element. -/
@[noinline] public def usetW (a : UInt64Array) (w : UInt64) : UInt64Array × UInt64 :=
  if h : (0 : USize).toNat < a.size then (a.uset 0 w h, 0) else (a, 0)

/-- A checked read of the last element. -/
@[noinline] public def getW (a : UInt64Array) (w : UInt64) : UInt64Array × UInt64 :=
  (a, if h : a.size - 1 < a.size then a[a.size - 1] else w)

/-- `extract` of all but the first element. -/
@[noinline] public def extractW (a : UInt64Array) (_w : UInt64) : UInt64Array × UInt64 :=
  (a, (a.extract 1 a.size).size.toUInt64)

/-- `++` of the array with itself. -/
@[noinline] public def appendW (a : UInt64Array) (_w : UInt64) : UInt64Array × UInt64 :=
  (a, (a ++ a).size.toUInt64)

/-- `ofFn`, of the same size. -/
@[noinline] public def ofFnW (a : UInt64Array) (w : UInt64) : UInt64Array × UInt64 :=
  (a, (UInt64Array.ofFn (n := a.size) fun i => i.val.toUInt64 * w).size.toUInt64)

/-- `toArray`. -/
@[noinline] public def toArrayW (a : UInt64Array) (_w : UInt64) : UInt64Array × UInt64 :=
  (a, a.toArray.size.toUInt64)

/-! ## Slices -/

/-- `toSlice`, `popFront` and `copy`. -/
@[noinline] public def sliceCopyW (a : UInt64Array) (_w : UInt64) : UInt64Array × UInt64 :=
  (a, a.toSlice.popFront.copy.size.toUInt64)

/-- `Slice.reverse` of the whole array. -/
@[noinline] public def sliceReverseW (a : UInt64Array) (_w : UInt64) : UInt64Array × UInt64 :=
  (a.toSlice.reverse.array, 0)

/-- `Slice.set!` of the first element. -/
@[noinline] public def sliceSetW (a : UInt64Array) (w : UInt64) : UInt64Array × UInt64 :=
  ((a.toSlice.set! 0 w).array, 0)

/-! ## Bytes -/

/-- `toBytesLE`. -/
@[noinline] public def toBytesW (a : UInt64Array) (_w : UInt64) : UInt64Array × UInt64 :=
  (a, a.toBytesLE.size.toUInt64)

/-- `ofBytesLE!`. -/
@[noinline] public def ofBytesW (b : ByteArray) (_w : UInt64) : ByteArray × UInt64 :=
  (b, (UInt64Array.ofBytesLE! b).size.toUInt64)

/-! ## The table -/

/-- Every probe, by name, as a function of the input size and the number of calls. -/
public def all : List (String × (Nat → Nat → UInt64)) := [
  ("foldlK", run foldlK), ("foldlW", run foldlW), ("foldrW", run foldrW), ("anyW", run anyW),
  ("containsW", run containsW), ("forInW", run forInW), ("sliceFoldlW", run sliceFoldlW),
  ("u8FoldlW", run u8FoldlW),
  ("foldlInPlaceK", run foldlInPlaceK), ("foldlInPlaceW", run foldlInPlaceW),
  ("foldrInPlaceW", run foldrInPlaceW), ("foldlInPlaceThenW", run foldlInPlaceThenW),
  ("foldlInPlaceRangeW", run foldlInPlaceRangeW), ("foldrInPlaceRangeW", run foldrInPlaceRangeW),
  ("foldlInPlaceRangeThenW", run foldlInPlaceRangeThenW),
  ("foldlInPlaceRangeWith2AccW", run foldlInPlaceRangeWith2AccW),
  ("foldlInPlace2W", run foldlInPlace2W), ("foldlInPlace2ThenW", run foldlInPlace2ThenW),
  ("u8FoldlInPlaceW", run u8FoldlInPlaceW), ("f64FoldlInPlaceW", run f64FoldlInPlaceW),
  ("foldlInPlaceG", run foldlInPlaceG), ("foldlInPlaceH", run foldlInPlaceH),
  ("inplaceForW", run inplaceForW), ("inplaceThenW", run inplaceThenW),
  ("inplaceBreakW", run inplaceBreakW), ("inplaceNestedW", run inplaceNestedW),
  ("inplaceSliceW", run inplaceSliceW),
  ("modifyAtW", run modifyAtW), ("modifyStrideW", run modifyStrideW),
  ("modifyStride2W", run modifyStride2W), ("zipModifyStrideW", run zipModifyStrideW),
  ("pushPopW", run pushPopW), ("pushBuildW", run pushBuildW), ("setW", run setW),
  ("usetW", run usetW), ("getW", run getW), ("extractW", run extractW), ("appendW", run appendW),
  ("ofFnW", run ofFnW), ("toArrayW", run toArrayW),
  ("sliceCopyW", run sliceCopyW), ("sliceReverseW", run sliceReverseW),
  ("sliceSetW", run sliceSetW),
  ("toBytesW", run toBytesW), ("ofBytesW", run ofBytesW)]

end ScalarArrayBench.Probes
