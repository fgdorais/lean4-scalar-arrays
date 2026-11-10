/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import ScalarArray
import ScalarArray.InPlaceSyntax
import ScalarArrayTest.Util
meta import ScalarArray
meta import ScalarArrayTest.Util

open ScalarArray ScalarArrayTest

/-!
Tests for `inplace` programs.
-/

/-- Prefix sums of the first `len` elements, in place, and their total. -/
private def prefixSums (a : UInt32Array) (len : USize) : Option (UInt32 × UInt32Array) :=
  if h : len.toNat ≤ a.size then
    some <| inplace a do
      for j < len with (s := 0) do
        let x ← a[j]
        let s := s + x
        a[j] := s
      return s
  else none

#guard prefixSums (UInt32Array.mk #[1, 2, 3, 4, 5]) 4 ==
  some (10, UInt32Array.mk #[1, 3, 6, 10, 5])
#guard prefixSums (UInt32Array.mk #[1, 2]) 3 == none

/-- Shifts the window of `len` elements at `off` up by one, from the top down, and returns the
element shifted out. -/
private def shiftUp (a : UInt8Array) (off len : USize) : Option (UInt8 × UInt8Array) :=
  if h : off.toNat + (len + 1).toNat ≤ a.size ∧ (len + 1).toNat = len.toNat + 1 then
    have h₀ : off.toNat < a.size := by lia
    have h₁ : off.toNat + len.toNat ≤ a.size := by lia
    have h₂ : (off + 1).toNat + len.toNat ≤ a.size := by
      rw [USize.toNat_add]; have := Nat.mod_le (off.toNat + (1 : USize).toNat) USize.size
      simp at this ⊢; lia
    some <| inplace a do
      for j < len, downward with (top := 0) do
        let x ← a[off + j]
        let top := if j + 1 = len then x else top
        a[(off + 1) + j] := x
      a[off] := 0
      return top
  else none

#guard shiftUp (UInt8Array.mk #[9, 1, 2, 3, 0, 9]) 1 3 ==
  some (3, UInt8Array.mk #[9, 0, 1, 2, 3, 9])

/-- `x + y + c` and its carry, for a carry `c ≤ 1`. -/
@[inline] private def addc (x y c : UInt64) : UInt64 × UInt64 :=
  let s := x + y + c
  (s, ((x &&& y) ||| ((x ||| y) &&& ~~~s)) >>> 63)

/-- `x - y - b` and its borrow, for a borrow `b ≤ 1`. -/
@[inline] private def subb (x y b : UInt64) : UInt64 × UInt64 :=
  let d := x - y - b
  (d, ((~~~x &&& y) ||| (~~~(x ^^^ y) &&& d)) >>> 63)

/--
The butterfly of lean4-mpn's FFT on the windows of `len` limbs at `xs`, `ys` and `ts`:
`x, t := x + y, x - y`, with the carry and the borrow kept apart.
-/
private def butterfly (a : UInt64Array) (xs ys ts len : USize) :
    Option ((UInt64 × UInt64) × UInt64Array) :=
  if h : xs.toNat + len.toNat ≤ a.size ∧ ys.toNat + len.toNat ≤ a.size ∧
      ts.toNat + len.toNat ≤ a.size then
    have hx := h.1
    have hy := h.2.1
    have ht := h.2.2
    some <| inplace a do
      for j < len with (c := 0) (b := 0) do
        let u ← a[xs + j]
        let v ← a[ys + j]
        let (s, c) := addc u v c
        let (d, b) := subb u v b
        a[xs + j] := s
        a[ts + j] := d
      return (c, b)
  else none

#guard butterfly (UInt64Array.mk #[5, 0xFFFFFFFFFFFFFFFF, 7, 6, 1, 3, 0, 0, 0]) 0 3 6 3 ==
  some ((0, 0), UInt64Array.mk #[11, 0, 11, 6, 1, 3,
    0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFD, 4])

-- A shared array is copied once, and an exclusive one is written in place.
#guard
  let a := UInt32Array.mk #[1, 2, 3]
  prefixSums a 3 == some (6, UInt32Array.mk #[1, 3, 6]) && a.toArray == #[1, 2, 3]

@[noinline] def UInt32Array.inplaceWritesInPlace (x : UInt32) : Bool :=
  let a := (UInt32Array.emptyWithCapacity 4).push x |>.push 2 |>.push 3
  let p := rawAddr a
  match prefixSums a 3 with
  | some (_, a) => rawAddr a == p && a.toArray == #[x, x + 2, x + 5]
  | none => false

#guard UInt32Array.inplaceWritesInPlace 1

-- Reads and writes go to the program's array only.
/-- error: an `inplace` program on `a` reads and writes only `a` -/
#guard_msgs in
example (a b : UInt8Array) (h : 0 < a.size) : UInt8 × UInt8Array :=
  inplace a do
    let x ← b[0]
    return x
