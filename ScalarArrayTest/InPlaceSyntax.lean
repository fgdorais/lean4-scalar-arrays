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
      for j in 0...len with (s := 0) do
        let x ← a[j]
        let s := s + x
        a[j] := s
      return s
  else none

#guard prefixSums (UInt32Array.mk #[1, 2, 3, 4, 5]) 4 ==
  some (10, UInt32Array.mk #[1, 3, 6, 10, 5])
#guard prefixSums (UInt32Array.mk #[1, 2]) 3 == none

/-- Doubles the elements at `lo` up to `hi - 1`, and counts them. -/
private def double (a : UInt8Array) (lo hi : USize) : Option (Nat × UInt8Array) :=
  if h : hi.toNat ≤ a.size then
    some <| inplace a do
      for j in lo...hi with (k := 0) do
        a[j] := 2 * a[j]
        k := k + 1
      return k
  else none

#guard double (UInt8Array.mk #[1, 2, 3, 4, 5]) 1 4 == some (3, UInt8Array.mk #[1, 4, 6, 8, 5])
#guard double (UInt8Array.mk #[1, 2, 3]) 2 1 == some (0, UInt8Array.mk #[1, 2, 3])

-- `*...hi` and `lo...<hi` are ranges too.
#guard
  let a := UInt8Array.mk #[1, 2, 3]
  have : (3 : USize).toNat ≤ a.size := by simp [a]
  (inplace a do
    for j in *...3 do
      a[j] := a[j] + 1
    for j in 1...<3 do
      a[j] := a[j] + 1).2.toArray == #[2, 4, 5]

/-- Lists the indices from `hi - 1` down to `lo`, and shifts that window up by one. -/
private def shiftRange (a : UInt8Array) (lo hi : USize) : Option (List Nat × UInt8Array) :=
  if h : hi.toNat + 1 ≤ a.size ∧ hi.toNat + 1 < USize.size then
    some <| inplace a do
      for j in reverse lo...hi with (l := ([] : List Nat)) do
        have hj1 : (j + 1).toNat < a.size := by
          rw [USize.toNat_add, USize.toNat_one, Nat.mod_eq_of_lt (by lia)]; lia
        a[j + 1] := a[j]
        l := j.toNat :: l
      return l
  else none

#guard shiftRange (UInt8Array.mk #[1, 2, 3, 4, 5]) 1 3 ==
  some ([1, 2], UInt8Array.mk #[1, 2, 2, 3, 5])
#guard shiftRange (UInt8Array.mk #[1, 2, 3]) 2 1 == some ([], UInt8Array.mk #[1, 2, 3])

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
      for j in reverse 0...len with (top := 0) do
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
      for j in 0...len with (c := 0) (b := 0) do
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

-- A program may use the array's size, without a copy.
@[noinline] def UInt32Array.inplaceUsesSize (x : UInt32) : Bool :=
  let a := (UInt32Array.emptyWithCapacity 4).push x |>.push 2 |>.push 3
  let p := rawAddr a
  have := a.toNat_usize_le
  let r := inplace a do
    for j in 0...a.usize do
      a[j] := a[j] + 1
  rawAddr r.2 == p && r.2.toArray == #[x + 1, 3, 4]

#guard UInt32Array.inplaceUsesSize 1

/-- Clamps each element of the window of `len` at `off` to at most `m`, and counts the clamped. -/
private def clamp (a : UInt16Array) (off len : USize) (m : UInt16) : Option (Nat × UInt16Array) :=
  if h : off.toNat + len.toNat ≤ a.size then
    some <| inplace a do
      for j in 0...len with (k := 0) do
        if a[off + j] > m then
          a[off + j] := m
          k := k + 1
      return k
  else none

#guard clamp (UInt16Array.mk #[9, 1, 7, 3, 8, 9]) 1 4 5 ==
  some (2, UInt16Array.mk #[9, 1, 5, 3, 5, 9])

/-- Nested reads, `let mut` and an `if` with an `else` at the top level of a program. -/
private def swapIfGreater (a : Int32Array) (i j : USize) : Option (Bool × Int32Array) :=
  if h : i.toNat < a.size ∧ j.toNat < a.size then
    some <| inplace a do
      let mut swapped := false
      if h' : a[i] > a[j] then
        let x ← a[i]
        a[i] := a[j]
        a[j] := x
        swapped := true
      else
        swapped := false
      return swapped
  else none

#guard swapIfGreater (Int32Array.mk #[3, -1]) 0 1 == some (true, Int32Array.mk #[-1, 3])
#guard swapIfGreater (Int32Array.mk #[-3, 1]) 0 1 == some (false, Int32Array.mk #[-3, 1])

/-- Nested loops: running sums along the rows of a `rows × cols` matrix, in place, and the total. -/
private def rowSums (a : UInt32Array) (rows cols : USize) : Option (UInt32 × UInt32Array) :=
  if h : rows.toNat * cols.toNat ≤ a.size ∧ (rows * cols).toNat = rows.toNat * cols.toNat then
  some <| inplace a do
    for r in 0...rows with (total := 0) do
      have hr : (r * cols).toNat + cols.toNat ≤ a.size := by
        have h₁ : (r.toNat + 1) * cols.toNat ≤ rows.toNat * cols.toNat :=
          Nat.mul_le_mul_right _ (by lia)
        have h₂ : r.toNat * cols.toNat < USize.size := by
          have := (rows * cols).toNat_lt_size
          have := Nat.mul_le_mul_right cols.toNat (Nat.le_of_lt (by lia : r.toNat < rows.toNat))
          lia
        rw [USize.toNat_mul, Nat.mod_eq_of_lt h₂]; rw [Nat.succ_mul] at h₁; lia
      for c in 0...cols with (s := 0) do
        s := s + a[r * cols + c]
        a[r * cols + c] := s
      total := total + s
    return total
  else none

#guard rowSums (UInt32Array.mk #[1, 2, 3, 4, 5, 6]) 2 3 ==
  some (21, UInt32Array.mk #[1, 3, 6, 4, 9, 15])

-- Reads and writes go to the program's array only.
/-- error: an `inplace` program on `a` reads and writes only `a` -/
#guard_msgs in
example (a b : UInt8Array) (h : 0 < a.size) : UInt8 × UInt8Array :=
  inplace a do
    let x ← b[0]
    return x

/--
error: `y` is not a mutable variable here: declare it with `let mut`, or carry it into the loop with `with (y := y)`
-/
#guard_msgs in
example (a : UInt8Array) (h : 0 < a.size) : UInt8 × UInt8Array :=
  inplace a do
    let mut y := 0
    for j in 0...1 do
      y := 1
    return y

