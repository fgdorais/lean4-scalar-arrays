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

/--
Shifts the number with little-endian 64-bit limbs `a` left by 1111 = 17 * 64 + 23 bits, keeping
`a.size` limbs, in place.
-/
private def shl1111 (a : UInt64Array) : UInt64Array :=
  if h : 18 ≤ a.size then
    (inplace a do
      for j in reverse 18...a.usize do
        a[j] := (a[j - 17] <<< 23) ||| (a[j - 18] >>> 41)
      a[17] := a[0] <<< 23
      for j in 0...17 do
        a[j] := 0).2
  else
    UInt64Array.mk (Array.replicate a.size 0)

/-- The number with little-endian 64-bit limbs `a`. -/
private def limbsToNat (a : UInt64Array) : Nat :=
  a.toArray.foldr (fun x n => n * 2 ^ 64 + x.toNat) 0

/-- The `n` low 64-bit limbs of `x`. -/
private def natToLimbs (n x : Nat) : UInt64Array :=
  UInt64Array.mk ((Array.range n).map fun i => (x >>> (64 * i)).toUInt64)

private def checkShl (n x : Nat) : Bool :=
  limbsToNat (shl1111 (natToLimbs n x)) == (x <<< 1111) % 2 ^ (64 * n)

#guard (List.range 24).all fun n => checkShl n (3 ^ (40 * n))
#guard (List.range 24).all fun n => checkShl n (2 ^ (64 * n) - 1)
#guard checkShl 18 1 && checkShl 18 (2 ^ 41) && checkShl 19 (2 ^ 41) && checkShl 17 1

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


/-!
`then k` hands the program's result and the new array, with its size, to `k`, which the program
calls where it ends, so no result pair is built.
-/

/-- The butterfly above, with the windows' carry and borrow and the new array handed to `k`. -/
@[inline] private def butterflyThen (a : UInt64Array) (xs ys ts len : USize)
    (k : UInt64 → UInt64 → (a' : UInt64Array) → a'.size = a.size → γ) (none : γ) : γ :=
  if h : xs.toNat + len.toNat ≤ a.size ∧ ys.toNat + len.toNat ≤ a.size ∧
      ts.toNat + len.toNat ≤ a.size then
    have hx := h.1
    have hy := h.2.1
    have ht := h.2.2
    inplace a do
      for j in 0...len with (c := 0) (b := 0) do
        let u ← a[xs + j]
        let v ← a[ys + j]
        let (s, c) := addc u v c
        let (d, b) := subb u v b
        a[xs + j] := s
        a[ts + j] := d
      return (c, b)
    then fun (c, b) a' h => k c b a' h
  else none

#guard butterflyThen (UInt64Array.mk #[5, 0xFFFFFFFFFFFFFFFF, 7, 6, 1, 3, 0, 0, 0]) 0 3 6 3
    (fun c b a _ => some ((c, b), a)) none ==
  butterfly (UInt64Array.mk #[5, 0xFFFFFFFFFFFFFFFF, 7, 6, 1, 3, 0, 0, 0]) 0 3 6 3

-- The size proof chains a second program on the new array.
#guard
  let a := UInt8Array.mk #[1, 2, 3]
  have : (3 : USize).toNat ≤ a.size := by simp [a]
  inplace a do
    for j in *...3 with (s := 0) do
      s := s + a[j]
      a[j] := s
    return s
  then fun s a' h =>
    have : (3 : USize).toNat ≤ a'.size := by simp [a, h]
    (s, (inplace a' do
      for j in *...3 do
        a'[j] := a'[j] + s).2.toArray) == (6, #[7, 9, 12])

-- Without `return`, the result is `()`; `then` works after an `if` at the end, too.
#guard
  let a := Int8Array.mk #[3, -1]
  have : 1 < a.size := by simp [a]
  inplace a do
    if a[0] > a[1] then
      let x ← a[0]
      a[0] := a[1]
      a[1] := x
  then fun () a' _ => a'.toArray == #[-1, 3]

/-!
The program doesn't keep the array alive, so an exclusive array is updated in place even when the
rest of the program after an `if` with loops uses mutable variables, or the array's size.
-/

/-- Sums the first `n` elements, forward or as a base-3 number backward, then fills them with it. -/
@[noinline] private def fillWithSum (a : UInt32Array) (n : USize) (h : n.toNat ≤ a.size)
    (b : Bool) : UInt32Array :=
  inplace a do
    let mut t := 0
    if b then
      for j in 0...n with (t := t) do
        t := t + a[j]
    else
      for j in reverse 0...n with (t := t) do
        t := t * 3 + a[j]
    for j in 0...n with (t := t) do
      a[j] := t
  then fun _ a' _ => a'

@[noinline] def UInt32Array.inplaceIfLoopsInPlace (x : UInt32) (b : Bool) : Bool :=
  let a := (UInt32Array.emptyWithCapacity 4).push x |>.push 2 |>.push 3
  let p := rawAddr a
  let a := fillWithSum a a.usize a.toNat_usize_le b
  rawAddr a == p && a.toArray == if b then #[x + 5, x + 5, x + 5] else
    let t := (3 * 3 + 2) * 3 + x
    #[t, t, t]

#guard UInt32Array.inplaceIfLoopsInPlace 1 true
#guard UInt32Array.inplaceIfLoopsInPlace 1 false

/-- Sets the first element, if asked, then fills the array with it. -/
@[noinline] private def fillWithFirst (a : UInt32Array) (h : 0 < a.size) (b : Bool) :
    UInt32Array :=
  inplace a do
    if b then
      a[0] := 7
    for j in 0...a.usize with (t := a[0]) do
      a[j] := t
  then fun _ a' _ => a'

@[noinline] def UInt32Array.inplaceSizeAfterIfInPlace (x : UInt32) : Bool :=
  let a := (UInt32Array.emptyWithCapacity 4).push x |>.push 2 |>.push 3
  let p := rawAddr a
  let a := fillWithFirst a (by simp [a]) true
  rawAddr a == p && a.toArray == #[7, 7, 7]

#guard UInt32Array.inplaceSizeAfterIfInPlace 1

-- Inside the program, `a` is the array before the program runs, so uses of it other than `a[i]`,
-- `a.size` and `a.usize` are errors.
/--
error: inside `inplace a do`, `a` is the array before the program runs: read its current elements with `a[i]`, at a `USize` index `i`, and its size with `a.size` or `a.usize`
-/
#guard_msgs in
example (a : UInt8Array) (h : 0 < a.size) : UInt8 × UInt8Array :=
  inplace a do
    a[0] := 42
    return a[0]!

/--
error: inside `inplace a do`, `a` is the array before the program runs: read its current elements with `a[i]`, at a `USize` index `i`, and its size with `a.size` or `a.usize`
-/
#guard_msgs in
example (a : UInt8Array) (h : 0 < a.size) : Nat × UInt8Array :=
  inplace a do
    a[0] := 42
    return a.toArray.size

-- Reads run before their statement, so reads under a binder or in a branch of a term are errors.
/--
error: `inplace` reads `a[i]` before the statement runs, so it can't read under a binder or in a branch of a term: read the element first, with `let x ← a[i]`, or branch with an `if` statement
-/
#guard_msgs in
example (a : UInt8Array) (j : USize) (h : 0 < a.size) : Unit × UInt8Array :=
  inplace a do
    a[0] := if h : j.toNat < a.size then a[j] else 0

/--
error: `inplace` reads `a[i]` before the statement runs, so it can't read under a binder or in a branch of a term: read the element first, with `let x ← a[i]`, or branch with an `if` statement
-/
#guard_msgs in
example (a : UInt8Array) (n : USize) (h : n.toNat ≤ a.size) : Bool × UInt8Array :=
  inplace a do
    for j in 0...n with (r := false) do
      if j + 1 < n && a[j + 1] > a[j] then
        r := true
    return r

/--
error: `inplace` reads `a[i]` before the statement runs, so it can't read under a binder or in a branch of a term: read the element first, with `let x ← a[i]`, or branch with an `if` statement
-/
#guard_msgs in
example (a : UInt8Array) (h : 4 ≤ a.size) : Unit × UInt8Array :=
  inplace a do
    a[0] := (List.range 3).foldl (fun s k => s + a[k.toUSize]) 0

-- A bound that `inplace_bound` can't prove is reported as such.
/--
error: inplace: cannot prove the bound of this index from the hypotheses in context:
  j.toNat < a.size
Add the missing fact with a `have` before the statement, or as a hypothesis around the program.
-/
#guard_msgs in
example (a : UInt8Array) (n : USize) : Unit × UInt8Array :=
  inplace a do
    for j in 0...n do
      a[j] := 0

/--
Type ascriptions, `unless`, a program bound with `let x ← m`, and `return` in both branches of the
last `if`.
-/
private def misc (a : UInt64Array) (h : 4 ≤ a.size) : UInt64 × UInt64Array :=
  inplace a do
    let mut t : UInt64 := 1
    let u : UInt64 := 5
    for j in 0...4 with (s : UInt64 := u) do
      s := s + a[j]
    unless s > 100 do
      a[0] := s
    let x ← UInt64Array.InPlace.read 1 (by inplace_bound)
    if x > 3 then
      return x + t
    else
      return s

#guard misc (UInt64Array.mk #[1, 2, 3, 4]) (by decide) == (15, UInt64Array.mk #[15, 2, 3, 4])
#guard misc (UInt64Array.mk #[1, 9, 3, 4]) (by decide) == (10, UInt64Array.mk #[22, 9, 3, 4])

/-!
Loops with three and four variables, which stay unboxed, and nested loops, whose inner loop ends by
calling the next step of the outer one.
-/

/-- `u - x - b` and its borrow, for a borrow `b ≤ 1`. -/
private def subB (u x b : UInt64) : UInt64 × UInt64 :=
  (u - x - b, (if u < x then 1 else 0) + (if u - x < b then 1 else 0))

/--
With windows `w₁ = a[0, len)`, `w₂ = a[len, 2 len + 1)` and `w₃ = a[2 len + 1, 3 len + 1)`:
`w₂[1 + j] -= w₁[j]` and `w₃ := (w₃ - w₁) <<< 1`, in one pass with two borrows and the carry of
the shift, and returns them.
-/
private def fused (a : UInt64Array) (len : USize) :
    Option ((UInt64 × UInt64 × UInt64) × UInt64Array) :=
  if h : 3 * len.toNat + 1 ≤ a.size ∧ 3 * len.toNat + 1 < USize.size then
    some <| inplace a do
      for j in 0...len with (b₂ : UInt64 := 0) (b₃ : UInt64 := 0) (s : UInt64 := 0) do
        have h₂ : (len + 1 + j).toNat < a.size := by inplace_bound
        have h₃ : (2 * len + 1 + j).toNat < a.size := by inplace_bound
        let x ← a[j]
        let (u, b₂') := subB a[len + 1 + j] x b₂
        let (t, b₃') := subB a[2 * len + 1 + j] x b₃
        a[len + 1 + j] := u
        a[2 * len + 1 + j] := (t <<< 1) ||| s
        b₂ := b₂'
        b₃ := b₃'
        s := t >>> 63
      return (b₂, b₃, s)
  else none

/-- `fused` in two passes, with one and two variables. -/
private def twoPasses (a : UInt64Array) (len : USize) :
    Option ((UInt64 × UInt64 × UInt64) × UInt64Array) :=
  if h : 3 * len.toNat + 1 ≤ a.size ∧ 3 * len.toNat + 1 < USize.size then
    some <| inplace a do
      for j in 0...len with (b₂ : UInt64 := 0) do
        have h₂ : (len + 1 + j).toNat < a.size := by inplace_bound
        let (u, b₂') := subB a[len + 1 + j] a[j] b₂
        a[len + 1 + j] := u
        b₂ := b₂'
      for j in 0...len with (b₃ : UInt64 := 0) (s : UInt64 := 0) do
        have h₃ : (2 * len + 1 + j).toNat < a.size := by inplace_bound
        let (t, b₃') := subB a[2 * len + 1 + j] a[j] b₃
        a[2 * len + 1 + j] := (t <<< 1) ||| s
        b₃ := b₃'
        s := t >>> 63
      return (b₂, b₃, s)
  else none

#guard
  let a := UInt64Array.mk #[5, 0, 7, 1, 9, 2, 3, 0xFFFFFFFFFFFFFFFF, 4, 0, 0x8000000000000000, 6, 1]
  fused a 4 == twoPasses a 4 && (fused a 4).isSome
#guard
  let a := UInt64Array.mk ((Array.range 31).map fun i => (i * 0x9E3779B97F4A7C15 : Nat).toUInt64)
  fused a 10 == twoPasses a 10 && (fused a 10).isSome

/-- The sum, minimum, maximum and number of odd elements of `a[lo, hi)`, in both directions. -/
private def stats (a : UInt8Array) (lo hi : USize) : Option ((Nat × UInt8 × UInt8 × Nat) × Bool) :=
  if h : hi.toNat ≤ a.size then
    let up := inplace a do
      for j in lo...hi with (s := 0) (m := 255) (M := 0) (o := 0) do
        let x ← a[j]
        s := s + x.toNat
        m := min m x
        M := max M x
        o := o + x.toNat % 2
      return (s, m, M, o)
    let down := inplace a do
      for j in reverse lo...hi with (s := 0) (m := 255) (M := 0) (o := 0) do
        let x ← a[j]
        s := s + x.toNat
        m := min m x
        M := max M x
        o := o + x.toNat % 2
      return (s, m, M, o)
    some (up.1, up.1 == down.1)
  else none

#guard stats (UInt8Array.mk #[9, 4, 7, 200, 1, 6]) 1 5 == some ((212, 1, 200, 2), true)
#guard stats (UInt8Array.mk #[9, 4]) 1 1 == some ((0, 255, 0, 0), true)

/-- The reverse of `stats`' order of visits, with three variables: the indices and a running sum. -/
private def visits (a : UInt8Array) (lo hi : USize) : Option (List Nat × Nat × Nat) :=
  if h : hi.toNat ≤ a.size then
    some (inplace a do
      for j in reverse lo...hi with (l := ([] : List Nat)) (s := 0) (k := 0) do
        l := j.toNat :: l
        s := s + a[j].toNat
        k := k + 1
      return (l, s, k)).1
  else none

#guard visits (UInt8Array.mk #[1, 2, 3, 4, 5]) 1 4 == some ([1, 2, 3], 9, 3)

/--
Running sums of the rows of `rows` by 4, offset by the total of the rows before, in place, and the
total: the inner loop has two variables, one carried from the outer loop.
-/
private def offsetRows (a : UInt32Array) (rows : USize) : Option (UInt32 × UInt32Array) :=
  if h : 4 * rows.toNat ≤ a.size ∧ 4 * rows.toNat < USize.size then
    some <| inplace a do
      for r in 0...rows with (tot := 0) do
        for c in 0...4 with (acc := 0) (t := tot) do
          have hc : (4 * r + c).toNat < a.size := by inplace_bound
          let x ← a[4 * r + c]
          acc := acc + x
          a[4 * r + c] := acc + tot
          t := t + x
        tot := t
      return tot
  else none

#guard offsetRows (UInt32Array.mk #[1, 2, 3, 4, 10, 20, 30, 40, 7]) 2 ==
  some (110, UInt32Array.mk #[1, 3, 6, 10, 20, 40, 70, 110, 7])

-- A loop has at most four variables.
/-- error: a loop has at most four variables -/
#guard_msgs in
example (a : UInt8Array) : Unit × UInt8Array :=
  inplace a do
    for j in 0...0 with (x := 0) (y := 0) (z := 0) (u := 0) (v := 0) do
      x := y + z + u + v
