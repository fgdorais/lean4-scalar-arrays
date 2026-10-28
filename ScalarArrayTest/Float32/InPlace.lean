/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import ScalarArray.Float32
import ScalarArrayTest.Util
meta import ScalarArray.Float32
meta import ScalarArrayTest.Util

open ScalarArray ScalarArrayTest

/-!
Tests for `Float32Array`: writes through slices and in-place folds.
-/

/-- A test value at the edge of the element type's range. -/
private abbrev big : Float32 := -1.5e38

/-- The size of an element in bytes. -/
private abbrev elemSize : UInt32 := 4

/-! Writing through slices -/

#guard ((Float32Array.mk #[1, 2, 3, 4])[1...3].set 1 big).array.toArray == #[1, 2, big, 4]
#guard ((Float32Array.mk #[1, 2, 3, 4])[1...3].set! 1 big).toList == [2, big]
#guard ((Float32Array.mk #[1, 2, 3, 4])[1...3].set! 2 big).array.toArray == #[1, 2, 3, 4]
#guard ((Float32Array.mk #[1, 2, 3, 4])[1...3].modify 0 (· * 10)).array.toArray == #[1, 20, 3, 4]
#guard ((Float32Array.mk #[1, 2, 3, 4])[1...3].modify 2 (· * 10)).array.toArray == #[1, 2, 3, 4]
#guard ((Float32Array.mk #[1, 2, 3, big])[1...4].swap 0 2).array.toArray == #[1, big, 3, 2]
#guard ((Float32Array.mk #[1, 2, 3, big])[1...4].swap 1 1).array.toArray == #[1, 2, 3, big]
#guard ((Float32Array.mk #[0, 1, 2, 3, 4, 0])[1...5].reverse).array.toArray == #[0, 4, 3, 2, 1, 0]
#guard ((Float32Array.mk #[0, 1, 2, 3, 0])[1...4].reverse).array.toArray == #[0, 3, 2, 1, 0]
#guard ((Float32Array.mk #[1, 2])[1...1].reverse).array.toArray == #[1, 2]
#guard (∅ : Float32Array.Slice).reverse.toList == []

-- `foldlInPlace` on a slice shifts its range right by one, inserting the initial accumulator.
#guard
  let r := (Float32Array.mk #[1, 2, 3, 4])[1...3].foldlInPlace 9 (fun _ _ x b => (b, x))
  r.1.array.toArray == #[1, 9, 2, 4] && r.2 == 3 && r.1.start == 1 && r.1.stop == 3
#guard
  let r := (Float32Array.mk #[1, 2, 3, 4])[2...2].foldlInPlace 9 (fun _ _ x b => (b, x))
  r.1.array.toArray == #[1, 2, 3, 4] && r.2 == 9

-- `foldrInPlace` shifts the range left by one, from the last element to the first.
#guard
  let r := (Float32Array.mk #[1, 2, 3, 4])[1...3].foldrInPlace 9 (fun _ _ x b => (b, x))
  r.1.array.toArray == #[1, 3, 9, 4] && r.2 == 2 && r.1.start == 1 && r.1.stop == 3
#guard
  let r := (Float32Array.mk #[1, 2, 3, 4])[2...2].foldrInPlace 9 (fun _ _ x b => (b, x))
  r.1.array.toArray == #[1, 2, 3, 4] && r.2 == 9

-- The `Then` versions hand the slice and the last accumulator to `g`, here to store it.
#guard
  let s := (Float32Array.mk #[1, 2, 3, 4])[0...4]
  (s.foldlInPlaceThen 9 (fun _ _ x b => (b, x)) (fun s b => s.set! 0 b)).toList == [4, 1, 2, 3] &&
    (s.foldrInPlaceThen 9 (fun _ _ x b => (b, x)) (fun s b => s.set! 3 b)).toList ==
      [2, 3, 4, 1]
#guard
  let r := (Float32Array.mk #[1, 2, 3, 4])[0...3].foldlInPlaceThen 9 (fun _ _ x b => (b, x))
    (fun s b => s.array.set! 3 b)
  r.toArray == #[9, 1, 2, 3]
#guard
  let a := Float32Array.mk #[1, 2, 3, 4]
  let r := a[1...3].foldlInPlaceThen 9 (fun _ _ x b => (b, x)) Prod.mk
  let r' := a[1...3].foldrInPlaceThen 9 (fun _ _ x b => (b, x)) Prod.mk
  r.1.array.toArray == #[1, 9, 2, 4] && r.2 == 3 &&
    r'.1.array.toArray == #[1, 3, 9, 4] && r'.2 == 2 && a.toArray == #[1, 2, 3, 4]

-- The indices passed to `f`, counted from the start of the slice, in the order of the visits.
#guard
  let s := (Float32Array.mk #[1, 2, 3, 4, 5])[1...4]
  (s.foldlInPlace [] (fun k _ x b => (x, k.toNat :: b))).2 == [2, 1, 0] &&
    (s.foldrInPlace [] (fun k _ x b => (x, k.toNat :: b))).2 == [0, 1, 2]

-- The folds agree with the pure folds of `foldlInPlace_eq_foldl_finRange` and
-- `foldrInPlace_eq_foldr_finRange`, and leave the array outside the slice unchanged.
#guard
  let s := (Float32Array.mk #[1, 2, 3, 4, 5])[1...4]
  let r := s.foldlInPlace 7 (fun _ _ x b => (x * 2 + b, x))
  let r' := s.foldrInPlace 7 (fun _ _ x b => (x * 2 + b, x))
  (r.1.copy.toList, r.2) == (List.finRange s.size).foldl
      (fun (acc : List Float32 × Float32) i => (acc.1 ++ [s[i] * 2 + acc.2], s[i])) ([], 7) &&
    (r'.1.copy.toList, r'.2) == (List.finRange s.size).foldr
      (fun i (acc : List Float32 × Float32) => ((s[i] * 2 + acc.2) :: acc.1, s[i])) ([], 7) &&
    r.1.array[0]! == 1 && r.1.array[4]! == 5 && r'.1.array[0]! == 1 && r'.1.array[4]! == 5 &&
    r.1.array.size == 5 && r'.1.array.size == 5

-- Writing through a slice of a shared array must leave the original unchanged.
#guard
  let a := Float32Array.mk #[1, 2, 3, 4]
  let s := a[1...4].set 0 big
  s.array.toArray == #[1, big, 3, 4] && a.toArray == #[1, 2, 3, 4]
#guard
  let a := Float32Array.mk #[1, 2, 3, 4]
  let s := a[0...4].reverse
  s.array.toArray == #[4, 3, 2, 1] && a.toArray == #[1, 2, 3, 4]
#guard
  let a := Float32Array.mk #[1, 2, 3, 4]
  let r := a[0...4].foldlInPlace 9 (fun _ _ x b => (b, x))
  r.1.array.toArray == #[9, 1, 2, 3] && a.toArray == #[1, 2, 3, 4]
#guard
  let a := Float32Array.mk #[1, 2, 3, 4]
  let r := a[0...4].foldrInPlace 9 (fun _ _ x b => (b, x))
  r.1.array.toArray == #[2, 3, 4, 9] && a.toArray == #[1, 2, 3, 4]

-- `f` must see the elements of the original even when it reads them from the shared array itself.
#guard
  let a := Float32Array.mk #[1, 2, 3, 4]
  let r := a[1...4].foldlInPlace 0 (fun k _ _ b => (a[k.toNat]!, b))
  let r' := a[1...4].foldrInPlace 0 (fun k _ _ b => (a[k.toNat]!, b))
  r.1.array.toArray == #[1, 1, 2, 3] && r'.1.array.toArray == #[1, 1, 2, 3] &&
    a.toArray == #[1, 2, 3, 4]
#guard
  let s := (Float32Array.mk #[1, 2, 3, 4])[0...4]
  let t := s.swap 0 3
  t.toList == [4, 2, 3, 1] && s.toList == [1, 2, 3, 4]

-- A slice of an array that is no longer used writes into that array, without copying it.
@[noinline] def Float32Array.writesThroughSliceInPlace (x : Float32) : Bool :=
  let a := (Float32Array.emptyWithCapacity 8).push x |>.push 2 |>.push 3 |>.push 4 |>.push x
  let p := rawAddr a
  let s := a[1...4]
  let s := s.set! 0 big
  let s := if h : 2 < s.size then s.swap 0 2 else s
  let s := s.modify 1 (· + 1)
  let s := s.reverse
  let (s, _) := s.foldlInPlace () (fun _ _ x b => (x + 1, b))
  let (s, _) := s.foldrInPlace () (fun _ _ x b => (x + 1, b))
  let s := s.foldlInPlaceThen () (fun _ _ x b => (x + 1, b)) (fun s _ => s)
  let s := s.foldrInPlaceThen () (fun _ _ x b => (x + 1, b)) (fun s _ => s)
  rawAddr s.array == p && s.array.toArray == #[x, big + 4, 8, 8, x]

#guard Float32Array.writesThroughSliceInPlace 1

-- Reversing a large slice takes linear time only when every swap writes in place.
#guard
  let n := 1000000
  let xs := (Array.range n).map Nat.toFloat32
  (Float32Array.mk xs)[0...n].reverse.array.toArray == xs.reverse

/-! Folding over windows of one array -/

-- `foldlInPlace2` and `foldlInPlace2Then` with the bounds checked at run time.
private def fold2 {β : Type} (a : Float32Array) (xs ys rs len : USize) (init : β)
    (f : (j : USize) → j.toNat < len.toNat → Float32 → Float32 → β → Float32 × β) :
    Option (Float32Array × β) :=
  if h : xs.toNat + len.toNat ≤ a.size ∧ ys.toNat + len.toNat ≤ a.size ∧
      rs.toNat + len.toNat ≤ a.size then
    some (a.foldlInPlace2 xs ys rs len h.1 h.2.1 h.2.2 init f)
  else
    none

private def fold2Then {β γ : Type} (a : Float32Array) (xs ys rs len : USize) (init : β)
    (f : (j : USize) → j.toNat < len.toNat → Float32 → Float32 → β → Float32 × β)
    (g : Float32Array → β → γ) : Option γ :=
  if h : xs.toNat + len.toNat ≤ a.size ∧ ys.toNat + len.toNat ≤ a.size ∧
      rs.toNat + len.toNat ≤ a.size then
    some (a.foldlInPlace2Then xs ys rs len h.1 h.2.1 h.2.2 init f fun a' _ b => g a' b)
  else
    none

-- Disjoint windows, and the accumulator.
#guard (fold2 (Float32Array.mk #[1, 2, 3, 4, 5, 6, 0, 0, 0]) 0 3 6 3 0
  (fun _ _ x y c => (x + y, c + 1))).map (fun r => (r.1.toArray, r.2)) ==
    some (#[1, 2, 3, 4, 5, 6, 5, 7, 9], 3)

-- Overlapping windows: each step reads what the earlier steps wrote.
#guard (fold2 (Float32Array.mk #[1, 0, 0, 0, 0]) 0 0 1 4 () (fun _ _ x y c => (x + y, c))).map
  (·.1.toArray) == some #[1, 2, 4, 8, 16]
#guard (fold2 (Float32Array.mk #[0, 1, 2, 3, big]) 1 1 0 4 () (fun _ _ x _ c => (x, c))).map
  (·.1.toArray) == some #[1, 2, 3, big, big]
#guard (fold2 (Float32Array.mk #[1, 2, 3, 4]) 0 1 0 3 () (fun _ _ x y c => (x + y, c))).map
  (·.1.toArray) == some #[3, 5, 7, 4]
#guard (fold2 (Float32Array.mk #[1, 1, 1, 1, 1]) 0 1 1 4 () (fun _ _ x y c => (x + y, c))).map
  (·.1.toArray) == some #[1, 2, 3, 4, 5]

-- The indices passed to `f`, in the order of the visits, and the empty fold.
#guard (fold2 (Float32Array.mk #[1, 2, 3]) 0 0 0 3 [] (fun j _ x _ c => (x, j.toNat :: c))).map
  (·.2) == some [2, 1, 0]
#guard (fold2 (Float32Array.mk #[1, 2, 3]) 3 0 1 0 big (fun _ _ x _ c => (x, c))).map
  (fun r => (r.1.toArray, r.2)) == some (#[1, 2, 3], big)

-- The `Then` form hands the array and the last accumulator to `g`, here to store it.
#guard fold2Then (Float32Array.mk #[1, 2, 3, 0]) 0 1 0 2 (0 : Float32)
  (fun _ _ x y c => (x + y, c + x)) (fun a c => (a.set! 3 c).toArray) == some #[3, 5, 3, 3]
#guard (fold2Then (Float32Array.mk #[1, 2]) 0 0 0 2 () (fun _ _ x _ c => (x + 1, c))
  Prod.mk).map (·.1.toArray) == some #[2, 3]

-- The size proof that `g` receives bounds its reads.
#guard
  let a := Float32Array.mk #[1, 2, 3]
  if h : (0 : USize).toNat + (2 : USize).toNat ≤ a.size ∧
      (1 : USize).toNat + (2 : USize).toNat ≤ a.size ∧ 2 < a.size then
    a.foldlInPlace2Then 0 1 0 2 h.1 h.2.1 h.1 () (fun _ _ x y c => (x + y, c))
      (fun a' h' _ => a'[2]'(by rw [h']; exact h.2.2) + a'[0]'(by rw [h']; lia)) == 6
  else false

-- Folding over windows of a shared array must leave the original unchanged, and `f` must see the
-- elements of the original when it reads them from the shared array itself.
#guard
  let a := Float32Array.mk #[1, 2, 3, 4]
  let r := fold2 a 0 1 0 3 () (fun _ _ x y c => (x + y, c))
  r.map (·.1.toArray) == some #[3, 5, 7, 4] && a.toArray == #[1, 2, 3, 4]
#guard
  let a := Float32Array.mk #[1, 2, 3, 4]
  let r := fold2 a 0 0 1 3 () (fun j _ _ _ c => (a[j.toNat]!, c))
  r.map (·.1.toArray) == some #[1, 1, 2, 3] && a.toArray == #[1, 2, 3, 4]

-- An exclusive array is written in place, without copying it.
@[noinline] def Float32Array.foldsWindowsInPlace (x : Float32) : Bool :=
  let a := (Float32Array.emptyWithCapacity 6).push x |>.push 2 |>.push 3 |>.push 0 |>.push 0
  let p := rawAddr a
  match fold2 a 0 1 2 3 () (fun _ _ x y c => (x + y, c)) with
  | some (a, _) => rawAddr a == p && a.toArray == #[x, 2, x + 2, x + 4, x + x + 6]
  | none => false

#guard Float32Array.foldsWindowsInPlace 1

-- Prefix sums in place over a large array take linear time only when every write is in place.
#guard
  let n := 100000
  let r := Id.run do
    let mut r := Array.replicate n (1 : Float32)
    for i in [1:n] do
      r := r.set! i (r[i - 1]! + r[i]!)
    return r
  (fold2 (Float32Array.replicate n 1) 0 1 1 (n - 1).toUSize () (fun _ _ x y c => (x + y, c))).map
    (·.1.toArray) == some r

/-! In-place folds over a `USize` range -/

-- The range folds with the bounds checked at run time, and the slice folds they are specified as.
private def foldlRange? {β : Type} (a : Float32Array) (start len : USize) (init : β)
    (f : (k : USize) → k.toNat < len.toNat → Float32 → β → Float32 × β) :
    Option (Float32Array × β) :=
  if h : start.toNat + len.toNat ≤ a.size then some (a.foldlInPlaceRange start len h init f)
  else none

private def foldrRange? {β : Type} (a : Float32Array) (start len : USize) (init : β)
    (f : (k : USize) → k.toNat < len.toNat → Float32 → β → Float32 × β) :
    Option (Float32Array × β) :=
  if h : start.toNat + len.toNat ≤ a.size then some (a.foldrInPlaceRange start len h init f)
  else none

private def foldlSlice {β : Type} (a : Float32Array) (start len : Nat) (init : β)
    (f : USize → Float32 → β → Float32 × β) : Float32Array × β :=
  let r := a[start...start + len].foldlInPlace init fun k _ => f k
  (r.1.array, r.2)

private def foldrSlice {β : Type} (a : Float32Array) (start len : Nat) (init : β)
    (f : USize → Float32 → β → Float32 × β) : Float32Array × β :=
  let r := a[start...start + len].foldrInPlace init fun k _ => f k
  (r.1.array, r.2)

-- Shifts the range by one, inserting the initial accumulator, and records the indices visited.
private def shift (k : USize) (x : Float32) (b : Float32 × List Nat) :
    Float32 × (Float32 × List Nat) :=
  (b.1, (x, k.toNat :: b.2))

#guard
  let a := Float32Array.mk #[1, 2, 3, 4, 5, big]
  [(0, 6), (1, 3), (2, 0), (0, 0), (6, 0), (5, 1), (0, 1)].all fun (start, len) =>
    let l := (foldlRange? a start.toUSize len.toUSize (big, []) fun k _ => shift k).map
      fun r => (r.1.toArray, r.2)
    let r := (foldrRange? a start.toUSize len.toUSize (big, []) fun k _ => shift k).map
      fun r => (r.1.toArray, r.2)
    let l' := foldlSlice a start len (big, []) shift
    let r' := foldrSlice a start len (big, []) shift
    l == some (l'.1.toArray, l'.2) && r == some (r'.1.toArray, r'.2)

#guard (foldlRange? (Float32Array.mk #[1, 2, 3, 4]) 1 2 (9 : Float32) fun _ _ x b => (b, x)).map
  (fun r => (r.1.toArray, r.2)) == some (#[1, 9, 2, 4], 3)
#guard (foldrRange? (Float32Array.mk #[1, 2, 3, 4]) 1 2 (9 : Float32) fun _ _ x b => (b, x)).map
  (fun r => (r.1.toArray, r.2)) == some (#[1, 3, 9, 4], 2)
#guard (foldlRange? (Float32Array.mk #[1, 2, 3, 4]) 4 0 (9 : Float32) fun _ _ x b => (b, x)).map
  (fun r => (r.1.toArray, r.2)) == some (#[1, 2, 3, 4], 9)

-- The `Then` versions hand the array and the last accumulator to `g`, here to store it.
#guard
  let a := Float32Array.mk #[1, 2, 3, 4]
  if h : (0 : USize).toNat + (3 : USize).toNat ≤ a.size then
    (a.foldlInPlaceRangeThen 0 3 h (9 : Float32) (fun _ _ x b => (b, x)) fun a _ b =>
        (a.set! 3 b).toArray) == #[9, 1, 2, 3] &&
      (a.foldrInPlaceRangeThen 0 3 h (9 : Float32) (fun _ _ x b => (b, x)) fun a _ b =>
        (a.set! 3 b).toArray) == #[2, 3, 9, 1] && a.toArray == #[1, 2, 3, 4]
  else false

-- `g` gets the size of the new array, for a bounded write without a check.
#guard
  let a := Float32Array.mk #[1, 2, 3, 4]
  if h : (0 : USize).toNat + (3 : USize).toNat ≤ a.size then
    (a.foldlInPlaceRangeThen 0 3 h (9 : Float32) (fun _ _ x b => (b, x)) fun a' ha b =>
        (a'.set 2 b (by rw [ha]; simp at h; lia)).toArray) == #[9, 1, 3, 4] &&
      (a.foldrInPlaceRangeThen 0 3 h (9 : Float32) (fun _ _ x b => (b, x)) fun a' ha b =>
        (a'.set 2 b (by rw [ha]; simp at h; lia)).toArray) == #[2, 3, 1, 4]
  else false

-- With two accumulators, the same as `foldlInPlaceRange` on the pair, here a Fibonacci-like
-- carry through the elements.
private def step2 (_ : USize) (x : Float32) (b₁ b₂ : Float32) : Float32 × Float32 × Float32 :=
  (x + b₁, b₂, b₁ + x)

#guard
  let a := Float32Array.mk #[1, 2, 3, 4, 5, big]
  [(0, 6), (1, 3), (2, 0), (6, 0), (5, 1)].all fun (start, len) =>
    let start := (start : Nat).toUSize
    let len := (len : Nat).toUSize
    if h : start.toNat + len.toNat ≤ a.size then
      let r := a.foldlInPlaceRangeWith2Acc start len h (7 : Float32) (big : Float32)
        fun k _ x b₁ b₂ => step2 k x b₁ b₂
      let r' := a.foldlInPlaceRange start len h ((7 : Float32), (big : Float32))
        fun k _ x b => step2 k x b.1 b.2
      r.1.toArray == r'.1.toArray && r.2 == r'.2 && a.toArray == #[1, 2, 3, 4, 5, big]
    else false

#guard
  let a := Float32Array.mk #[1, 2, 3, 4]
  if h : (1 : USize).toNat + (2 : USize).toNat ≤ a.size then
    let r := a.foldlInPlaceRangeWith2Acc 1 2 h (10 : Float32) (20 : Float32)
      fun _ _ x b₁ b₂ => (b₁, b₂, x)
    r.1.toArray == #[1, 10, 20, 4] && r.2 == (2, 3)
  else false

-- The `Then` version hands both accumulators to `g`, with the size of the new array.
#guard
  let a := Float32Array.mk #[1, 2, 3, 4]
  if h : (0 : USize).toNat + (2 : USize).toNat ≤ a.size ∧ 4 ≤ a.size then
    (a.foldlInPlaceRangeWith2AccThen 0 2 h.1 (10 : Float32) (20 : Float32)
        (fun _ _ x b₁ b₂ => (b₁, b₂, x)) fun a' ha b₁ b₂ =>
          ((a'.set 2 b₁ (by have := h.2; rw [ha]; lia)).set 3 b₂
            (by have := h.2; simp only [Float32Array.size_set, ha]; lia)).toArray) ==
      #[10, 20, 1, 2]
  else false

-- A shared array is left unchanged, and an exclusive one is written in place.
#guard
  let a := Float32Array.mk #[1, 2, 3, 4]
  let r := foldlRange? a 0 4 (9 : Float32) fun _ _ x b => (b, x)
  let r' := foldrRange? a 0 4 (9 : Float32) fun _ _ x b => (b, x)
  r.map (·.1.toArray) == some #[9, 1, 2, 3] && r'.map (·.1.toArray) == some #[2, 3, 4, 9] &&
    a.toArray == #[1, 2, 3, 4]

@[noinline] def Float32Array.foldsRangeInPlace (x : Float32) : Bool :=
  let a := (Float32Array.emptyWithCapacity 8).push x |>.push 2 |>.push 3 |>.push 4 |>.push x
  let p := rawAddr a
  match foldlRange? a 1 3 () (fun _ _ x b => (x + 1, b)) with
  | some (a, _) =>
    match foldrRange? a 1 3 () (fun _ _ x b => (x + 1, b)) with
    | some (a, _) => rawAddr a == p && a.toArray == #[x, 4, 5, 6, x]
    | none => false
  | none => false

#guard Float32Array.foldsRangeInPlace 1
