/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import ScalarArray.Int64
import ScalarArrayTest.Util
meta import ScalarArray.Int64
meta import ScalarArrayTest.Util

open ScalarArray ScalarArrayTest

/-!
Tests for `Int64Array`: lemmas, used from another module.
-/

/-- A test value at the edge of the element type's range. -/
private abbrev big : Int64 := -9223372036854775808

/-- The size of an element in bytes. -/
private abbrev elemSize : UInt32 := 8

/-! Lemmas -/

example (a : Int64Array) (v : Int64) : (a.push v).pop = a := by simp [Int64Array.ext_iff]
example : (Int64Array.replicate 3 big)[1] = big := by simp
example (a b : Int64Array) (h : 0 < a.size) : (a ++ b)[0]'(by simp; lia) = a[0] := by simp [h]
example (a : Int64Array) (i : Nat) (v : Int64) (h : i < a.size) :
    (a.set i v h)[i]'(by simpa) = v := by simp
example (a : Int64Array) : a.extract 0 a.size = a := by simp
example (a : Int64Array) (v : Int64) : (a.push v).pop = a :=
  Int64Array.ext_getElem (by simp) (by simp_all)
example (a : Int64Array) (v : Int64) : (a.push v).pop = a :=
  Int64Array.ext_getElem? fun i => by
    by_cases h : i < a.size <;> simp [h, getElem?_pos, getElem?_neg]
example (a b : Int64Array) (h : a.toArray = b.toArray) : a = b := by simpa using h

/-! Lists -/

#guard (Int64Array.ofList [1, 2, big]).toArray == #[1, 2, big]
#guard (Int64Array.ofList []).toArray == #[]
#guard [1, 2, big].toInt64Array == Int64Array.mk #[1, 2, big]
#guard (Int64Array.ofList ((List.range 100000).map Nat.toInt64)).toArray ==
  (Array.range 100000).map Nat.toInt64
#guard rawElemSize (Int64Array.ofList [1, 2]) == elemSize

/-! More lemmas -/

example (a b c : Int64Array) : a ++ b ++ c = a ++ (b ++ c) := Int64Array.append_assoc ..
example (a : Int64Array) : a ++ ∅ = a := by simp
example (a b : Int64Array) : (a ++ b).extract 0 a.size = a := by simp
example (a : Int64Array) (i : Nat) (v : Int64) : (a.set! i v).size = a.size := by simp
example (l : List Int64) : (Int64Array.ofList l).toList = l := by simp
example (a : Int64Array) : Int64Array.ofList a.toList = a := by simp

/-! Lemmas from another module -/

example (a : Int64Array) (i : USize) (v : Int64) (h) (j : Nat) (hj) :
    (a.uset i v h)[j]'hj = if i.toNat = j then v else a[j]'(by simpa using hj) := by
  simp
example (a : Int64Array) (v : Int64) :
    (a.set! 0 v)[0]? = if 0 < a.size then some v else none := by
  simp
example (a : Int64Array) (v : Int64) (h : 1 < (a.set! 0 v).size) :
    (a.set! 0 v)[1] = a[1]'(by simpa using h) := by
  simp
example (a : Int64Array) (p : Int64 → Bool) : (a.popWhile p).size ≤ a.size :=
  Int64Array.size_popWhile_le p a
example (src dest : Int64Array) :
    (src.copySlice 0 dest 0 src.size).size = max dest.size src.size := by
  simp
example (a : Int64Array) (f : Nat → Int64 → Option Nat) :
    a.toList.foldlM f 0 = a.foldlM f 0 := by
  simp
example (a : Int64Array) (f : Int64 → Nat → Option Nat) :
    a.toList.foldrM f 0 = a.foldrM f 0 := by
  simp
example (a : Int64Array) (f : Int64 → StateM Nat PUnit) : forM a.toList f = forM a f := by
  simp
example (a b : Int64Array) (x : Int64) (h : x ∈ a) : x ∈ (a ++ b).toList := by
  simp [h]
example (a : Int64Array) (x : Int64) : x ∈ a.push x := by
  simp
example (a : Int64Array) (i : Nat) (h : i < a.size) : a[i] ∈ a.toList := by
  simpa using Int64Array.getElem_mem h
example (a : Int64Array) (start stop : Nat) (p : Int64 → Bool) :
    (a.toSlice start stop).any p = (a.extract start stop).any p := by
  simp
example (a : Int64Array) (start stop : Nat) :
    (a.toSlice start stop).toList = (a.toList.extract start stop) := by
  simp
example (s : Int64Array.Slice) (p : Int64 → Bool) : s.count p = s.copy.toList.countP p := by
  simp
example (s : Int64Array.Slice) (p : Int64 → Bool) :
    s.find? p = s.copy.toList.find? p ∧ s.findRev? p = s.copy.toList.reverse.find? p := by
  simp
example (s : Int64Array.Slice) (f : Nat → Int64 → Nat) :
    s.foldl f 0 = s.copy.toList.foldl f 0 := by
  simp
example (s : Int64Array.Slice) (f : Int64 → StateM Nat PUnit) :
    forM s f = forM s.copy.toList f := by
  simp
example (s : Int64Array.Slice) (x : Int64) : x ∈ s ↔ x ∈ s.copy.toList := by
  simp
example (s t : Int64Array.Slice) : (s == t) = (s.copy == t.copy) := by
  simp
example (a : Int64Array) : a.iter.toInt64Array = a := by
  simp
example (s : Int64Array.Slice) : s.iter.toInt64Array = s.copy := by
  simp
example : (∅ : Int64Array.Slice).size = 0 := by
  simp
example (s : Int64Array.Slice) (i : Nat) (v : Int64) (h : i < s.size) :
    (s.set i v h).copy = s.copy.set i v (by simpa using h) := by
  simp
example (s : Int64Array.Slice) (i j : Nat) (hi : i < s.size) (hj : j < s.size) :
    (s.swap i j hi hj)[i]'(by simpa using hi) = s[j] := by
  simp; intro h; subst h; rfl
example (s : Int64Array.Slice) : s.reverse.copy.toList = s.copy.toList.reverse := by
  simp
example (s : Int64Array.Slice) (f : Int64 → Int64) : (s.modify 0 f).size = s.size := by
  simp
example (s : Int64Array.Slice) (f : (k : USize) → k.toNat < s.size → Int64 → Nat → Int64 × Nat) :
    (s.foldlInPlace 0 f).1.size = s.size := by
  simp
example (s : Int64Array.Slice) (f : (k : USize) → k.toNat < s.size → Int64 → Nat → Int64 × Nat) :
    (s.foldrInPlace 0 f).1.size = s.size := by
  simp
example (s : Int64Array.Slice) (f : (k : USize) → k.toNat < s.size → Int64 → Nat → Int64 × Nat) :
    (s.foldrInPlaceThen 0 f fun t _ => t).size = s.size := by
  simp
example (s : Int64Array.Slice) (f : (k : USize) → k.toNat < s.size → Int64 → Nat → Int64 × Nat) :
    (s.foldlInPlace 0 f).1.array.size = s.array.size ∧
      (s.foldrInPlace 0 f).1.array.size = s.array.size := by
  simp
example (s : Int64Array.Slice) (f : (k : USize) → k.toNat < s.size → Int64 → Nat → Int64 × Nat)
    (h : 0 < s.start) : (s.foldlInPlace 0 f).1.array[0]? = s.array[0]? :=
  s.getElem?_array_foldlInPlace 0 f 0 (.inl h)
example (s : Int64Array.Slice) (f : (k : USize) → k.toNat < s.size → Int64 → Nat → Int64 × Nat) :
    (s.foldrInPlace 0 f).1.array[s.stop]? = s.array[s.stop]? :=
  s.getElem?_array_foldrInPlace 0 f _ (.inr (Nat.le_refl _))

-- Mapping each element and counting, as a pure fold.
example (s : Int64Array.Slice) :
    (s.foldlInPlace 0 fun _ _ x b => (x + 1, b + 1)).2 =
      ((List.finRange s.size).foldl (fun acc i => (acc.1 ++ [s[i] + 1], acc.2 + 1))
        ([], 0)).2 :=
  congrArg Prod.snd (s.foldlInPlace_eq_foldl_finRange _ _)
example (s : Int64Array.Slice) :
    (s.foldrInPlace 0 fun _ _ x b => (x + 1, b + 1)).1.copy.toList =
      ((List.finRange s.size).foldr (fun i acc => ((s[i] + 1) :: acc.1, acc.2 + 1))
        ([], 0)).1 :=
  congrArg Prod.fst (s.foldrInPlace_eq_foldr_finRange _ _)
example (a : Int64Array) (xs ys rs len : USize) (hx hy hr)
    (f : (j : USize) → j.toNat < len.toNat → Int64 → Int64 → Nat → Int64 × Nat) :
    (a.foldlInPlace2Then xs ys rs len hx hy hr 0 f fun a' _ _ => a').size = a.size := by
  simp
example (a : Int64Array) (start len : USize) (h : start.toNat + len.toNat ≤ a.size)
    (f : (k : USize) → k.toNat < len.toNat → Int64 → Nat → Int64 × Nat) :
    (a.foldlInPlaceRange start len h 0 f).2 =
      ((a.toSlice start.toNat (start.toNat + len.toNat)).foldlInPlace 0
        fun k hk => f k (by simp at hk; lia)).2 := by
  simp
example (a : Int64Array) (start len : USize) (h : start.toNat + len.toNat ≤ a.size)
    (f : (k : USize) → k.toNat < len.toNat → Int64 → Nat → Int64 × Nat) :
    a.foldrInPlaceRangeThen start len h 0 f (fun a' _ b => (a', b)) =
      a.foldrInPlaceRange start len h 0 f := by
  simp
example (a : Int64Array) (start len : USize) (h : start.toNat + len.toNat ≤ a.size)
    (f : (k : USize) → k.toNat < len.toNat → Int64 → Nat → Int64 × Nat) :
    (a.foldlInPlaceRange start len h 0 f).1.size = a.size ∧
      (a.foldrInPlaceRange start len h 0 f).1.size = a.size := by
  simp

/-! `grind` -/

example (a : Int64Array) (v w : Int64) : ((a.push v).push w).size = a.size + 2 := by grind
example (a : Int64Array) (i : Nat) (v : Int64) (h : i < a.size) :
    (a.set i v h)[i]'(by grind) = v := by grind
example (a b : Int64Array) (i : Nat) (h : i < a.size) :
    (a ++ b)[i]'(by grind) = a[i] := by grind
example (a : Int64Array) (v x : Int64) (h : x ∈ a) : x ∈ a.push v := by grind
example (a : Int64Array) (i : Nat) (v : Int64) (j : Nat) (h : j < a.size) (hij : i ≠ j) :
    (a.set! i v)[j]'(by grind) = a[j] := by grind
example (x : Int64) : ¬x ∈ (Int64Array.empty) := by grind
