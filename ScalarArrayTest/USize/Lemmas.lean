/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import ScalarArray.USize
import ScalarArrayTest.Util
meta import ScalarArray.USize
meta import ScalarArrayTest.Util

open ScalarArray ScalarArrayTest

/-!
Tests for `USizeArray`: lemmas, used from another module.
-/

/-- A test value at the edge of the element type's range. -/
private abbrev big : USize := 18446744073709551615

/-- The size of an element in bytes. -/
private abbrev elemSize : UInt32 := (System.Platform.numBits / 8).toUInt32

/-! Lemmas -/

example (a : USizeArray) (v : USize) : (a.push v).pop = a := by simp [USizeArray.ext_iff]
example : (USizeArray.replicate 3 big)[1] = big := by simp
example (a b : USizeArray) (h : 0 < a.size) : (a ++ b)[0]'(by simp; lia) = a[0] := by simp [h]
example (a : USizeArray) (i : Nat) (v : USize) (h : i < a.size) :
    (a.set i v h)[i]'(by simpa) = v := by simp
example (a : USizeArray) : a.extract 0 a.size = a := by simp
example (a : USizeArray) (v : USize) : (a.push v).pop = a :=
  USizeArray.ext_getElem (by simp) (by simp_all)
example (a : USizeArray) (v : USize) : (a.push v).pop = a :=
  USizeArray.ext_getElem? fun i => by
    by_cases h : i < a.size <;> simp [h, getElem?_pos, getElem?_neg]
example (a b : USizeArray) (h : a.toArray = b.toArray) : a = b := by simpa using h

/-! Lists -/

#guard (USizeArray.ofList [1, 2, big]).toArray == #[1, 2, big]
#guard (USizeArray.ofList []).toArray == #[]
#guard [1, 2, big].toUSizeArray == USizeArray.mk #[1, 2, big]
#guard (USizeArray.ofList ((List.range 100000).map Nat.toUSize)).toArray ==
  (Array.range 100000).map Nat.toUSize
#guard rawElemSize (USizeArray.ofList [1, 2]) == elemSize

/-! More lemmas -/

example (a b c : USizeArray) : a ++ b ++ c = a ++ (b ++ c) := USizeArray.append_assoc ..
example (a : USizeArray) : a ++ ∅ = a := by simp
example (a b : USizeArray) : (a ++ b).extract 0 a.size = a := by simp
example (a : USizeArray) (i : Nat) (v : USize) : (a.set! i v).size = a.size := by simp
example (l : List USize) : (USizeArray.ofList l).toList = l := by simp
example (a : USizeArray) : USizeArray.ofList a.toList = a := by simp

/-! Lemmas from another module -/

example (a : USizeArray) (i : USize) (v : USize) (h) (j : Nat) (hj) :
    (a.uset i v h)[j]'hj = if i.toNat = j then v else a[j]'(by simpa using hj) := by
  simp
example (a : USizeArray) (v : USize) :
    (a.set! 0 v)[0]? = if 0 < a.size then some v else none := by
  simp
example (a : USizeArray) (v : USize) (h : 1 < (a.set! 0 v).size) :
    (a.set! 0 v)[1] = a[1]'(by simpa using h) := by
  simp
example (a : USizeArray) (p : USize → Bool) : (a.popWhile p).size ≤ a.size :=
  USizeArray.size_popWhile_le p a
example (src dest : USizeArray) :
    (src.copySlice 0 dest 0 src.size).size = max dest.size src.size := by
  simp
example (a : USizeArray) (f : Nat → USize → Option Nat) :
    a.toList.foldlM f 0 = a.foldlM f 0 := by
  simp
example (a : USizeArray) (f : USize → Nat → Option Nat) :
    a.toList.foldrM f 0 = a.foldrM f 0 := by
  simp
example (a : USizeArray) (f : USize → StateM Nat PUnit) : forM a.toList f = forM a f := by
  simp
example (a b : USizeArray) (x : USize) (h : x ∈ a) : x ∈ (a ++ b).toList := by
  simp [h]
example (a : USizeArray) (x : USize) : x ∈ a.push x := by
  simp
example (a : USizeArray) (i : Nat) (h : i < a.size) : a[i] ∈ a.toList := by
  simpa using USizeArray.getElem_mem h
example (a : USizeArray) (start stop : Nat) (p : USize → Bool) :
    (a.toSlice start stop).any p = (a.extract start stop).any p := by
  simp
example (a : USizeArray) (start stop : Nat) :
    (a.toSlice start stop).toList = (a.toList.extract start stop) := by
  simp
example (s : USizeArray.Slice) (p : USize → Bool) : s.count p = s.copy.toList.countP p := by
  simp
example (s : USizeArray.Slice) (p : USize → Bool) :
    s.find? p = s.copy.toList.find? p ∧ s.findRev? p = s.copy.toList.reverse.find? p := by
  simp
example (s : USizeArray.Slice) (f : Nat → USize → Nat) :
    s.foldl f 0 = s.copy.toList.foldl f 0 := by
  simp
example (s : USizeArray.Slice) (f : USize → StateM Nat PUnit) :
    forM s f = forM s.copy.toList f := by
  simp
example (s : USizeArray.Slice) (x : USize) : x ∈ s ↔ x ∈ s.copy.toList := by
  simp
example (s t : USizeArray.Slice) : (s == t) = (s.copy == t.copy) := by
  simp
example (a : USizeArray) : a.iter.toUSizeArray = a := by
  simp
example (s : USizeArray.Slice) : s.iter.toUSizeArray = s.copy := by
  simp
example : (∅ : USizeArray.Slice).size = 0 := by
  simp
example (s : USizeArray.Slice) (i : Nat) (v : USize) (h : i < s.size) :
    (s.set i v h).copy = s.copy.set i v (by simpa using h) := by
  simp
example (s : USizeArray.Slice) (i j : Nat) (hi : i < s.size) (hj : j < s.size) :
    (s.swap i j hi hj)[i]'(by simpa using hi) = s[j] := by
  simp; intro h; subst h; rfl
example (s : USizeArray.Slice) : s.reverse.copy.toList = s.copy.toList.reverse := by
  simp
example (s : USizeArray.Slice) (f : USize → USize) : (s.modify 0 f).size = s.size := by
  simp
example (s : USizeArray.Slice) (f : (k : USize) → k.toNat < s.size → USize → Nat → USize × Nat) :
    (s.foldlInPlace 0 f).1.size = s.size := by
  simp
example (s : USizeArray.Slice) (f : (k : USize) → k.toNat < s.size → USize → Nat → USize × Nat) :
    (s.foldrInPlace 0 f).1.size = s.size := by
  simp
example (s : USizeArray.Slice) (f : (k : USize) → k.toNat < s.size → USize → Nat → USize × Nat) :
    (s.foldrInPlaceThen 0 f fun t _ => t).size = s.size := by
  simp
example (s : USizeArray.Slice) (f : (k : USize) → k.toNat < s.size → USize → Nat → USize × Nat) :
    (s.foldlInPlace 0 f).1.array.size = s.array.size ∧
      (s.foldrInPlace 0 f).1.array.size = s.array.size := by
  simp
example (s : USizeArray.Slice) (f : (k : USize) → k.toNat < s.size → USize → Nat → USize × Nat)
    (h : 0 < s.start) : (s.foldlInPlace 0 f).1.array[0]? = s.array[0]? :=
  s.getElem?_array_foldlInPlace 0 f 0 (.inl h)
example (s : USizeArray.Slice) (f : (k : USize) → k.toNat < s.size → USize → Nat → USize × Nat) :
    (s.foldrInPlace 0 f).1.array[s.stop]? = s.array[s.stop]? :=
  s.getElem?_array_foldrInPlace 0 f _ (.inr (Nat.le_refl _))

-- Mapping each element and counting, as a pure fold.
example (s : USizeArray.Slice) :
    (s.foldlInPlace 0 fun _ _ x b => (x + 1, b + 1)).2 =
      ((List.finRange s.size).foldl (fun acc i => (acc.1 ++ [s[i] + 1], acc.2 + 1))
        ([], 0)).2 :=
  congrArg Prod.snd (s.foldlInPlace_eq_foldl_finRange _ _)
example (s : USizeArray.Slice) :
    (s.foldrInPlace 0 fun _ _ x b => (x + 1, b + 1)).1.copy.toList =
      ((List.finRange s.size).foldr (fun i acc => ((s[i] + 1) :: acc.1, acc.2 + 1))
        ([], 0)).1 :=
  congrArg Prod.fst (s.foldrInPlace_eq_foldr_finRange _ _)
example (a : USizeArray) (xs ys rs len : USize) (hx hy hr)
    (f : (j : USize) → j.toNat < len.toNat → USize → USize → Nat → USize × Nat) :
    (a.foldlInPlace2Then xs ys rs len hx hy hr 0 f fun a' _ _ => a').size = a.size := by
  simp
example (a : USizeArray) (start len : USize) (h : start.toNat + len.toNat ≤ a.size)
    (f : (k : USize) → k.toNat < len.toNat → USize → Nat → USize × Nat) :
    (a.foldlInPlaceRange start len h 0 f).2 =
      ((a.toSlice start.toNat (start.toNat + len.toNat)).foldlInPlace 0
        fun k hk => f k (by simp at hk; lia)).2 := by
  simp
example (a : USizeArray) (start len : USize) (h : start.toNat + len.toNat ≤ a.size)
    (f : (k : USize) → k.toNat < len.toNat → USize → Nat → USize × Nat) :
    a.foldrInPlaceRangeThen start len h 0 f (fun a' _ b => (a', b)) =
      a.foldrInPlaceRange start len h 0 f := by
  simp
example (a : USizeArray) (start len : USize) (h : start.toNat + len.toNat ≤ a.size)
    (f : (k : USize) → k.toNat < len.toNat → USize → Nat → USize × Nat) :
    (a.foldlInPlaceRange start len h 0 f).1.size = a.size ∧
      (a.foldrInPlaceRange start len h 0 f).1.size = a.size := by
  simp

/-! `grind` -/

example (a : USizeArray) (v w : USize) : ((a.push v).push w).size = a.size + 2 := by grind
example (a : USizeArray) (i : Nat) (v : USize) (h : i < a.size) :
    (a.set i v h)[i]'(by grind) = v := by grind
example (a b : USizeArray) (i : Nat) (h : i < a.size) :
    (a ++ b)[i]'(by grind) = a[i] := by grind
example (a : USizeArray) (v x : USize) (h : x ∈ a) : x ∈ a.push v := by grind
example (a : USizeArray) (i : Nat) (v : USize) (j : Nat) (h : j < a.size) (hij : i ≠ j) :
    (a.set! i v)[j]'(by grind) = a[j] := by grind
example (x : USize) : ¬x ∈ (USizeArray.empty) := by grind
