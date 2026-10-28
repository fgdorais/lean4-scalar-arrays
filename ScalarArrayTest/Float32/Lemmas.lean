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
Tests for `Float32Array`: lemmas, used from another module.
-/

/-- A test value at the edge of the element type's range. -/
private abbrev big : Float32 := -1.5e38

/-- The size of an element in bytes. -/
private abbrev elemSize : UInt32 := 4

/-! Lemmas -/

example (a : Float32Array) (v : Float32) : (a.push v).pop = a := by simp [Float32Array.ext_iff]
example : (Float32Array.replicate 3 big)[1] = big := by simp
example (a b : Float32Array) (h : 0 < a.size) : (a ++ b)[0]'(by simp; lia) = a[0] := by simp [h]
example (a : Float32Array) (i : Nat) (v : Float32) (h : i < a.size) :
    (a.set i v h)[i]'(by simpa) = v := by simp
example (a : Float32Array) : a.extract 0 a.size = a := by simp
example (a : Float32Array) (v : Float32) : (a.push v).pop = a :=
  Float32Array.ext_getElem (by simp) (by simp_all)
example (a : Float32Array) (v : Float32) : (a.push v).pop = a :=
  Float32Array.ext_getElem? fun i => by
    by_cases h : i < a.size <;> simp [h, getElem?_pos, getElem?_neg]
example (a b : Float32Array) (h : a.toArray = b.toArray) : a = b := by simpa using h

/-! Lists -/

#guard (Float32Array.ofList [1, 2, big]).toArray == #[1, 2, big]
#guard (Float32Array.ofList []).toArray == #[]
#guard [1, 2, big].toFloat32Array == Float32Array.mk #[1, 2, big]
#guard (Float32Array.ofList ((List.range 100000).map Nat.toFloat32)).toArray ==
  (Array.range 100000).map Nat.toFloat32
#guard rawElemSize (Float32Array.ofList [1, 2]) == elemSize

/-! More lemmas -/

example (a b c : Float32Array) : a ++ b ++ c = a ++ (b ++ c) := Float32Array.append_assoc ..
example (a : Float32Array) : a ++ ∅ = a := by simp
example (a b : Float32Array) : (a ++ b).extract 0 a.size = a := by simp
example (a : Float32Array) (i : Nat) (v : Float32) : (a.set! i v).size = a.size := by simp
example (l : List Float32) : (Float32Array.ofList l).toList = l := by simp
example (a : Float32Array) : Float32Array.ofList a.toList = a := by simp

/-! Lemmas from another module -/

example (a : Float32Array) (i : USize) (v : Float32) (h) (j : Nat) (hj) :
    (a.uset i v h)[j]'hj = if i.toNat = j then v else a[j]'(by simpa using hj) := by
  simp
example (a : Float32Array) (v : Float32) :
    (a.set! 0 v)[0]? = if 0 < a.size then some v else none := by
  simp
example (a : Float32Array) (v : Float32) (h : 1 < (a.set! 0 v).size) :
    (a.set! 0 v)[1] = a[1]'(by simpa using h) := by
  simp
example (a : Float32Array) (p : Float32 → Bool) : (a.popWhile p).size ≤ a.size :=
  Float32Array.size_popWhile_le p a
example (src dest : Float32Array) :
    (src.copySlice 0 dest 0 src.size).size = max dest.size src.size := by
  simp
example (a : Float32Array) (f : Nat → Float32 → Option Nat) :
    a.toList.foldlM f 0 = a.foldlM f 0 := by
  simp
example (a : Float32Array) (f : Float32 → Nat → Option Nat) :
    a.toList.foldrM f 0 = a.foldrM f 0 := by
  simp
example (a : Float32Array) (f : Float32 → StateM Nat PUnit) : forM a.toList f = forM a f := by
  simp
example (a b : Float32Array) (x : Float32) (h : x ∈ a) : x ∈ (a ++ b).toList := by
  simp [h]
example (a : Float32Array) (x : Float32) : x ∈ a.push x := by
  simp
example (a : Float32Array) (i : Nat) (h : i < a.size) : a[i] ∈ a.toList := by
  simpa using Float32Array.getElem_mem h
example (a : Float32Array) (start stop : Nat) (p : Float32 → Bool) :
    (a.toSlice start stop).any p = (a.extract start stop).any p := by
  simp
example (a : Float32Array) (start stop : Nat) :
    (a.toSlice start stop).toList = (a.toList.extract start stop) := by
  simp
example (s : Float32Array.Slice) (p : Float32 → Bool) : s.count p = s.copy.toList.countP p := by
  simp
example (s : Float32Array.Slice) (p : Float32 → Bool) :
    s.find? p = s.copy.toList.find? p ∧ s.findRev? p = s.copy.toList.reverse.find? p := by
  simp
example (s : Float32Array.Slice) (f : Nat → Float32 → Nat) :
    s.foldl f 0 = s.copy.toList.foldl f 0 := by
  simp
example (s : Float32Array.Slice) (f : Float32 → StateM Nat PUnit) :
    forM s f = forM s.copy.toList f := by
  simp
example (s : Float32Array.Slice) (x : Float32) : x ∈ s ↔ x ∈ s.copy.toList := by
  simp
example (s t : Float32Array.Slice) : (s == t) = (s.copy == t.copy) := by
  simp
example (a : Float32Array) : a.iter.toFloat32Array = a := by
  simp
example (s : Float32Array.Slice) : s.iter.toFloat32Array = s.copy := by
  simp
example : (∅ : Float32Array.Slice).size = 0 := by
  simp
example (s : Float32Array.Slice) (i : Nat) (v : Float32) (h : i < s.size) :
    (s.set i v h).copy = s.copy.set i v (by simpa using h) := by
  simp
example (s : Float32Array.Slice) (i j : Nat) (hi : i < s.size) (hj : j < s.size) :
    (s.swap i j hi hj)[i]'(by simpa using hi) = s[j] := by
  simp; intro h; subst h; rfl
example (s : Float32Array.Slice) : s.reverse.copy.toList = s.copy.toList.reverse := by
  simp
example (s : Float32Array.Slice) (f : Float32 → Float32) : (s.modify 0 f).size = s.size := by
  simp
example (s : Float32Array.Slice) (f : (k : USize) → k.toNat < s.size → Float32 → Nat → Float32 × Nat) :
    (s.foldlInPlace 0 f).1.size = s.size := by
  simp
example (s : Float32Array.Slice) (f : (k : USize) → k.toNat < s.size → Float32 → Nat → Float32 × Nat) :
    (s.foldrInPlace 0 f).1.size = s.size := by
  simp
example (s : Float32Array.Slice) (f : (k : USize) → k.toNat < s.size → Float32 → Nat → Float32 × Nat) :
    (s.foldrInPlaceThen 0 f fun t _ => t).size = s.size := by
  simp
example (s : Float32Array.Slice) (f : (k : USize) → k.toNat < s.size → Float32 → Nat → Float32 × Nat) :
    (s.foldlInPlace 0 f).1.array.size = s.array.size ∧
      (s.foldrInPlace 0 f).1.array.size = s.array.size := by
  simp
example (s : Float32Array.Slice) (f : (k : USize) → k.toNat < s.size → Float32 → Nat → Float32 × Nat)
    (h : 0 < s.start) : (s.foldlInPlace 0 f).1.array[0]? = s.array[0]? :=
  s.getElem?_array_foldlInPlace 0 f 0 (.inl h)
example (s : Float32Array.Slice) (f : (k : USize) → k.toNat < s.size → Float32 → Nat → Float32 × Nat) :
    (s.foldrInPlace 0 f).1.array[s.stop]? = s.array[s.stop]? :=
  s.getElem?_array_foldrInPlace 0 f _ (.inr (Nat.le_refl _))

-- Mapping each element and counting, as a pure fold.
example (s : Float32Array.Slice) :
    (s.foldlInPlace 0 fun _ _ x b => (x + 1, b + 1)).2 =
      ((List.finRange s.size).foldl (fun acc i => (acc.1 ++ [s[i] + 1], acc.2 + 1))
        ([], 0)).2 :=
  congrArg Prod.snd (s.foldlInPlace_eq_foldl_finRange _ _)
example (s : Float32Array.Slice) :
    (s.foldrInPlace 0 fun _ _ x b => (x + 1, b + 1)).1.copy.toList =
      ((List.finRange s.size).foldr (fun i acc => ((s[i] + 1) :: acc.1, acc.2 + 1))
        ([], 0)).1 :=
  congrArg Prod.fst (s.foldrInPlace_eq_foldr_finRange _ _)
example (a : Float32Array) (xs ys rs len : USize) (hx hy hr)
    (f : (j : USize) → j.toNat < len.toNat → Float32 → Float32 → Nat → Float32 × Nat) :
    (a.foldlInPlace2Then xs ys rs len hx hy hr 0 f fun a' _ _ => a').size = a.size := by
  simp
example (a : Float32Array) (start len : USize) (h : start.toNat + len.toNat ≤ a.size)
    (f : (k : USize) → k.toNat < len.toNat → Float32 → Nat → Float32 × Nat) :
    (a.foldlInPlaceRange start len h 0 f).2 =
      ((a.toSlice start.toNat (start.toNat + len.toNat)).foldlInPlace 0
        fun k hk => f k (by simp at hk; lia)).2 := by
  simp
example (a : Float32Array) (start len : USize) (h : start.toNat + len.toNat ≤ a.size)
    (f : (k : USize) → k.toNat < len.toNat → Float32 → Nat → Float32 × Nat) :
    a.foldrInPlaceRangeThen start len h 0 f (fun a' _ b => (a', b)) =
      a.foldrInPlaceRange start len h 0 f := by
  simp
example (a : Float32Array) (start len : USize) (h : start.toNat + len.toNat ≤ a.size)
    (f : (k : USize) → k.toNat < len.toNat → Float32 → Nat → Float32 × Nat) :
    (a.foldlInPlaceRange start len h 0 f).1.size = a.size ∧
      (a.foldrInPlaceRange start len h 0 f).1.size = a.size := by
  simp

/-! `grind` -/

example (a : Float32Array) (v w : Float32) : ((a.push v).push w).size = a.size + 2 := by grind
example (a : Float32Array) (i : Nat) (v : Float32) (h : i < a.size) :
    (a.set i v h)[i]'(by grind) = v := by grind
example (a b : Float32Array) (i : Nat) (h : i < a.size) :
    (a ++ b)[i]'(by grind) = a[i] := by grind
example (a : Float32Array) (v x : Float32) (h : x ∈ a) : x ∈ a.push v := by grind
example (a : Float32Array) (i : Nat) (v : Float32) (j : Nat) (h : j < a.size) (hij : i ≠ j) :
    (a.set! i v)[j]'(by grind) = a[j] := by grind
example (x : Float32) : ¬x ∈ (Float32Array.empty) := by grind
