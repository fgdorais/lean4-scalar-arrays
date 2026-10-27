/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import ScalarArray.Int32
import ScalarArrayTest.Util
meta import ScalarArray.Int32
meta import ScalarArrayTest.Util

open ScalarArray ScalarArrayTest

/-!
Tests for `Int32Array`: decidable equality and membership, and hashing; left out of the float
types.
-/

/-- A test value at the edge of the element type's range. -/
private abbrev big : Int32 := -2147483648

/-- The size of an element in bytes. -/
private abbrev elemSize : UInt32 := 4

/-! Decidable equality and hashing -/

#guard decide (Int32Array.mk #[1, 2, big] = Int32Array.mk #[1, 2, big])
#guard !decide (Int32Array.mk #[1, 2, big] = Int32Array.mk #[1, 2, 0])
#guard hash (Int32Array.mk #[1, 2, big]) == hash #[(1 : Int32), 2, big]
#guard hash (Int32Array.empty) == hash (#[] : Array Int32)
#guard hash ((Int32Array.emptyWithCapacity 100).push 1) == hash (Int32Array.mk #[1])

/-! Decidable membership and slice hashing -/

#guard (2 : Int32) ∈ Int32Array.mk #[1, 2, big]
#guard big ∈ Int32Array.mk #[1, 2, big]
#guard (3 : Int32) ∉ Int32Array.mk #[1, 2, big]
#guard (0 : Int32) ∉ Int32Array.empty
#guard big ∈ (Int32Array.mk #[0, 1, 2, big])[1...4]
#guard (0 : Int32) ∉ (Int32Array.mk #[0, 1, 2, big])[1...4]
#guard (2 : Int32) ∉ (Int32Array.mk #[0, 1, 2, big])[0...2]
#guard hash (Int32Array.mk #[0, 1, 2, big])[1...3] == hash (Int32Array.mk #[1, 2])
#guard hash (Int32Array.mk #[0, 1, 2, big])[1...3] == hash (Int32Array.mk #[big, 1, 2])[1...3]
#guard hash (∅ : Int32Array.Slice) == hash Int32Array.empty
#guard hash (Int32Array.mk #[1, 2])[1...1] == hash (∅ : Int32Array.Slice)

-- `decide` evaluates equality and membership for arrays and slices of literals.
example : Int32Array.mk #[1, 2] = Int32Array.mk #[1, 2] := by decide
example : Int32Array.mk #[1, 2] ≠ Int32Array.mk #[1, 3] := by decide
example : Int32Array.mk #[1, 2] ≠ Int32Array.mk #[1, 2, 3] := by decide
example : (2 : Int32) ∈ Int32Array.mk #[1, 2] := by decide
example : (3 : Int32) ∉ Int32Array.mk #[1, 2] := by decide
example : (2 : Int32) ∈ (Int32Array.mk #[1, 2, 3])[1...3] := by decide
example : (1 : Int32) ∉ (Int32Array.mk #[1, 2, 3])[1...3] := by decide

-- Lemmas that need decidable equality, used from another module.
example (a : Int32Array) (x : Int32) : a.contains x ↔ x ∈ a.toList := by simp
example (a : Int32Array) (x : Int32) (h : x ∈ a) :
    (if a.contains x then 1 else 0) = 1 := by simp [h]
example (s : Int32Array.Slice) (x : Int32) : s.contains x ↔ x ∈ s.copy := by simp
example (s t : Int32Array.Slice) (h : s.copy = t.copy) : s == t := by simp [h]
example (s t : Int32Array.Slice) (h : s == t) : hash s = hash t :=
  LawfulHashable.hash_eq s t h
