/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import ScalarArray.Int16
import ScalarArrayTest.Util
meta import ScalarArray.Int16
meta import ScalarArrayTest.Util

open ScalarArray ScalarArrayTest

/-!
Tests for `Int16Array`: decidable equality and membership, and hashing; left out of the float
types.
-/

/-- A test value at the edge of the element type's range. -/
private abbrev big : Int16 := -32768

/-- The size of an element in bytes. -/
private abbrev elemSize : UInt32 := 2

/-! Decidable equality and hashing -/

#guard decide (Int16Array.mk #[1, 2, big] = Int16Array.mk #[1, 2, big])
#guard !decide (Int16Array.mk #[1, 2, big] = Int16Array.mk #[1, 2, 0])
#guard hash (Int16Array.mk #[1, 2, big]) == hash #[(1 : Int16), 2, big]
#guard hash (Int16Array.empty) == hash (#[] : Array Int16)
#guard hash ((Int16Array.emptyWithCapacity 100).push 1) == hash (Int16Array.mk #[1])

/-! Decidable membership and slice hashing -/

#guard (2 : Int16) ∈ Int16Array.mk #[1, 2, big]
#guard big ∈ Int16Array.mk #[1, 2, big]
#guard (3 : Int16) ∉ Int16Array.mk #[1, 2, big]
#guard (0 : Int16) ∉ Int16Array.empty
#guard big ∈ (Int16Array.mk #[0, 1, 2, big])[1...4]
#guard (0 : Int16) ∉ (Int16Array.mk #[0, 1, 2, big])[1...4]
#guard (2 : Int16) ∉ (Int16Array.mk #[0, 1, 2, big])[0...2]
#guard hash (Int16Array.mk #[0, 1, 2, big])[1...3] == hash (Int16Array.mk #[1, 2])
#guard hash (Int16Array.mk #[0, 1, 2, big])[1...3] == hash (Int16Array.mk #[big, 1, 2])[1...3]
#guard hash (∅ : Int16Array.Slice) == hash Int16Array.empty
#guard hash (Int16Array.mk #[1, 2])[1...1] == hash (∅ : Int16Array.Slice)

-- `decide` evaluates equality and membership for arrays and slices of literals.
example : Int16Array.mk #[1, 2] = Int16Array.mk #[1, 2] := by decide
example : Int16Array.mk #[1, 2] ≠ Int16Array.mk #[1, 3] := by decide
example : Int16Array.mk #[1, 2] ≠ Int16Array.mk #[1, 2, 3] := by decide
example : (2 : Int16) ∈ Int16Array.mk #[1, 2] := by decide
example : (3 : Int16) ∉ Int16Array.mk #[1, 2] := by decide
example : (2 : Int16) ∈ (Int16Array.mk #[1, 2, 3])[1...3] := by decide
example : (1 : Int16) ∉ (Int16Array.mk #[1, 2, 3])[1...3] := by decide

-- Lemmas that need decidable equality, used from another module.
example (a : Int16Array) (x : Int16) : a.contains x ↔ x ∈ a.toList := by simp
example (a : Int16Array) (x : Int16) (h : x ∈ a) :
    (if a.contains x then 1 else 0) = 1 := by simp [h]
example (s : Int16Array.Slice) (x : Int16) : s.contains x ↔ x ∈ s.copy := by simp
example (s t : Int16Array.Slice) (h : s.copy = t.copy) : s == t := by simp [h]
example (s t : Int16Array.Slice) (h : s == t) : hash s = hash t :=
  LawfulHashable.hash_eq s t h
