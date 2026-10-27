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
Tests for `Int64Array`: decidable equality and membership, and hashing; left out of the float
types.
-/

/-- A test value at the edge of the element type's range. -/
private abbrev big : Int64 := -9223372036854775808

/-- The size of an element in bytes. -/
private abbrev elemSize : UInt32 := 8

/-! Decidable equality and hashing -/

#guard decide (Int64Array.mk #[1, 2, big] = Int64Array.mk #[1, 2, big])
#guard !decide (Int64Array.mk #[1, 2, big] = Int64Array.mk #[1, 2, 0])
#guard hash (Int64Array.mk #[1, 2, big]) == hash #[(1 : Int64), 2, big]
#guard hash (Int64Array.empty) == hash (#[] : Array Int64)
#guard hash ((Int64Array.emptyWithCapacity 100).push 1) == hash (Int64Array.mk #[1])

/-! Decidable membership and slice hashing -/

#guard (2 : Int64) ∈ Int64Array.mk #[1, 2, big]
#guard big ∈ Int64Array.mk #[1, 2, big]
#guard (3 : Int64) ∉ Int64Array.mk #[1, 2, big]
#guard (0 : Int64) ∉ Int64Array.empty
#guard big ∈ (Int64Array.mk #[0, 1, 2, big])[1...4]
#guard (0 : Int64) ∉ (Int64Array.mk #[0, 1, 2, big])[1...4]
#guard (2 : Int64) ∉ (Int64Array.mk #[0, 1, 2, big])[0...2]
#guard hash (Int64Array.mk #[0, 1, 2, big])[1...3] == hash (Int64Array.mk #[1, 2])
#guard hash (Int64Array.mk #[0, 1, 2, big])[1...3] == hash (Int64Array.mk #[big, 1, 2])[1...3]
#guard hash (∅ : Int64Array.Slice) == hash Int64Array.empty
#guard hash (Int64Array.mk #[1, 2])[1...1] == hash (∅ : Int64Array.Slice)

-- `decide` evaluates equality and membership for arrays and slices of literals.
example : Int64Array.mk #[1, 2] = Int64Array.mk #[1, 2] := by decide
example : Int64Array.mk #[1, 2] ≠ Int64Array.mk #[1, 3] := by decide
example : Int64Array.mk #[1, 2] ≠ Int64Array.mk #[1, 2, 3] := by decide
example : (2 : Int64) ∈ Int64Array.mk #[1, 2] := by decide
example : (3 : Int64) ∉ Int64Array.mk #[1, 2] := by decide
example : (2 : Int64) ∈ (Int64Array.mk #[1, 2, 3])[1...3] := by decide
example : (1 : Int64) ∉ (Int64Array.mk #[1, 2, 3])[1...3] := by decide

-- Lemmas that need decidable equality, used from another module.
example (a : Int64Array) (x : Int64) : a.contains x ↔ x ∈ a.toList := by simp
example (a : Int64Array) (x : Int64) (h : x ∈ a) :
    (if a.contains x then 1 else 0) = 1 := by simp [h]
example (s : Int64Array.Slice) (x : Int64) : s.contains x ↔ x ∈ s.copy := by simp
example (s t : Int64Array.Slice) (h : s.copy = t.copy) : s == t := by simp [h]
example (s t : Int64Array.Slice) (h : s == t) : hash s = hash t :=
  LawfulHashable.hash_eq s t h
