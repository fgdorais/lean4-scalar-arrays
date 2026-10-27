/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import ScalarArray.UInt64
import ScalarArrayTest.Util
meta import ScalarArray.UInt64
meta import ScalarArrayTest.Util

open ScalarArray ScalarArrayTest

/-!
Tests for `UInt64Array`: decidable equality and membership, and hashing; left out of the float
types.
-/

/-- A test value at the edge of the element type's range. -/
private abbrev big : UInt64 := 18446744073709551615

/-- The size of an element in bytes. -/
private abbrev elemSize : UInt32 := 8

/-! Decidable equality and hashing -/

#guard decide (UInt64Array.mk #[1, 2, big] = UInt64Array.mk #[1, 2, big])
#guard !decide (UInt64Array.mk #[1, 2, big] = UInt64Array.mk #[1, 2, 0])
#guard hash (UInt64Array.mk #[1, 2, big]) == hash #[(1 : UInt64), 2, big]
#guard hash (UInt64Array.empty) == hash (#[] : Array UInt64)
#guard hash ((UInt64Array.emptyWithCapacity 100).push 1) == hash (UInt64Array.mk #[1])

/-! Decidable membership and slice hashing -/

#guard (2 : UInt64) ∈ UInt64Array.mk #[1, 2, big]
#guard big ∈ UInt64Array.mk #[1, 2, big]
#guard (3 : UInt64) ∉ UInt64Array.mk #[1, 2, big]
#guard (0 : UInt64) ∉ UInt64Array.empty
#guard big ∈ (UInt64Array.mk #[0, 1, 2, big])[1...4]
#guard (0 : UInt64) ∉ (UInt64Array.mk #[0, 1, 2, big])[1...4]
#guard (2 : UInt64) ∉ (UInt64Array.mk #[0, 1, 2, big])[0...2]
#guard hash (UInt64Array.mk #[0, 1, 2, big])[1...3] == hash (UInt64Array.mk #[1, 2])
#guard hash (UInt64Array.mk #[0, 1, 2, big])[1...3] == hash (UInt64Array.mk #[big, 1, 2])[1...3]
#guard hash (∅ : UInt64Array.Slice) == hash UInt64Array.empty
#guard hash (UInt64Array.mk #[1, 2])[1...1] == hash (∅ : UInt64Array.Slice)

-- `decide` evaluates equality and membership for arrays and slices of literals.
example : UInt64Array.mk #[1, 2] = UInt64Array.mk #[1, 2] := by decide
example : UInt64Array.mk #[1, 2] ≠ UInt64Array.mk #[1, 3] := by decide
example : UInt64Array.mk #[1, 2] ≠ UInt64Array.mk #[1, 2, 3] := by decide
example : (2 : UInt64) ∈ UInt64Array.mk #[1, 2] := by decide
example : (3 : UInt64) ∉ UInt64Array.mk #[1, 2] := by decide
example : (2 : UInt64) ∈ (UInt64Array.mk #[1, 2, 3])[1...3] := by decide
example : (1 : UInt64) ∉ (UInt64Array.mk #[1, 2, 3])[1...3] := by decide

-- Lemmas that need decidable equality, used from another module.
example (a : UInt64Array) (x : UInt64) : a.contains x ↔ x ∈ a.toList := by simp
example (a : UInt64Array) (x : UInt64) (h : x ∈ a) :
    (if a.contains x then 1 else 0) = 1 := by simp [h]
example (s : UInt64Array.Slice) (x : UInt64) : s.contains x ↔ x ∈ s.copy := by simp
example (s t : UInt64Array.Slice) (h : s.copy = t.copy) : s == t := by simp [h]
example (s t : UInt64Array.Slice) (h : s == t) : hash s = hash t :=
  LawfulHashable.hash_eq s t h
