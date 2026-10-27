/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import ScalarArray.UInt32
import ScalarArrayTest.Util
meta import ScalarArray.UInt32
meta import ScalarArrayTest.Util

open ScalarArray ScalarArrayTest

/-!
Tests for `UInt32Array`: decidable equality and membership, and hashing; left out of the float
types.
-/

/-- A test value at the edge of the element type's range. -/
private abbrev big : UInt32 := 4294967295

/-- The size of an element in bytes. -/
private abbrev elemSize : UInt32 := 4

/-! Decidable equality and hashing -/

#guard decide (UInt32Array.mk #[1, 2, big] = UInt32Array.mk #[1, 2, big])
#guard !decide (UInt32Array.mk #[1, 2, big] = UInt32Array.mk #[1, 2, 0])
#guard hash (UInt32Array.mk #[1, 2, big]) == hash #[(1 : UInt32), 2, big]
#guard hash (UInt32Array.empty) == hash (#[] : Array UInt32)
#guard hash ((UInt32Array.emptyWithCapacity 100).push 1) == hash (UInt32Array.mk #[1])

/-! Decidable membership and slice hashing -/

#guard (2 : UInt32) ∈ UInt32Array.mk #[1, 2, big]
#guard big ∈ UInt32Array.mk #[1, 2, big]
#guard (3 : UInt32) ∉ UInt32Array.mk #[1, 2, big]
#guard (0 : UInt32) ∉ UInt32Array.empty
#guard big ∈ (UInt32Array.mk #[0, 1, 2, big])[1...4]
#guard (0 : UInt32) ∉ (UInt32Array.mk #[0, 1, 2, big])[1...4]
#guard (2 : UInt32) ∉ (UInt32Array.mk #[0, 1, 2, big])[0...2]
#guard hash (UInt32Array.mk #[0, 1, 2, big])[1...3] == hash (UInt32Array.mk #[1, 2])
#guard hash (UInt32Array.mk #[0, 1, 2, big])[1...3] == hash (UInt32Array.mk #[big, 1, 2])[1...3]
#guard hash (∅ : UInt32Array.Slice) == hash UInt32Array.empty
#guard hash (UInt32Array.mk #[1, 2])[1...1] == hash (∅ : UInt32Array.Slice)

-- `decide` evaluates equality and membership for arrays and slices of literals.
example : UInt32Array.mk #[1, 2] = UInt32Array.mk #[1, 2] := by decide
example : UInt32Array.mk #[1, 2] ≠ UInt32Array.mk #[1, 3] := by decide
example : UInt32Array.mk #[1, 2] ≠ UInt32Array.mk #[1, 2, 3] := by decide
example : (2 : UInt32) ∈ UInt32Array.mk #[1, 2] := by decide
example : (3 : UInt32) ∉ UInt32Array.mk #[1, 2] := by decide
example : (2 : UInt32) ∈ (UInt32Array.mk #[1, 2, 3])[1...3] := by decide
example : (1 : UInt32) ∉ (UInt32Array.mk #[1, 2, 3])[1...3] := by decide

-- Lemmas that need decidable equality, used from another module.
example (a : UInt32Array) (x : UInt32) : a.contains x ↔ x ∈ a.toList := by simp
example (a : UInt32Array) (x : UInt32) (h : x ∈ a) :
    (if a.contains x then 1 else 0) = 1 := by simp [h]
example (s : UInt32Array.Slice) (x : UInt32) : s.contains x ↔ x ∈ s.copy := by simp
example (s t : UInt32Array.Slice) (h : s.copy = t.copy) : s == t := by simp [h]
example (s t : UInt32Array.Slice) (h : s == t) : hash s = hash t :=
  LawfulHashable.hash_eq s t h
