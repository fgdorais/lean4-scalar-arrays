/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import ScalarArray.UInt16
import ScalarArrayTest.Util
meta import ScalarArray.UInt16
meta import ScalarArrayTest.Util

open ScalarArray ScalarArrayTest

/-!
Tests for `UInt16Array`: decidable equality and membership, and hashing; left out of the float
types.
-/

/-- A test value at the edge of the element type's range. -/
private abbrev big : UInt16 := 65535

/-- The size of an element in bytes. -/
private abbrev elemSize : UInt32 := 2

/-! Decidable equality and hashing -/

#guard decide (UInt16Array.mk #[1, 2, big] = UInt16Array.mk #[1, 2, big])
#guard !decide (UInt16Array.mk #[1, 2, big] = UInt16Array.mk #[1, 2, 0])
#guard hash (UInt16Array.mk #[1, 2, big]) == hash #[(1 : UInt16), 2, big]
#guard hash (UInt16Array.empty) == hash (#[] : Array UInt16)
#guard hash ((UInt16Array.emptyWithCapacity 100).push 1) == hash (UInt16Array.mk #[1])

/-! Decidable membership and slice hashing -/

#guard (2 : UInt16) ∈ UInt16Array.mk #[1, 2, big]
#guard big ∈ UInt16Array.mk #[1, 2, big]
#guard (3 : UInt16) ∉ UInt16Array.mk #[1, 2, big]
#guard (0 : UInt16) ∉ UInt16Array.empty
#guard big ∈ (UInt16Array.mk #[0, 1, 2, big])[1...4]
#guard (0 : UInt16) ∉ (UInt16Array.mk #[0, 1, 2, big])[1...4]
#guard (2 : UInt16) ∉ (UInt16Array.mk #[0, 1, 2, big])[0...2]
#guard hash (UInt16Array.mk #[0, 1, 2, big])[1...3] == hash (UInt16Array.mk #[1, 2])
#guard hash (UInt16Array.mk #[0, 1, 2, big])[1...3] == hash (UInt16Array.mk #[big, 1, 2])[1...3]
#guard hash (∅ : UInt16Array.Slice) == hash UInt16Array.empty
#guard hash (UInt16Array.mk #[1, 2])[1...1] == hash (∅ : UInt16Array.Slice)

-- `decide` evaluates equality and membership for arrays and slices of literals.
example : UInt16Array.mk #[1, 2] = UInt16Array.mk #[1, 2] := by decide
example : UInt16Array.mk #[1, 2] ≠ UInt16Array.mk #[1, 3] := by decide
example : UInt16Array.mk #[1, 2] ≠ UInt16Array.mk #[1, 2, 3] := by decide
example : (2 : UInt16) ∈ UInt16Array.mk #[1, 2] := by decide
example : (3 : UInt16) ∉ UInt16Array.mk #[1, 2] := by decide
example : (2 : UInt16) ∈ (UInt16Array.mk #[1, 2, 3])[1...3] := by decide
example : (1 : UInt16) ∉ (UInt16Array.mk #[1, 2, 3])[1...3] := by decide

-- Lemmas that need decidable equality, used from another module.
example (a : UInt16Array) (x : UInt16) : a.contains x ↔ x ∈ a.toList := by simp
example (a : UInt16Array) (x : UInt16) (h : x ∈ a) :
    (if a.contains x then 1 else 0) = 1 := by simp [h]
example (s : UInt16Array.Slice) (x : UInt16) : s.contains x ↔ x ∈ s.copy := by simp
example (s t : UInt16Array.Slice) (h : s.copy = t.copy) : s == t := by simp [h]
example (s t : UInt16Array.Slice) (h : s == t) : hash s = hash t :=
  LawfulHashable.hash_eq s t h
