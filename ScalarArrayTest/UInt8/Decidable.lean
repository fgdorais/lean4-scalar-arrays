/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import ScalarArray.UInt8
import ScalarArrayTest.Util
meta import ScalarArray.UInt8
meta import ScalarArrayTest.Util

open ScalarArray ScalarArrayTest

/-!
Tests for `UInt8Array`: decidable equality and membership, and hashing; left out of the float
types.
-/

/-- A test value at the edge of the element type's range. -/
private abbrev big : UInt8 := 255

/-- The size of an element in bytes. -/
private abbrev elemSize : UInt32 := 1

/-! Decidable equality and hashing -/

#guard decide (UInt8Array.mk #[1, 2, big] = UInt8Array.mk #[1, 2, big])
#guard !decide (UInt8Array.mk #[1, 2, big] = UInt8Array.mk #[1, 2, 0])
#guard hash (UInt8Array.mk #[1, 2, big]) == hash #[(1 : UInt8), 2, big]
#guard hash (UInt8Array.empty) == hash (#[] : Array UInt8)
#guard hash ((UInt8Array.emptyWithCapacity 100).push 1) == hash (UInt8Array.mk #[1])

/-! Decidable membership and slice hashing -/

#guard (2 : UInt8) ∈ UInt8Array.mk #[1, 2, big]
#guard big ∈ UInt8Array.mk #[1, 2, big]
#guard (3 : UInt8) ∉ UInt8Array.mk #[1, 2, big]
#guard (0 : UInt8) ∉ UInt8Array.empty
#guard big ∈ (UInt8Array.mk #[0, 1, 2, big])[1...4]
#guard (0 : UInt8) ∉ (UInt8Array.mk #[0, 1, 2, big])[1...4]
#guard (2 : UInt8) ∉ (UInt8Array.mk #[0, 1, 2, big])[0...2]
#guard hash (UInt8Array.mk #[0, 1, 2, big])[1...3] == hash (UInt8Array.mk #[1, 2])
#guard hash (UInt8Array.mk #[0, 1, 2, big])[1...3] == hash (UInt8Array.mk #[big, 1, 2])[1...3]
#guard hash (∅ : UInt8Array.Slice) == hash UInt8Array.empty
#guard hash (UInt8Array.mk #[1, 2])[1...1] == hash (∅ : UInt8Array.Slice)

-- `decide` evaluates equality and membership for arrays and slices of literals.
example : UInt8Array.mk #[1, 2] = UInt8Array.mk #[1, 2] := by decide
example : UInt8Array.mk #[1, 2] ≠ UInt8Array.mk #[1, 3] := by decide
example : UInt8Array.mk #[1, 2] ≠ UInt8Array.mk #[1, 2, 3] := by decide
example : (2 : UInt8) ∈ UInt8Array.mk #[1, 2] := by decide
example : (3 : UInt8) ∉ UInt8Array.mk #[1, 2] := by decide
example : (2 : UInt8) ∈ (UInt8Array.mk #[1, 2, 3])[1...3] := by decide
example : (1 : UInt8) ∉ (UInt8Array.mk #[1, 2, 3])[1...3] := by decide

-- Lemmas that need decidable equality, used from another module.
example (a : UInt8Array) (x : UInt8) : a.contains x ↔ x ∈ a.toList := by simp
example (a : UInt8Array) (x : UInt8) (h : x ∈ a) :
    (if a.contains x then 1 else 0) = 1 := by simp [h]
example (s : UInt8Array.Slice) (x : UInt8) : s.contains x ↔ x ∈ s.copy := by simp
example (s t : UInt8Array.Slice) (h : s.copy = t.copy) : s == t := by simp [h]
example (s t : UInt8Array.Slice) (h : s == t) : hash s = hash t :=
  LawfulHashable.hash_eq s t h
