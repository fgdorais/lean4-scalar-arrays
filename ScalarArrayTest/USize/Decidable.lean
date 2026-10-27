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
Tests for `USizeArray`: decidable equality and membership, and hashing; left out of the float
types.
-/

/-- A test value at the edge of the element type's range. -/
private abbrev big : USize := 18446744073709551615

/-- The size of an element in bytes. -/
private abbrev elemSize : UInt32 := (System.Platform.numBits / 8).toUInt32

/-! Decidable equality and hashing -/

#guard decide (USizeArray.mk #[1, 2, big] = USizeArray.mk #[1, 2, big])
#guard !decide (USizeArray.mk #[1, 2, big] = USizeArray.mk #[1, 2, 0])
#guard hash (USizeArray.mk #[1, 2, big]) == hash #[(1 : USize), 2, big]
#guard hash (USizeArray.empty) == hash (#[] : Array USize)
#guard hash ((USizeArray.emptyWithCapacity 100).push 1) == hash (USizeArray.mk #[1])

/-! Decidable membership and slice hashing -/

#guard (2 : USize) ∈ USizeArray.mk #[1, 2, big]
#guard big ∈ USizeArray.mk #[1, 2, big]
#guard (3 : USize) ∉ USizeArray.mk #[1, 2, big]
#guard (0 : USize) ∉ USizeArray.empty
#guard big ∈ (USizeArray.mk #[0, 1, 2, big])[1...4]
#guard (0 : USize) ∉ (USizeArray.mk #[0, 1, 2, big])[1...4]
#guard (2 : USize) ∉ (USizeArray.mk #[0, 1, 2, big])[0...2]
#guard hash (USizeArray.mk #[0, 1, 2, big])[1...3] == hash (USizeArray.mk #[1, 2])
#guard hash (USizeArray.mk #[0, 1, 2, big])[1...3] == hash (USizeArray.mk #[big, 1, 2])[1...3]
#guard hash (∅ : USizeArray.Slice) == hash USizeArray.empty
#guard hash (USizeArray.mk #[1, 2])[1...1] == hash (∅ : USizeArray.Slice)

-- Lemmas that need decidable equality, used from another module.
example (a : USizeArray) (x : USize) : a.contains x ↔ x ∈ a.toList := by simp
example (a : USizeArray) (x : USize) (h : x ∈ a) :
    (if a.contains x then 1 else 0) = 1 := by simp [h]
example (s : USizeArray.Slice) (x : USize) : s.contains x ↔ x ∈ s.copy := by simp
example (s t : USizeArray.Slice) (h : s.copy = t.copy) : s == t := by simp [h]
example (s t : USizeArray.Slice) (h : s == t) : hash s = hash t :=
  LawfulHashable.hash_eq s t h
