/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import ScalarArray.ISize
import ScalarArrayTest.Util
meta import ScalarArray.ISize
meta import ScalarArrayTest.Util

open ScalarArray ScalarArrayTest

/-!
Tests for `ISizeArray`: decidable equality and membership, and hashing; left out of the float
types.
-/

/-- A test value at the edge of the element type's range. -/
private abbrev big : ISize := -9223372036854775808

/-- The size of an element in bytes. -/
private abbrev elemSize : UInt32 := (System.Platform.numBits / 8).toUInt32

/-! Decidable equality and hashing -/

#guard decide (ISizeArray.mk #[1, 2, big] = ISizeArray.mk #[1, 2, big])
#guard !decide (ISizeArray.mk #[1, 2, big] = ISizeArray.mk #[1, 2, 0])
#guard hash (ISizeArray.mk #[1, 2, big]) == hash #[(1 : ISize), 2, big]
#guard hash (ISizeArray.empty) == hash (#[] : Array ISize)
#guard hash ((ISizeArray.emptyWithCapacity 100).push 1) == hash (ISizeArray.mk #[1])

/-! Decidable membership and slice hashing -/

#guard (2 : ISize) ∈ ISizeArray.mk #[1, 2, big]
#guard big ∈ ISizeArray.mk #[1, 2, big]
#guard (3 : ISize) ∉ ISizeArray.mk #[1, 2, big]
#guard (0 : ISize) ∉ ISizeArray.empty
#guard big ∈ (ISizeArray.mk #[0, 1, 2, big])[1...4]
#guard (0 : ISize) ∉ (ISizeArray.mk #[0, 1, 2, big])[1...4]
#guard (2 : ISize) ∉ (ISizeArray.mk #[0, 1, 2, big])[0...2]
#guard hash (ISizeArray.mk #[0, 1, 2, big])[1...3] == hash (ISizeArray.mk #[1, 2])
#guard hash (ISizeArray.mk #[0, 1, 2, big])[1...3] == hash (ISizeArray.mk #[big, 1, 2])[1...3]
#guard hash (∅ : ISizeArray.Slice) == hash ISizeArray.empty
#guard hash (ISizeArray.mk #[1, 2])[1...1] == hash (∅ : ISizeArray.Slice)

-- Lemmas that need decidable equality, used from another module.
example (a : ISizeArray) (x : ISize) : a.contains x ↔ x ∈ a.toList := by simp
example (a : ISizeArray) (x : ISize) (h : x ∈ a) :
    (if a.contains x then 1 else 0) = 1 := by simp [h]
example (s : ISizeArray.Slice) (x : ISize) : s.contains x ↔ x ∈ s.copy := by simp
example (s t : ISizeArray.Slice) (h : s.copy = t.copy) : s == t := by simp [h]
example (s t : ISizeArray.Slice) (h : s == t) : hash s = hash t :=
  LawfulHashable.hash_eq s t h
