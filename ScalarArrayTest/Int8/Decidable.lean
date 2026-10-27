/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import ScalarArray.Int8
import ScalarArrayTest.Util
meta import ScalarArray.Int8
meta import ScalarArrayTest.Util

open ScalarArray ScalarArrayTest

/-!
Tests for `Int8Array`: decidable equality and membership, and hashing; left out of the float
types.
-/

/-- A test value at the edge of the element type's range. -/
private abbrev big : Int8 := -128

/-- The size of an element in bytes. -/
private abbrev elemSize : UInt32 := 1

/-! Decidable equality and hashing -/

#guard decide (Int8Array.mk #[1, 2, big] = Int8Array.mk #[1, 2, big])
#guard !decide (Int8Array.mk #[1, 2, big] = Int8Array.mk #[1, 2, 0])
#guard hash (Int8Array.mk #[1, 2, big]) == hash #[(1 : Int8), 2, big]
#guard hash (Int8Array.empty) == hash (#[] : Array Int8)
#guard hash ((Int8Array.emptyWithCapacity 100).push 1) == hash (Int8Array.mk #[1])

/-! Decidable membership and slice hashing -/

#guard (2 : Int8) ∈ Int8Array.mk #[1, 2, big]
#guard big ∈ Int8Array.mk #[1, 2, big]
#guard (3 : Int8) ∉ Int8Array.mk #[1, 2, big]
#guard (0 : Int8) ∉ Int8Array.empty
#guard big ∈ (Int8Array.mk #[0, 1, 2, big])[1...4]
#guard (0 : Int8) ∉ (Int8Array.mk #[0, 1, 2, big])[1...4]
#guard (2 : Int8) ∉ (Int8Array.mk #[0, 1, 2, big])[0...2]
#guard hash (Int8Array.mk #[0, 1, 2, big])[1...3] == hash (Int8Array.mk #[1, 2])
#guard hash (Int8Array.mk #[0, 1, 2, big])[1...3] == hash (Int8Array.mk #[big, 1, 2])[1...3]
#guard hash (∅ : Int8Array.Slice) == hash Int8Array.empty
#guard hash (Int8Array.mk #[1, 2])[1...1] == hash (∅ : Int8Array.Slice)

-- `decide` evaluates equality and membership for arrays and slices of literals.
example : Int8Array.mk #[1, 2] = Int8Array.mk #[1, 2] := by decide
example : Int8Array.mk #[1, 2] ≠ Int8Array.mk #[1, 3] := by decide
example : Int8Array.mk #[1, 2] ≠ Int8Array.mk #[1, 2, 3] := by decide
example : (2 : Int8) ∈ Int8Array.mk #[1, 2] := by decide
example : (3 : Int8) ∉ Int8Array.mk #[1, 2] := by decide
example : (2 : Int8) ∈ (Int8Array.mk #[1, 2, 3])[1...3] := by decide
example : (1 : Int8) ∉ (Int8Array.mk #[1, 2, 3])[1...3] := by decide

-- Lemmas that need decidable equality, used from another module.
example (a : Int8Array) (x : Int8) : a.contains x ↔ x ∈ a.toList := by simp
example (a : Int8Array) (x : Int8) (h : x ∈ a) :
    (if a.contains x then 1 else 0) = 1 := by simp [h]
example (s : Int8Array.Slice) (x : Int8) : s.contains x ↔ x ∈ s.copy := by simp
example (s t : Int8Array.Slice) (h : s.copy = t.copy) : s == t := by simp [h]
example (s t : Int8Array.Slice) (h : s == t) : hash s = hash t :=
  LawfulHashable.hash_eq s t h
