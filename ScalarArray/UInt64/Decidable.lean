/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ScalarArray.UInt64.InPlace
import all ScalarArray.Internal
import all ScalarArray.UInt64.Basic
import all ScalarArray.UInt64.Array
import all ScalarArray.UInt64.Slice
import all ScalarArray.UInt64.Lemmas
import all ScalarArray.UInt64.InPlace
import Init.Data.Iterators.Lemmas.Basic
import Init.Data.Slice.InternalLemmas

/-!
# Decidable membership and hashing for `UInt64Array`

Decidable membership, slice hashing and the lawful `BEq` and `Hashable`
instances on slices. Left out of the float types, which have no `DecidableEq`.
-/

namespace ScalarArray

namespace UInt64Array

public theorem contains_iff_mem {a : UInt64Array} {x : UInt64} :
    a.contains x = true ↔ x ∈ a := by
  simp only [contains, Array.contains_iff_mem, mem_toArray]

private def decMemImpl (x : UInt64) (a : UInt64Array) : Decidable (x ∈ a) :=
  decidable_of_iff _ contains_iff_mem

/--
Decides membership with `contains`. Logically it decides membership in `a.toList`, so that `decide`
can evaluate it.
-/
@[implemented_by decMemImpl, expose]
public def decMem (x : UInt64) (a : UInt64Array) : Decidable (x ∈ a) :=
  decidable_of_iff _ mem_toList

public instance (x : UInt64) (a : UInt64Array) : Decidable (x ∈ a) := decMem x a

@[simp] public theorem contains_eq_mem {a : UInt64Array} {x : UInt64} :
    a.contains x = decide (x ∈ a) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, contains_iff_mem]

public theorem Slice.contains_iff_mem {s : UInt64Array.Slice} {x : UInt64} :
    s.contains x = true ↔ x ∈ s := by
  simp

private def Slice.decMemImpl (x : UInt64) (s : UInt64Array.Slice) : Decidable (x ∈ s) :=
  decidable_of_iff _ Slice.contains_iff_mem

/--
Decides membership with `contains`. Logically it decides membership in `s.copy.toList`, so that
`decide` can evaluate it.
-/
@[implemented_by Slice.decMemImpl, expose]
public def Slice.decMem (x : UInt64) (s : UInt64Array.Slice) : Decidable (x ∈ s) :=
  decidable_of_iff (x ∈ s.copy.toList) (by simp)

public instance (x : UInt64) (s : UInt64Array.Slice) : Decidable (x ∈ s) := Slice.decMem x s

private def Slice.hashImpl (s : UInt64Array.Slice) : UInt64 :=
  s.foldl (fun r x => mixHash r (Hashable.hash x)) 7

/-- The same hash as `s.copy`, so slices with the same elements have the same hash. -/
@[implemented_by Slice.hashImpl]
public def Slice.hash (s : UInt64Array.Slice) : UInt64 :=
  Hashable.hash s.copy

public instance : Hashable UInt64Array.Slice := ⟨Slice.hash⟩

public theorem Slice.hash_eq_hash_copy (s : UInt64Array.Slice) :
    Hashable.hash s = Hashable.hash s.copy := by
  rfl

public theorem Slice.beq_iff_copy_eq {s t : UInt64Array.Slice} :
    (s == t) = true ↔ s.copy = t.copy := by
  simp

public instance : EquivBEq UInt64Array.Slice where
  rfl := by simp
  symm h := by simp_all
  trans h₁ h₂ := by simp_all

public instance : LawfulHashable UInt64Array.Slice where
  hash_eq s t h := by
    rw [Slice.hash_eq_hash_copy, Slice.hash_eq_hash_copy, Slice.beq_iff_copy_eq.mp h]

end UInt64Array

end ScalarArray
