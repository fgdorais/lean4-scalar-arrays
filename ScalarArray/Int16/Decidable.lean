/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ScalarArray.Int16.InPlace
import all ScalarArray.Internal
import all ScalarArray.Int16.Basic
import all ScalarArray.Int16.Array
import all ScalarArray.Int16.Slice
import all ScalarArray.Int16.Lemmas
import all ScalarArray.Int16.InPlace
import Init.Data.Iterators.Lemmas.Basic
import Init.Data.Slice.InternalLemmas

/-!
# Decidable membership and hashing for `Int16Array`

Decidable membership, slice hashing and the lawful `BEq` and `Hashable`
instances on slices. Left out of the float types, which have no `DecidableEq`.
-/

namespace ScalarArray

namespace Int16Array

public theorem contains_iff_mem {a : Int16Array} {x : Int16} :
    a.contains x = true ↔ x ∈ a := by
  simp only [contains, Array.contains_iff_mem, mem_toArray]

private def decMemImpl (x : Int16) (a : Int16Array) : Decidable (x ∈ a) :=
  decidable_of_iff _ contains_iff_mem

/--
Decides membership with `contains`. Logically it decides membership in `a.toList`, so that `decide`
can evaluate it.
-/
@[implemented_by decMemImpl, expose]
public def decMem (x : Int16) (a : Int16Array) : Decidable (x ∈ a) :=
  decidable_of_iff _ mem_toList

public instance (x : Int16) (a : Int16Array) : Decidable (x ∈ a) := decMem x a

@[simp] public theorem contains_eq_mem {a : Int16Array} {x : Int16} :
    a.contains x = decide (x ∈ a) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, contains_iff_mem]

public theorem Slice.contains_iff_mem {s : Int16Array.Slice} {x : Int16} :
    s.contains x = true ↔ x ∈ s := by
  simp

private def Slice.decMemImpl (x : Int16) (s : Int16Array.Slice) : Decidable (x ∈ s) :=
  decidable_of_iff _ Slice.contains_iff_mem

/--
Decides membership with `contains`. Logically it decides membership in `s.copy.toList`, so that
`decide` can evaluate it.
-/
@[implemented_by Slice.decMemImpl, expose]
public def Slice.decMem (x : Int16) (s : Int16Array.Slice) : Decidable (x ∈ s) :=
  decidable_of_iff (x ∈ s.copy.toList) (by simp)

public instance (x : Int16) (s : Int16Array.Slice) : Decidable (x ∈ s) := Slice.decMem x s

private def Slice.hashImpl (s : Int16Array.Slice) : UInt64 :=
  s.foldl (fun r x => mixHash r (Hashable.hash x)) 7

/-- The same hash as `s.copy`, so slices with the same elements have the same hash. -/
@[implemented_by Slice.hashImpl]
public def Slice.hash (s : Int16Array.Slice) : UInt64 :=
  Hashable.hash s.copy

public instance : Hashable Int16Array.Slice := ⟨Slice.hash⟩

public theorem Slice.hash_eq_hash_copy (s : Int16Array.Slice) :
    Hashable.hash s = Hashable.hash s.copy := by
  rfl

public theorem Slice.beq_iff_copy_eq {s t : Int16Array.Slice} :
    (s == t) = true ↔ s.copy = t.copy := by
  simp

public instance : EquivBEq Int16Array.Slice where
  rfl := by simp
  symm h := by simp_all
  trans h₁ h₂ := by simp_all

public instance : LawfulHashable Int16Array.Slice where
  hash_eq s t h := by
    rw [Slice.hash_eq_hash_copy, Slice.hash_eq_hash_copy, Slice.beq_iff_copy_eq.mp h]

end Int16Array

end ScalarArray
