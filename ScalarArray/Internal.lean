/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

/-!
# Scalar arrays

`ScalarArray` exposes the Lean runtime's scalar array objects (`lean_sarray_object`), the
representation behind `ByteArray` and `FloatArray`. A scalar array is a header recording the
element size, the size and the capacity, followed by the elements stored unboxed.

This module only describes the header: allocation, size and capacity queries, copying and
resizing. Everything here is private. The typed array modules use it as their runtime
representation through `import all ScalarArray.Internal`.
-/

private inductive ScalarArray : Type
  | allocate (elemSize : UInt32) (size capacity : USize) (h : size ≤ capacity)

attribute [extern "lean_alloc_sarray"] ScalarArray.allocate

namespace ScalarArray

@[extern "lean_sarray_elem_size"]
private def elemSize : @& ScalarArray → UInt32
  | allocate elemSize _ _ _ => elemSize

@[extern "lean_sarray_size"]
private def size : @& ScalarArray → USize
  | allocate _ size _ _ => size

@[extern "lean_sarray_capacity"]
private def capacity : @& ScalarArray → USize
  | allocate _ _ capacity _ => capacity

private theorem size_le_capacity : (a : ScalarArray) → a.size ≤ a.capacity
  | allocate _ _ _ h => h

@[extern "lean_copy_sarray"]
private def copyWithCapacity (a : ScalarArray) (capacity : USize) (h : a.size ≤ capacity) :
    ScalarArray :=
  allocate a.elemSize a.size capacity h

@[inline]
private def copy (a : ScalarArray) : ScalarArray :=
  a.copyWithCapacity a.capacity a.size_le_capacity

@[extern c inline "#1;\nlean_sarray_set_size(#1, #2)"]
private unsafe def resizeUnsafe (a : ScalarArray) (size : USize) (h : size ≤ a.capacity)
    (_exclusive : isExclusiveUnsafe a := by rfl) : ScalarArray :=
  allocate a.elemSize size a.capacity h

@[extern "lean_sarray_ensure_exclusive"]
private def ensureExclusive (a : ScalarArray) : ScalarArray := a.copy

/-! ## Loop indices -/

/-- The guard `i < stop` of a loop over `USize` indices bounds the index by any bound on `stop`. -/
private theorem toNat_lt_of_lt {i stop : USize} {n : Nat} (h : i < stop) (hn : stop.toNat ≤ n) :
    i.toNat < n := by
  have := USize.lt_iff_toNat_lt.1 h
  lia

/-- `i + 1` doesn't wrap around when `i < stop`. -/
private theorem toNat_add_one_of_lt {i stop : USize} (h : i < stop) :
    (i + 1).toNat = i.toNat + 1 := by
  have := USize.lt_iff_toNat_lt.1 h
  have := stop.toNat_lt_size
  rw [USize.toNat_add, USize.toNat_one, Nat.mod_eq_of_lt (by lia)]

/-- `i - 1` doesn't wrap around when `j < i`. -/
private theorem toNat_sub_one_of_lt {i j : USize} (h : j < i) : (i - 1).toNat = i.toNat - 1 := by
  have := USize.lt_iff_toNat_lt.1 h
  rw [USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.2 (by simp; lia)), USize.toNat_one]

/-- `j + 1` is at most one more than `j`, even when it wraps around. -/
private theorem toNat_add_one_le (j : USize) : (j + 1).toNat ≤ j.toNat + 1 := by
  rw [USize.toNat_add, USize.toNat_one]
  exact Nat.mod_le _ _

/-- `USize` subtraction is at least the truncated subtraction of the `Nat` values. -/
private theorem toNat_sub_le_toNat_sub (a b : USize) : a.toNat - b.toNat ≤ (a - b).toNat := by
  by_cases h : b ≤ a
  · exact Nat.le_of_eq (USize.toNat_sub_of_le _ _ h).symm
  · have := USize.lt_iff_toNat_lt.1 (USize.not_le.1 h)
    lia

/-- The measure `stop - i` of a loop over `USize` indices decreases at each step. -/
private theorem sub_toNat_add_one_lt {i stop : USize} (h : i < stop) :
    stop.toNat - (i + 1).toNat < stop.toNat - i.toNat := by
  have := USize.lt_iff_toNat_lt.1 h
  rw [toNat_add_one_of_lt h]
  lia
