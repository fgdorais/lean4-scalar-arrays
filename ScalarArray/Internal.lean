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
private def copyWithCapacity (a : ScalarArray) (capacity : USize) (h : a.size ≤ capacity) : ScalarArray :=
  allocate a.elemSize a.size capacity h

@[inline]
private def copy (a : ScalarArray) : ScalarArray :=
  a.copyWithCapacity a.capacity a.size_le_capacity

@[extern c inline "#1;\nlean_sarray_set_size(#1, #2)"]
private unsafe def resizeUnsafe (a : ScalarArray) (size : USize) (h : size ≤ a.capacity) (_exclusive : isExclusiveUnsafe a := by rfl) : ScalarArray :=
  allocate a.elemSize size a.capacity h

@[extern "lean_sarray_ensure_exclusive"]
private def ensureExclusive (a : ScalarArray) : ScalarArray := a.copy
