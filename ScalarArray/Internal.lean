/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

/-!
# The runtime representation of scalar arrays

`ScalarArray.Raw` exposes the Lean runtime's scalar array objects (`lean_sarray_object`), the
representation behind `ByteArray` and `FloatArray`. A scalar array is a header recording the
element size, the size and the capacity, followed by the elements stored unboxed.

This module binds the runtime functions on that header: allocation, size and capacity queries,
copying, resizing and copies of raw bytes. The typed array modules use it as their runtime
representation through `import all ScalarArray.Internal`, and reach it with `unsafeCast`. Their own
externs are only those that are part of their API, such as `size`, `decEq` and `markLinear`, and
the reads and writes `uget` and `setUnsafe`, whose C names the element type.

Only what the typed modules' inlined code calls is public: the type, `size`, `capacity`,
`resizeUnsafe` and `ensureExclusive`. Inlined code can only use declarations of publicly imported
modules, so the typed modules import this one publicly, and these are visible wherever
`ScalarArray` is imported. They are not part of the API. The rest is private.
-/

namespace ScalarArray

/-- A Lean runtime scalar array, whatever its element type. -/
public inductive Raw : Type
  | allocate (elemSize : UInt32) (size capacity : USize) (h : size ≤ capacity)

attribute [extern "lean_alloc_sarray"] Raw.allocate

namespace Raw

@[extern "lean_sarray_elem_size"]
private def elemSize : @& Raw → UInt32
  | allocate elemSize _ _ _ => elemSize

/-- The number of elements of `a`. -/
@[extern "lean_sarray_size"]
public def size : @& Raw → USize
  | allocate _ size _ _ => size

/-- The number of elements `a` has room for before it must be reallocated. -/
@[extern "lean_sarray_capacity"]
public def capacity : @& Raw → USize
  | allocate _ _ capacity _ => capacity

private theorem size_le_capacity : (a : Raw) → a.size ≤ a.capacity
  | allocate _ _ _ h => h

@[extern "lean_copy_sarray"]
private def copyWithCapacity (a : Raw) (capacity : USize) (h : a.size ≤ capacity) :
    Raw :=
  allocate a.elemSize a.size capacity h

@[inline]
private def copy (a : Raw) : Raw :=
  a.copyWithCapacity a.capacity a.size_le_capacity

/--
Sets the size of `a` to `size`, in place. Only valid when `a` is exclusive; the elements past the
old size are uninitialized until they are stored.
-/
@[extern c inline "#1;\nlean_sarray_set_size(#1, #2)"]
public unsafe def resizeUnsafe (a : Raw) (size : USize) (h : size ≤ a.capacity)
    (_exclusive : isExclusiveUnsafe a := by rfl) : Raw :=
  allocate a.elemSize size a.capacity h

/-- Returns `a` itself when it is not shared, and a copy otherwise. -/
-- `never_extract`: once inlined, `c.ensureExclusive` on a closed array `c` would otherwise be
-- hoisted into a shared constant, which the following in-place write would then modify.
@[never_extract, extern "lean_sarray_ensure_exclusive"]
public def ensureExclusive (a : Raw) : Raw := a.copy

/--
Copies `n` bytes of the data of `src`, starting at byte `srcOff`, into the data of `dest`, starting
at byte `destOff`. Only valid when `dest` is exclusive and both ranges are within the capacities.
The ranges may overlap.
-/
-- `memmove` rather than `memcpy`, so that overlapping ranges are never undefined behavior; for
-- ranges that don't overlap it is as fast. `lean.h` doesn't include `string.h`, so the code
-- declares `memmove` itself, at block scope, which standard C allows for library functions. Unlike
-- `__builtin_memmove`, this also compiles with MSVC, and GCC and Clang still treat it as their
-- builtin.
-- TODO: core has no runtime function that copies a slice of a scalar array with any element size;
-- `lean_byte_array_copy_slice` only works for bytes. Replace this once core has one.
@[extern c inline "#1;\n{ extern void * memmove(void *, void const *, size_t); \
  memmove(lean_sarray_cptr(#1) + #4, lean_sarray_cptr(#2) + #3, #5); }"]
private unsafe def memmoveUnsafe :
    Raw → @& Raw → (srcOff destOff n : USize) → Raw
  | dest, _, _, _, _ => dest

end Raw

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
