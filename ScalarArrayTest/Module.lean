/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ScalarArray
meta import ScalarArray

/-!
Compiles code that calls `get`, `set`, `uset` and `mk` from another module. Their implementations
are attached with separate `attribute [implemented_by …]` commands, and a private target there is
not visible outside its module, so this file fails to compile when one of them is private. The
other test files are not modules, so they cannot catch this.
-/

open ScalarArray

namespace ScalarArrayTest.Module

/-- Sets the first element twice and reads it back, and builds an array with `mk`. -/
def probeUInt8 (a : UInt8Array) (h : 0 < a.size) : UInt8 × Nat :=
  let b := (a.set 0 1 h).uset 0 2 (by simpa using h)
  (b.get 0 (by simpa [b] using h), (UInt8Array.mk #[1, 2, 3]).size)

#guard probeUInt8 (UInt8Array.ofList [5, 6]) (by simp) == (2, 3)

/-- Sets the first element twice and reads it back, and builds an array with `mk`. -/
def probeUInt16 (a : UInt16Array) (h : 0 < a.size) : UInt16 × Nat :=
  let b := (a.set 0 1 h).uset 0 2 (by simpa using h)
  (b.get 0 (by simpa [b] using h), (UInt16Array.mk #[1, 2, 3]).size)

#guard probeUInt16 (UInt16Array.ofList [5, 6]) (by simp) == (2, 3)

/-- Sets the first element twice and reads it back, and builds an array with `mk`. -/
def probeUInt32 (a : UInt32Array) (h : 0 < a.size) : UInt32 × Nat :=
  let b := (a.set 0 1 h).uset 0 2 (by simpa using h)
  (b.get 0 (by simpa [b] using h), (UInt32Array.mk #[1, 2, 3]).size)

#guard probeUInt32 (UInt32Array.ofList [5, 6]) (by simp) == (2, 3)

/-- Sets the first element twice and reads it back, and builds an array with `mk`. -/
def probeUInt64 (a : UInt64Array) (h : 0 < a.size) : UInt64 × Nat :=
  let b := (a.set 0 1 h).uset 0 2 (by simpa using h)
  (b.get 0 (by simpa [b] using h), (UInt64Array.mk #[1, 2, 3]).size)

#guard probeUInt64 (UInt64Array.ofList [5, 6]) (by simp) == (2, 3)

/-- Sets the first element twice and reads it back, and builds an array with `mk`. -/
def probeUSize (a : USizeArray) (h : 0 < a.size) : USize × Nat :=
  let b := (a.set 0 1 h).uset 0 2 (by simpa using h)
  (b.get 0 (by simpa [b] using h), (USizeArray.mk #[1, 2, 3]).size)

#guard probeUSize (USizeArray.ofList [5, 6]) (by simp) == (2, 3)

/-- Sets the first element twice and reads it back, and builds an array with `mk`. -/
def probeInt8 (a : Int8Array) (h : 0 < a.size) : Int8 × Nat :=
  let b := (a.set 0 1 h).uset 0 2 (by simpa using h)
  (b.get 0 (by simpa [b] using h), (Int8Array.mk #[1, 2, 3]).size)

#guard probeInt8 (Int8Array.ofList [5, 6]) (by simp) == (2, 3)

/-- Sets the first element twice and reads it back, and builds an array with `mk`. -/
def probeInt16 (a : Int16Array) (h : 0 < a.size) : Int16 × Nat :=
  let b := (a.set 0 1 h).uset 0 2 (by simpa using h)
  (b.get 0 (by simpa [b] using h), (Int16Array.mk #[1, 2, 3]).size)

#guard probeInt16 (Int16Array.ofList [5, 6]) (by simp) == (2, 3)

/-- Sets the first element twice and reads it back, and builds an array with `mk`. -/
def probeInt32 (a : Int32Array) (h : 0 < a.size) : Int32 × Nat :=
  let b := (a.set 0 1 h).uset 0 2 (by simpa using h)
  (b.get 0 (by simpa [b] using h), (Int32Array.mk #[1, 2, 3]).size)

#guard probeInt32 (Int32Array.ofList [5, 6]) (by simp) == (2, 3)

/-- Sets the first element twice and reads it back, and builds an array with `mk`. -/
def probeInt64 (a : Int64Array) (h : 0 < a.size) : Int64 × Nat :=
  let b := (a.set 0 1 h).uset 0 2 (by simpa using h)
  (b.get 0 (by simpa [b] using h), (Int64Array.mk #[1, 2, 3]).size)

#guard probeInt64 (Int64Array.ofList [5, 6]) (by simp) == (2, 3)

/-- Sets the first element twice and reads it back, and builds an array with `mk`. -/
def probeISize (a : ISizeArray) (h : 0 < a.size) : ISize × Nat :=
  let b := (a.set 0 1 h).uset 0 2 (by simpa using h)
  (b.get 0 (by simpa [b] using h), (ISizeArray.mk #[1, 2, 3]).size)

#guard probeISize (ISizeArray.ofList [5, 6]) (by simp) == (2, 3)

/-- Sets the first element twice and reads it back, and builds an array with `mk`. -/
def probeFloat32 (a : Float32Array) (h : 0 < a.size) : Float32 × Nat :=
  let b := (a.set 0 1 h).uset 0 2 (by simpa using h)
  (b.get 0 (by simpa [b] using h), (Float32Array.mk #[1, 2, 3]).size)

#guard probeFloat32 (Float32Array.ofList [5, 6]) (by simp) == (2, 3)

/-- Sets the first element twice and reads it back, and builds an array with `mk`. -/
def probeFloat64 (a : Float64Array) (h : 0 < a.size) : Float × Nat :=
  let b := (a.set 0 1 h).uset 0 2 (by simpa using h)
  (b.get 0 (by simpa [b] using h), (Float64Array.mk #[1, 2, 3]).size)

#guard probeFloat64 (Float64Array.ofList [5, 6]) (by simp) == (2, 3)

end ScalarArrayTest.Module
