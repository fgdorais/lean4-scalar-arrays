/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ScalarArray.UInt8
public import ScalarArray.Float64

/-!
# Conversions to and from core's scalar arrays

`UInt8Array` and core's `ByteArray` have the same runtime representation, a scalar array with
element size 1, and so do `Float64Array` and core's `FloatArray`, with element size 8. The
conversions between them are the identity at runtime, so they never copy.
-/

namespace ScalarArray

namespace UInt8Array

private unsafe def toByteArrayImpl (a : UInt8Array) : ByteArray := unsafeCast a

/-- The same array as a `ByteArray`, without copying. -/
@[implemented_by toByteArrayImpl, expose]
public def toByteArray (a : UInt8Array) : ByteArray := ⟨a.toArray⟩

private unsafe def ofByteArrayImpl (b : ByteArray) : UInt8Array := unsafeCast b

/-- The same array as a `UInt8Array`, without copying. -/
@[implemented_by ofByteArrayImpl, expose]
public def ofByteArray (b : ByteArray) : UInt8Array := mk b.data

@[simp] public theorem data_toByteArray (a : UInt8Array) : a.toByteArray.data = a.toArray := rfl

@[simp] public theorem toArray_ofByteArray (b : ByteArray) : (ofByteArray b).toArray = b.data := rfl

@[simp] public theorem size_toByteArray (a : UInt8Array) : a.toByteArray.size = a.size := by
  simp [← ByteArray.size_data]

@[simp] public theorem size_ofByteArray (b : ByteArray) : (ofByteArray b).size = b.size := by
  simp [← ByteArray.size_data, -size_toArray, size_eq_toArray_size]

@[simp] public theorem ofByteArray_toByteArray (a : UInt8Array) :
    ofByteArray a.toByteArray = a := by
  simp [UInt8Array.ext_iff]

@[simp] public theorem toByteArray_ofByteArray (b : ByteArray) :
    (ofByteArray b).toByteArray = b := by
  rfl

end UInt8Array

namespace Float64Array

private unsafe def toFloatArrayImpl (a : Float64Array) : FloatArray := unsafeCast a

/-- The same array as a `FloatArray`, without copying. -/
@[implemented_by toFloatArrayImpl, expose]
public def toFloatArray (a : Float64Array) : FloatArray := ⟨a.toArray⟩

private unsafe def ofFloatArrayImpl (b : FloatArray) : Float64Array := unsafeCast b

/-- The same array as a `Float64Array`, without copying. -/
@[implemented_by ofFloatArrayImpl, expose]
public def ofFloatArray (b : FloatArray) : Float64Array := mk b.data

@[simp] public theorem data_toFloatArray (a : Float64Array) : a.toFloatArray.data = a.toArray := rfl

@[simp] public theorem toArray_ofFloatArray (b : FloatArray) :
    (ofFloatArray b).toArray = b.data := rfl

@[simp] public theorem ofFloatArray_toFloatArray (a : Float64Array) :
    ofFloatArray a.toFloatArray = a := by
  simp [Float64Array.ext_iff]

@[simp] public theorem toFloatArray_ofFloatArray (b : FloatArray) :
    (ofFloatArray b).toFloatArray = b := by
  rfl

end Float64Array

end ScalarArray

/-- The same array as a `UInt8Array`, without copying. -/
@[inline, expose]
public def ByteArray.toUInt8Array (b : ByteArray) : ScalarArray.UInt8Array :=
  ScalarArray.UInt8Array.ofByteArray b

/-- The same array as a `Float64Array`, without copying. -/
@[inline, expose]
public def FloatArray.toFloat64Array (b : FloatArray) : ScalarArray.Float64Array :=
  ScalarArray.Float64Array.ofFloatArray b
