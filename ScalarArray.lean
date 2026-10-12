/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ScalarArray.UInt8
public import ScalarArray.UInt16
public import ScalarArray.UInt32
public import ScalarArray.UInt64
public import ScalarArray.USize
public import ScalarArray.Int8
public import ScalarArray.Int16
public import ScalarArray.Int32
public import ScalarArray.Int64
public import ScalarArray.ISize
public import ScalarArray.Float32
public import ScalarArray.Float64

/-!
# Scalar arrays

Unboxed arrays of scalar values, backed by the Lean runtime's scalar arrays:

* unsigned integers: `UInt8Array`, `UInt16Array`, `UInt32Array`, `UInt64Array`, `USizeArray`;
* signed integers: `Int8Array`, `Int16Array`, `Int32Array`, `Int64Array`, `ISizeArray`;
* floating point: `Float32Array`, `Float64Array`.

All of them live in the `ScalarArray` namespace and share the same API.
-/
