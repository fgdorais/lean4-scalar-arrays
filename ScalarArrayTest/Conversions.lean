/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import ScalarArray.Conversions
import ScalarArrayTest.Util
meta import ScalarArray.Conversions
meta import ScalarArrayTest.Util

open ScalarArray ScalarArrayTest

/-! `UInt8Array` and `ByteArray` -/

#guard (UInt8Array.mk #[1, 2, 255]).toByteArray.data == #[1, 2, 255]
#guard (UInt8Array.mk #[1, 2, 255]).toByteArray == ByteArray.mk #[1, 2, 255]
#guard (UInt8Array.ofByteArray (ByteArray.mk #[1, 2, 255])).toArray == #[1, 2, 255]
#guard (ByteArray.mk #[1, 2, 255]).toUInt8Array == UInt8Array.mk #[1, 2, 255]
#guard UInt8Array.empty.toByteArray.size == 0

-- Core's functions work on the converted arrays, and ours on core's.
#guard ((UInt8Array.mk #[1, 2]).toByteArray.push 255).toList == [1, 2, 255]
#guard ((ByteArray.mk #[1, 2]).toUInt8Array.push 255).toArray == #[1, 2, 255]
#guard (UInt8Array.mk ((Array.range 1000).map Nat.toUInt8)).toByteArray.hash ==
  (ByteArray.mk ((Array.range 1000).map Nat.toUInt8)).hash

-- Converting then writing must leave a shared original unchanged.
#guard
  let a := UInt8Array.mk #[1, 2]
  let b := a.toByteArray.set! 0 255
  b.data == #[255, 2] && a.toArray == #[1, 2]

#guard
  let b := ByteArray.mk #[1, 2]
  let a := b.toUInt8Array.set! 0 255
  a.toArray == #[255, 2] && b.data == #[1, 2]

-- The arrays are built from a parameter so that they aren't extracted as shared closed terms.
@[noinline] def toByteArrayDoesNotCopy (x : UInt8) : Bool :=
  let a := UInt8Array.mk #[x, 2]
  let p := rawAddr a
  rawAddr a.toByteArray == p

@[noinline] def ofByteArrayDoesNotCopy (x : UInt8) : Bool :=
  let b := ByteArray.mk #[x, 2]
  let p := rawAddr b
  rawAddr b.toUInt8Array == p

#guard toByteArrayDoesNotCopy 1
#guard ofByteArrayDoesNotCopy 1

/-! `Float64Array` and `FloatArray` -/

#guard (Float64Array.mk #[1.0, -1.5e300]).toFloatArray.data == #[1.0, -1.5e300]
#guard (Float64Array.ofFloatArray (FloatArray.mk #[1.0, -1.5e300])).toArray == #[1.0, -1.5e300]
#guard (FloatArray.mk #[1.0, -1.5e300]).toFloat64Array == Float64Array.mk #[1.0, -1.5e300]
#guard ((Float64Array.mk #[1.0]).toFloatArray.push 2.5).data == #[1.0, 2.5]
#guard ((FloatArray.mk #[1.0]).toFloat64Array.push 2.5).toArray == #[1.0, 2.5]

#guard
  let a := Float64Array.mk #[1.0, 2.0]
  let b := a.toFloatArray.set! 0 3.0
  b.data == #[3.0, 2.0] && a.toArray == #[1.0, 2.0]

@[noinline] def toFloatArrayDoesNotCopy (x : Float) : Bool :=
  let a := Float64Array.mk #[x, 2.0]
  let p := rawAddr a
  rawAddr a.toFloatArray == p

@[noinline] def ofFloatArrayDoesNotCopy (x : Float) : Bool :=
  let b := FloatArray.mk #[x, 2.0]
  let p := rawAddr b
  rawAddr b.toFloat64Array == p

#guard toFloatArrayDoesNotCopy 1.0
#guard ofFloatArrayDoesNotCopy 1.0

/-! Lemmas -/

example (a : UInt8Array) : UInt8Array.ofByteArray a.toByteArray = a := by simp
example (b : ByteArray) : b.toUInt8Array.toByteArray = b := by simp [ByteArray.toUInt8Array]
example (a : UInt8Array) : a.toByteArray.size = a.size := by simp
example (a : Float64Array) : Float64Array.ofFloatArray a.toFloatArray = a := by simp
