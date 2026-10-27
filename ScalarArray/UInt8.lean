/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ScalarArray.UInt8.Basic
public import ScalarArray.UInt8.Array
public import ScalarArray.UInt8.Slice
public import ScalarArray.UInt8.Lemmas
public import ScalarArray.UInt8.InPlace
public import ScalarArray.UInt8.Decidable

/-!
# Arrays of `UInt8`

`ScalarArray.UInt8Array` stores `UInt8` values unboxed in a Lean runtime scalar array,
1 byte per element. Its logical model is `Array UInt8`: `UInt8Array.mk` and
`UInt8Array.toArray` convert between the two, and every operation is specified by its effect on
the model.

Reads and in-place writes are inline C. `uset`, `set` and `push` update the array in place when it
is not shared and copy it otherwise, like `Array` and `ByteArray`.
-/
