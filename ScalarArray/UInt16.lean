/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ScalarArray.UInt16.Basic
public import ScalarArray.UInt16.Array
public import ScalarArray.UInt16.Slice
public import ScalarArray.UInt16.Lemmas
public import ScalarArray.UInt16.InPlace
public import ScalarArray.UInt16.Decidable

/-!
# Arrays of `UInt16`

`ScalarArray.UInt16Array` stores `UInt16` values unboxed in a Lean runtime scalar array,
2 bytes per element. Its logical model is `Array UInt16`: `UInt16Array.mk` and
`UInt16Array.toArray` convert between the two, and every operation is specified by its effect on
the model.

Reads and in-place writes are inline C. `uset`, `set` and `push` update the array in place when it
is not shared and copy it otherwise, like `Array` and `ByteArray`.
-/
