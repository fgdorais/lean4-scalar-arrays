/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ScalarArray.UInt64.Basic
public import ScalarArray.UInt64.Array
public import ScalarArray.UInt64.Slice
public import ScalarArray.UInt64.Lemmas
public import ScalarArray.UInt64.InPlace
public import ScalarArray.UInt64.Decidable

/-!
# Arrays of `UInt64`

`ScalarArray.UInt64Array` stores `UInt64` values unboxed in a Lean runtime scalar array,
8 bytes per element. Its logical model is `Array UInt64`: `UInt64Array.mk` and
`UInt64Array.toArray` convert between the two, and every operation is specified by its effect on
the model.

Reads and in-place writes are inline C. `uset`, `set` and `push` update the array in place when it
is not shared and copy it otherwise, like `Array` and `ByteArray`.
-/
