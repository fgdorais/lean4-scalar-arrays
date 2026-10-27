/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ScalarArray.Int32.Basic
public import ScalarArray.Int32.Array
public import ScalarArray.Int32.Slice
public import ScalarArray.Int32.Lemmas
public import ScalarArray.Int32.InPlace
public import ScalarArray.Int32.Decidable

/-!
# Arrays of `Int32`

`ScalarArray.Int32Array` stores `Int32` values unboxed in a Lean runtime scalar array,
4 bytes per element. Its logical model is `Array Int32`: `Int32Array.mk` and
`Int32Array.toArray` convert between the two, and every operation is specified by its effect on
the model.

Reads and in-place writes are inline C. `uset`, `set` and `push` update the array in place when it
is not shared and copy it otherwise, like `Array` and `ByteArray`.
-/
