/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ScalarArray.Int64.Basic
public import ScalarArray.Int64.Array
public import ScalarArray.Int64.Slice
public import ScalarArray.Int64.Lemmas
public import ScalarArray.Int64.InPlace
public import ScalarArray.Int64.Decidable

/-!
# Arrays of `Int64`

`ScalarArray.Int64Array` stores `Int64` values unboxed in a Lean runtime scalar array,
8 bytes per element. Its logical model is `Array Int64`: `Int64Array.mk` and
`Int64Array.toArray` convert between the two, and every operation is specified by its effect on
the model.

Reads and in-place writes are inline C. `uset`, `set` and `push` update the array in place when it
is not shared and copy it otherwise, like `Array` and `ByteArray`.
-/
