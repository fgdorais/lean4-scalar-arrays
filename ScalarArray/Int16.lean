/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ScalarArray.Int16.Basic
public import ScalarArray.Int16.Array
public import ScalarArray.Int16.Slice
public import ScalarArray.Int16.Lemmas
public import ScalarArray.Int16.InPlace
public import ScalarArray.Int16.Decidable

/-!
# Arrays of `Int16`

`ScalarArray.Int16Array` stores `Int16` values unboxed in a Lean runtime scalar array,
2 bytes per element. Its logical model is `Array Int16`: `Int16Array.mk` and
`Int16Array.toArray` convert between the two, and every operation is specified by its effect on
the model.

Reads and in-place writes are inline C. `uset`, `set` and `push` update the array in place when it
is not shared and copy it otherwise, like `Array` and `ByteArray`.
-/
