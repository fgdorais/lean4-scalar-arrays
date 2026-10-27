/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ScalarArray.USize.Basic
public import ScalarArray.USize.Array
public import ScalarArray.USize.Slice
public import ScalarArray.USize.Lemmas
public import ScalarArray.USize.InPlace
public import ScalarArray.USize.Decidable

/-!
# Arrays of `USize`

`ScalarArray.USizeArray` stores `USize` values unboxed in a Lean runtime scalar array,
one machine word per element. Its logical model is `Array USize`: `USizeArray.mk` and
`USizeArray.toArray` convert between the two, and every operation is specified by its effect on
the model.

Reads and in-place writes are inline C. `uset`, `set` and `push` update the array in place when it
is not shared and copy it otherwise, like `Array` and `ByteArray`.
-/
