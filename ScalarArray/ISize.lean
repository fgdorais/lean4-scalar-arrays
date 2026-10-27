/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ScalarArray.ISize.Basic
public import ScalarArray.ISize.Array
public import ScalarArray.ISize.Slice
public import ScalarArray.ISize.Lemmas
public import ScalarArray.ISize.InPlace
public import ScalarArray.ISize.Decidable

/-!
# Arrays of `ISize`

`ScalarArray.ISizeArray` stores `ISize` values unboxed in a Lean runtime scalar array,
one machine word per element. Its logical model is `Array ISize`: `ISizeArray.mk` and
`ISizeArray.toArray` convert between the two, and every operation is specified by its effect on
the model.

Reads and in-place writes are inline C. `uset`, `set` and `push` update the array in place when it
is not shared and copy it otherwise, like `Array` and `ByteArray`.
-/
