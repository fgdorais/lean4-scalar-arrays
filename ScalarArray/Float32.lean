/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ScalarArray.Float32.Basic
public import ScalarArray.Float32.Array
public import ScalarArray.Float32.Slice
public import ScalarArray.Float32.Lemmas
public import ScalarArray.Float32.InPlace

/-!
# Arrays of `Float32`

`ScalarArray.Float32Array` stores `Float32` values unboxed in a Lean runtime scalar array,
4 bytes per element. Its logical model is `Array Float32`: `Float32Array.mk` and
`Float32Array.toArray` convert between the two, and every operation is specified by its effect on
the model.

Reads and in-place writes are inline C. `uset`, `set` and `push` update the array in place when it
is not shared and copy it otherwise, like `Array` and `ByteArray`.
-/
