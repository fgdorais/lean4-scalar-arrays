/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ScalarArray.Float64.Basic
public import ScalarArray.Float64.Array
public import ScalarArray.Float64.Slice
public import ScalarArray.Float64.Lemmas
public import ScalarArray.Float64.InPlace

/-!
# Arrays of `Float`

`ScalarArray.Float64Array` stores `Float` values unboxed in a Lean runtime scalar array,
8 bytes per element. Its logical model is `Array Float`: `Float64Array.mk` and
`Float64Array.toArray` convert between the two, and every operation is specified by its effect on
the model.

Reads and in-place writes are inline C. `uset`, `set` and `push` update the array in place when it
is not shared and copy it otherwise, like `Array` and `ByteArray`.

`Float64Array` has the same runtime representation as the core `FloatArray`, with the same API
as the other arrays in this library.
-/
