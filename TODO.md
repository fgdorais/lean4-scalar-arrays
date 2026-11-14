# TODO

Open work on Scalar Arrays, roughly by area. Entries name `UInt16Array`, but each one applies to all
13 array types, which are generated from the `UInt16` templates (see [CONTRIBUTING.md]).

[CONTRIBUTING.md]: CONTRIBUTING.md

## New operations

- Array versions of in-place operations that only slices have: `modify`, `swap`, `reverse`.
- New in-place operations: `insertIdx`, `eraseIdx`, and in-place `take`, `shrink` and `drop`.
- Array versions of slice queries: `find?`, `count`, `findRev?`. `findSome?` is missing on both.
- Possibly: `map`, `sum`, `max?`, `isPrefixOf`, `Slice.isEmpty`, `Std.Iter.count`, `sort`,
  `binSearch`. Prefer the `Std.Iterators` combinators where they are enough.
- Lexicographic `LT` and `Ord` instances.

## API cleanups

- Move the public unsafe helpers (`setUnsafe`, `pushGrowUnsafe`, `ensureCapacityGrowUnsafe` and
  the public `…Impl`s) into a sub-namespace, so they drop out of dot completion.
- The `Impl` suffix names both `implemented_by` targets, which are unsafe, and `csimp` targets,
  which are safe. Pick one meaning.
- The `2` in names means two windows or maps (`foldlInPlace2`, `modifyAt2`) but two loop variables
  in `forIn2`, and `foldlInPlaceRangeWith2Acc` spells it differently again.
- Give `popWhile` a safe implementation proved by `csimp` instead of `implemented_by`.

## Lemmas

- An exact size equation for `popWhile` (only `size_popWhile_le` so far).
- A `@[simp]` normal form for `Slice.getD`, like `getD_eq_getD_getElem?` for arrays.
- Lemmas relating the slice iterators to `Slice.copy` beyond `toList`, for `Std.Iter` combinators
  such as `count` and `findSome?`, and for `Slice.findIdx?`.
- The slice-iterator lemma in `Lemmas.lean` relies on core's
  `Std.Slice.Internal.toList_eq_toList_iter` and `iter_eq_toIteratorIter`, which may break on a
  toolchain bump. Replace them when core has public versions.

## `ScalarArray.Notation`

- `runInPlaceThen` still allocates the final `((), s)` pair; removing it needs a separate API for
  terminal programs.
- A program with no writes copies the array (the docs say to skip `inplace` there). The macro
  could reject such programs.

## `ScalarArray.Bytes`

Still experimental. Before it graduates:

- Lemmas for `ofBytesLE?` and `ofBytesBE?`.
- Safe implementations proved by `csimp` for the conversions and `byteSwap`, instead of
  `implemented_by`.
- Better names for the top-level `UInt16.byteSwap`, `UInt32.byteSwap` and `UInt64.byteSwap`,
  which could clash with core.
- A float round-trip lemma, which needs `Float.ofBits_toBits` in core.

## Waiting on core

- `UIntX` lemmas next to `toNat_sub_of_le` in `Init/Data/UInt/Lemmas.lean`: `toNat_add_of_lt`,
  `toNat_mul_of_lt` (`BitVec` has both), and the loop steps `(i + 1).toNat = i.toNat + 1` for
  `i < j` and `(i - 1).toNat = i.toNat - 1` for `j < i`. Then drop the private copies in
  `ScalarArray.Internal`.
- A runtime function for element-sized slice copies (`lean_byte_array_copy_slice` copies bytes
  only), to replace the inline `memcpy`.
- leanprover/lean4#15925: `isExclusiveUnsafe` lacks `never_extract`.
- A private `implemented_by` target attached by a separate `attribute [implemented_by …]` command
  is invisible to other modules, which is why `getImpl`, `setImpl`, `usetImpl` and `mkImpl` are
  public. Not filed yet.
- Floats: a `beq` lemma, `size_toFloatArray` and `size_ofFloatArray` in `Conversions`, and
  decidable membership and hashing. Also document that `x ∈ a` uses `=` while `contains` uses
  `==`, so they differ on NaN and ±0.
- `decide` can't evaluate `USize` and `ISize` literals because `System.Platform.numBits` is opaque,
  so those tests skip the `decide` examples (`WORD_TEST_DECIDE` in `generate.py`).

## Housekeeping

- Add `python3 scripts/generate.py --check` to CI.
