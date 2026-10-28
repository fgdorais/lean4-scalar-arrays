# Lean 4 / Scalar Arrays

[![CI](https://github.com/fgdorais/lean4-scalar-arrays/actions/workflows/cd-pipeline.yml/badge.svg)](https://github.com/fgdorais/lean4-scalar-arrays/actions/workflows/cd-pipeline.yml)

Compact, unboxed arrays of machine integers and floats for Lean 4.

Lean's core library stores `UInt8` and `Float` values unboxed in `ByteArray` and `FloatArray`.
Every other scalar type has to go in an `Array`, where each element takes a pointer-sized slot,
and 64-bit values and `Float32` are also boxed in their own heap object. This library adds
unboxed arrays for all of Lean's fixed-width scalar types. They work like `Array`, support
in-place updates, and have a simple `Array`-based model for proofs.

| Type                        | Element   | Bytes per element | With `Array` (64-bit) |
|-----------------------------|-----------|-------------------|-----------------------|
| `ScalarArray.UInt8Array`    | `UInt8`   | 1                 | 8                     |
| `ScalarArray.UInt16Array`   | `UInt16`  | 2                 | 8                     |
| `ScalarArray.UInt32Array`   | `UInt32`  | 4                 | 8                     |
| `ScalarArray.UInt64Array`   | `UInt64`  | 8                 | 8 + 16 on the heap    |
| `ScalarArray.USizeArray`    | `USize`   | machine word      | 8 + 16 on the heap    |
| `ScalarArray.Int8Array`     | `Int8`    | 1                 | 8                     |
| `ScalarArray.Int16Array`    | `Int16`   | 2                 | 8                     |
| `ScalarArray.Int32Array`    | `Int32`   | 4                 | 8                     |
| `ScalarArray.Int64Array`    | `Int64`   | 8                 | 8 + 16 on the heap    |
| `ScalarArray.ISizeArray`    | `ISize`   | machine word      | 8 + 16 on the heap    |
| `ScalarArray.Float32Array`  | `Float32` | 4                 | 8 + 16 on the heap    |
| `ScalarArray.Float64Array`  | `Float`   | 8                 | 8 + 16 on the heap    |

`UInt8Array` and `Float64Array` have the same memory layout as the core `ByteArray` and
`FloatArray`. They're included so that all the scalar types share one API.

## Installation

The library depends only on Lean itself. The `main` branch follows the newest Lean release,
including release candidates, and the `nightly-testing` branch follows the newest Lean nightly.
Releases are tagged `vX.Y.Z`. Add one to your `lakefile.toml`, or `main` for the latest changes:

```toml
[[require]]
name = "lean4-scalar-arrays"
git = "https://github.com/fgdorais/lean4-scalar-arrays"
rev = "v1.0.0"
```

Then `import ScalarArray` for every type, or `import ScalarArray.UInt32` and so on for just one.
The experimental `ScalarArray.Bytes`, which converts the arrays to and from `ByteArray` in little-
or big-endian byte order, is not part of `import ScalarArray` and has to be imported on its own.

Reads, writes and copies are implemented in C, so the library is built with `precompileModules`,
and Lake loads the compiled code whenever a file that imports it runs `#eval` or `#guard`. This
works in the editor, with `lake build` and with `lake lean`, but not with a bare `lake env lean`.

## Usage

```lean
import ScalarArray

open ScalarArray

def squares (n : Nat) : UInt32Array := Id.run do
  let mut a := UInt32Array.emptyWithCapacity n
  for i in 0...n do
    a := a.push (i * i).toUInt32
  return a

#eval (squares 5).toList  -- [0, 1, 4, 9, 16]
#eval (squares 5)[3]!     -- 9

example (a : UInt32Array) (x : UInt32) : (a.push x).size = a.size + 1 := by simp
```

## API

Every type `XArray` with element type `X` has the same API, which follows core's `ByteArray`. For
`Float64Array`, `X` is `Float`.

| Group        | Declarations                                                                |
|--------------|-----------------------------------------------------------------------------|
| Construction | `mk : Array X → XArray`, `empty`, `emptyWithCapacity`, `{}`, `replicate`, `ofFn`, `ofList`, `List.toXArray`, `Std.Iter.toXArray`, `Std.Iter.toXArrayWithCapacity` |
| Conversion   | `toArray : XArray → Array X`, `toList`, `ofList`, `List.toXArray`; `UInt8Array.toByteArray`, `UInt8Array.ofByteArray`, `ByteArray.toUInt8Array`, `Float64Array.toFloatArray`, `Float64Array.ofFloatArray` and `FloatArray.toFloat64Array`, which never copy |
| Size         | `size : XArray → Nat`, `usize : XArray → USize`, `isEmpty`                  |
| Reading      | `get`, `uget`, `get!`, `getD`, `back`, `back?`, `back!`, and `a[i]`, `a[i]?`, `a[i]!` with `Nat` or `USize` indices |
| Writing      | `set`, `uset`, `set!`, `push`, `pop`, `popWhile`, `copySlice`               |
| Combining    | `append`, `a ++ b`, `copySlice`                                             |
| Slicing      | `extract`, `copySlice`, `toSlice` and core's slice notation `a[i...j]`, `Slice.copy` |
| Iteration    | `foldl`, `foldr`, `foldlM`, `foldrM`, `forM`, `forIn`, `for x in a`, `any`, `all`, `contains`, `iter` |
| Search       | `findIdx?`, `findFinIdx?`, `any`, `all`, `contains`; for slices also `find?`, `findRev?`, `findRevM?`, `findSomeRevM?`, `count` |
| Membership   | `x ∈ a`, `x ∈ s`, `contains`; for integer types also `Decidable (x ∈ a)` and `Decidable (x ∈ s)` (`decMem`, `Slice.decMem`) |
| Slices       | `XArray.Slice` with core's slice notation (`a[i...j]`, `a[i...=j]`, `a[i...*]`, `a[*...j]`, …), `toSlice`, `Slice.empty`, `{}`, `array`, `start`, `stop`, `size`, `get`, `getD`, `get!`, `s[i]`, `popFront`, `slice`, `copy`, `for x in s`, `foldl`, `foldlM`, `forM`, `foldr`, `foldrM`, `forRevM`, `any`, `all`, `contains`, `count`, `find?`, `findRev?`, `findRevM?`, `findSomeRevM?`, `iter`, `toArray`, `toList`, `s == t` |
| Slice writes | `Slice.set`, `set!`, `modify`, `swap`, `reverse`, `foldlInPlace`, `foldrInPlace`, `foldlInPlaceThen`, `foldrInPlaceThen`, which write into the slice's array; `s.array` gives the whole array back |
| In-place folds | `Slice.foldlInPlace`, `Slice.foldrInPlace` and their `Then` forms; `foldlInPlace2` and `foldlInPlace2Then`, which write one window of an array from two others; `foldlInPlaceRange`, `foldrInPlaceRange` and their `Then` forms, the slice folds over `USize` bounds; `foldlInPlaceRangeWith2Acc` and its `Then` form, with two accumulators that stay unboxed |
| Iterators    | `a.iter` and `s.iter` for the `Std.Iterators` API, and `Std.Iter.toXArray` and `Std.Iter.toXArrayWithCapacity` to collect an iterator into an array |
| Equality     | `a == b` and `s == t`; for integer types also `DecidableEq` (`decEq`), `Hashable` (`hash`), and for slices `Hashable` (`Slice.hash`), `EquivBEq` and `LawfulHashable` |
| Linearity    | `markLinear`, `propagateMark`                                               |
| Memory       | `ensureExclusive`, `ensureCapacity`, `ensureExclusiveWithCapacity`, which are logically the identity |
| Byte order   | In the experimental `ScalarArray.Bytes`, for the 16-, 32- and 64-bit integer and float arrays: `toBytesLE`, `toBytesBE`, `Slice.toBytesLE`, `Slice.toBytesBE`, `ofBytesLE?`, `ofBytesLE!`, `ofBytesBE?`, `ofBytesBE!`; for the integer ones also `byteSwap` |
| Instances    | `Inhabited`, `EmptyCollection`, `GetElem`, `Append`, `ForIn`, `ForM`, `Membership`, `Coe XArray XArray.Slice`, `Repr`, `ToString`; `BEq`, `DecidableEq`, `Hashable`, `EquivBEq` and `LawfulHashable` as under Equality; core's `Sliceable` instances for the slice notation, and `Std.Iterator` for slices |
| Lemmas       | `ext`, `ext_getElem`, `ext_getElem?` and `toArray_inj`; `casesMk`, the default for `cases` and `induction`; `toArray_*`, `size_*` and `getElem_*` simp lemmas for every operation that builds or changes an array; core's `ByteArray` lemmas about `++`, `extract`, `copySlice` and `set!`; `grind` lemmas for size, elements and membership, where core marks the matching `Array` lemma |

As with `Array`:

- writes update the array in place when it is not shared, and copy it first when it is;
- `push` and `++` grow the capacity geometrically, so repeated pushes or appends take amortized
  constant time per element;
- `get!` panics on an out-of-bounds index, while `getD` and `a[i]?` don't.

As with `ByteArray`, `set!` returns the array unchanged when the index is out of bounds, `get`,
`uget`, `set` and `uset` prove their bounds with `get_elem_tactic` by default, and `foldl` and
`foldlM` take optional `start` and `stop` indices.

`a ++ b` copies the elements of `b` with a single `memmove`, into `a` itself when it is not shared
and has room. `extract` and `copySlice` also copy with a single `memmove`. Iteration reads the
elements directly, without building an `Array`.

`UInt8Array` converts to and from core's `ByteArray` with `toByteArray`, `ofByteArray` and
`ByteArray.toUInt8Array`, and `Float64Array` to and from core's `FloatArray` with `toFloatArray`,
`ofFloatArray` and `FloatArray.toFloat64Array`, in `ScalarArray.Conversions`, which
`import ScalarArray` includes. These conversions never copy, so core's functions can be used
directly on these arrays and vice versa.

Slices are `Std.Slice`s, like core's `Subarray`, so they work with the generic slice API and core's
range notation `a[i...j]` (the older `a[i:j]` notation only applies to `Array`). Taking a slice
never copies the array; `Slice.copy` makes a new array with a single `memmove`.

Slices can also be written to. `s.set i v` replaces the element at index `i` of the slice in the
underlying array, and `s.array` gives back the whole array. The writes work in place when neither
the slice nor its array is shared, so a slice taken from an array that is no longer used writes
into that array:

```lean
def reverseMiddle (a : UInt32Array) : UInt32Array :=
  a[1...a.size - 1].reverse.array   -- in place: `a` is not used after taking the slice
```

Arrays and slices also have iterators, so the `Std.Iterators` combinators cover operations that
don't have their own function here, and `Std.Iter.toXArray` turns the result back into an array:

```lean
(a.iter.map (· * 2)).toUInt32Array          -- map
(a.iter.filter (· > 0)).toUInt32Array       -- filter
a[2...*].copy                                -- drop
(a.iter.zip b.iter |>.map fun (x, y) => x + y).toUInt32Array  -- zipWith
a.iter.length                                -- size
```

`Std.Iter.toXArrayWithCapacity` allocates up front when the number of elements is known or
bounded, for example `(a.iter.map f).toUInt32ArrayWithCapacity a.size`.

Equality on the integer types compares the arrays' memory with `memcmp`, and their hash agrees
with the hash of `toArray`. `Float32Array` and `Float64Array` compare elements with floating-point
`==`, like `Array Float`, so they have no `DecidableEq` or `Hashable` instance: `NaN` is not equal
to itself and `0.0 == -0.0`.

## How it works

Each `XArray` is defined as a quotient of `Array X` by the empty relation: `XArray.mk` and
`XArray.toArray` convert between the two, and every operation is defined by what it does to that
array. That model is what you reason about in proofs. It is a quotient rather than a structure so
that compiled code can't match on it and run `Array` code on what is really a scalar array.

At runtime, an `XArray` is a Lean scalar array object: a small header (element size, size and
capacity) followed by the elements stored unboxed. The operations are implemented through
`extern` (inline C for reads and writes) and `implemented_by`, so the compiled code never
builds the `Array`. The header is described by an internal type, `ScalarArray.Raw`, in
`ScalarArray.Internal`. It and the few operations on it that inlined code calls are public, but
they are not part of the API; the rest of that module is private.

The implementations written in safe Lean, such as the loops behind `toArray`, `foldlM` and
`forIn`, are proved equal to their specifications by `csimp` theorems. The `extern` and unsafe
`implemented_by` code is connected to the model only by testing, so the test suite runs against
the compiled code.

## Stability

Releases are git tags `vX.Y.Z`, with release notes on GitHub. Starting with version 1.0.0,
breaking changes to the API are made only in a new major version.
The following are not covered by this promise:

- `ScalarArray.Internal`, including `ScalarArray.Raw`, and the declarations whose documentation
  says they are for internal use only;
- the experimental `ScalarArray.Bytes`;
- which lemmas are `@[simp]` or `@[grind]`, so `simp` and `grind` proofs may need adjusting after
  an upgrade;
- changes forced by changes to Lean and its core library, which is still evolving; in particular,
  slices and iterators are built on `Std.Slice` and `Std.Iterators`. The release notes will say
  when this happens.

## Development

```bash
lake build
```

```bash
lake test
```

The tests in `ScalarArrayTest` are `#guard` checks that run when the test library is built, so
`lake build` runs them as well, and CI builds with `--wfail`. Both libraries use
`precompileModules`, so the checks call the compiled C implementation rather than evaluating the
Lean model. They cover every operation, sharing (writes to a shared array must not affect other
references to it), indices beyond 16 bits, huge `Nat` indices, the runtime element size and
capacity, and bit-exact round-trips of special floating-point values.

Each type `X` has a module `ScalarArray.X`, which imports its parts:

| Part | Contents |
|---|---|
| `ScalarArray.X.Basic` | the type and its model, reads, writes, `push`, capacity, `append`, `copySlice` |
| `ScalarArray.X.Array` | removing elements, search, building arrays, iteration, equality, hashing, printing |
| `ScalarArray.X.Slice` | slices: the type, reads, slice notation, iterators, folds and searches, membership, equality; collecting iterators into arrays |
| `ScalarArray.X.Lemmas` | lemmas about arrays and slices |
| `ScalarArray.X.InPlace` | writes through slices and in-place folds |
| `ScalarArray.X.Decidable` | decidable membership, slice hashing; not for `Float32` and `Float64` |

The tests in `ScalarArrayTest.X` are split the same way.

`lake exe bench` times the main operations of `UInt8Array`, `UInt32Array`, `UInt64Array` and
`Float64Array`, and compares each with the same operation on core's `ByteArray`, `Array` or
`FloatArray`. `lake build` compiles it so that it keeps up with the API, but CI doesn't run it.
To run it on GitHub, add the `benchmark` label to a pull request, which compares the pull request
with its base, or start the Benchmarks workflow from the Actions tab. The results are in the run's
summary.

The source and test files for the twelve types are generated from the `UInt16` versions, in
`ScalarArray/UInt16/` and `ScalarArrayTest/UInt16/`. Make changes there, then regenerate the other
types:

```bash
python3 scripts/generate.py
```

`python3 scripts/generate.py --check` changes nothing and fails if a generated file is out of date.
The generated files are marked `linguist-generated` in `.gitattributes`, so GitHub collapses them in
diffs.

## Documentation

You can generate the API documentation locally with `lake build ScalarArray:docs` in the `docs`
directory.

-----

* The `Lean 4 / Scalar Arrays` library is copyright © 2026 François G. Dorais. The library is
  released under the [Apache 2.0 license](https://www.apache.org/licenses/LICENSE-2.0). See the
  file LICENSE for additional details.
