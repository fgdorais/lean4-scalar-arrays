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
So is `ScalarArray.Notation`, the `inplace a do …` notation for in-place programs, because
importing it makes `inplace` a keyword. It adds nothing else outside of `inplace … do` blocks.

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
| Slices       | `XArray.Slice` with core's slice notation (`a[i...j]`, `a[i...=j]`, `a[i...*]`, `a[*...j]`, …), `toSlice`, `Slice.empty`, `{}`, `array`, `start`, `stop`, `size`, `usize`, `get`, `getD`, `get!`, `s[i]`, `popFront`, `slice`, `copy`, `for x in s`, `foldl`, `foldlM`, `forM`, `foldr`, `foldrM`, `forRevM`, `any`, `all`, `contains`, `count`, `find?`, `findRev?`, `findRevM?`, `findSomeRevM?`, `iter`, `toArray`, `toList`, `s == t` |
| Slice writes | `Slice.set`, `set!`, `modify`, `swap`, `reverse`, `foldlInPlace`, `foldrInPlace`, `foldlInPlaceThen`, `foldrInPlaceThen`, which write into the slice's array; `s.array` gives the whole array back |
| In-place folds | `Slice.foldlInPlace`, `Slice.foldrInPlace` and their `Then` forms; `foldlInPlace2` and `foldlInPlace2Then`, which write one window of an array from two others; `foldlInPlaceRange`, `foldrInPlaceRange` and their `Then` forms, the slice folds over `USize` bounds; `foldlInPlaceRangeWith2Acc` and its `Then` form, with two accumulators that stay unboxed |
| In-place programs | `XArray.InPlace n α`, a monad of programs that read and write an array of size `n` in place: `InPlace.read`, `readThen`, `write`, `InPlace.ite`, `InPlace.dite`; the loops `forIn lo hi` and `forInRev lo hi` (from `hi - 1` down to `lo`), whose bodies get both `lo ≤ j` and `j < hi`, `forIn2` and `forInRev2` with two unboxed accumulators, and their `Bind` forms (`forInBind`, …), which run straight into the rest of the program; run with `a.runInPlace m` or `m.run a h`, or a single loop with `runForInThen`, `runForInRevThen` and `runForIn2Then`. Tail programs `InPlace.Tail n γ` end by handing their result and the new array to a continuation, without a result pair: `Tail.bind`, `readThen`, `writeThen`, `Tail.ite`, `Tail.dite`, the `Bind` loops and `Tail.done x k`, and loops in continuation-passing style `Tail.forIn`, `Tail.forInRev` and their forms with two to four variables (`Tail.forIn2`, …), whose body ends by calling `next`, so that nested loops allocate nothing; run with `a.runInPlaceThen t`, or on a slice's window with `s.runInPlaceThenOf n h t`. For kernels that no fold shape covers, such as a butterfly that writes two windows with two carries |
| `inplace` notation | In `ScalarArray.Notation`: `inplace a do …`, an in-place program on an array or a slice `a` written with reads `let x := a[i]` (or `a[i]` in any term), writes `a[i] := e`, `let`, `let mut` and `x := e`, `have`, `if … then … else …` and `if let`, loops `for j in lo...hi with (x := init) … do …` with up to four unboxed variables and `for j in reverse lo...hi …`, with `for h : j in …` naming the bounds of `j`, and `return e`, and an optional `then k` that hands the result and the new array to `k` with no result pair; it compiles to the same loops as hand-written programs, and the tactic `inplace_bound` proves the index bounds, including `USize` arithmetic such as `j - 17` |
| Loop specifications | `modifyAt idx lo hi g`, which writes `g i a[idx i]` at the index `idx i` for each step `i` of a range, the model of a loop over a map of indices, with `getElem_modifyAt_idx` and `getElem_modifyAt_of_forall_ne`; `ScalarArray.Stride`, the strides `off + inc * i`, with `Stride.Fits` and `toNat_idx_toUSize` for their `USize` indices; `ScalarArray.iterRange` and `iterRangeRev`, the models of loops up and down, with `iterRange_prod_of_snd` for a loop that only reads; whole-loop lemmas for tail programs, `Tail.run_forInFrom` and `Tail.run_forInRevFrom` for a loop whose step maps its variable and the array, `_unit` for a loop with no variable, such as a loop of loops, and `_modify` and `_write` for the loops `for j in lo...hi do a[e j] := …` of the `inplace` notation; `modifyAt2` and `zipModifyAt`, two updates at a time on two index maps of one array or on two arrays, with `modifyAt2_eq` and `zipModifyAt_eq`, and `Stride.idx_ne_idx_of_same_inc` and `idx_ne_idx_of_lt_off` for strides that never meet |
| Strided loops | `modifyStride`, `modifyStride2` and `zipModifyStride`, loops that run `modifyAt`, `modifyAt2` and `zipModifyAt` on strides, such as a BLAS `scal` or a plane rotation (`drot`) of two vectors or of two rows of a matrix, with one exclusivity check per array |
| Iterators    | `a.iter` and `s.iter` for the `Std.Iterators` API, `Std.Iter.toXArray` and `Std.Iter.toXArrayWithCapacity` to collect an iterator into an array, and `Std.Iter.toXSlice` for the rest of a slice iterator as a slice, whose `start` is its position |
| Equality     | `a == b` and `s == t`; for integer types also `DecidableEq` (`decEq`), `Hashable` (`hash`), and for slices `Hashable` (`Slice.hash`), `EquivBEq` and `LawfulHashable` |
| Linearity    | `markLinear`, `propagateMark`                                               |
| Memory       | `ensureExclusive`, `ensureCapacity`, `ensureExclusiveWithCapacity`, which are logically the identity |
| Byte order   | In the experimental `ScalarArray.Bytes`, for the 16-, 32- and 64-bit integer and float arrays: `toBytesLE`, `toBytesBE`, `Slice.toBytesLE`, `Slice.toBytesBE`, `ofBytesLE?`, `ofBytesLE!`, `ofBytesBE?`, `ofBytesBE!`, `Slice.ofBytesLE?`, `Slice.ofBytesLE!`, `Slice.ofBytesBE?`, `Slice.ofBytesBE!`; for the integer ones also `byteSwap` |
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

In-place programs cover loops that no fold shape fits. In `ScalarArray.Notation`,
`inplace a do …` writes one in a small imperative language, and
compiles it to the same unboxed loop as a hand-written program. Here a single pass adds and
subtracts two windows of `a` with a carry and a borrow, writing the sum over `x` and the
difference to `t`:

```lean
import ScalarArray
import ScalarArray.Notation

open ScalarArray

def addSub (a : UInt64Array) (x y t len : USize) (hx : x.toNat + len.toNat ≤ a.size)
    (hy : y.toNat + len.toNat ≤ a.size) (ht : t.toNat + len.toNat ≤ a.size) :
    (UInt64 × UInt64) × UInt64Array :=
  inplace a do
    for j in 0...len with (c := 0) (b := 0) do
      let u := a[x + j]
      let v := a[y + j]
      let s := u + v + c
      let d := u - v - b
      a[x + j] := s
      a[t + j] := d
      c := if s < u || (s == u && c == 1) then 1 else 0
      b := if u < v || (u == v && b == 1) then 1 else 0
    return (c, b)
```

The index bounds are proved by the tactic `inplace_bound`, here from the window hypotheses.

The result is a pair of the program's result and the new array. A program can instead end with
`then k`, which hands them to `k`, with the new array's size, where the loop ends: no pair is
built, and the carries reach `k` unboxed. With `return (c, b)` above,
`then fun (c, b) a' h => g c b a' h` calls `g` with `h : a'.size = a.size`.

The whole-loop lemmas of `InPlace.Tail` prove what such a loop does. Here a loop doubles the
elements at the first `n` steps of a stride `s`, such as a column of a matrix, and
`run_forInFrom_modify` turns it into `modifyAt`, whose lemmas give each element:

```lean
def double (a : Float64Array) (s : Stride) (n : USize) (h : s.Fits n.toNat a.size)
    (hs : a.size < USize.size) : Float64Array :=
  let o := s.off.toUSize
  let c := s.inc.toUSize
  (inplace a do
    for k in 0...n do
      have hk : (o + c * k).toNat < a.size := s.toNat_idx_toUSize_lt h hs (by assumption)
      a[o + c * k] := 2 * a[o + c * k]).2

theorem double_eq (a : Float64Array) (s : Stride) (n : USize) (h : s.Fits n.toNat a.size)
    (hs : a.size < USize.size) :
    double a s n h hs = a.modifyAt s.idx 0 n.toNat fun _ v => 2 * v := by
  simp only [double, Float64Array.runInPlaceThenOf_eq, Float64Array.InPlace.Tail.forIn_eq]
  rw [Float64Array.InPlace.Tail.run_forInFrom_modify (idx := s.idx) (G := fun _ v => 2 * v)
    (he := fun _ _ hk => s.toNat_idx_toUSize h hs hk) (hg := fun _ _ _ _ => rfl)]
  simp
```

The loop computes `o` and `c` once, before it starts, and runs as fast as the contiguous loop
`a[k] := 2 * a[k]` at stride `1`. The same loop is `a.modifyStride s n.toNat (2 * ·) h`.

A plane rotation of two vectors writes two arrays at each step. `zipModifyStride` runs it as one
loop, with no check at each store, and `zipModifyAt_eq` gives the result as a `modifyAt` of each:

```lean
def rot (x y : Float64Array) (c s : Float) (n : Nat) (hx : Stride.Fits ⟨0, 1⟩ n x.size)
    (hy : Stride.Fits ⟨0, 1⟩ n y.size) : Float64Array × Float64Array :=
  Float64Array.zipModifyStride x y ⟨0, 1⟩ ⟨0, 1⟩ n (fun u v => c * u + s * v)
    (fun u v => c * v - s * u) hx hy
```

`x` and `y` may be the same array, which the loop then copies once. On two rows of one matrix,
`modifyStride2` updates both in place.

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
`forIn`, and the in-place folds, which run as in-place programs, are proved equal to their
specifications by `csimp` theorems. The `extern` and unsafe `implemented_by` code is connected to
the model only by testing, so the test suite runs against the compiled code.

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
| `ScalarArray.X.Program` | in-place programs: `InPlace`, `read`, `write`, the loops and `runInPlace`; tail programs `InPlace.Tail` and `runInPlaceThen` |
| `ScalarArray.X.InPlace` | writes through slices and in-place folds, which are in-place programs |
| `ScalarArray.X.Stride` | updates at index maps (`modifyAt`, `modifyAt2`, `zipModifyAt`), strided loops and whole-loop lemmas for tail programs |
| `ScalarArray.X.Decidable` | decidable membership, slice hashing; not for `Float32` and `Float64` |

The tests in `ScalarArrayTest.X` are split the same way. `ScalarArray.Stride` holds the parts of
loop specifications that name no element type: strides and the models `iterRange` and
`iterRangeRev`.

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

The documentation of the latest release is at
[www.dorais.org/lean4-scalar-arrays/doc](https://www.dorais.org/lean4-scalar-arrays/doc/). Each
release, starting with 1.0.0, also has its documentation attached on GitHub.

You can also generate the documentation locally with `lake build ScalarArray:docs` in the `docs`
directory.

-----

* The `Lean 4 / Scalar Arrays` library is copyright © 2026 François G. Dorais. The library is
  released under the [Apache 2.0 license](https://www.apache.org/licenses/LICENSE-2.0). See the
  file LICENSE for additional details.
