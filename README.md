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

The library is a Batteries cell: the `main` branch follows the Lean toolchain of Batteries `main`,
and the `nightly-testing` branch follows Batteries `nightly-testing` and the latest Lean nightly,
so it can be used together with Batteries. Add it to your `lakefile.toml`:

```toml
[[require]]
name = "lean4-scalar-arrays"
git = "https://github.com/fgdorais/lean4-scalar-arrays"
rev = "main"
```

Then `import ScalarArray` for every type, or `import ScalarArray.UInt32` and so on for just one.

## Usage

```lean
import ScalarArray

open ScalarArray

def squares (n : Nat) : UInt32Array := Id.run do
  let mut a := UInt32Array.emptyWithCapacity n
  for i in [0:n] do
    a := a.push (i * i).toUInt32
  return a

#eval (squares 5).toList  -- [0, 1, 4, 9, 16]
#eval (squares 5)[3]!     -- 9

example (a : UInt32Array) (x : UInt32) : (a.push x).size = a.size + 1 := by simp
```

## API

Every type `XArray` with element type `X` has the same API. For `Float64Array`, `X` is `Float`.

| Group        | Declarations                                                                |
|--------------|-----------------------------------------------------------------------------|
| Construction | `mk : Array X → XArray`, `empty`, `emptyWithCapacity`, `{}`, `replicate`, `ofFn` |
| Conversion   | `data : XArray → Array X`, `toList`                                         |
| Size         | `size : XArray → Nat`, `usize : XArray → USize`, `isEmpty`                  |
| Reading      | `get`, `uget`, `get!`, `getD`, `back`, `back?`, `back!`, and `a[i]`, `a[i]?`, `a[i]!` with `Nat` or `USize` indices |
| Writing      | `set`, `uset`, `set!`, `push`, `pop`                                        |
| Slicing      | `append`, `a ++ b`, `extract`                                               |
| Iteration    | `foldl`, `foldr`, `foldlM`, `foldrM`, `forM`, `for x in a`, `any`, `all`, `contains` |
| Equality     | `a == b`; for integer types also `DecidableEq` and `Hashable`               |
| Instances    | `Inhabited`, `EmptyCollection`, `GetElem`, `Append`, `ForIn`, `Repr`, `ToString` |
| Lemmas       | `ext`, `ext_getElem`; `data_*`, `size_*` and `getElem_*` simp lemmas for every operation that builds or changes an array; `foldl_eq_foldl_data`, `foldr_eq_foldr_data` |

As with `Array`:

- writes update the array in place when it is not shared, and copy it first when it is;
- `push` and `++` grow the capacity geometrically, so repeated pushes or appends take amortized
  constant time per element;
- `get!` and `set!` panic on an out-of-bounds index, while `getD` and `a[i]?` don't.

`a ++ b` copies the elements of `b` with a single `memcpy`, into `a` itself when it is not shared
and has room, and `extract` copies its slice with a single `memcpy`. Iteration reads the elements
directly, without building an `Array`.

Equality on the integer types compares the arrays' memory with `memcmp`, and their hash agrees
with the hash of `data`. `Float32Array` and `Float64Array` compare elements with floating-point
`==`, like `Array Float`, so they have no `DecidableEq` or `Hashable` instance: `NaN` is not equal
to itself and `0.0 == -0.0`.

## How it works

Each `XArray` is defined as an inductive type wrapping an `Array X`, and every operation is
defined by what it does to that array. That model is what you reason about in proofs.

At runtime, an `XArray` is a Lean scalar array object: a small header (element size, size and
capacity) followed by the elements stored unboxed. The operations are implemented through
`extern` (inline C for reads and writes) and `implemented_by`, so the compiled code never
builds the `Array`. The header is described by an internal type, `ScalarArray`, in
`ScalarArray.Internal`. Everything in that module is private and not part of the API.

The model and the C implementation are connected only by testing, so the test suite runs
against the compiled code.

## Development

```bash
lake build
```

```bash
lake test
```

The tests in `ScalarArrayTest` are `#guard` checks that run when the test library is built, so
`lake build` runs them as well, and CI builds with `--wfail`. The
library uses `precompileModules`, so the checks call the compiled C implementation rather than
evaluating the Lean model. They cover every operation, sharing (writes to a shared array must
not affect other references to it), indices beyond 16 bits, huge `Nat` indices, the runtime
element size and capacity, and bit-exact round-trips of special floating-point values.

The source files for the twelve types are identical apart from the type names, the C element
type and the element size. A change to one should be made to all of them.

-----

* The `Lean 4 / Scalar Arrays` library is copyright © 2026 François G. Dorais. The library is released under the [Apache 2.0 license](http://www.apache.org/licenses/LICENSE-2.0). See the file LICENSE for additional details.
