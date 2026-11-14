# Contributing

Thanks for your interest in Scalar Arrays. This file collects the conventions the library follows.
When in doubt, copy what the code nearby already does.

## Building and testing

```sh
lake build --wfail   # the library, the tests and the benchmarks, with warnings as errors
lake test            # the `#guard` tests in `ScalarArrayTest`
lake exe bench       # the benchmarks, when a change may affect speed
```

CI runs `lake build --wfail` and `lake test` on Linux (x86 and ARM), macOS and Windows for every
pull request to `main`.

## Generated files

The 13 array types are generated from the `UInt16` versions. Edit only the templates,
`ScalarArray/UInt16.lean`, `ScalarArray/UInt16/`, `ScalarArrayTest/UInt16.lean` and
`ScalarArrayTest/UInt16/`, then regenerate the other types:

```sh
python3 scripts/generate.py           # regenerate
python3 scripts/generate.py --check   # check that nothing is out of date
```

`ScalarArray/Bytes.lean` and its tests come from `scripts/bytes_template.py`. Anything that doesn't
name an element type, such as `ScalarArray.Stride`, goes in a shared module instead.

## Files

- Every file that allows comments starts with the copyright and license header, and every Lean file
  is a `module`.
- Each module has a `/-! # Title -/` docstring, with `/-! ## … -/` headers for its parts.
- Every public declaration has a docstring (`linter.missingDocs` is on). Use `--` comments to
  explain why the code is the way it is.
- Mark declarations `public` one at a time, and `@[expose]` only where other modules must unfold
  the body. Implementation details live in `ScalarArray.Internal`, which is not part of the API.
- Keep lines to 100 columns, except for Markdown tables and URLs. In a `#guard_msgs` docstring,
  wrap a long message and use `#guard_msgs (whitespace := lax)`.

## Lean style

- `variable` only right after `namespace` or a named `section`.
- `fun x => …`, not `↦` or `λ`; `<|` and `|>`, not `$`.
- `theorem`, not `lemma`.
- In attribute lists, `simp` comes before `grind`, and `expose` comes last: `@[simp, grind =]`,
  `@[inline, expose]`.
- Name unused hypotheses with a leading underscore (`_h`).

## Proofs

- Prefer `lia` and `grind` to `omega`.
- `lia` and `grind` run out of memory on literal `2^64` moduli, so keep `USize.size` symbolic.
  `grind` proves the usual `USize` wrap-around index facts.
- Lemma names follow core: `size_push`, `toArray_set`, `getElem_set`. Mark lemmas `grind` where core
  marks the matching `Array` lemma.

## Design

- Follow core's `ByteArray` and `FloatArray`: `size : Nat` is primary, and `usize` is
  `size.toUSize`.
- Keep `extern` and `unsafe` code to a minimum. A fast implementation `fooImpl` should be safe Lean,
  proved equal to the specification by `@[csimp] theorem foo_eq_fooImpl : @foo = @fooImpl`. Use
  `implemented_by` only when that isn't possible. Mutating externs are `never_extract`.
- Prefer the `Std.Iterators` combinators on `a.iter` and `s.iter` to adding new array functions,
  and there is no separate `Iterator` type.
- Slices are `XArray.Slice`, built on `Std.Slice`. Arrays coerce to slices, but slices don't coerce
  to arrays: use `Slice.copy`.
- The library has no dependencies besides Lean itself.
- `import ScalarArray` imports neither the experimental `ScalarArray.Bytes` nor
  `ScalarArray.Notation`, which makes `inplace` a keyword. The notation must not change anything
  outside `inplace … do` blocks; `ScalarArrayTest/NotationScope.lean` checks this.

## Naming

- `foo?` returns an `Option` and `foo!` panics on bad input, except that `set!` leaves the array
  unchanged, as in `ByteArray`. A `u` prefix takes a `USize` index (`uget`, `uset`).
- `fooThen` hands its result to a continuation instead of returning a pair. `fooBind` is a loop that
  runs straight into the rest of a program.
- In-place loops are `forIn lo hi` and `forInRev lo hi` (from `hi - 1` down to `lo`).
- A `2` suffix means two of something in one array, such as two windows (`foldlInPlace2`) or two
  index maps (`modifyAt2`); a `zip` prefix means two arrays (`zipModifyAt`).
- Avoid names that mean something else in core.

## Commits and pull requests

- Pull requests are squash-merged. The title is the commit message, in the
  [Conventional Commits](https://www.conventionalcommits.org) style, in lower case:
  `feat: …`, `fix: …`, `perf: …`, `refactor: …`, `docs: …` or `chore: …`. Changes to CI and
  workflows are `chore:`.
- Don't rewrite a branch's history after pushing it; merge `main` into it instead.
- Releases are git tags `vX.Y.Z`; the lakefile has no version.
