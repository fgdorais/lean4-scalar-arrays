/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import ScalarArray
import ScalarArray.Notation
meta import ScalarArray

/-!
# The fast Walsh–Hadamard transform on `Int32Array`

The Walsh–Hadamard transform of a vector `a` of size `n = 2 ^ k` is the vector `b` with
`b[i] = ∑ j, (-1) ^ popcount (i &&& j) * a[j]`. The fast transform computes it in place in `k`
stages: at stage `h = 1, 2, 4, …`, it replaces each pair `a[j]`, `a[j + h]` with `j &&& h = 0` by
their sum and difference, a *butterfly*. Integer arithmetic makes the result exact, so it is easy to
check against the definition.

Each butterfly reads two elements and writes two, which no fold covers. This example writes the
transform as an in-place program twice: first with the `InPlace` API, then in the `inplace`
notation of `ScalarArray.Notation`, which compiles to the same loops.
-/

open ScalarArray

namespace Hadamard

/-! ## The definition -/

/-- Whether `n` has an odd number of one bits, among its low 32. -/
def oddBits (n : Nat) : Bool := (List.range 32).foldl (fun b k => b ^^ n.testBit k) false

/-- The transform of `a`, straight from the definition, in `n ^ 2` steps. -/
def spec (a : Int32Array) : Int32Array :=
  .ofFn (n := a.size) fun i => Id.run do
    let mut s := 0
    for h : j in 0...a.size do
      let x := a[j]'(Std.Rco.lt_upper_of_mem h)
      s := if oddBits (i.val &&& j) then s - x else s + x
    return s

#guard (spec (.mk #[1, 0, 0, 0])).toList == [1, 1, 1, 1]
#guard (spec (.mk #[1, 2, 3, 4])).toList == [10, -2, -4, 0]

/-! ## With the `InPlace` API

A program `InPlace n α` reads and writes an array of size `n` and returns an `α`. `InPlace.read i h`
and `InPlace.write i h v` need the bound `h : i.toNat < n` of their `USize` index, and the loop
`InPlace.forIn lo hi init body` gives its body the bounds of `j`. Here the bound of `j + h` is
checked at run time with `InPlace.dite`, which passes the proof to its branch, so that the program
needs no proof about powers of two. The check costs one comparison per butterfly. `InPlace.ite` and
`InPlace.dite` branch inside the program, where `if … then … else …` would build both programs as
closures first.

The array size `n` is a parameter of the program's type, so `usize` and `hn` stand for `a.usize`
and its bound.
-/

/-- One stage of butterflies, at distance `h`. -/
def stage (n : Nat) (usize : USize) (hn : usize.toNat ≤ n) (h : USize) :
    Int32Array.InPlace n Unit :=
  Int32Array.InPlace.forIn 0 usize () fun j _ hj _ =>
    Int32Array.InPlace.ite (j &&& h == 0)
      (Int32Array.InPlace.dite (j + h < usize)
        (fun hb => do
          have hj : j.toNat < n := by grind
          have hjh : (j + h).toNat < n := by grind
          let x ← Int32Array.InPlace.read j hj
          let y ← Int32Array.InPlace.read (j + h) hjh
          Int32Array.InPlace.write j hj (x + y)
          Int32Array.InPlace.write (j + h) hjh (x - y))
        (fun _ => pure ()))
      (pure ())

/-- The transform, for an array whose size is a power of two. -/
def transform (a : Int32Array) : Int32Array := Id.run do
  let mut a := a
  let mut h : USize := 1
  while h < a.usize do
    a := (a.runInPlace (stage a.size a.usize a.toNat_usize_le h)).2
    h := 2 * h
  return a

#guard transform (.mk #[1, 2, 3, 4]) == spec (.mk #[1, 2, 3, 4])

/-! ## With the `inplace` notation

The same program reads much like pseudocode, and the `inplace_bound` tactic proves the index bounds
from the loop range and from the run-time check `hb`. The whole transform, all its stages, is one
program, so the array is checked for sharing once instead of once per stage.
-/

/-- The transform, for an array whose size is `2 ^ k`. -/
def fwht (a : Int32Array) (k : USize) : Int32Array :=
  (inplace a do
    for s in 0...k do
      let h : USize := 1 <<< s
      for j in 0...a.usize do
        if j &&& h == 0 then
          if hb : j + h < a.usize then
            let x := a[j]
            let y := a[j + h]
            a[j] := x + y
            a[j + h] := x - y).2

#guard fwht (.mk #[1, 2, 3, 4]) 2 == spec (.mk #[1, 2, 3, 4])

/-- A test vector of size `2 ^ 6`. -/
def test : Int32Array := .ofFn (n := 64) fun i => (i.val * 37 % 23 : Nat).toInt32 - 11

#guard transform test == spec test
#guard fwht test 6 == spec test

-- Applying the transform twice multiplies by `n`.
#guard (fwht (fwht test 6) 6).toList == test.toList.map (64 * ·)

/-! ## An application: XOR convolution

The transform turns the XOR convolution `c[i] = ∑ j, a[j] * b[i ^^^ j]` into a pointwise product:
transform `a` and `b`, multiply, transform back and divide by `n`. The pointwise steps are
iterator combinators, which build new arrays.
-/

/-- The XOR convolution of two arrays of size `2 ^ k`. -/
def xorConv (a b : Int32Array) (k : USize) : Int32Array :=
  let p := ((fwht a k).iter.zip (fwht b k).iter |>.map fun (x, y) => x * y).toInt32Array
  let n := (1 <<< k.toNat : Nat).toInt32
  ((fwht p k).iter.map (· / n)).toInt32Array

/-- The XOR convolution, straight from the definition. -/
def xorConvSpec (a b : Int32Array) : Int32Array :=
  .ofFn (n := a.size) fun i => Id.run do
    let mut s := 0
    for j in 0...a.size do
      s := s + a[j]! * b[i.val ^^^ j]!
    return s

#guard xorConv (.mk #[1, 2, 3, 4]) (.mk #[5, 6, 7, 8]) 2 ==
  xorConvSpec (.mk #[1, 2, 3, 4]) (.mk #[5, 6, 7, 8])
#guard xorConv test (fwht test 6) 6 == xorConvSpec test (fwht test 6)

end Hadamard
