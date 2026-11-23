/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import ScalarArray
import ScalarArray.Notation
meta import ScalarArray

/-!
# Tutorial

A short walk through the library on `UInt32Array`, from building arrays to proving that a loop
does what it should. Every other array type has the same API with its own element type in place of
`UInt32`: `Int16Array` of `Int16`, `Float32Array` of `Float32`, and so on.

Each `#guard` is checked when the file is built. In a `module`, `#guard` and `#eval` run code at
compile time, so they need `meta import ScalarArray` as well as `import ScalarArray`.
-/

open ScalarArray

/-! ## Building and reading

An array is built from an `Array`, a list or a function, or by pushing elements one at a time.
`a[i]` needs a proof that `i` is in bounds; `a[i]?` and `a[i]!` don't.
-/

#guard (UInt32Array.mk #[1, 2, 3]).toList == [1, 2, 3]
#guard [1, 2, 3].toUInt32Array == UInt32Array.mk #[1, 2, 3]
#guard (UInt32Array.ofFn (n := 4) fun i => i.val.toUInt32 * 10).toList == [0, 10, 20, 30]

/-- The squares `0, 1, 4, …, (n - 1) ^ 2`, with room for all of them reserved up front. -/
def squares (n : Nat) : UInt32Array := Id.run do
  let mut a := UInt32Array.emptyWithCapacity n
  for i in 0...n do
    a := a.push (i * i).toUInt32
  return a

#guard (squares 5).toList == [0, 1, 4, 9, 16]
#guard (squares 5)[3]! == 9
#guard (squares 5)[7]? == none

-- Folds, `for` loops and searches read the elements directly, without building an `Array`.
#guard (squares 5).foldl (· + ·) 0 == 30
#guard (squares 5).any (· > 10)
#guard (squares 5).findIdx? (· > 5) == some 3

/-! ## Writing and sharing

Writes such as `set!` and `push` change the array in place when it is not shared, and copy it first
when it is, just like `Array`. So a value that is still in use never changes.
-/

#guard
  let a := squares 4
  let b := a.set! 0 100
  a.toList == [0, 1, 4, 9] && b.toList == [100, 1, 4, 9]

#guard (squares 2 ++ squares 3).toList == [0, 1, 0, 1, 4]
#guard ((squares 5).popWhile (· > 3)).toList == [0, 1]

/-! ## Slices

`a[i...j]` is the slice of `a` from `i` up to `j - 1`. Taking a slice never copies, and an array
coerces to its whole slice, so functions on slices take arrays too. There is no coercion back:
`Slice.copy` makes a new array, and `Slice.array` gives back the whole underlying array.

Slices can be written to. When neither the slice nor its array is shared, the writes go into the
array itself.
-/

#guard (squares 6)[2...5].toList == [4, 9, 16]
#guard (squares 6)[3...*].copy.toList == [9, 16, 25]

/-- The sum of a slice. -/
def sum (s : UInt32Array.Slice) : UInt32 := s.foldl (· + ·) 0

#guard sum (squares 6)[2...5] == 29
#guard sum (squares 4) == 14

-- Reverses the middle of the array, in place.
#guard (squares 5)[1...4].reverse.array.toList == [0, 9, 4, 1, 16]

/-! ## Iterators

`a.iter` and `s.iter` are `Std.Iterators` iterators, so their combinators cover what has no function
of its own here, and `toUInt32Array` collects the result into a new array.
-/

#guard ((squares 5).iter.map (· + 1)).toUInt32Array.toList == [1, 2, 5, 10, 17]
#guard ((squares 5).iter.filter (· % 2 == 0)).toUInt32Array.toList == [0, 4, 16]

/-! ## In-place loops

`ScalarArray.Notation`, which has to be imported on its own, adds `inplace a do …` for loops that
read and write `a` in place. Its index bounds are proved by the `inplace_bound` tactic from the
facts in context, here `h`. The value of the program is that of its `return`, where `a` is the
new array, here `(s, a)`, or the new array if it doesn't return.
-/

/-- Doubles the first `n` elements, and returns their old sum. -/
def doubleFirst (a : UInt32Array) (n : USize) (h : n.toNat ≤ a.size) : UInt32 × UInt32Array :=
  inplace a do
    for j in 0...n with (s := 0) do
      let x := a[j]
      s := s + x
      a[j] := 2 * x
    return (s, a)

#guard doubleFirst (.mk #[0, 1, 4, 9, 16]) 3 (by simp) == (5, UInt32Array.mk #[0, 2, 8, 9, 16])

/-! ## Proofs

Arrays have a model, `toArray : UInt32Array → Array UInt32`, and simp lemmas that say how each
operation changes the size and the elements.
-/

example (a : UInt32Array) (x : UInt32) : (a.push x).size = a.size + 1 := by simp

example (a : UInt32Array) (x : UInt32) : (a.push x)[a.size]! = x := by simp

example (a b : UInt32Array) : (a ++ b).toList = a.toList ++ b.toList := by simp

/-!
A loop is proved correct in two steps. First, `Tail.run_forInFrom_modify` turns a loop of the form
`for j in lo...hi do a[e j] := g a[e j]` into its specification, `modifyAt`, a function that does
the same updates one index at a time. Then the lemmas about `modifyAt` give the elements.
-/

/-- Doubles the first `n` elements. -/
def double (a : UInt32Array) (n : USize) (h : n.toNat ≤ a.size) : UInt32Array :=
  inplace a do
    for j in 0...n do
      a[j] := 2 * a[j]

#guard double (.mk #[0, 1, 4, 9, 16]) 3 (by simp) == UInt32Array.mk #[0, 2, 8, 9, 16]

theorem double_eq (a : UInt32Array) (n : USize) (h : n.toNat ≤ a.size) :
    double a n h = a.modifyAt id 0 n.toNat fun _ v => 2 * v := by
  simp only [double, UInt32Array.runInPlaceThenOf_eq, UInt32Array.InPlace.Tail.forIn_eq]
  rw [UInt32Array.InPlace.Tail.run_forInFrom_modify (idx := id) (G := fun _ v => 2 * v)
    (he := fun _ _ _ => rfl) (hg := fun _ _ _ _ => rfl)]
  simp

theorem getElem_double (a : UInt32Array) (n : USize) (h : n.toNat ≤ a.size) (i : Nat)
    (hi : i < n.toNat) : (double a n h)[i]'(by simp [double_eq]; lia) = 2 * a[i]'(by lia) := by
  simp only [double_eq]
  exact UInt32Array.getElem_modifyAt_idx a id _ (fun _ _ _ _ _ _ e => e) (Nat.zero_le _) hi _

theorem getElem_double_of_le (a : UInt32Array) (n : USize) (h : n.toNat ≤ a.size) (i : Nat)
    (hi : n.toNat ≤ i) (hia : i < a.size) :
    (double a n h)[i]'(by simp [double_eq, hia]) = a[i] := by
  simp only [double_eq]
  exact UInt32Array.getElem_modifyAt_of_forall_ne a id _ (fun _ _ hj => by simp; lia) _
