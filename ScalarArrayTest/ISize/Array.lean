/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import ScalarArray.ISize
import ScalarArrayTest.Util
meta import ScalarArray.ISize
meta import ScalarArrayTest.Util

open ScalarArray ScalarArrayTest

/-!
Tests for `ISizeArray`: printing, equality, iteration, removing elements, building arrays and
search.
-/

/-- A test value at the edge of the element type's range. -/
private abbrev big : ISize := -9223372036854775808

/-- The size of an element in bytes. -/
private abbrev elemSize : UInt32 := (System.Platform.numBits / 8).toUInt32

/-! Printing -/

#guard toString (ISizeArray.mk #[1, 2]) == "ISizeArray.mk " ++ toString #[(1 : ISize), 2]
#guard reprStr (ISizeArray.mk #[1, 2]) ==
  "ScalarArray.ISizeArray.mk " ++ reprStr #[(1 : ISize), 2]
#guard reprStr (some (ISizeArray.mk #[1, 2])) ==
  "some (ScalarArray.ISizeArray.mk " ++ reprStr #[(1 : ISize), 2] ++ ")"
#guard reprStr (ISizeArray.mk #[1, 2, 3])[1...2] ==
  "(ScalarArray.ISizeArray.mk " ++ reprStr #[(1 : ISize), 2, 3] ++ ")[1...2]"
#guard reprStr (some (ISizeArray.mk #[1, 2, 3])[1...2]) ==
  "some (ScalarArray.ISizeArray.mk " ++ reprStr #[(1 : ISize), 2, 3] ++ ")[1...2]"

-- What `repr` prints evaluates to the input, also as an argument.
#guard ScalarArray.ISizeArray.mk #[1, 2] == ISizeArray.mk #[1, 2]
#guard (some (ScalarArray.ISizeArray.mk #[1, 2])) == some (ISizeArray.mk #[1, 2])
#guard
  let s := (ScalarArray.ISizeArray.mk #[1, 2, 3])[1...2]
  s.array == ISizeArray.mk #[1, 2, 3] && s.start == 1 && s.stop == 2
#guard
  let s? := some (ScalarArray.ISizeArray.mk #[1, 2, 3])[1...2]
  s?.map (fun s => (s.array.toArray, s.start, s.stop)) == some (#[1, 2, 3], 1, 2)

/-! Equality -/

#guard ISizeArray.mk #[1, 2, big] == ISizeArray.mk #[1, 2, big]
#guard ISizeArray.mk #[1, 2, big] != ISizeArray.mk #[1, 2, 0]
#guard ISizeArray.mk #[1, 2] != ISizeArray.mk #[1, 2, 0]
#guard ISizeArray.mk #[1, 2, 0] != ISizeArray.mk #[1, 2]
#guard ISizeArray.empty == ISizeArray.emptyWithCapacity 10
#guard (ISizeArray.mk #[1, 2] ++ ISizeArray.mk #[big]) == ISizeArray.mk #[1, 2, big]
-- Capacity and leftover memory past the size don't matter.
#guard (ISizeArray.emptyWithCapacity 100).push 1 == ISizeArray.mk #[1]
#guard (ISizeArray.mk #[1, 2, 3]).pop == ISizeArray.mk #[1, 2]
#guard (ISizeArray.mk (Array.replicate 100000 0)).set! 99999 big !=
  ISizeArray.mk (Array.replicate 100000 0)

/-! Iteration -/

#guard (ISizeArray.mk #[1, 2, big]).foldl (fun acc x => x :: acc) [] == [big, 2, 1]
#guard (ISizeArray.mk #[1, 2, big]).foldr (fun x acc => x :: acc) [] == [1, 2, big]
#guard ISizeArray.empty.foldl (fun acc x => x :: acc) [] == []
#guard ISizeArray.empty.foldr (fun x acc => x :: acc) [] == []
#guard (ISizeArray.mk #[1, 2, big]).foldlM (m := Option)
  (fun acc x => if x == 2 then none else some (x :: acc)) [] == none
#guard (ISizeArray.mk #[1, big]).foldrM (m := Option) (fun x acc => some (x :: acc)) [] ==
  some [1, big]

#guard Id.run do
  let mut r : List ISize := []
  for x in ISizeArray.mk #[1, 2, big] do
    r := x :: r
  return r == [big, 2, 1]

#guard Id.run do
  let mut r : List ISize := []
  for x in ISizeArray.mk #[1, 2, 3, 4] do
    if x == 3 then break
    r := x :: r
  return r == [2, 1]

#guard
  let r : StateM (List ISize) Unit := (ISizeArray.mk #[1, 2, big]).forM fun x => modify (x :: ·)
  (r.run []).2 == [big, 2, 1]

#guard
  let xs := (Array.range 100000).map Nat.toISize
  let f := fun (acc : List ISize) x => if x == 0 then x :: acc else acc
  (ISizeArray.mk xs).foldl f [] == xs.foldl f []

#guard (ISizeArray.mk #[1, 2, big]).any (· == big)
#guard !(ISizeArray.mk #[1, 2, 3]).any (· == big)
#guard (ISizeArray.mk #[1, 2, 3]).all (· != big)
#guard !(ISizeArray.mk #[1, big, 3]).all (· != big)
#guard !ISizeArray.empty.any (fun _ => true) && ISizeArray.empty.all (fun _ => false)
#guard (ISizeArray.mk #[1, 2, big]).contains big
#guard !(ISizeArray.mk #[1, 2, 3]).contains big && !ISizeArray.empty.contains big

-- Early exits, and loops in a monad other than `Id`.
#guard (ISizeArray.mk #[1, 2, big]).foldrM (m := Option)
  (fun x acc => if x == 1 then none else some (x :: acc)) [] == none
#guard (ISizeArray.mk #[big, 2, 1]).foldrM (m := Option)
  (fun x acc => if x == big then none else some (x :: acc)) [] == none
#guard
  let r : StateM (List ISize) Unit := do
    for x in ISizeArray.mk #[1, 2, big, 3] do
      if x == big then break
      modify (x :: ·)
  (r.run []).2 == [2, 1]
#guard
  let r : StateM (List ISize) Unit :=
    (ISizeArray.mk #[1, 2, big]).foldrM (fun x _ => modify (x :: ·)) ⟨⟩
  (r.run []).2 == [1, 2, big]
#guard Id.run do
  let mut r : List ISize := []
  for x in ISizeArray.empty do
    r := x :: r
  return r == []
#guard !(ISizeArray.mk #[1, 2, 3]).contains big
#guard (ISizeArray.mk (Array.replicate 100000 0) |>.set! 99999 big).contains big

/-! Removing elements -/

#guard ISizeArray.empty.isEmpty && !(ISizeArray.mk #[1]).isEmpty
#guard (ISizeArray.mk #[1]).pop.isEmpty
#guard (ISizeArray.mk #[1, 2, big]).pop.toArray == #[1, 2]
#guard ISizeArray.empty.pop.toArray == #[]
#guard ((ISizeArray.mk #[1, 2, 3]).pop.push big).toArray == #[1, 2, big]
#guard (ISizeArray.mk #[1, 2, big]).back? == some big
#guard ISizeArray.empty.back? == none
#guard (ISizeArray.mk #[1, 2, big]).back! == big
#guard (ISizeArray.mk #[1, 2, big]).back (by decide) == big

-- Popping from a shared array must leave the original unchanged.
#guard
  let a := ISizeArray.mk #[1, 2, 3]
  let b := a.pop
  b.toArray == #[1, 2] && a.toArray == #[1, 2, 3]

-- The array is built from a parameter so that it isn't extracted as a shared closed term.
@[noinline] def ISizeArray.popsInPlace (x : ISize) : Bool :=
  let a := (ISizeArray.mk #[x]).push x
  let p := rawAddr a
  let a := a.pop
  rawAddr a == p && a.toArray == #[x]

#guard ISizeArray.popsInPlace 1

#guard (ISizeArray.mk #[1, 0, big, 0, 0]).popWhile (· == 0) == ISizeArray.mk #[1, 0, big]
#guard (ISizeArray.mk #[1, 0, big]).popWhile (· == 0) == ISizeArray.mk #[1, 0, big]
#guard (ISizeArray.mk #[0, 0]).popWhile (· == 0) == ISizeArray.empty
#guard ISizeArray.empty.popWhile (· == 0) == ISizeArray.empty

-- Popping several elements from an exclusive array.
@[noinline] def ISizeArray.popsWhileInPlace (x : ISize) : Bool :=
  let a := (ISizeArray.mk #[x]).push 0 |>.push 0
  let p := rawAddr a
  let a := a.popWhile (· == 0)
  rawAddr a == p && a.toArray == #[x]

#guard ISizeArray.popsWhileInPlace 1

example (p : ISize → Bool) (a : ISizeArray) :
    (a.popWhile p).toArray = a.toArray.popWhile p := by simp

#guard ((ISizeArray.mk #[1, 2, 3, big]).extract 1 3).toArray == #[2, 3]
#guard ((ISizeArray.mk #[1, 2, 3, big]).extract 2 100).toArray == #[3, big]
#guard ((ISizeArray.mk #[1, 2, 3]).extract 0 3).toArray == #[1, 2, 3]
#guard ((ISizeArray.mk #[1, 2, 3]).extract 2 1).toArray == #[]
#guard ((ISizeArray.mk #[1, 2, 3]).extract 5 9).toArray == #[]
#guard ((ISizeArray.mk #[1, 2, 3]).extract (2 ^ 70) (2 ^ 71)).toArray == #[]
#guard ((ISizeArray.mk #[1, 2, 3]).extract 1 (2 ^ 70)).toArray == #[2, 3]
#guard
  let xs := (Array.range 100000).map Nat.toISize
  ((ISizeArray.mk xs).extract 70000 70010).toArray == xs.extract 70000 70010
#guard rawElemSize ((ISizeArray.mk #[1, 2, 3]).extract 1 2) == elemSize

-- The extracted array is independent of the original.
#guard
  let a := ISizeArray.mk #[1, 2, 3]
  let b := (a.extract 0 2).set! 0 big
  b.toArray == #[big, 2] && a.toArray == #[1, 2, 3]

/-! Building arrays -/

#guard (ISizeArray.replicate 3 big).toArray == #[big, big, big]
#guard (ISizeArray.replicate 0 1).toArray == #[]
#guard (ISizeArray.replicate 100000 big).toArray == Array.replicate 100000 big
#guard (ISizeArray.ofFn (n := 4) fun i => i.val.toISize).toArray == #[0, 1, 2, 3]
#guard (ISizeArray.ofFn (n := 0) fun i => i.val.toISize).toArray == #[]
#guard rawElemSize (ISizeArray.replicate 2 1) == elemSize
#guard rawElemSize (ISizeArray.ofFn (n := 2) fun _ => 1) == elemSize

/-! Folds over part of an array -/

#guard (ISizeArray.mk #[1, 2, 3, big]).foldl (fun acc x => x :: acc) [] 1 3 == [3, 2]
#guard (ISizeArray.mk #[1, 2, 3, big]).foldl (fun acc x => x :: acc) [] 2 == [big, 3]
#guard (ISizeArray.mk #[1, 2, 3, big]).foldl (fun acc x => x :: acc) [] 1 100 == [big, 3, 2]
#guard (ISizeArray.mk #[1, 2, 3, big]).foldl (fun acc x => x :: acc) [] 3 1 == []
#guard (ISizeArray.mk #[1, 2, 3, big]).foldl (fun acc x => x :: acc) [] 9 12 == []
#guard (ISizeArray.mk #[1, 2, 3]).foldlM (m := Option)
  (fun acc x => if x == 1 then none else some (x :: acc)) [] 1 == some [3, 2]

/-! Linearity markers -/

#guard ((ISizeArray.mk #[1, 2]).markLinear.push big).toArray == #[1, 2, big]
#guard ((ISizeArray.mk #[1]).propagateMark (ISizeArray.mk #[2, big])).toArray == #[2, big]

-- The mark goes on an exclusive array: a shared array is copied first and the copy is marked, and
-- an exclusive one is marked in place. The arrays are built from a parameter so that they aren't
-- extracted as shared closed terms.
@[noinline] def ISizeArray.marksCopyOfShared (x : ISize) : Bool :=
  let a := (ISizeArray.emptyWithCapacity 2).push x
  let b := a.markLinear
  rawAddr b != rawAddr a && b.toArray == #[x] && a.toArray == #[x]

@[noinline] def ISizeArray.marksExclusiveInPlace (x : ISize) : Bool :=
  let a := (ISizeArray.emptyWithCapacity 2).push x
  let p := rawAddr a
  let a := a.markLinear
  rawAddr a == p && a.toArray == #[x]

#guard ISizeArray.marksCopyOfShared 1
#guard ISizeArray.marksExclusiveInPlace 1

/-! Search -/

#guard (ISizeArray.mk #[1, 2, big, 2]).findIdx? (· == 2) == some 1
#guard (ISizeArray.mk #[1, 2, big, 2]).findIdx? (· == 2) 2 == some 3
#guard (ISizeArray.mk #[1, 2, big, 2]).findIdx? (· == 3) == none
#guard (ISizeArray.mk #[1, 2, big, 2]).findIdx? (· == 1) 9 == none
#guard ((ISizeArray.mk #[1, 2, big, 2]).findFinIdx? (· == big)).map (·.val) == some 2
