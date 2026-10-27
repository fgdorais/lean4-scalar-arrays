/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import ScalarArray.USize
import ScalarArrayTest.Util
meta import ScalarArray.USize
meta import ScalarArrayTest.Util

open ScalarArray ScalarArrayTest

/-!
Tests for `USizeArray`: printing, equality, iteration, removing elements, building arrays and
search.
-/

/-- A test value at the edge of the element type's range. -/
private abbrev big : USize := 18446744073709551615

/-- The size of an element in bytes. -/
private abbrev elemSize : UInt32 := (System.Platform.numBits / 8).toUInt32

/-! Printing -/

#guard toString (USizeArray.mk #[1, 2]) == "USizeArray.mk " ++ toString #[(1 : USize), 2]
#guard reprStr (USizeArray.mk #[1, 2]) ==
  "ScalarArray.USizeArray.mk " ++ reprStr #[(1 : USize), 2]
#guard reprStr (some (USizeArray.mk #[1, 2])) ==
  "some (ScalarArray.USizeArray.mk " ++ reprStr #[(1 : USize), 2] ++ ")"
#guard reprStr (USizeArray.mk #[1, 2, 3])[1...2] ==
  "(ScalarArray.USizeArray.mk " ++ reprStr #[(1 : USize), 2, 3] ++ ")[1...2]"
#guard reprStr (some (USizeArray.mk #[1, 2, 3])[1...2]) ==
  "some (ScalarArray.USizeArray.mk " ++ reprStr #[(1 : USize), 2, 3] ++ ")[1...2]"

-- What `repr` prints evaluates to the input, also as an argument.
#guard ScalarArray.USizeArray.mk #[1, 2] == USizeArray.mk #[1, 2]
#guard (some (ScalarArray.USizeArray.mk #[1, 2])) == some (USizeArray.mk #[1, 2])
#guard
  let s := (ScalarArray.USizeArray.mk #[1, 2, 3])[1...2]
  s.array == USizeArray.mk #[1, 2, 3] && s.start == 1 && s.stop == 2
#guard
  let s? := some (ScalarArray.USizeArray.mk #[1, 2, 3])[1...2]
  s?.map (fun s => (s.array.toArray, s.start, s.stop)) == some (#[1, 2, 3], 1, 2)

/-! Equality -/

#guard USizeArray.mk #[1, 2, big] == USizeArray.mk #[1, 2, big]
#guard USizeArray.mk #[1, 2, big] != USizeArray.mk #[1, 2, 0]
#guard USizeArray.mk #[1, 2] != USizeArray.mk #[1, 2, 0]
#guard USizeArray.mk #[1, 2, 0] != USizeArray.mk #[1, 2]
#guard USizeArray.empty == USizeArray.emptyWithCapacity 10
#guard (USizeArray.mk #[1, 2] ++ USizeArray.mk #[big]) == USizeArray.mk #[1, 2, big]
-- Capacity and leftover memory past the size don't matter.
#guard (USizeArray.emptyWithCapacity 100).push 1 == USizeArray.mk #[1]
#guard (USizeArray.mk #[1, 2, 3]).pop == USizeArray.mk #[1, 2]
#guard (USizeArray.mk (Array.replicate 100000 0)).set! 99999 big !=
  USizeArray.mk (Array.replicate 100000 0)

/-! Iteration -/

#guard (USizeArray.mk #[1, 2, big]).foldl (fun acc x => x :: acc) [] == [big, 2, 1]
#guard (USizeArray.mk #[1, 2, big]).foldr (fun x acc => x :: acc) [] == [1, 2, big]
#guard USizeArray.empty.foldl (fun acc x => x :: acc) [] == []
#guard USizeArray.empty.foldr (fun x acc => x :: acc) [] == []
#guard (USizeArray.mk #[1, 2, big]).foldlM (m := Option)
  (fun acc x => if x == 2 then none else some (x :: acc)) [] == none
#guard (USizeArray.mk #[1, big]).foldrM (m := Option) (fun x acc => some (x :: acc)) [] ==
  some [1, big]

#guard Id.run do
  let mut r : List USize := []
  for x in USizeArray.mk #[1, 2, big] do
    r := x :: r
  return r == [big, 2, 1]

#guard Id.run do
  let mut r : List USize := []
  for x in USizeArray.mk #[1, 2, 3, 4] do
    if x == 3 then break
    r := x :: r
  return r == [2, 1]

#guard
  let r : StateM (List USize) Unit := (USizeArray.mk #[1, 2, big]).forM fun x => modify (x :: ·)
  (r.run []).2 == [big, 2, 1]

#guard
  let xs := (Array.range 100000).map Nat.toUSize
  let f := fun (acc : List USize) x => if x == 0 then x :: acc else acc
  (USizeArray.mk xs).foldl f [] == xs.foldl f []

#guard (USizeArray.mk #[1, 2, big]).any (· == big)
#guard !(USizeArray.mk #[1, 2, 3]).any (· == big)
#guard (USizeArray.mk #[1, 2, 3]).all (· != big)
#guard !(USizeArray.mk #[1, big, 3]).all (· != big)
#guard !USizeArray.empty.any (fun _ => true) && USizeArray.empty.all (fun _ => false)
#guard (USizeArray.mk #[1, 2, big]).contains big
#guard !(USizeArray.mk #[1, 2, 3]).contains big && !USizeArray.empty.contains big

-- Early exits, and loops in a monad other than `Id`.
#guard (USizeArray.mk #[1, 2, big]).foldrM (m := Option)
  (fun x acc => if x == 1 then none else some (x :: acc)) [] == none
#guard (USizeArray.mk #[big, 2, 1]).foldrM (m := Option)
  (fun x acc => if x == big then none else some (x :: acc)) [] == none
#guard
  let r : StateM (List USize) Unit := do
    for x in USizeArray.mk #[1, 2, big, 3] do
      if x == big then break
      modify (x :: ·)
  (r.run []).2 == [2, 1]
#guard
  let r : StateM (List USize) Unit :=
    (USizeArray.mk #[1, 2, big]).foldrM (fun x _ => modify (x :: ·)) ⟨⟩
  (r.run []).2 == [1, 2, big]
#guard Id.run do
  let mut r : List USize := []
  for x in USizeArray.empty do
    r := x :: r
  return r == []
#guard !(USizeArray.mk #[1, 2, 3]).contains big
#guard (USizeArray.mk (Array.replicate 100000 0) |>.set! 99999 big).contains big

/-! Removing elements -/

#guard USizeArray.empty.isEmpty && !(USizeArray.mk #[1]).isEmpty
#guard (USizeArray.mk #[1]).pop.isEmpty
#guard (USizeArray.mk #[1, 2, big]).pop.toArray == #[1, 2]
#guard USizeArray.empty.pop.toArray == #[]
#guard ((USizeArray.mk #[1, 2, 3]).pop.push big).toArray == #[1, 2, big]
#guard (USizeArray.mk #[1, 2, big]).back? == some big
#guard USizeArray.empty.back? == none
#guard (USizeArray.mk #[1, 2, big]).back! == big
#guard (USizeArray.mk #[1, 2, big]).back (by decide) == big

-- Popping from a shared array must leave the original unchanged.
#guard
  let a := USizeArray.mk #[1, 2, 3]
  let b := a.pop
  b.toArray == #[1, 2] && a.toArray == #[1, 2, 3]

-- The array is built from a parameter so that it isn't extracted as a shared closed term.
@[noinline] def USizeArray.popsInPlace (x : USize) : Bool :=
  let a := (USizeArray.mk #[x]).push x
  let p := rawAddr a
  let a := a.pop
  rawAddr a == p && a.toArray == #[x]

#guard USizeArray.popsInPlace 1

#guard (USizeArray.mk #[1, 0, big, 0, 0]).popWhile (· == 0) == USizeArray.mk #[1, 0, big]
#guard (USizeArray.mk #[1, 0, big]).popWhile (· == 0) == USizeArray.mk #[1, 0, big]
#guard (USizeArray.mk #[0, 0]).popWhile (· == 0) == USizeArray.empty
#guard USizeArray.empty.popWhile (· == 0) == USizeArray.empty

-- Popping several elements from an exclusive array.
@[noinline] def USizeArray.popsWhileInPlace (x : USize) : Bool :=
  let a := (USizeArray.mk #[x]).push 0 |>.push 0
  let p := rawAddr a
  let a := a.popWhile (· == 0)
  rawAddr a == p && a.toArray == #[x]

#guard USizeArray.popsWhileInPlace 1

example (p : USize → Bool) (a : USizeArray) :
    (a.popWhile p).toArray = a.toArray.popWhile p := by simp

#guard ((USizeArray.mk #[1, 2, 3, big]).extract 1 3).toArray == #[2, 3]
#guard ((USizeArray.mk #[1, 2, 3, big]).extract 2 100).toArray == #[3, big]
#guard ((USizeArray.mk #[1, 2, 3]).extract 0 3).toArray == #[1, 2, 3]
#guard ((USizeArray.mk #[1, 2, 3]).extract 2 1).toArray == #[]
#guard ((USizeArray.mk #[1, 2, 3]).extract 5 9).toArray == #[]
#guard ((USizeArray.mk #[1, 2, 3]).extract (2 ^ 70) (2 ^ 71)).toArray == #[]
#guard ((USizeArray.mk #[1, 2, 3]).extract 1 (2 ^ 70)).toArray == #[2, 3]
#guard
  let xs := (Array.range 100000).map Nat.toUSize
  ((USizeArray.mk xs).extract 70000 70010).toArray == xs.extract 70000 70010
#guard rawElemSize ((USizeArray.mk #[1, 2, 3]).extract 1 2) == elemSize

-- The extracted array is independent of the original.
#guard
  let a := USizeArray.mk #[1, 2, 3]
  let b := (a.extract 0 2).set! 0 big
  b.toArray == #[big, 2] && a.toArray == #[1, 2, 3]

/-! Building arrays -/

#guard (USizeArray.replicate 3 big).toArray == #[big, big, big]
#guard (USizeArray.replicate 0 1).toArray == #[]
#guard (USizeArray.replicate 100000 big).toArray == Array.replicate 100000 big
#guard (USizeArray.ofFn (n := 4) fun i => i.val.toUSize).toArray == #[0, 1, 2, 3]
#guard (USizeArray.ofFn (n := 0) fun i => i.val.toUSize).toArray == #[]
#guard rawElemSize (USizeArray.replicate 2 1) == elemSize
#guard rawElemSize (USizeArray.ofFn (n := 2) fun _ => 1) == elemSize

/-! Folds over part of an array -/

#guard (USizeArray.mk #[1, 2, 3, big]).foldl (fun acc x => x :: acc) [] 1 3 == [3, 2]
#guard (USizeArray.mk #[1, 2, 3, big]).foldl (fun acc x => x :: acc) [] 2 == [big, 3]
#guard (USizeArray.mk #[1, 2, 3, big]).foldl (fun acc x => x :: acc) [] 1 100 == [big, 3, 2]
#guard (USizeArray.mk #[1, 2, 3, big]).foldl (fun acc x => x :: acc) [] 3 1 == []
#guard (USizeArray.mk #[1, 2, 3, big]).foldl (fun acc x => x :: acc) [] 9 12 == []
#guard (USizeArray.mk #[1, 2, 3]).foldlM (m := Option)
  (fun acc x => if x == 1 then none else some (x :: acc)) [] 1 == some [3, 2]

/-! Linearity markers -/

#guard ((USizeArray.mk #[1, 2]).markLinear.push big).toArray == #[1, 2, big]
#guard ((USizeArray.mk #[1]).propagateMark (USizeArray.mk #[2, big])).toArray == #[2, big]

-- The mark goes on an exclusive array: a shared array is copied first and the copy is marked, and
-- an exclusive one is marked in place. The arrays are built from a parameter so that they aren't
-- extracted as shared closed terms.
@[noinline] def USizeArray.marksCopyOfShared (x : USize) : Bool :=
  let a := (USizeArray.emptyWithCapacity 2).push x
  let b := a.markLinear
  rawAddr b != rawAddr a && b.toArray == #[x] && a.toArray == #[x]

@[noinline] def USizeArray.marksExclusiveInPlace (x : USize) : Bool :=
  let a := (USizeArray.emptyWithCapacity 2).push x
  let p := rawAddr a
  let a := a.markLinear
  rawAddr a == p && a.toArray == #[x]

#guard USizeArray.marksCopyOfShared 1
#guard USizeArray.marksExclusiveInPlace 1

/-! Search -/

#guard (USizeArray.mk #[1, 2, big, 2]).findIdx? (· == 2) == some 1
#guard (USizeArray.mk #[1, 2, big, 2]).findIdx? (· == 2) 2 == some 3
#guard (USizeArray.mk #[1, 2, big, 2]).findIdx? (· == 3) == none
#guard (USizeArray.mk #[1, 2, big, 2]).findIdx? (· == 1) 9 == none
#guard ((USizeArray.mk #[1, 2, big, 2]).findFinIdx? (· == big)).map (·.val) == some 2
