/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import ScalarArray.Int16
import ScalarArrayTest.Util
meta import ScalarArray.Int16
meta import ScalarArrayTest.Util

open ScalarArray ScalarArrayTest

/-!
Tests for `Int16Array`: printing, equality, iteration, removing elements, building arrays and
search.
-/

/-- A test value at the edge of the element type's range. -/
private abbrev big : Int16 := -32768

/-- The size of an element in bytes. -/
private abbrev elemSize : UInt32 := 2

/-! Printing -/

#guard toString (Int16Array.mk #[1, 2]) == "Int16Array.mk " ++ toString #[(1 : Int16), 2]
#guard reprStr (Int16Array.mk #[1, 2]) ==
  "ScalarArray.Int16Array.mk " ++ reprStr #[(1 : Int16), 2]
#guard reprStr (some (Int16Array.mk #[1, 2])) ==
  "some (ScalarArray.Int16Array.mk " ++ reprStr #[(1 : Int16), 2] ++ ")"
#guard reprStr (Int16Array.mk #[1, 2, 3])[1...2] ==
  "(ScalarArray.Int16Array.mk " ++ reprStr #[(1 : Int16), 2, 3] ++ ")[1...2]"
#guard reprStr (some (Int16Array.mk #[1, 2, 3])[1...2]) ==
  "some (ScalarArray.Int16Array.mk " ++ reprStr #[(1 : Int16), 2, 3] ++ ")[1...2]"

-- What `repr` prints evaluates to the input, also as an argument.
#guard ScalarArray.Int16Array.mk #[1, 2] == Int16Array.mk #[1, 2]
#guard (some (ScalarArray.Int16Array.mk #[1, 2])) == some (Int16Array.mk #[1, 2])
#guard
  let s := (ScalarArray.Int16Array.mk #[1, 2, 3])[1...2]
  s.array == Int16Array.mk #[1, 2, 3] && s.start == 1 && s.stop == 2
#guard
  let s? := some (ScalarArray.Int16Array.mk #[1, 2, 3])[1...2]
  s?.map (fun s => (s.array.toArray, s.start, s.stop)) == some (#[1, 2, 3], 1, 2)

/-! Equality -/

#guard Int16Array.mk #[1, 2, big] == Int16Array.mk #[1, 2, big]
#guard Int16Array.mk #[1, 2, big] != Int16Array.mk #[1, 2, 0]
#guard Int16Array.mk #[1, 2] != Int16Array.mk #[1, 2, 0]
#guard Int16Array.mk #[1, 2, 0] != Int16Array.mk #[1, 2]
#guard Int16Array.empty == Int16Array.emptyWithCapacity 10
#guard (Int16Array.mk #[1, 2] ++ Int16Array.mk #[big]) == Int16Array.mk #[1, 2, big]
-- Capacity and leftover memory past the size don't matter.
#guard (Int16Array.emptyWithCapacity 100).push 1 == Int16Array.mk #[1]
#guard (Int16Array.mk #[1, 2, 3]).pop == Int16Array.mk #[1, 2]
#guard (Int16Array.mk (Array.replicate 100000 0)).set! 99999 big !=
  Int16Array.mk (Array.replicate 100000 0)

/-! Iteration -/

#guard (Int16Array.mk #[1, 2, big]).foldl (fun acc x => x :: acc) [] == [big, 2, 1]
#guard (Int16Array.mk #[1, 2, big]).foldr (fun x acc => x :: acc) [] == [1, 2, big]
#guard Int16Array.empty.foldl (fun acc x => x :: acc) [] == []
#guard Int16Array.empty.foldr (fun x acc => x :: acc) [] == []
#guard (Int16Array.mk #[1, 2, big]).foldlM (m := Option)
  (fun acc x => if x == 2 then none else some (x :: acc)) [] == none
#guard (Int16Array.mk #[1, big]).foldrM (m := Option) (fun x acc => some (x :: acc)) [] ==
  some [1, big]

#guard Id.run do
  let mut r : List Int16 := []
  for x in Int16Array.mk #[1, 2, big] do
    r := x :: r
  return r == [big, 2, 1]

#guard Id.run do
  let mut r : List Int16 := []
  for x in Int16Array.mk #[1, 2, 3, 4] do
    if x == 3 then break
    r := x :: r
  return r == [2, 1]

#guard
  let r : StateM (List Int16) Unit := (Int16Array.mk #[1, 2, big]).forM fun x => modify (x :: ·)
  (r.run []).2 == [big, 2, 1]

#guard
  let xs := (Array.range 100000).map Nat.toInt16
  let f := fun (acc : List Int16) x => if x == 0 then x :: acc else acc
  (Int16Array.mk xs).foldl f [] == xs.foldl f []

#guard (Int16Array.mk #[1, 2, big]).any (· == big)
#guard !(Int16Array.mk #[1, 2, 3]).any (· == big)
#guard (Int16Array.mk #[1, 2, 3]).all (· != big)
#guard !(Int16Array.mk #[1, big, 3]).all (· != big)
#guard !Int16Array.empty.any (fun _ => true) && Int16Array.empty.all (fun _ => false)
#guard (Int16Array.mk #[1, 2, big]).contains big
#guard !(Int16Array.mk #[1, 2, 3]).contains big && !Int16Array.empty.contains big

-- Early exits, and loops in a monad other than `Id`.
#guard (Int16Array.mk #[1, 2, big]).foldrM (m := Option)
  (fun x acc => if x == 1 then none else some (x :: acc)) [] == none
#guard (Int16Array.mk #[big, 2, 1]).foldrM (m := Option)
  (fun x acc => if x == big then none else some (x :: acc)) [] == none
#guard
  let r : StateM (List Int16) Unit := do
    for x in Int16Array.mk #[1, 2, big, 3] do
      if x == big then break
      modify (x :: ·)
  (r.run []).2 == [2, 1]
#guard
  let r : StateM (List Int16) Unit :=
    (Int16Array.mk #[1, 2, big]).foldrM (fun x _ => modify (x :: ·)) ⟨⟩
  (r.run []).2 == [1, 2, big]
#guard Id.run do
  let mut r : List Int16 := []
  for x in Int16Array.empty do
    r := x :: r
  return r == []
#guard !(Int16Array.mk #[1, 2, 3]).contains big
#guard (Int16Array.mk (Array.replicate 100000 0) |>.set! 99999 big).contains big

/-! Removing elements -/

#guard Int16Array.empty.isEmpty && !(Int16Array.mk #[1]).isEmpty
#guard (Int16Array.mk #[1]).pop.isEmpty
#guard (Int16Array.mk #[1, 2, big]).pop.toArray == #[1, 2]
#guard Int16Array.empty.pop.toArray == #[]
#guard ((Int16Array.mk #[1, 2, 3]).pop.push big).toArray == #[1, 2, big]
#guard (Int16Array.mk #[1, 2, big]).back? == some big
#guard Int16Array.empty.back? == none
#guard (Int16Array.mk #[1, 2, big]).back! == big
#guard (Int16Array.mk #[1, 2, big]).back (by decide) == big

-- Popping from a shared array must leave the original unchanged.
#guard
  let a := Int16Array.mk #[1, 2, 3]
  let b := a.pop
  b.toArray == #[1, 2] && a.toArray == #[1, 2, 3]

-- The array is built from a parameter so that it isn't extracted as a shared closed term.
@[noinline] def Int16Array.popsInPlace (x : Int16) : Bool :=
  let a := (Int16Array.mk #[x]).push x
  let p := rawAddr a
  let a := a.pop
  rawAddr a == p && a.toArray == #[x]

#guard Int16Array.popsInPlace 1

#guard (Int16Array.mk #[1, 0, big, 0, 0]).popWhile (· == 0) == Int16Array.mk #[1, 0, big]
#guard (Int16Array.mk #[1, 0, big]).popWhile (· == 0) == Int16Array.mk #[1, 0, big]
#guard (Int16Array.mk #[0, 0]).popWhile (· == 0) == Int16Array.empty
#guard Int16Array.empty.popWhile (· == 0) == Int16Array.empty

-- Popping several elements from an exclusive array.
@[noinline] def Int16Array.popsWhileInPlace (x : Int16) : Bool :=
  let a := (Int16Array.mk #[x]).push 0 |>.push 0
  let p := rawAddr a
  let a := a.popWhile (· == 0)
  rawAddr a == p && a.toArray == #[x]

#guard Int16Array.popsWhileInPlace 1

example (p : Int16 → Bool) (a : Int16Array) :
    (a.popWhile p).toArray = a.toArray.popWhile p := by simp

#guard ((Int16Array.mk #[1, 2, 3, big]).extract 1 3).toArray == #[2, 3]
#guard ((Int16Array.mk #[1, 2, 3, big]).extract 2 100).toArray == #[3, big]
#guard ((Int16Array.mk #[1, 2, 3]).extract 0 3).toArray == #[1, 2, 3]
#guard ((Int16Array.mk #[1, 2, 3]).extract 2 1).toArray == #[]
#guard ((Int16Array.mk #[1, 2, 3]).extract 5 9).toArray == #[]
#guard ((Int16Array.mk #[1, 2, 3]).extract (2 ^ 70) (2 ^ 71)).toArray == #[]
#guard ((Int16Array.mk #[1, 2, 3]).extract 1 (2 ^ 70)).toArray == #[2, 3]
#guard
  let xs := (Array.range 100000).map Nat.toInt16
  ((Int16Array.mk xs).extract 70000 70010).toArray == xs.extract 70000 70010
#guard rawElemSize ((Int16Array.mk #[1, 2, 3]).extract 1 2) == elemSize

-- The extracted array is independent of the original.
#guard
  let a := Int16Array.mk #[1, 2, 3]
  let b := (a.extract 0 2).set! 0 big
  b.toArray == #[big, 2] && a.toArray == #[1, 2, 3]

/-! Building arrays -/

#guard (Int16Array.replicate 3 big).toArray == #[big, big, big]
#guard (Int16Array.replicate 0 1).toArray == #[]
#guard (Int16Array.replicate 100000 big).toArray == Array.replicate 100000 big
#guard (Int16Array.ofFn (n := 4) fun i => i.val.toInt16).toArray == #[0, 1, 2, 3]
#guard (Int16Array.ofFn (n := 0) fun i => i.val.toInt16).toArray == #[]
#guard rawElemSize (Int16Array.replicate 2 1) == elemSize
#guard rawElemSize (Int16Array.ofFn (n := 2) fun _ => 1) == elemSize

/-! Folds over part of an array -/

#guard (Int16Array.mk #[1, 2, 3, big]).foldl (fun acc x => x :: acc) [] 1 3 == [3, 2]
#guard (Int16Array.mk #[1, 2, 3, big]).foldl (fun acc x => x :: acc) [] 2 == [big, 3]
#guard (Int16Array.mk #[1, 2, 3, big]).foldl (fun acc x => x :: acc) [] 1 100 == [big, 3, 2]
#guard (Int16Array.mk #[1, 2, 3, big]).foldl (fun acc x => x :: acc) [] 3 1 == []
#guard (Int16Array.mk #[1, 2, 3, big]).foldl (fun acc x => x :: acc) [] 9 12 == []
#guard (Int16Array.mk #[1, 2, 3]).foldlM (m := Option)
  (fun acc x => if x == 1 then none else some (x :: acc)) [] 1 == some [3, 2]

/-! Linearity markers -/

#guard ((Int16Array.mk #[1, 2]).markLinear.push big).toArray == #[1, 2, big]
#guard ((Int16Array.mk #[1]).propagateMark (Int16Array.mk #[2, big])).toArray == #[2, big]

/-! Search -/

#guard (Int16Array.mk #[1, 2, big, 2]).findIdx? (· == 2) == some 1
#guard (Int16Array.mk #[1, 2, big, 2]).findIdx? (· == 2) 2 == some 3
#guard (Int16Array.mk #[1, 2, big, 2]).findIdx? (· == 3) == none
#guard (Int16Array.mk #[1, 2, big, 2]).findIdx? (· == 1) 9 == none
#guard ((Int16Array.mk #[1, 2, big, 2]).findFinIdx? (· == big)).map (·.val) == some 2
