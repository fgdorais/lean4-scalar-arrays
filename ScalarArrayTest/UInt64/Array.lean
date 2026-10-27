/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import ScalarArray.UInt64
import ScalarArrayTest.Util
meta import ScalarArray.UInt64
meta import ScalarArrayTest.Util

open ScalarArray ScalarArrayTest

/-!
Tests for `UInt64Array`: printing, equality, iteration, removing elements, building arrays and
search.
-/

/-- A test value at the edge of the element type's range. -/
private abbrev big : UInt64 := 18446744073709551615

/-- The size of an element in bytes. -/
private abbrev elemSize : UInt32 := 8

/-! Printing -/

#guard toString (UInt64Array.mk #[1, 2]) == "UInt64Array.mk " ++ toString #[(1 : UInt64), 2]
#guard reprStr (UInt64Array.mk #[1, 2]) ==
  "ScalarArray.UInt64Array.mk " ++ reprStr #[(1 : UInt64), 2]
#guard reprStr (some (UInt64Array.mk #[1, 2])) ==
  "some (ScalarArray.UInt64Array.mk " ++ reprStr #[(1 : UInt64), 2] ++ ")"
#guard reprStr (UInt64Array.mk #[1, 2, 3])[1...2] ==
  "(ScalarArray.UInt64Array.mk " ++ reprStr #[(1 : UInt64), 2, 3] ++ ")[1...2]"
#guard reprStr (some (UInt64Array.mk #[1, 2, 3])[1...2]) ==
  "some (ScalarArray.UInt64Array.mk " ++ reprStr #[(1 : UInt64), 2, 3] ++ ")[1...2]"

-- What `repr` prints evaluates to the input, also as an argument.
#guard ScalarArray.UInt64Array.mk #[1, 2] == UInt64Array.mk #[1, 2]
#guard (some (ScalarArray.UInt64Array.mk #[1, 2])) == some (UInt64Array.mk #[1, 2])
#guard
  let s := (ScalarArray.UInt64Array.mk #[1, 2, 3])[1...2]
  s.array == UInt64Array.mk #[1, 2, 3] && s.start == 1 && s.stop == 2
#guard
  let s? := some (ScalarArray.UInt64Array.mk #[1, 2, 3])[1...2]
  s?.map (fun s => (s.array.toArray, s.start, s.stop)) == some (#[1, 2, 3], 1, 2)

/-! Equality -/

#guard UInt64Array.mk #[1, 2, big] == UInt64Array.mk #[1, 2, big]
#guard UInt64Array.mk #[1, 2, big] != UInt64Array.mk #[1, 2, 0]
#guard UInt64Array.mk #[1, 2] != UInt64Array.mk #[1, 2, 0]
#guard UInt64Array.mk #[1, 2, 0] != UInt64Array.mk #[1, 2]
#guard UInt64Array.empty == UInt64Array.emptyWithCapacity 10
#guard (UInt64Array.mk #[1, 2] ++ UInt64Array.mk #[big]) == UInt64Array.mk #[1, 2, big]
-- Capacity and leftover memory past the size don't matter.
#guard (UInt64Array.emptyWithCapacity 100).push 1 == UInt64Array.mk #[1]
#guard (UInt64Array.mk #[1, 2, 3]).pop == UInt64Array.mk #[1, 2]
#guard (UInt64Array.mk (Array.replicate 100000 0)).set! 99999 big !=
  UInt64Array.mk (Array.replicate 100000 0)

/-! Iteration -/

#guard (UInt64Array.mk #[1, 2, big]).foldl (fun acc x => x :: acc) [] == [big, 2, 1]
#guard (UInt64Array.mk #[1, 2, big]).foldr (fun x acc => x :: acc) [] == [1, 2, big]
#guard UInt64Array.empty.foldl (fun acc x => x :: acc) [] == []
#guard UInt64Array.empty.foldr (fun x acc => x :: acc) [] == []
#guard (UInt64Array.mk #[1, 2, big]).foldlM (m := Option)
  (fun acc x => if x == 2 then none else some (x :: acc)) [] == none
#guard (UInt64Array.mk #[1, big]).foldrM (m := Option) (fun x acc => some (x :: acc)) [] ==
  some [1, big]

#guard Id.run do
  let mut r : List UInt64 := []
  for x in UInt64Array.mk #[1, 2, big] do
    r := x :: r
  return r == [big, 2, 1]

#guard Id.run do
  let mut r : List UInt64 := []
  for x in UInt64Array.mk #[1, 2, 3, 4] do
    if x == 3 then break
    r := x :: r
  return r == [2, 1]

#guard
  let r : StateM (List UInt64) Unit := (UInt64Array.mk #[1, 2, big]).forM fun x => modify (x :: ·)
  (r.run []).2 == [big, 2, 1]

#guard
  let xs := (Array.range 100000).map Nat.toUInt64
  let f := fun (acc : List UInt64) x => if x == 0 then x :: acc else acc
  (UInt64Array.mk xs).foldl f [] == xs.foldl f []

#guard (UInt64Array.mk #[1, 2, big]).any (· == big)
#guard !(UInt64Array.mk #[1, 2, 3]).any (· == big)
#guard (UInt64Array.mk #[1, 2, 3]).all (· != big)
#guard !(UInt64Array.mk #[1, big, 3]).all (· != big)
#guard !UInt64Array.empty.any (fun _ => true) && UInt64Array.empty.all (fun _ => false)
#guard (UInt64Array.mk #[1, 2, big]).contains big
#guard !(UInt64Array.mk #[1, 2, 3]).contains big && !UInt64Array.empty.contains big

-- Early exits, and loops in a monad other than `Id`.
#guard (UInt64Array.mk #[1, 2, big]).foldrM (m := Option)
  (fun x acc => if x == 1 then none else some (x :: acc)) [] == none
#guard (UInt64Array.mk #[big, 2, 1]).foldrM (m := Option)
  (fun x acc => if x == big then none else some (x :: acc)) [] == none
#guard
  let r : StateM (List UInt64) Unit := do
    for x in UInt64Array.mk #[1, 2, big, 3] do
      if x == big then break
      modify (x :: ·)
  (r.run []).2 == [2, 1]
#guard
  let r : StateM (List UInt64) Unit :=
    (UInt64Array.mk #[1, 2, big]).foldrM (fun x _ => modify (x :: ·)) ⟨⟩
  (r.run []).2 == [1, 2, big]
#guard Id.run do
  let mut r : List UInt64 := []
  for x in UInt64Array.empty do
    r := x :: r
  return r == []
#guard !(UInt64Array.mk #[1, 2, 3]).contains big
#guard (UInt64Array.mk (Array.replicate 100000 0) |>.set! 99999 big).contains big

/-! Removing elements -/

#guard UInt64Array.empty.isEmpty && !(UInt64Array.mk #[1]).isEmpty
#guard (UInt64Array.mk #[1]).pop.isEmpty
#guard (UInt64Array.mk #[1, 2, big]).pop.toArray == #[1, 2]
#guard UInt64Array.empty.pop.toArray == #[]
#guard ((UInt64Array.mk #[1, 2, 3]).pop.push big).toArray == #[1, 2, big]
#guard (UInt64Array.mk #[1, 2, big]).back? == some big
#guard UInt64Array.empty.back? == none
#guard (UInt64Array.mk #[1, 2, big]).back! == big
#guard (UInt64Array.mk #[1, 2, big]).back (by decide) == big

-- Popping from a shared array must leave the original unchanged.
#guard
  let a := UInt64Array.mk #[1, 2, 3]
  let b := a.pop
  b.toArray == #[1, 2] && a.toArray == #[1, 2, 3]

-- The array is built from a parameter so that it isn't extracted as a shared closed term.
@[noinline] def UInt64Array.popsInPlace (x : UInt64) : Bool :=
  let a := (UInt64Array.mk #[x]).push x
  let p := rawAddr a
  let a := a.pop
  rawAddr a == p && a.toArray == #[x]

#guard UInt64Array.popsInPlace 1

#guard (UInt64Array.mk #[1, 0, big, 0, 0]).popWhile (· == 0) == UInt64Array.mk #[1, 0, big]
#guard (UInt64Array.mk #[1, 0, big]).popWhile (· == 0) == UInt64Array.mk #[1, 0, big]
#guard (UInt64Array.mk #[0, 0]).popWhile (· == 0) == UInt64Array.empty
#guard UInt64Array.empty.popWhile (· == 0) == UInt64Array.empty

-- Popping several elements from an exclusive array.
@[noinline] def UInt64Array.popsWhileInPlace (x : UInt64) : Bool :=
  let a := (UInt64Array.mk #[x]).push 0 |>.push 0
  let p := rawAddr a
  let a := a.popWhile (· == 0)
  rawAddr a == p && a.toArray == #[x]

#guard UInt64Array.popsWhileInPlace 1

example (p : UInt64 → Bool) (a : UInt64Array) :
    (a.popWhile p).toArray = a.toArray.popWhile p := by simp

#guard ((UInt64Array.mk #[1, 2, 3, big]).extract 1 3).toArray == #[2, 3]
#guard ((UInt64Array.mk #[1, 2, 3, big]).extract 2 100).toArray == #[3, big]
#guard ((UInt64Array.mk #[1, 2, 3]).extract 0 3).toArray == #[1, 2, 3]
#guard ((UInt64Array.mk #[1, 2, 3]).extract 2 1).toArray == #[]
#guard ((UInt64Array.mk #[1, 2, 3]).extract 5 9).toArray == #[]
#guard ((UInt64Array.mk #[1, 2, 3]).extract (2 ^ 70) (2 ^ 71)).toArray == #[]
#guard ((UInt64Array.mk #[1, 2, 3]).extract 1 (2 ^ 70)).toArray == #[2, 3]
#guard
  let xs := (Array.range 100000).map Nat.toUInt64
  ((UInt64Array.mk xs).extract 70000 70010).toArray == xs.extract 70000 70010
#guard rawElemSize ((UInt64Array.mk #[1, 2, 3]).extract 1 2) == elemSize

-- The extracted array is independent of the original.
#guard
  let a := UInt64Array.mk #[1, 2, 3]
  let b := (a.extract 0 2).set! 0 big
  b.toArray == #[big, 2] && a.toArray == #[1, 2, 3]

/-! Building arrays -/

#guard (UInt64Array.replicate 3 big).toArray == #[big, big, big]
#guard (UInt64Array.replicate 0 1).toArray == #[]
#guard (UInt64Array.replicate 100000 big).toArray == Array.replicate 100000 big
#guard (UInt64Array.ofFn (n := 4) fun i => i.val.toUInt64).toArray == #[0, 1, 2, 3]
#guard (UInt64Array.ofFn (n := 0) fun i => i.val.toUInt64).toArray == #[]
#guard rawElemSize (UInt64Array.replicate 2 1) == elemSize
#guard rawElemSize (UInt64Array.ofFn (n := 2) fun _ => 1) == elemSize

/-! Folds over part of an array -/

#guard (UInt64Array.mk #[1, 2, 3, big]).foldl (fun acc x => x :: acc) [] 1 3 == [3, 2]
#guard (UInt64Array.mk #[1, 2, 3, big]).foldl (fun acc x => x :: acc) [] 2 == [big, 3]
#guard (UInt64Array.mk #[1, 2, 3, big]).foldl (fun acc x => x :: acc) [] 1 100 == [big, 3, 2]
#guard (UInt64Array.mk #[1, 2, 3, big]).foldl (fun acc x => x :: acc) [] 3 1 == []
#guard (UInt64Array.mk #[1, 2, 3, big]).foldl (fun acc x => x :: acc) [] 9 12 == []
#guard (UInt64Array.mk #[1, 2, 3]).foldlM (m := Option)
  (fun acc x => if x == 1 then none else some (x :: acc)) [] 1 == some [3, 2]

/-! Linearity markers -/

#guard ((UInt64Array.mk #[1, 2]).markLinear.push big).toArray == #[1, 2, big]
#guard ((UInt64Array.mk #[1]).propagateMark (UInt64Array.mk #[2, big])).toArray == #[2, big]

-- The mark goes on an exclusive array: a shared array is copied first and the copy is marked, and
-- an exclusive one is marked in place. The arrays are built from a parameter so that they aren't
-- extracted as shared closed terms.
@[noinline] def UInt64Array.marksCopyOfShared (x : UInt64) : Bool :=
  let a := (UInt64Array.emptyWithCapacity 2).push x
  let b := a.markLinear
  rawAddr b != rawAddr a && b.toArray == #[x] && a.toArray == #[x]

@[noinline] def UInt64Array.marksExclusiveInPlace (x : UInt64) : Bool :=
  let a := (UInt64Array.emptyWithCapacity 2).push x
  let p := rawAddr a
  let a := a.markLinear
  rawAddr a == p && a.toArray == #[x]

#guard UInt64Array.marksCopyOfShared 1
#guard UInt64Array.marksExclusiveInPlace 1

/-! Search -/

#guard (UInt64Array.mk #[1, 2, big, 2]).findIdx? (· == 2) == some 1
#guard (UInt64Array.mk #[1, 2, big, 2]).findIdx? (· == 2) 2 == some 3
#guard (UInt64Array.mk #[1, 2, big, 2]).findIdx? (· == 3) == none
#guard (UInt64Array.mk #[1, 2, big, 2]).findIdx? (· == 1) 9 == none
#guard ((UInt64Array.mk #[1, 2, big, 2]).findFinIdx? (· == big)).map (·.val) == some 2
