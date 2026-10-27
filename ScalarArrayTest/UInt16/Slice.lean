/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import ScalarArray.UInt16
import ScalarArrayTest.Util
meta import ScalarArray.UInt16
meta import ScalarArrayTest.Util

open ScalarArray ScalarArrayTest

/-!
Tests for `UInt16Array`: slices, their API and iterators.
-/

/-- A test value at the edge of the element type's range. -/
private abbrev big : UInt16 := 65535

/-- The size of an element in bytes. -/
private abbrev elemSize : UInt32 := 2

/-! Slices -/

#guard
  let a := UInt16Array.mk #[1, 2, 3, big]
  let s := a[1...3]
  s.size == 2 && s[0]! == 2 && s[1]! == 3 && s.getD 2 7 == 7 && s.copy == UInt16Array.mk #[2, 3] &&
    s.toList == [2, 3] && s.toArray == #[2, 3]

#guard
  let a := UInt16Array.mk #[1, 2, 3, big]
  a[1...=3].toList == [2, 3, big] && a[*...2].toList == [1, 2] && a[2...*].toList == [3, big] &&
    a[*...*].toList == [1, 2, 3, big] && a[0<...2].toList == [2] &&
    a[0<...=2].toList == [2, 3] && a[*...=1].toList == [1, 2] && a[1<...*].toList == [3, big]

-- Bounds are clamped.
#guard
  let a := UInt16Array.mk #[1, 2, 3, big]
  a[2...100].toList == [3, big] && a[3...1].size == 0 && a[9...12].size == 0 &&
    (a.toSlice 1 (2 ^ 70)).toList == [2, 3, big]

-- Slices of slices.
#guard
  let s := (UInt16Array.mk #[1, 2, 3, big])[1...4]
  s[1...2].toList == [3] && s[0...100].toList == [2, 3, big] && s[*...*].toList == [2, 3, big] &&
    s[2...*].toList == [big] && s[5...6].size == 0

#guard
  let s := (UInt16Array.mk #[1, 2, 3, big])[1...4]
  s.popFront.toList == [3, big] && s.popFront.popFront.popFront.popFront.size == 0

#guard (∅ : UInt16Array.Slice).size == 0 && (default : UInt16Array.Slice).toList == []

-- An array coerces to the slice of all its elements.
#guard
  let s : UInt16Array.Slice := UInt16Array.mk #[1, 2, big]
  s.toList == [1, 2, big] && s.start == 0

-- A slice does not coerce back to an array, since that would copy.
example (s : UInt16Array.Slice) : UInt16Array := s.copy

#guard Id.run do
  let mut r : List UInt16 := []
  for x in (UInt16Array.mk #[1, 2, 3, big])[1...*] do
    r := x :: r
  return r == [big, 3, 2]

#guard (UInt16Array.mk #[1, 2, 3, big])[1...*].foldl (fun acc x => x :: acc) [] == [big, 3, 2]

#guard
  let xs := (Array.range 100000).map Nat.toUInt16
  let s := (UInt16Array.mk xs)[70000...70010]
  s.toArray == xs.extract 70000 70010 && s.copy.toArray == xs.extract 70000 70010

#guard toString (UInt16Array.mk #[1, 2, 3])[1...*] == toString (UInt16Array.mk #[2, 3])

-- Taking a slice doesn't copy the array.
@[noinline] def UInt16Array.slicesWithoutCopying (x : UInt16) : Bool :=
  let a := UInt16Array.mk #[x, 2, 3]
  let p := rawAddr a
  rawAddr a[1...2].array == p

#guard UInt16Array.slicesWithoutCopying 1

example (s : UInt16Array.Slice) : s.copy.size = s.size := by simp

/-! Slice API -/

#guard
  let s := (UInt16Array.mk #[1, 2, 3, big, 2])[1...5]
  s.foldr (fun x acc => x :: acc) [] == [2, 3, big, 2] &&
    s.foldl (fun acc x => x :: acc) [] == [2, big, 3, 2] &&
    s.any (· == big) && !s.any (· == 1) && s.all (· != 1) && !s.all (· == 2) &&
    s.contains big && !s.contains 1 && s.count (· == 2) == 2 &&
    s.find? (· > 2) == some 3 && s.findRev? (· != big) == some 2 && s.findRev? (· == 1) == none

#guard (UInt16Array.mk #[1, 2, 3])[1...1].foldr (fun x acc => x :: acc) [] == []
#guard (UInt16Array.mk #[1, 2, 3])[3...*].find? (fun _ => true) == none

#guard
  let s := (UInt16Array.mk #[1, 2, 3, big])[1...*]
  let r : StateM (List UInt16) Unit := s.forRevM fun x => modify (x :: ·)
  (r.run []).2 == [2, 3, big]

#guard Id.run ((UInt16Array.mk #[1, 2, big])[*...*].findSomeRevM?
  (fun x => pure (if x == 2 then some x else none))) == some 2

-- The loops over slices stay within the slice, both with `start > 0` and with `stop < size`.
#guard
  let s := (UInt16Array.mk #[big, 1, 2, 3, big])[1...4]
  s.foldr (fun x acc => x :: acc) [] == [1, 2, 3] &&
    s.foldl (fun acc x => x :: acc) [] == [3, 2, 1] && s.toList == [1, 2, 3] &&
    !s.any (· == big) && s.all (· != big) && !s.contains big && s.count (· != big) == 3 &&
    s.find? (· == big) == none && s.findRev? (· == big) == none &&
    s.find? (· != 1) == some 2 && s.findRev? (· != 3) == some 2

#guard Id.run do
  let mut r : List UInt16 := []
  for x in (UInt16Array.mk #[big, 1, 2, 3, big])[1...4] do
    r := x :: r
  return r == [3, 2, 1]

-- Early exits.
#guard Id.run do
  let mut r : List UInt16 := []
  for x in (UInt16Array.mk #[big, 1, 2, 3, big])[1...5] do
    if x == 3 then break
    r := x :: r
  return r == [2, 1]

#guard
  let s := (UInt16Array.mk #[1, 2, big, 3, big])[1...5]
  s.any (· == big) && !s.all (· != big) && s.find? (· == big) == some big &&
    s.find? (· != 2) == some big && s.findRev? (· == big) == some big &&
    s.findRev? (· != big) == some 3

-- Empty slices.
#guard
  let s := (UInt16Array.mk #[1, 2, 3])[1...1]
  s.foldl (fun acc x => x :: acc) [] == [] && s.toList == [] && !s.any (fun _ => true) &&
    s.all (fun _ => false) && s.count (fun _ => true) == 0 && s.find? (fun _ => true) == none &&
    s.findRev? (fun _ => true) == none && Id.run do
      let mut r : List UInt16 := []
      for x in s do
        r := x :: r
      return r == []
#guard
  let s := (∅ : UInt16Array.Slice)
  s.foldr (fun x acc => x :: acc) [] == [] && s.foldl (fun acc x => x :: acc) [] == [] &&
    !s.any (fun _ => true)

-- Loops in a monad other than `Id`.
#guard
  let r : StateM (List UInt16) Unit := do
    for x in (UInt16Array.mk #[big, 1, 2, 3, big])[1...5] do
      if x == 3 then break
      modify (x :: ·)
  (r.run []).2 == [2, 1]
#guard
  let s := (UInt16Array.mk #[big, 1, 2, 3, big])[1...4]
  let r : StateM (List UInt16) Unit := s.foldrM (fun x _ => modify (x :: ·)) ⟨⟩
  (r.run []).2 == [1, 2, 3]
#guard
  let s := (UInt16Array.mk #[big, 1, 2, 3, big])[1...4]
  let r : StateM (List UInt16) Unit := s.foldlM (fun _ x => modify (x :: ·)) ⟨⟩
  (r.run []).2 == [3, 2, 1]
#guard (UInt16Array.mk #[big, 1, 2, 3, big])[1...4].foldlM (m := Option)
  (fun acc x => if x == 2 then none else some (x :: acc)) [] == none
#guard (UInt16Array.mk #[big, 1, 2, 3, big])[1...4].foldrM (m := Option)
  (fun x acc => if x == 2 then none else some (x :: acc)) [] == none
#guard (UInt16Array.mk #[big, 1, 2, 3, big])[1...4].foldlM (m := Option)
  (fun acc x => some (x :: acc)) [] == some [3, 2, 1]
#guard (UInt16Array.mk #[big, 1, 2, 3, big])[1...4].findSomeRevM? (m := Option)
  (fun x => if x == 3 then some none else some (some x)) == some (some 2)
#guard
  let xs := (Array.range 100000).map Nat.toUInt16
  let s := (UInt16Array.mk xs)[100...99900]
  let f := fun (acc : List UInt16) x => if x == 0 then x :: acc else acc
  s.foldl f [] == (xs.extract 100 99900).foldl f [] &&
    s.foldr (fun x acc => f acc x) [] == (xs.extract 100 99900).foldr (fun x acc => f acc x) []

/-! The `Std.Iterators` API on arrays and slices -/

#guard (UInt16Array.mk #[1, 2, 3]).iter.toList == [1, 2, 3]
#guard ((UInt16Array.mk #[1, 2, 3]).iter.map (· * 2)).toUInt16Array == UInt16Array.mk #[2, 4, 6]
#guard ((UInt16Array.mk #[1, 2, 3, big]).iter.filter (· != 2)).toUInt16Array ==
  UInt16Array.mk #[1, 3, big]
#guard ((UInt16Array.mk #[1, 2, 3, big]).iter.take 2).toUInt16Array == UInt16Array.mk #[1, 2]
#guard ((UInt16Array.mk #[1, 2, 3, big]).iter.drop 2).toUInt16Array == UInt16Array.mk #[3, big]
#guard (((UInt16Array.mk #[1, 2, 3]).iter.zip (UInt16Array.mk #[big, 5]).iter).map
  fun (x, y) => x + y).toUInt16Array == UInt16Array.mk #[1 + big, 7]
#guard ((UInt16Array.mk #[1, 2, 3, big])[1...3].iter.map (· + 1)).toUInt16Array ==
  UInt16Array.mk #[3, 4]
#guard (UInt16Array.mk #[1, 2, 3]).iter.length == 3
#guard UInt16Array.empty.iter.toUInt16Array == UInt16Array.empty
#guard
  let xs := (Array.range 100000).map Nat.toUInt16
  ((UInt16Array.mk xs).iter.map (· + 1)).toUInt16Array.toArray == xs.map (· + 1)
#guard rawElemSize ((UInt16Array.mk #[1]).iter.toUInt16Array) == elemSize
#guard (UInt16Array.mk #[1, 2, 3]).iter.toUInt16ArrayWithCapacity 100 ==
  UInt16Array.mk #[1, 2, 3]
#guard rawCapacity ((UInt16Array.mk #[1, 2, 3]).iter.toUInt16ArrayWithCapacity 100) ≥ 100

/-! Membership, `ForM` and slice equality -/

#guard
  let a := UInt16Array.mk #[1, 2, big]
  let r : StateM (List UInt16) PUnit := forM a fun x => modify (x :: ·)
  (r.run []).2 == [big, 2, 1]
#guard
  let s := (UInt16Array.mk #[0, 1, 2, big])[1...3]
  let r : StateM (List UInt16) PUnit := forM s fun x => modify (x :: ·)
  (r.run []).2 == [2, 1]
#guard
  let r : StateM (List UInt16) PUnit := forM UInt16Array.empty fun x => modify (x :: ·)
  (r.run []).2 == []
#guard (UInt16Array.mk #[0, 1, 2, big])[1...3] == (UInt16Array.mk #[1, 2, 5])[0...2]
#guard (UInt16Array.mk #[1, big, 1, big])[0...2] == (UInt16Array.mk #[1, big, 1, big])[2...4]
#guard (UInt16Array.mk #[0, 1, 2, big])[1...3] != (UInt16Array.mk #[1, 2, 5])[0...3]
#guard (UInt16Array.mk #[0, 1, 2, big])[1...3] != (UInt16Array.mk #[1, big])[0...2]
#guard (UInt16Array.mk #[0, 1, 2, big])[1...3] != (UInt16Array.mk #[2, 1])[0...2]
#guard (∅ : UInt16Array.Slice) == (UInt16Array.mk #[1, 2])[1...1]
#guard (UInt16Array.mk #[1, 2, big] : UInt16Array.Slice) ==
  (UInt16Array.mk #[0, 1, 2, big])[1...*]
#guard
  let xs := (Array.range 100000).map Nat.toUInt16
  (UInt16Array.mk (#[0] ++ xs))[1...*] == (UInt16Array.mk (xs ++ #[0]))[0...100000] &&
    (UInt16Array.mk (#[0] ++ xs))[1...*] != (UInt16Array.mk (xs.set! 99999 0))[0...100000]
