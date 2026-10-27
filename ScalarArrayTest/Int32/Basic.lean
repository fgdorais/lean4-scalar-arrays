/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import ScalarArray.Int32
import ScalarArrayTest.Util
meta import ScalarArray.Int32
meta import ScalarArrayTest.Util

open ScalarArray ScalarArrayTest

/-!
Tests for `Int32Array`: construction, reads, writes, `push`, capacity, `append` and `copySlice`.
-/

/-- A test value at the edge of the element type's range. -/
private abbrev big : Int32 := -2147483648

/-- The size of an element in bytes. -/
private abbrev elemSize : UInt32 := 4

/-! Construction and conversion -/

#guard (Int32Array.mk #[1, 2, 3, big]).toArray == #[1, 2, 3, big]
#guard (Int32Array.mk #[1, 2, 3, big]).toList == [1, 2, 3, big]
#guard (Int32Array.mk #[]).toArray == #[]
#guard Int32Array.empty.toArray == #[]
#guard (∅ : Int32Array).toArray == #[]
#guard (default : Int32Array).toArray == #[]
#guard (Int32Array.emptyWithCapacity 100).toArray == #[]
#guard (Int32Array.mk (Array.range 1000 |>.map Nat.toInt32)).toArray ==
  (Array.range 1000).map Nat.toInt32

/-! Case analysis -/

-- `cases` splits an array as `mk a`, also in compiled code.
private def headOrZero (a : Int32Array) : Int32 := by
  cases a with | mk a => exact a[0]?.getD 0

#guard headOrZero (Int32Array.mk #[7, 8]) == 7
#guard headOrZero Int32Array.empty == 0

-- There is no constructor to match on, which would run `Array` code on a scalar array.
/--
error: Invalid `⟨...⟩` notation: The expected type `Quot fun x x_1 => False` is not an inductive type

Note: This notation can only be used when the expected type is an inductive type with a single constructor
-/
#guard_msgs in
example (a : Int32Array) : Int32 := match a with | ⟨a⟩ => a[0]!

/-! Size -/

#guard (Int32Array.mk #[1, 2, 3, big]).size == 4
#guard (Int32Array.mk #[1, 2, 3, big]).usize == 4
#guard Int32Array.empty.size == 0
#guard (Int32Array.emptyWithCapacity 100).size == 0

/-! Reading -/

#guard (Int32Array.mk #[1, 2, 3, big])[0] == 1
#guard (Int32Array.mk #[1, 2, 3, big])[3] == big
#guard (Int32Array.mk #[1, 2, 3, big])[(2 : USize)] == 3
#guard (Int32Array.mk #[1, 2, 3, big]).get! 1 == 2
#guard (Int32Array.mk #[1, 2, 3, big]).getD 2 7 == 3
#guard (Int32Array.mk #[1, 2, 3, big]).getD 4 7 == 7
#guard (Int32Array.mk #[1, 2, 3, big])[4]? == none
#guard (Int32Array.mk #[1, 2, 3, big])[1]? == some 2

/-! Writing -/

#guard ((Int32Array.mk #[1, 2, 3]).set 1 42 (by decide)).toArray == #[1, 42, 3]
#guard ((Int32Array.mk #[1, 2, 3]).uset 2 42 (by simp)).toArray == #[1, 2, 42]
#guard ((Int32Array.mk #[1, 2, 3]).set! 0 big).toArray == #[big, 2, 3]

-- Writing to a shared array must leave the original unchanged. The result is checked first so
-- that it is computed while the original is still live.
#guard
  let a := Int32Array.mk #[1, 2, 3]
  let b := a.set! 1 42
  b.toArray == #[1, 42, 3] && a.toArray == #[1, 2, 3]
#guard
  let a := Int32Array.mk #[1, 2, 3]
  let b := a.uset 0 big (by simp [a])
  b.toArray == #[big, 2, 3] && a.toArray == #[1, 2, 3]
#guard
  let a := Int32Array.mk #[1, 2, 3]
  let b := a.set 2 big (by simp [a])
  b.toArray == #[1, 2, big] && a.toArray == #[1, 2, 3]

-- Repeated writes to an exclusive array.
#guard Id.run do
  let mut a := Int32Array.mk (Array.replicate 1000 0)
  for i in [0:1000] do
    a := a.set! i (i * 3).toInt32
  return a.toArray == (Array.range 1000).map fun i => (i * 3).toInt32

/-! Pushing -/

#guard (Int32Array.empty.push 5 |>.push 6).toArray == #[5, 6]
#guard ((Int32Array.emptyWithCapacity 1).push 5 |>.push 6 |>.push 7).toArray == #[5, 6, 7]
#guard ((Int32Array.mk #[1, 2]).push 3).toArray == #[1, 2, 3]

-- Pushing past the capacity many times.
#guard Id.run do
  let mut a := Int32Array.empty
  for i in [0:10000] do
    a := a.push i.toInt32
  return a.size == 10000 && a.toArray == (Array.range 10000).map Nat.toInt32

-- Pushing to a shared array must leave the original unchanged. The results are checked first so
-- that they are computed while the original is still live.
#guard
  let a := (Int32Array.emptyWithCapacity 10).push 1
  let b := a.push 2
  let c := a.push 3
  c.toArray == #[1, 3] && b.toArray == #[1, 2] && a.toArray == #[1]

-- Inlined `push` and `uset` on a closed array must copy it on every call, not write into a shared
-- constant: a later call must not change an earlier result.
@[noinline] def Int32Array.pushOntoConstant (x : Int32) : Int32Array :=
  (Int32Array.emptyWithCapacity 10).push x

@[noinline] def Int32Array.usetConstant (x : Int32) : Int32Array :=
  (Int32Array.mk #[0, 0]).uset 0 x

#guard
  let a := Int32Array.pushOntoConstant 1
  let b := Int32Array.pushOntoConstant 2
  b.toArray == #[2] && a.toArray == #[1]

#guard
  let a := Int32Array.usetConstant 1
  let b := Int32Array.usetConstant 2
  b.toArray == #[2, 0] && a.toArray == #[1, 0]

/-! Every index, through both `Nat` and `USize` indices -/

#guard
  let a := Int32Array.mk ((Array.range 300).map Nat.toInt32)
  (List.range 300).all fun i =>
    a[i]! == i.toInt32 && a.getD i 0 == i.toInt32 && a.get! i == i.toInt32 &&
      (if h : i.toUSize.toNat < a.size then a[i.toUSize] == i.toInt32 else false)

/-! Writes don't touch neighbouring elements -/

#guard ((Int32Array.mk #[0, 0, 0]).set! 1 big).toArray == #[0, big, 0]
#guard ((Int32Array.mk #[big, big, big]).set! 1 0).toArray == #[big, 0, big]
#guard ((Int32Array.mk #[0, 0, 0]).push big |>.push 0).toArray == #[0, 0, 0, big, 0]

/-! Indices beyond 16 bits, and huge `Nat` indices -/

#guard
  let a := (Int32Array.mk (Array.replicate 100000 0)).set! 99999 big |>.set! 70000 1
  a.size == 100000 && a[99999]! == big && a[70000]! == 1 && a[99998]! == 0 &&
    a[70000 % 65536]! == 0 && a.toArray[99999]! == big && a.toArray[70000]! == 1 &&
    (if h : (70000 : USize).toNat < a.size then a[(70000 : USize)] == 1 else false)

#guard (Int32Array.mk #[1, 2, 3])[2 ^ 70]? == none
#guard (Int32Array.mk #[1, 2, 3]).getD (2 ^ 70) 7 == 7

/-! Pushing onto a shared array that is at full capacity -/

#guard
  let a := Int32Array.mk #[1]
  let b := a.push 2
  b.toArray == #[1, 2] && a.toArray == #[1]

#guard
  let a := Int32Array.mk #[]
  let b := a.push 2
  b.toArray == #[2] && a.toArray == #[]

/-! Conversions don't alias -/

#guard
  let a := #[(1 : Int32), 2, 3]
  let b := (Int32Array.mk a).set! 0 big
  b.toArray == #[big, 2, 3] && a == #[1, 2, 3]

#guard
  let a := Int32Array.mk #[1, 2, 3]
  let d := a.toArray.set! 0 big
  d == #[big, 2, 3] && a.toArray == #[1, 2, 3]

/-! Runtime representation -/

#guard rawElemSize (Int32Array.mk #[1, 2, 3]) == elemSize
#guard rawElemSize (Int32Array.emptyWithCapacity 10) == elemSize
#guard rawElemSize (Int32Array.empty.push 1) == elemSize
#guard rawElemSize ((Int32Array.mk #[1]).push 2) == elemSize
#guard rawCapacity (Int32Array.emptyWithCapacity 100) ≥ 100
#guard rawCapacity (Int32Array.mk #[1, 2, 3]) ≥ 3
-- Growth is geometric, so pushing is amortized constant time.
#guard rawCapacity ((Int32Array.mk #[1, 2, 3, 4]).push 5) ≥ 8


/-! Ensuring exclusivity and capacity -/

#guard (Int32Array.mk #[1, 2, 3]).ensureExclusive.toArray == #[1, 2, 3]
#guard ((Int32Array.mk #[1, 2, 3]).ensureCapacity 100).toArray == #[1, 2, 3]
#guard ((Int32Array.mk #[1, 2, 3]).ensureCapacity 0).toArray == #[1, 2, 3]
#guard ((Int32Array.mk #[1, 2, 3]).ensureExclusiveWithCapacity 100).toArray == #[1, 2, 3]
#guard ((Int32Array.mk #[1, 2, 3]).ensureExclusiveWithCapacity 0).toArray == #[1, 2, 3]

#guard rawCapacity ((Int32Array.mk #[1, 2, 3]).ensureCapacity 100) ≥ 100
#guard rawCapacity ((Int32Array.mk #[1, 2, 3]).ensureExclusiveWithCapacity 100) ≥ 100
-- A copy never has less room than the size.
#guard rawCapacity ((Int32Array.mk #[1, 2, 3]).ensureExclusiveWithCapacity 0) ≥ 3
#guard rawElemSize ((Int32Array.mk #[1, 2, 3]).ensureCapacity 100) == elemSize

-- The array is built from a parameter so that it isn't extracted as a shared closed term.
@[noinline] def Int32Array.ensuresInPlace (x : Int32) : Bool :=
  let a := (Int32Array.emptyWithCapacity 10).push x
  let p := rawAddr a
  let a := a.ensureExclusive.ensureCapacity 5 |>.ensureExclusiveWithCapacity 10
  rawAddr a == p && a.toArray == #[x]

-- Pushes after `ensureExclusiveWithCapacity` don't reallocate.
@[noinline] def Int32Array.pushesInPlaceAfterEnsure (x : Int32) : Bool :=
  let a := (Int32Array.mk #[x]).ensureExclusiveWithCapacity 4
  let p := rawAddr a
  let a := a.push 2 |>.push 3 |>.push 4
  rawAddr a == p && a.toArray == #[x, 2, 3, 4]

-- `ensureCapacity` doesn't copy a shared array that has room.
@[noinline] def Int32Array.ensureCapacityKeepsShared (x : Int32) : Bool :=
  let a := (Int32Array.emptyWithCapacity 10).push x
  let b := a.ensureCapacity 5
  rawAddr b == rawAddr a && b.toArray == #[x]

-- `ensureExclusiveWithCapacity` copies a shared array once, even when it also needs room.
@[noinline] def Int32Array.ensureExclusiveWithCapacityCopiesShared (x : Int32) : Bool :=
  let a := (Int32Array.emptyWithCapacity 2).push x
  let b := a.ensureExclusiveWithCapacity 20
  rawAddr b != rawAddr a && rawCapacity b ≥ 20 && b.toArray == #[x] && a.toArray == #[x]

#guard Int32Array.ensuresInPlace 1
#guard Int32Array.pushesInPlaceAfterEnsure 1
#guard Int32Array.ensureCapacityKeepsShared 1
#guard Int32Array.ensureExclusiveWithCapacityCopiesShared 1

-- After any of them, a write to a shared array must leave the original unchanged. The results
-- are checked first so that they are computed while the original is still live.
#guard
  let a := Int32Array.mk #[1, 2, 3]
  let b := a.ensureExclusive.set! 0 big
  b.toArray == #[big, 2, 3] && a.toArray == #[1, 2, 3]
#guard
  let a := Int32Array.mk #[1, 2, 3]
  let b := (a.ensureCapacity 10).set! 0 big |>.push 4
  b.toArray == #[big, 2, 3, 4] && a.toArray == #[1, 2, 3]
#guard
  let a := Int32Array.mk #[1, 2, 3]
  let b := (a.ensureExclusiveWithCapacity 10).set! 0 big |>.push 4
  b.toArray == #[big, 2, 3, 4] && a.toArray == #[1, 2, 3]

-- On a closed array, they must not hand out a shared constant: a later call must not change an
-- earlier result.
@[noinline] def Int32Array.ensureExclusiveConstant (x : Int32) : Int32Array :=
  (Int32Array.mk #[0, 0]).ensureExclusive.uset 0 x

@[noinline] def Int32Array.ensureCapacityConstant (x : Int32) : Int32Array :=
  ((Int32Array.mk #[0, 0]).ensureCapacity 10).uset 0 x |>.push x

@[noinline] def Int32Array.ensureExclusiveWithCapacityConstant (x : Int32) : Int32Array :=
  ((Int32Array.mk #[0, 0]).ensureExclusiveWithCapacity 10).uset 0 x |>.push x

#guard
  let a := Int32Array.ensureExclusiveConstant 1
  let b := Int32Array.ensureExclusiveConstant 2
  b.toArray == #[2, 0] && a.toArray == #[1, 0]

#guard
  let a := Int32Array.ensureCapacityConstant 1
  let b := Int32Array.ensureCapacityConstant 2
  b.toArray == #[2, 0, 2] && a.toArray == #[1, 0, 1]

#guard
  let a := Int32Array.ensureExclusiveWithCapacityConstant 1
  let b := Int32Array.ensureExclusiveWithCapacityConstant 2
  b.toArray == #[2, 0, 2] && a.toArray == #[1, 0, 1]


/-! Appending -/

#guard (Int32Array.mk #[1, 2] ++ Int32Array.mk #[3, big]).toArray == #[1, 2, 3, big]
#guard ((Int32Array.mk #[1, 2]).append (Int32Array.mk #[3])).toArray == #[1, 2, 3]
#guard (Int32Array.mk #[1, 2] ++ Int32Array.empty).toArray == #[1, 2]
#guard (Int32Array.empty ++ Int32Array.mk #[1, 2]).toArray == #[1, 2]
#guard (Int32Array.empty ++ Int32Array.empty).toArray == #[]
#guard (Int32Array.mk #[0, 0] ++ Int32Array.mk #[big] ++ Int32Array.mk #[0]).toArray ==
  #[0, 0, big, 0]

-- Appending an array to itself, with and without room.
#guard
  let a := Int32Array.mk #[1, 2, 3]
  (a ++ a).toArray == #[1, 2, 3, 1, 2, 3]

#guard
  let a := (Int32Array.emptyWithCapacity 10).push 1 |>.push 2
  (a ++ a).toArray == #[1, 2, 1, 2]

-- Appending to a shared array must leave the original unchanged, with and without room. The
-- results are checked first so that they are computed while the original is still live.
#guard
  let a := (Int32Array.emptyWithCapacity 10).push 1
  let b := a ++ Int32Array.mk #[2, 3]
  let c := a ++ Int32Array.mk #[4]
  c.toArray == #[1, 4] && b.toArray == #[1, 2, 3] && a.toArray == #[1]

#guard
  let a := Int32Array.mk #[1]
  let b := a ++ Int32Array.mk #[2, 3]
  b.toArray == #[1, 2, 3] && a.toArray == #[1]

-- The right operand is never modified.
#guard
  let b := Int32Array.mk #[2, 3]
  let c := Int32Array.mk #[1] ++ b
  c.toArray == #[1, 2, 3] && b.toArray == #[2, 3]

-- Many appends to an exclusive array.
#guard Id.run do
  let mut a := Int32Array.empty
  let mut r : Array Int32 := #[]
  for i in [0:1000] do
    a := a ++ Int32Array.mk #[i.toInt32, (i * 7).toInt32, big]
    r := r ++ #[i.toInt32, (i * 7).toInt32, big]
  return a.toArray == r

-- Large arrays on both sides.
#guard
  let xs := (Array.range 50000).map Nat.toInt32
  let ys := (Array.range 50000).map fun i => (i * 3).toInt32
  (Int32Array.mk xs ++ Int32Array.mk ys).toArray == xs ++ ys

-- An exclusive array with room is appended to in place, and growth is geometric.
-- The array is built from a parameter so that it isn't extracted as a shared closed term.
@[noinline] def Int32Array.appendsInPlace (x : Int32) : Bool :=
  let a := (Int32Array.emptyWithCapacity 10).push x
  let p := rawAddr a
  let a := a ++ Int32Array.mk #[2, 3]
  rawAddr a == p && a.toArray == #[x, 2, 3]

@[noinline] def Int32Array.appendsToCopyWhenShared (x : Int32) : Bool :=
  let a := (Int32Array.emptyWithCapacity 10).push x
  let p := rawAddr a
  let b := a ++ Int32Array.mk #[2, 3]
  rawAddr b != p && b.toArray == #[x, 2, 3] && a.toArray == #[x]

#guard Int32Array.appendsInPlace 1
#guard Int32Array.appendsToCopyWhenShared 1

#guard rawCapacity ((Int32Array.emptyWithCapacity 10).push 1 ++ Int32Array.mk #[2, 3]) ≥ 10
#guard rawCapacity (Int32Array.mk #[1, 2, 3, 4] ++ Int32Array.mk #[5]) ≥ 8
#guard rawCapacity (Int32Array.mk #[1] ++ Int32Array.mk (Array.replicate 10 0)) ≥ 11
#guard rawElemSize (Int32Array.mk #[1] ++ Int32Array.mk #[2]) == elemSize

/-! Default bounds proofs -/

#guard (Int32Array.mk #[1, 2, big]).get 2 == big
#guard (Int32Array.mk #[1, 2, big]).uget 2 == big
#guard ((Int32Array.mk #[1, 2, 3]).set 1 big).toArray == #[1, big, 3]
#guard ((Int32Array.mk #[1, 2, 3]).uset 1 big).toArray == #[1, big, 3]

/-! `set!` leaves the array unchanged when the index is out of bounds, like `ByteArray.set!`. -/

#guard ((Int32Array.mk #[1, 2, 3]).set! 3 big).toArray == #[1, 2, 3]
#guard ((Int32Array.mk #[1, 2, 3]).set! (2 ^ 70) big).toArray == #[1, 2, 3]

/-! Copying slices -/

#guard
  let src := Int32Array.mk #[10, 11, 12, big]
  let dest := Int32Array.mk #[1, 2, 3, 4, 5]
  (src.copySlice 1 dest 2 2).toArray == #[1, 2, 11, 12, 5] &&
  (src.copySlice 1 dest 4 3).toArray == #[1, 2, 3, 4, 11, 12, big] &&
  (src.copySlice 0 dest 9 2).toArray == #[1, 2, 3, 4, 5, 10, 11] &&
  (src.copySlice 9 dest 1 2).toArray == #[1, 2, 3, 4, 5] &&
  (src.copySlice 2 dest 0 10).toArray == #[12, big, 3, 4, 5] &&
  (src.copySlice 0 dest 0 0).toArray == #[1, 2, 3, 4, 5] &&
  (src.copySlice 0 Int32Array.empty 0 4).toArray == #[10, 11, 12, big] &&
  dest.toArray == #[1, 2, 3, 4, 5] && src.toArray == #[10, 11, 12, big]

-- Copying from an array into itself.
#guard
  let a := Int32Array.mk #[1, 2, 3, big]
  (a.copySlice 0 a 2 4).toArray == #[1, 2, 1, 2, 3, big]

#guard
  let xs := (Array.range 100000).map Nat.toInt32
  let a := Int32Array.mk xs
  (a.copySlice 70000 (Int32Array.replicate 10 0) 5 10).toArray ==
    Array.replicate 5 0 ++ xs.extract 70000 70010

#guard rawElemSize ((Int32Array.mk #[1]).copySlice 0 Int32Array.empty 0 1) == elemSize

@[noinline] def Int32Array.copiesSliceInPlace (x : Int32) : Bool :=
  let dest := (Int32Array.emptyWithCapacity 10).push x |>.push x |>.push x
  let p := rawAddr dest
  let dest := (Int32Array.mk #[big, big]).copySlice 0 dest 1 2
  rawAddr dest == p && dest.toArray == #[x, big, big]

@[noinline] def Int32Array.copySliceGrowth (x : Int32) : Bool :=
  let dest := (Int32Array.mk #[x, x, x, x])
  rawCapacity ((Int32Array.mk #[x]).copySlice 0 dest 4 1 (exact := false)) ≥ 8 &&
    rawCapacity ((Int32Array.mk #[x]).copySlice 0 dest 4 1) == 5

#guard Int32Array.copiesSliceInPlace 1
#guard Int32Array.copySliceGrowth 1
