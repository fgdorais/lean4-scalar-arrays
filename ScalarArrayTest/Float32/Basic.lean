/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import ScalarArray.Float32
import ScalarArrayTest.Util
meta import ScalarArray.Float32
meta import ScalarArrayTest.Util

open ScalarArray ScalarArrayTest

/-!
Tests for `Float32Array`: construction, reads, writes, `push`, capacity, `append` and `copySlice`.
-/

/-- A test value at the edge of the element type's range. -/
private abbrev big : Float32 := -1.5e38

/-- The size of an element in bytes. -/
private abbrev elemSize : UInt32 := 4

/-! Construction and conversion -/

#guard (Float32Array.mk #[1, 2, 3, big]).toArray == #[1, 2, 3, big]
#guard (Float32Array.mk #[1, 2, 3, big]).toList == [1, 2, 3, big]
#guard (Float32Array.mk #[]).toArray == #[]
#guard Float32Array.empty.toArray == #[]
#guard (∅ : Float32Array).toArray == #[]
#guard (default : Float32Array).toArray == #[]
#guard (Float32Array.emptyWithCapacity 100).toArray == #[]
#guard (Float32Array.mk (Array.range 1000 |>.map Nat.toFloat32)).toArray ==
  (Array.range 1000).map Nat.toFloat32

/-! Case analysis -/

-- `cases` splits an array as `mk a`, also in compiled code.
private def headOrZero (a : Float32Array) : Float32 := by
  cases a with | mk a => exact a[0]?.getD 0

#guard headOrZero (Float32Array.mk #[7, 8]) == 7
#guard headOrZero Float32Array.empty == 0

-- There is no constructor to match on, which would run `Array` code on a scalar array.
/--
error: Invalid `⟨...⟩` notation: The expected type `Quot fun x x_1 => False` is not an inductive type

Note: This notation can only be used when the expected type is an inductive type with a single constructor
-/
#guard_msgs in
example (a : Float32Array) : Float32 := match a with | ⟨a⟩ => a[0]!

/-! Size -/

#guard (Float32Array.mk #[1, 2, 3, big]).size == 4
#guard (Float32Array.mk #[1, 2, 3, big]).usize == 4
#guard Float32Array.empty.size == 0
#guard (Float32Array.emptyWithCapacity 100).size == 0

/-! Reading -/

#guard (Float32Array.mk #[1, 2, 3, big])[0] == 1
#guard (Float32Array.mk #[1, 2, 3, big])[3] == big
#guard (Float32Array.mk #[1, 2, 3, big])[(2 : USize)] == 3
#guard (Float32Array.mk #[1, 2, 3, big]).get! 1 == 2
#guard (Float32Array.mk #[1, 2, 3, big]).getD 2 7 == 3
#guard (Float32Array.mk #[1, 2, 3, big]).getD 4 7 == 7
#guard (Float32Array.mk #[1, 2, 3, big])[4]? == none
#guard (Float32Array.mk #[1, 2, 3, big])[1]? == some 2

/-! Writing -/

#guard ((Float32Array.mk #[1, 2, 3]).set 1 42 (by decide)).toArray == #[1, 42, 3]
#guard ((Float32Array.mk #[1, 2, 3]).uset 2 42 (by simp)).toArray == #[1, 2, 42]
#guard ((Float32Array.mk #[1, 2, 3]).set! 0 big).toArray == #[big, 2, 3]

-- Writing to a shared array must leave the original unchanged. The result is checked first so
-- that it is computed while the original is still live.
#guard
  let a := Float32Array.mk #[1, 2, 3]
  let b := a.set! 1 42
  b.toArray == #[1, 42, 3] && a.toArray == #[1, 2, 3]
#guard
  let a := Float32Array.mk #[1, 2, 3]
  let b := a.uset 0 big (by simp [a])
  b.toArray == #[big, 2, 3] && a.toArray == #[1, 2, 3]
#guard
  let a := Float32Array.mk #[1, 2, 3]
  let b := a.set 2 big (by simp [a])
  b.toArray == #[1, 2, big] && a.toArray == #[1, 2, 3]

-- Repeated writes to an exclusive array.
#guard Id.run do
  let mut a := Float32Array.mk (Array.replicate 1000 0)
  for i in [0:1000] do
    a := a.set! i (i * 3).toFloat32
  return a.toArray == (Array.range 1000).map fun i => (i * 3).toFloat32

/-! Pushing -/

#guard (Float32Array.empty.push 5 |>.push 6).toArray == #[5, 6]
#guard ((Float32Array.emptyWithCapacity 1).push 5 |>.push 6 |>.push 7).toArray == #[5, 6, 7]
#guard ((Float32Array.mk #[1, 2]).push 3).toArray == #[1, 2, 3]

-- Pushing past the capacity many times.
#guard Id.run do
  let mut a := Float32Array.empty
  for i in [0:10000] do
    a := a.push i.toFloat32
  return a.size == 10000 && a.toArray == (Array.range 10000).map Nat.toFloat32

-- Pushing to a shared array must leave the original unchanged. The results are checked first so
-- that they are computed while the original is still live.
#guard
  let a := (Float32Array.emptyWithCapacity 10).push 1
  let b := a.push 2
  let c := a.push 3
  c.toArray == #[1, 3] && b.toArray == #[1, 2] && a.toArray == #[1]

-- Inlined `push` and `uset` on a closed array must copy it on every call, not write into a shared
-- constant: a later call must not change an earlier result.
@[noinline] def Float32Array.pushOntoConstant (x : Float32) : Float32Array :=
  (Float32Array.emptyWithCapacity 10).push x

@[noinline] def Float32Array.usetConstant (x : Float32) : Float32Array :=
  (Float32Array.mk #[0, 0]).uset 0 x

#guard
  let a := Float32Array.pushOntoConstant 1
  let b := Float32Array.pushOntoConstant 2
  b.toArray == #[2] && a.toArray == #[1]

#guard
  let a := Float32Array.usetConstant 1
  let b := Float32Array.usetConstant 2
  b.toArray == #[2, 0] && a.toArray == #[1, 0]

/-! Every index, through both `Nat` and `USize` indices -/

#guard
  let a := Float32Array.mk ((Array.range 300).map Nat.toFloat32)
  (List.range 300).all fun i =>
    a[i]! == i.toFloat32 && a.getD i 0 == i.toFloat32 && a.get! i == i.toFloat32 &&
      (if h : i.toUSize.toNat < a.size then a[i.toUSize] == i.toFloat32 else false)

/-! Writes don't touch neighbouring elements -/

#guard ((Float32Array.mk #[0, 0, 0]).set! 1 big).toArray == #[0, big, 0]
#guard ((Float32Array.mk #[big, big, big]).set! 1 0).toArray == #[big, 0, big]
#guard ((Float32Array.mk #[0, 0, 0]).push big |>.push 0).toArray == #[0, 0, 0, big, 0]

/-! Indices beyond 16 bits, and huge `Nat` indices -/

#guard
  let a := (Float32Array.mk (Array.replicate 100000 0)).set! 99999 big |>.set! 70000 1
  a.size == 100000 && a[99999]! == big && a[70000]! == 1 && a[99998]! == 0 &&
    a[70000 % 65536]! == 0 && a.toArray[99999]! == big && a.toArray[70000]! == 1 &&
    (if h : (70000 : USize).toNat < a.size then a[(70000 : USize)] == 1 else false)

#guard (Float32Array.mk #[1, 2, 3])[2 ^ 70]? == none
#guard (Float32Array.mk #[1, 2, 3]).getD (2 ^ 70) 7 == 7

/-! Pushing onto a shared array that is at full capacity -/

#guard
  let a := Float32Array.mk #[1]
  let b := a.push 2
  b.toArray == #[1, 2] && a.toArray == #[1]

#guard
  let a := Float32Array.mk #[]
  let b := a.push 2
  b.toArray == #[2] && a.toArray == #[]

/-! Conversions don't alias -/

#guard
  let a := #[(1 : Float32), 2, 3]
  let b := (Float32Array.mk a).set! 0 big
  b.toArray == #[big, 2, 3] && a == #[1, 2, 3]

#guard
  let a := Float32Array.mk #[1, 2, 3]
  let d := a.toArray.set! 0 big
  d == #[big, 2, 3] && a.toArray == #[1, 2, 3]

/-! Runtime representation -/

#guard rawElemSize (Float32Array.mk #[1, 2, 3]) == elemSize
#guard rawElemSize (Float32Array.emptyWithCapacity 10) == elemSize
#guard rawElemSize (Float32Array.empty.push 1) == elemSize
#guard rawElemSize ((Float32Array.mk #[1]).push 2) == elemSize
#guard rawCapacity (Float32Array.emptyWithCapacity 100) ≥ 100
#guard rawCapacity (Float32Array.mk #[1, 2, 3]) ≥ 3
-- Growth is geometric, so pushing is amortized constant time.
#guard rawCapacity ((Float32Array.mk #[1, 2, 3, 4]).push 5) ≥ 8


/-! Ensuring exclusivity and capacity -/

#guard (Float32Array.mk #[1, 2, 3]).ensureExclusive.toArray == #[1, 2, 3]
#guard ((Float32Array.mk #[1, 2, 3]).ensureCapacity 100).toArray == #[1, 2, 3]
#guard ((Float32Array.mk #[1, 2, 3]).ensureCapacity 0).toArray == #[1, 2, 3]
#guard ((Float32Array.mk #[1, 2, 3]).ensureExclusiveWithCapacity 100).toArray == #[1, 2, 3]
#guard ((Float32Array.mk #[1, 2, 3]).ensureExclusiveWithCapacity 0).toArray == #[1, 2, 3]

#guard rawCapacity ((Float32Array.mk #[1, 2, 3]).ensureCapacity 100) ≥ 100
#guard rawCapacity ((Float32Array.mk #[1, 2, 3]).ensureExclusiveWithCapacity 100) ≥ 100
-- A copy never has less room than the size.
#guard rawCapacity ((Float32Array.mk #[1, 2, 3]).ensureExclusiveWithCapacity 0) ≥ 3
#guard rawElemSize ((Float32Array.mk #[1, 2, 3]).ensureCapacity 100) == elemSize

-- The array is built from a parameter so that it isn't extracted as a shared closed term.
@[noinline] def Float32Array.ensuresInPlace (x : Float32) : Bool :=
  let a := (Float32Array.emptyWithCapacity 10).push x
  let p := rawAddr a
  let a := a.ensureExclusive.ensureCapacity 5 |>.ensureExclusiveWithCapacity 10
  rawAddr a == p && a.toArray == #[x]

-- Pushes after `ensureExclusiveWithCapacity` don't reallocate.
@[noinline] def Float32Array.pushesInPlaceAfterEnsure (x : Float32) : Bool :=
  let a := (Float32Array.mk #[x]).ensureExclusiveWithCapacity 4
  let p := rawAddr a
  let a := a.push 2 |>.push 3 |>.push 4
  rawAddr a == p && a.toArray == #[x, 2, 3, 4]

-- `ensureCapacity` doesn't copy a shared array that has room.
@[noinline] def Float32Array.ensureCapacityKeepsShared (x : Float32) : Bool :=
  let a := (Float32Array.emptyWithCapacity 10).push x
  let b := a.ensureCapacity 5
  rawAddr b == rawAddr a && b.toArray == #[x]

-- `ensureExclusiveWithCapacity` copies a shared array once, even when it also needs room.
@[noinline] def Float32Array.ensureExclusiveWithCapacityCopiesShared (x : Float32) : Bool :=
  let a := (Float32Array.emptyWithCapacity 2).push x
  let b := a.ensureExclusiveWithCapacity 20
  rawAddr b != rawAddr a && rawCapacity b ≥ 20 && b.toArray == #[x] && a.toArray == #[x]

#guard Float32Array.ensuresInPlace 1
#guard Float32Array.pushesInPlaceAfterEnsure 1
#guard Float32Array.ensureCapacityKeepsShared 1
#guard Float32Array.ensureExclusiveWithCapacityCopiesShared 1

-- After any of them, a write to a shared array must leave the original unchanged. The results
-- are checked first so that they are computed while the original is still live.
#guard
  let a := Float32Array.mk #[1, 2, 3]
  let b := a.ensureExclusive.set! 0 big
  b.toArray == #[big, 2, 3] && a.toArray == #[1, 2, 3]
#guard
  let a := Float32Array.mk #[1, 2, 3]
  let b := (a.ensureCapacity 10).set! 0 big |>.push 4
  b.toArray == #[big, 2, 3, 4] && a.toArray == #[1, 2, 3]
#guard
  let a := Float32Array.mk #[1, 2, 3]
  let b := (a.ensureExclusiveWithCapacity 10).set! 0 big |>.push 4
  b.toArray == #[big, 2, 3, 4] && a.toArray == #[1, 2, 3]

-- On a closed array, they must not hand out a shared constant: a later call must not change an
-- earlier result.
@[noinline] def Float32Array.ensureExclusiveConstant (x : Float32) : Float32Array :=
  (Float32Array.mk #[0, 0]).ensureExclusive.uset 0 x

@[noinline] def Float32Array.ensureCapacityConstant (x : Float32) : Float32Array :=
  ((Float32Array.mk #[0, 0]).ensureCapacity 10).uset 0 x |>.push x

@[noinline] def Float32Array.ensureExclusiveWithCapacityConstant (x : Float32) : Float32Array :=
  ((Float32Array.mk #[0, 0]).ensureExclusiveWithCapacity 10).uset 0 x |>.push x

#guard
  let a := Float32Array.ensureExclusiveConstant 1
  let b := Float32Array.ensureExclusiveConstant 2
  b.toArray == #[2, 0] && a.toArray == #[1, 0]

#guard
  let a := Float32Array.ensureCapacityConstant 1
  let b := Float32Array.ensureCapacityConstant 2
  b.toArray == #[2, 0, 2] && a.toArray == #[1, 0, 1]

#guard
  let a := Float32Array.ensureExclusiveWithCapacityConstant 1
  let b := Float32Array.ensureExclusiveWithCapacityConstant 2
  b.toArray == #[2, 0, 2] && a.toArray == #[1, 0, 1]


/-! Appending -/

#guard (Float32Array.mk #[1, 2] ++ Float32Array.mk #[3, big]).toArray == #[1, 2, 3, big]
#guard ((Float32Array.mk #[1, 2]).append (Float32Array.mk #[3])).toArray == #[1, 2, 3]
#guard (Float32Array.mk #[1, 2] ++ Float32Array.empty).toArray == #[1, 2]
#guard (Float32Array.empty ++ Float32Array.mk #[1, 2]).toArray == #[1, 2]
#guard (Float32Array.empty ++ Float32Array.empty).toArray == #[]
#guard (Float32Array.mk #[0, 0] ++ Float32Array.mk #[big] ++ Float32Array.mk #[0]).toArray ==
  #[0, 0, big, 0]

-- Appending an array to itself, with and without room.
#guard
  let a := Float32Array.mk #[1, 2, 3]
  (a ++ a).toArray == #[1, 2, 3, 1, 2, 3]

#guard
  let a := (Float32Array.emptyWithCapacity 10).push 1 |>.push 2
  (a ++ a).toArray == #[1, 2, 1, 2]

-- Appending to a shared array must leave the original unchanged, with and without room. The
-- results are checked first so that they are computed while the original is still live.
#guard
  let a := (Float32Array.emptyWithCapacity 10).push 1
  let b := a ++ Float32Array.mk #[2, 3]
  let c := a ++ Float32Array.mk #[4]
  c.toArray == #[1, 4] && b.toArray == #[1, 2, 3] && a.toArray == #[1]

#guard
  let a := Float32Array.mk #[1]
  let b := a ++ Float32Array.mk #[2, 3]
  b.toArray == #[1, 2, 3] && a.toArray == #[1]

-- The right operand is never modified.
#guard
  let b := Float32Array.mk #[2, 3]
  let c := Float32Array.mk #[1] ++ b
  c.toArray == #[1, 2, 3] && b.toArray == #[2, 3]

-- Many appends to an exclusive array.
#guard Id.run do
  let mut a := Float32Array.empty
  let mut r : Array Float32 := #[]
  for i in [0:1000] do
    a := a ++ Float32Array.mk #[i.toFloat32, (i * 7).toFloat32, big]
    r := r ++ #[i.toFloat32, (i * 7).toFloat32, big]
  return a.toArray == r

-- Large arrays on both sides.
#guard
  let xs := (Array.range 50000).map Nat.toFloat32
  let ys := (Array.range 50000).map fun i => (i * 3).toFloat32
  (Float32Array.mk xs ++ Float32Array.mk ys).toArray == xs ++ ys

-- An exclusive array with room is appended to in place, and growth is geometric.
-- The array is built from a parameter so that it isn't extracted as a shared closed term.
@[noinline] def Float32Array.appendsInPlace (x : Float32) : Bool :=
  let a := (Float32Array.emptyWithCapacity 10).push x
  let p := rawAddr a
  let a := a ++ Float32Array.mk #[2, 3]
  rawAddr a == p && a.toArray == #[x, 2, 3]

@[noinline] def Float32Array.appendsToCopyWhenShared (x : Float32) : Bool :=
  let a := (Float32Array.emptyWithCapacity 10).push x
  let p := rawAddr a
  let b := a ++ Float32Array.mk #[2, 3]
  rawAddr b != p && b.toArray == #[x, 2, 3] && a.toArray == #[x]

#guard Float32Array.appendsInPlace 1
#guard Float32Array.appendsToCopyWhenShared 1

#guard rawCapacity ((Float32Array.emptyWithCapacity 10).push 1 ++ Float32Array.mk #[2, 3]) ≥ 10
#guard rawCapacity (Float32Array.mk #[1, 2, 3, 4] ++ Float32Array.mk #[5]) ≥ 8
#guard rawCapacity (Float32Array.mk #[1] ++ Float32Array.mk (Array.replicate 10 0)) ≥ 11
#guard rawElemSize (Float32Array.mk #[1] ++ Float32Array.mk #[2]) == elemSize

/-! Default bounds proofs -/

#guard (Float32Array.mk #[1, 2, big]).get 2 == big
#guard (Float32Array.mk #[1, 2, big]).uget 2 == big
#guard ((Float32Array.mk #[1, 2, 3]).set 1 big).toArray == #[1, big, 3]
#guard ((Float32Array.mk #[1, 2, 3]).uset 1 big).toArray == #[1, big, 3]

/-! `set!` leaves the array unchanged when the index is out of bounds, like `ByteArray.set!`. -/

#guard ((Float32Array.mk #[1, 2, 3]).set! 3 big).toArray == #[1, 2, 3]
#guard ((Float32Array.mk #[1, 2, 3]).set! (2 ^ 70) big).toArray == #[1, 2, 3]

/-! Copying slices -/

#guard
  let src := Float32Array.mk #[10, 11, 12, big]
  let dest := Float32Array.mk #[1, 2, 3, 4, 5]
  (src.copySlice 1 dest 2 2).toArray == #[1, 2, 11, 12, 5] &&
  (src.copySlice 1 dest 4 3).toArray == #[1, 2, 3, 4, 11, 12, big] &&
  (src.copySlice 0 dest 9 2).toArray == #[1, 2, 3, 4, 5, 10, 11] &&
  (src.copySlice 9 dest 1 2).toArray == #[1, 2, 3, 4, 5] &&
  (src.copySlice 2 dest 0 10).toArray == #[12, big, 3, 4, 5] &&
  (src.copySlice 0 dest 0 0).toArray == #[1, 2, 3, 4, 5] &&
  (src.copySlice 0 Float32Array.empty 0 4).toArray == #[10, 11, 12, big] &&
  dest.toArray == #[1, 2, 3, 4, 5] && src.toArray == #[10, 11, 12, big]

-- Copying from an array into itself.
#guard
  let a := Float32Array.mk #[1, 2, 3, big]
  (a.copySlice 0 a 2 4).toArray == #[1, 2, 1, 2, 3, big]

#guard
  let xs := (Array.range 100000).map Nat.toFloat32
  let a := Float32Array.mk xs
  (a.copySlice 70000 (Float32Array.replicate 10 0) 5 10).toArray ==
    Array.replicate 5 0 ++ xs.extract 70000 70010

#guard rawElemSize ((Float32Array.mk #[1]).copySlice 0 Float32Array.empty 0 1) == elemSize

@[noinline] def Float32Array.copiesSliceInPlace (x : Float32) : Bool :=
  let dest := (Float32Array.emptyWithCapacity 10).push x |>.push x |>.push x
  let p := rawAddr dest
  let dest := (Float32Array.mk #[big, big]).copySlice 0 dest 1 2
  rawAddr dest == p && dest.toArray == #[x, big, big]

@[noinline] def Float32Array.copySliceGrowth (x : Float32) : Bool :=
  let dest := (Float32Array.mk #[x, x, x, x])
  rawCapacity ((Float32Array.mk #[x]).copySlice 0 dest 4 1 (exact := false)) ≥ 8 &&
    rawCapacity ((Float32Array.mk #[x]).copySlice 0 dest 4 1) == 5

#guard Float32Array.copiesSliceInPlace 1
#guard Float32Array.copySliceGrowth 1

-- Copying an array onto itself, shifted by one in each direction, so that the two ranges overlap.
-- The arrays are long enough that a plain `memcpy` would not happen to get them right, and the
-- expected elements come from `f`, not from the array that was overwritten.
@[noinline] def Float32Array.copySliceOntoItselfForward (x : Float32) : Bool :=
  let f (i : Nat) : Float32 := (i % 251).toFloat32 + x
  let a := Float32Array.ofFn (n := 10000) fun i => f i
  let b := a.copySlice 0 a 1 9999
  b.size == 10000 && b[0]! == f 0 && (List.range 9999).all fun i => b[i + 1]! == f i

@[noinline] def Float32Array.copySliceOntoItselfBackward (x : Float32) : Bool :=
  let f (i : Nat) : Float32 := (i % 251).toFloat32 + x
  let a := Float32Array.ofFn (n := 10000) fun i => f i
  let b := a.copySlice 1 a 0 9999
  b.size == 10000 && b[9999]! == f 9999 && (List.range 9999).all fun i => b[i]! == f (i + 1)

#guard Float32Array.copySliceOntoItselfForward 1
#guard Float32Array.copySliceOntoItselfBackward 1
