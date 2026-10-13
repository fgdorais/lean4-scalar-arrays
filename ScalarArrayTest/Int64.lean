/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ScalarArray.Int64
import ScalarArrayTest.Util

open ScalarArray ScalarArrayTest

/-! Construction and conversion -/

#guard (Int64Array.mk #[1, 2, 3, (-9223372036854775808)]).data == #[1, 2, 3, (-9223372036854775808)]
#guard (Int64Array.mk #[1, 2, 3, (-9223372036854775808)]).toList == [1, 2, 3, (-9223372036854775808)]
#guard (Int64Array.mk #[]).data == #[]
#guard Int64Array.empty.data == #[]
#guard (∅ : Int64Array).data == #[]
#guard (default : Int64Array).data == #[]
#guard (Int64Array.emptyWithCapacity 100).data == #[]
#guard (Int64Array.mk (Array.range 1000 |>.map Nat.toInt64)).data == (Array.range 1000).map Nat.toInt64

/-! Size -/

#guard (Int64Array.mk #[1, 2, 3, (-9223372036854775808)]).size == 4
#guard (Int64Array.mk #[1, 2, 3, (-9223372036854775808)]).usize == 4
#guard Int64Array.empty.size == 0
#guard (Int64Array.emptyWithCapacity 100).size == 0

/-! Reading -/

#guard (Int64Array.mk #[1, 2, 3, (-9223372036854775808)])[0] == 1
#guard (Int64Array.mk #[1, 2, 3, (-9223372036854775808)])[3] == (-9223372036854775808)
#guard (Int64Array.mk #[1, 2, 3, (-9223372036854775808)])[(2 : USize)] == 3
#guard (Int64Array.mk #[1, 2, 3, (-9223372036854775808)]).get! 1 == 2
#guard (Int64Array.mk #[1, 2, 3, (-9223372036854775808)]).getD 2 7 == 3
#guard (Int64Array.mk #[1, 2, 3, (-9223372036854775808)]).getD 4 7 == 7
#guard (Int64Array.mk #[1, 2, 3, (-9223372036854775808)])[4]? == none
#guard (Int64Array.mk #[1, 2, 3, (-9223372036854775808)])[1]? == some 2

/-! Writing -/

#guard ((Int64Array.mk #[1, 2, 3]).set 1 42 (by decide)).data == #[1, 42, 3]
#guard ((Int64Array.mk #[1, 2, 3]).uset 2 42 (by simp)).data == #[1, 2, 42]
#guard ((Int64Array.mk #[1, 2, 3]).set! 0 (-9223372036854775808)).data == #[(-9223372036854775808), 2, 3]
#guard ((Int64Array.mk #[1, 2, 3]).setD 0 0).data == #[0, 2, 3]
#guard ((Int64Array.mk #[1, 2, 3]).setD 3 42).data == #[1, 2, 3]

-- Writing to a shared array must leave the original unchanged. The result is checked first so
-- that it is computed while the original is still live.
#guard
  let a := Int64Array.mk #[1, 2, 3]
  let b := a.set! 1 42
  b.data == #[1, 42, 3] && a.data == #[1, 2, 3]

-- Repeated writes to an exclusive array.
#guard Id.run do
  let mut a := Int64Array.mk (Array.replicate 1000 0)
  for i in [0:1000] do
    a := a.set! i (i * 3).toInt64
  return a.data == (Array.range 1000).map fun i => (i * 3).toInt64

/-! Pushing -/

#guard (Int64Array.empty.push 5 |>.push 6).data == #[5, 6]
#guard ((Int64Array.emptyWithCapacity 1).push 5 |>.push 6 |>.push 7).data == #[5, 6, 7]
#guard ((Int64Array.mk #[1, 2]).push 3).data == #[1, 2, 3]

-- Pushing past the capacity many times.
#guard Id.run do
  let mut a := Int64Array.empty
  for i in [0:10000] do
    a := a.push i.toInt64
  return a.size == 10000 && a.data == (Array.range 10000).map Nat.toInt64

-- Pushing to a shared array must leave the original unchanged. The results are checked first so
-- that they are computed while the original is still live.
#guard
  let a := (Int64Array.emptyWithCapacity 10).push 1
  let b := a.push 2
  let c := a.push 3
  c.data == #[1, 3] && b.data == #[1, 2] && a.data == #[1]

/-! Printing -/

#guard toString (Int64Array.mk #[1, 2]) == "Int64Array.mk " ++ toString #[(1 : Int64), 2]
#guard reprStr (Int64Array.mk #[1, 2]) == "Int64Array.mk " ++ reprStr #[(1 : Int64), 2]

/-! Every index, through both `Nat` and `USize` indices -/

#guard
  let a := Int64Array.mk ((Array.range 300).map Nat.toInt64)
  (List.range 300).all fun i =>
    a[i]! == i.toInt64 && a.getD i 0 == i.toInt64 && a.get! i == i.toInt64 &&
      (if h : i.toUSize.toNat < a.size then a[i.toUSize] == i.toInt64 else false)

/-! Writes don't touch neighbouring elements -/

#guard ((Int64Array.mk #[0, 0, 0]).set! 1 (-9223372036854775808)).data == #[0, (-9223372036854775808), 0]
#guard ((Int64Array.mk #[(-9223372036854775808), (-9223372036854775808), (-9223372036854775808)]).set! 1 0).data == #[(-9223372036854775808), 0, (-9223372036854775808)]
#guard ((Int64Array.mk #[0, 0, 0]).push (-9223372036854775808) |>.push 0).data == #[0, 0, 0, (-9223372036854775808), 0]

/-! Indices beyond 16 bits, and huge `Nat` indices -/

#guard
  let a := (Int64Array.mk (Array.replicate 100000 0)).set! 99999 (-9223372036854775808) |>.set! 70000 1
  a.size == 100000 && a[99999]! == (-9223372036854775808) && a[70000]! == 1 && a[99998]! == 0 &&
    a[70000 % 65536]! == 0 && a.data[99999]! == (-9223372036854775808) && a.data[70000]! == 1 &&
    (if h : (70000 : USize).toNat < a.size then a[(70000 : USize)] == 1 else false)

#guard (Int64Array.mk #[1, 2, 3])[2 ^ 70]? == none
#guard (Int64Array.mk #[1, 2, 3]).getD (2 ^ 70) 7 == 7
#guard ((Int64Array.mk #[1, 2, 3]).setD (2 ^ 70) 7).data == #[1, 2, 3]

/-! Pushing onto a shared array that is at full capacity -/

#guard
  let a := Int64Array.mk #[1]
  let b := a.push 2
  b.data == #[1, 2] && a.data == #[1]

#guard
  let a := Int64Array.mk #[]
  let b := a.push 2
  b.data == #[2] && a.data == #[]

/-! Conversions don't alias -/

#guard
  let a := #[(1 : Int64), 2, 3]
  let b := (Int64Array.mk a).set! 0 (-9223372036854775808)
  b.data == #[(-9223372036854775808), 2, 3] && a == #[1, 2, 3]

#guard
  let a := Int64Array.mk #[1, 2, 3]
  let d := a.data.set! 0 (-9223372036854775808)
  d == #[(-9223372036854775808), 2, 3] && a.data == #[1, 2, 3]

/-! Runtime representation -/

#guard rawElemSize (Int64Array.mk #[1, 2, 3]) == (8 : UInt32)
#guard rawElemSize (Int64Array.emptyWithCapacity 10) == (8 : UInt32)
#guard rawElemSize (Int64Array.empty.push 1) == (8 : UInt32)
#guard rawElemSize ((Int64Array.mk #[1]).push 2) == (8 : UInt32)
#guard rawCapacity (Int64Array.emptyWithCapacity 100) ≥ 100
#guard rawCapacity (Int64Array.mk #[1, 2, 3]) ≥ 3
-- Growth is geometric, so pushing is amortized constant time.
#guard rawCapacity ((Int64Array.mk #[1, 2, 3, 4]).push 5) ≥ 8


/-! Appending -/

#guard (Int64Array.mk #[1, 2] ++ Int64Array.mk #[3, (-9223372036854775808)]).data == #[1, 2, 3, (-9223372036854775808)]
#guard ((Int64Array.mk #[1, 2]).append (Int64Array.mk #[3])).data == #[1, 2, 3]
#guard (Int64Array.mk #[1, 2] ++ Int64Array.empty).data == #[1, 2]
#guard (Int64Array.empty ++ Int64Array.mk #[1, 2]).data == #[1, 2]
#guard (Int64Array.empty ++ Int64Array.empty).data == #[]
#guard (Int64Array.mk #[0, 0] ++ Int64Array.mk #[(-9223372036854775808)] ++ Int64Array.mk #[0]).data ==
  #[0, 0, (-9223372036854775808), 0]

-- Appending an array to itself, with and without room.
#guard
  let a := Int64Array.mk #[1, 2, 3]
  (a ++ a).data == #[1, 2, 3, 1, 2, 3]

#guard
  let a := (Int64Array.emptyWithCapacity 10).push 1 |>.push 2
  (a ++ a).data == #[1, 2, 1, 2]

-- Appending to a shared array must leave the original unchanged, with and without room. The
-- results are checked first so that they are computed while the original is still live.
#guard
  let a := (Int64Array.emptyWithCapacity 10).push 1
  let b := a ++ Int64Array.mk #[2, 3]
  let c := a ++ Int64Array.mk #[4]
  c.data == #[1, 4] && b.data == #[1, 2, 3] && a.data == #[1]

#guard
  let a := Int64Array.mk #[1]
  let b := a ++ Int64Array.mk #[2, 3]
  b.data == #[1, 2, 3] && a.data == #[1]

-- The right operand is never modified.
#guard
  let b := Int64Array.mk #[2, 3]
  let c := Int64Array.mk #[1] ++ b
  c.data == #[1, 2, 3] && b.data == #[2, 3]

-- Many appends to an exclusive array.
#guard Id.run do
  let mut a := Int64Array.empty
  let mut r : Array Int64 := #[]
  for i in [0:1000] do
    a := a ++ Int64Array.mk #[i.toInt64, (i * 7).toInt64, (-9223372036854775808)]
    r := r ++ #[i.toInt64, (i * 7).toInt64, (-9223372036854775808)]
  return a.data == r

-- Large arrays on both sides.
#guard
  let xs := (Array.range 50000).map Nat.toInt64
  let ys := (Array.range 50000).map fun i => (i * 3).toInt64
  (Int64Array.mk xs ++ Int64Array.mk ys).data == xs ++ ys

-- An exclusive array with room is appended to in place, and growth is geometric.
-- The array is built from a parameter so that it isn't extracted as a shared closed term.
@[noinline] def Int64Array.appendsInPlace (x : Int64) : Bool :=
  let a := (Int64Array.emptyWithCapacity 10).push x
  let p := rawAddr a
  let a := a ++ Int64Array.mk #[2, 3]
  rawAddr a == p && a.data == #[x, 2, 3]

@[noinline] def Int64Array.appendsToCopyWhenShared (x : Int64) : Bool :=
  let a := (Int64Array.emptyWithCapacity 10).push x
  let p := rawAddr a
  let b := a ++ Int64Array.mk #[2, 3]
  rawAddr b != p && b.data == #[x, 2, 3] && a.data == #[x]

#guard Int64Array.appendsInPlace 1
#guard Int64Array.appendsToCopyWhenShared 1

#guard rawCapacity ((Int64Array.emptyWithCapacity 10).push 1 ++ Int64Array.mk #[2, 3]) ≥ 10
#guard rawCapacity (Int64Array.mk #[1, 2, 3, 4] ++ Int64Array.mk #[5]) ≥ 8
#guard rawCapacity (Int64Array.mk #[1] ++ Int64Array.mk (Array.replicate 10 0)) ≥ 11
#guard rawElemSize (Int64Array.mk #[1] ++ Int64Array.mk #[2]) == (8 : UInt32)
