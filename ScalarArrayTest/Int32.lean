/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ScalarArray.Int32
import ScalarArrayTest.Util

open ScalarArray ScalarArrayTest

/-! Construction and conversion -/

#guard (Int32Array.mk #[1, 2, 3, (-2147483648)]).data == #[1, 2, 3, (-2147483648)]
#guard (Int32Array.mk #[1, 2, 3, (-2147483648)]).toList == [1, 2, 3, (-2147483648)]
#guard (Int32Array.mk #[]).data == #[]
#guard Int32Array.empty.data == #[]
#guard (∅ : Int32Array).data == #[]
#guard (default : Int32Array).data == #[]
#guard (Int32Array.emptyWithCapacity 100).data == #[]
#guard (Int32Array.mk (Array.range 1000 |>.map Nat.toInt32)).data == (Array.range 1000).map Nat.toInt32

/-! Size -/

#guard (Int32Array.mk #[1, 2, 3, (-2147483648)]).size == 4
#guard (Int32Array.mk #[1, 2, 3, (-2147483648)]).usize == 4
#guard Int32Array.empty.size == 0
#guard (Int32Array.emptyWithCapacity 100).size == 0

/-! Reading -/

#guard (Int32Array.mk #[1, 2, 3, (-2147483648)])[0] == 1
#guard (Int32Array.mk #[1, 2, 3, (-2147483648)])[3] == (-2147483648)
#guard (Int32Array.mk #[1, 2, 3, (-2147483648)])[(2 : USize)] == 3
#guard (Int32Array.mk #[1, 2, 3, (-2147483648)]).get! 1 == 2
#guard (Int32Array.mk #[1, 2, 3, (-2147483648)]).getD 2 7 == 3
#guard (Int32Array.mk #[1, 2, 3, (-2147483648)]).getD 4 7 == 7
#guard (Int32Array.mk #[1, 2, 3, (-2147483648)])[4]? == none
#guard (Int32Array.mk #[1, 2, 3, (-2147483648)])[1]? == some 2

/-! Writing -/

#guard ((Int32Array.mk #[1, 2, 3]).set 1 42 (by decide)).data == #[1, 42, 3]
#guard ((Int32Array.mk #[1, 2, 3]).uset 2 42 (by simp)).data == #[1, 2, 42]
#guard ((Int32Array.mk #[1, 2, 3]).set! 0 (-2147483648)).data == #[(-2147483648), 2, 3]
#guard ((Int32Array.mk #[1, 2, 3]).setD 0 0).data == #[0, 2, 3]
#guard ((Int32Array.mk #[1, 2, 3]).setD 3 42).data == #[1, 2, 3]

-- Writing to a shared array must leave the original unchanged. The result is checked first so
-- that it is computed while the original is still live.
#guard
  let a := Int32Array.mk #[1, 2, 3]
  let b := a.set! 1 42
  b.data == #[1, 42, 3] && a.data == #[1, 2, 3]

-- Repeated writes to an exclusive array.
#guard Id.run do
  let mut a := Int32Array.mk (Array.replicate 1000 0)
  for i in [0:1000] do
    a := a.set! i (i * 3).toInt32
  return a.data == (Array.range 1000).map fun i => (i * 3).toInt32

/-! Pushing -/

#guard (Int32Array.empty.push 5 |>.push 6).data == #[5, 6]
#guard ((Int32Array.emptyWithCapacity 1).push 5 |>.push 6 |>.push 7).data == #[5, 6, 7]
#guard ((Int32Array.mk #[1, 2]).push 3).data == #[1, 2, 3]

-- Pushing past the capacity many times.
#guard Id.run do
  let mut a := Int32Array.empty
  for i in [0:10000] do
    a := a.push i.toInt32
  return a.size == 10000 && a.data == (Array.range 10000).map Nat.toInt32

-- Pushing to a shared array must leave the original unchanged. The results are checked first so
-- that they are computed while the original is still live.
#guard
  let a := (Int32Array.emptyWithCapacity 10).push 1
  let b := a.push 2
  let c := a.push 3
  c.data == #[1, 3] && b.data == #[1, 2] && a.data == #[1]

/-! Printing -/

#guard toString (Int32Array.mk #[1, 2]) == "Int32Array.mk " ++ toString #[(1 : Int32), 2]
#guard reprStr (Int32Array.mk #[1, 2]) == "Int32Array.mk " ++ reprStr #[(1 : Int32), 2]

/-! Every index, through both `Nat` and `USize` indices -/

#guard
  let a := Int32Array.mk ((Array.range 300).map Nat.toInt32)
  (List.range 300).all fun i =>
    a[i]! == i.toInt32 && a.getD i 0 == i.toInt32 && a.get! i == i.toInt32 &&
      (if h : i.toUSize.toNat < a.size then a[i.toUSize] == i.toInt32 else false)

/-! Writes don't touch neighbouring elements -/

#guard ((Int32Array.mk #[0, 0, 0]).set! 1 (-2147483648)).data == #[0, (-2147483648), 0]
#guard ((Int32Array.mk #[(-2147483648), (-2147483648), (-2147483648)]).set! 1 0).data == #[(-2147483648), 0, (-2147483648)]
#guard ((Int32Array.mk #[0, 0, 0]).push (-2147483648) |>.push 0).data == #[0, 0, 0, (-2147483648), 0]

/-! Indices beyond 16 bits, and huge `Nat` indices -/

#guard
  let a := (Int32Array.mk (Array.replicate 100000 0)).set! 99999 (-2147483648) |>.set! 70000 1
  a.size == 100000 && a[99999]! == (-2147483648) && a[70000]! == 1 && a[99998]! == 0 &&
    a[70000 % 65536]! == 0 && a.data[99999]! == (-2147483648) && a.data[70000]! == 1 &&
    (if h : (70000 : USize).toNat < a.size then a[(70000 : USize)] == 1 else false)

#guard (Int32Array.mk #[1, 2, 3])[2 ^ 70]? == none
#guard (Int32Array.mk #[1, 2, 3]).getD (2 ^ 70) 7 == 7
#guard ((Int32Array.mk #[1, 2, 3]).setD (2 ^ 70) 7).data == #[1, 2, 3]

/-! Pushing onto a shared array that is at full capacity -/

#guard
  let a := Int32Array.mk #[1]
  let b := a.push 2
  b.data == #[1, 2] && a.data == #[1]

#guard
  let a := Int32Array.mk #[]
  let b := a.push 2
  b.data == #[2] && a.data == #[]

/-! Conversions don't alias -/

#guard
  let a := #[(1 : Int32), 2, 3]
  let b := (Int32Array.mk a).set! 0 (-2147483648)
  b.data == #[(-2147483648), 2, 3] && a == #[1, 2, 3]

#guard
  let a := Int32Array.mk #[1, 2, 3]
  let d := a.data.set! 0 (-2147483648)
  d == #[(-2147483648), 2, 3] && a.data == #[1, 2, 3]

/-! Runtime representation -/

#guard rawElemSize (Int32Array.mk #[1, 2, 3]) == (4 : UInt32)
#guard rawElemSize (Int32Array.emptyWithCapacity 10) == (4 : UInt32)
#guard rawElemSize (Int32Array.empty.push 1) == (4 : UInt32)
#guard rawElemSize ((Int32Array.mk #[1]).push 2) == (4 : UInt32)
#guard rawCapacity (Int32Array.emptyWithCapacity 100) ≥ 100
#guard rawCapacity (Int32Array.mk #[1, 2, 3]) ≥ 3
-- Growth is geometric, so pushing is amortized constant time.
#guard rawCapacity ((Int32Array.mk #[1, 2, 3, 4]).push 5) ≥ 8


/-! Appending -/

#guard (Int32Array.mk #[1, 2] ++ Int32Array.mk #[3, (-2147483648)]).data == #[1, 2, 3, (-2147483648)]
#guard ((Int32Array.mk #[1, 2]).append (Int32Array.mk #[3])).data == #[1, 2, 3]
#guard (Int32Array.mk #[1, 2] ++ Int32Array.empty).data == #[1, 2]
#guard (Int32Array.empty ++ Int32Array.mk #[1, 2]).data == #[1, 2]
#guard (Int32Array.empty ++ Int32Array.empty).data == #[]
#guard (Int32Array.mk #[0, 0] ++ Int32Array.mk #[(-2147483648)] ++ Int32Array.mk #[0]).data ==
  #[0, 0, (-2147483648), 0]

-- Appending an array to itself, with and without room.
#guard
  let a := Int32Array.mk #[1, 2, 3]
  (a ++ a).data == #[1, 2, 3, 1, 2, 3]

#guard
  let a := (Int32Array.emptyWithCapacity 10).push 1 |>.push 2
  (a ++ a).data == #[1, 2, 1, 2]

-- Appending to a shared array must leave the original unchanged, with and without room. The
-- results are checked first so that they are computed while the original is still live.
#guard
  let a := (Int32Array.emptyWithCapacity 10).push 1
  let b := a ++ Int32Array.mk #[2, 3]
  let c := a ++ Int32Array.mk #[4]
  c.data == #[1, 4] && b.data == #[1, 2, 3] && a.data == #[1]

#guard
  let a := Int32Array.mk #[1]
  let b := a ++ Int32Array.mk #[2, 3]
  b.data == #[1, 2, 3] && a.data == #[1]

-- The right operand is never modified.
#guard
  let b := Int32Array.mk #[2, 3]
  let c := Int32Array.mk #[1] ++ b
  c.data == #[1, 2, 3] && b.data == #[2, 3]

-- Many appends to an exclusive array.
#guard Id.run do
  let mut a := Int32Array.empty
  let mut r : Array Int32 := #[]
  for i in [0:1000] do
    a := a ++ Int32Array.mk #[i.toInt32, (i * 7).toInt32, (-2147483648)]
    r := r ++ #[i.toInt32, (i * 7).toInt32, (-2147483648)]
  return a.data == r

-- Large arrays on both sides.
#guard
  let xs := (Array.range 50000).map Nat.toInt32
  let ys := (Array.range 50000).map fun i => (i * 3).toInt32
  (Int32Array.mk xs ++ Int32Array.mk ys).data == xs ++ ys

-- An exclusive array with room is appended to in place, and growth is geometric.
-- The array is built from a parameter so that it isn't extracted as a shared closed term.
@[noinline] def Int32Array.appendsInPlace (x : Int32) : Bool :=
  let a := (Int32Array.emptyWithCapacity 10).push x
  let p := rawAddr a
  let a := a ++ Int32Array.mk #[2, 3]
  rawAddr a == p && a.data == #[x, 2, 3]

@[noinline] def Int32Array.appendsToCopyWhenShared (x : Int32) : Bool :=
  let a := (Int32Array.emptyWithCapacity 10).push x
  let p := rawAddr a
  let b := a ++ Int32Array.mk #[2, 3]
  rawAddr b != p && b.data == #[x, 2, 3] && a.data == #[x]

#guard Int32Array.appendsInPlace 1
#guard Int32Array.appendsToCopyWhenShared 1

#guard rawCapacity ((Int32Array.emptyWithCapacity 10).push 1 ++ Int32Array.mk #[2, 3]) ≥ 10
#guard rawCapacity (Int32Array.mk #[1, 2, 3, 4] ++ Int32Array.mk #[5]) ≥ 8
#guard rawCapacity (Int32Array.mk #[1] ++ Int32Array.mk (Array.replicate 10 0)) ≥ 11
#guard rawElemSize (Int32Array.mk #[1] ++ Int32Array.mk #[2]) == (4 : UInt32)
