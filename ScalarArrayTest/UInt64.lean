/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ScalarArray.UInt64
import ScalarArrayTest.Util

open ScalarArray ScalarArrayTest

/-! Construction and conversion -/

#guard (UInt64Array.mk #[1, 2, 3, 18446744073709551615]).data == #[1, 2, 3, 18446744073709551615]
#guard (UInt64Array.mk #[1, 2, 3, 18446744073709551615]).toList == [1, 2, 3, 18446744073709551615]
#guard (UInt64Array.mk #[]).data == #[]
#guard UInt64Array.empty.data == #[]
#guard (∅ : UInt64Array).data == #[]
#guard (default : UInt64Array).data == #[]
#guard (UInt64Array.emptyWithCapacity 100).data == #[]
#guard (UInt64Array.mk (Array.range 1000 |>.map Nat.toUInt64)).data == (Array.range 1000).map Nat.toUInt64

/-! Size -/

#guard (UInt64Array.mk #[1, 2, 3, 18446744073709551615]).size == 4
#guard (UInt64Array.mk #[1, 2, 3, 18446744073709551615]).usize == 4
#guard UInt64Array.empty.size == 0
#guard (UInt64Array.emptyWithCapacity 100).size == 0

/-! Reading -/

#guard (UInt64Array.mk #[1, 2, 3, 18446744073709551615])[0] == 1
#guard (UInt64Array.mk #[1, 2, 3, 18446744073709551615])[3] == 18446744073709551615
#guard (UInt64Array.mk #[1, 2, 3, 18446744073709551615])[(2 : USize)] == 3
#guard (UInt64Array.mk #[1, 2, 3, 18446744073709551615]).get! 1 == 2
#guard (UInt64Array.mk #[1, 2, 3, 18446744073709551615]).getD 2 7 == 3
#guard (UInt64Array.mk #[1, 2, 3, 18446744073709551615]).getD 4 7 == 7
#guard (UInt64Array.mk #[1, 2, 3, 18446744073709551615])[4]? == none
#guard (UInt64Array.mk #[1, 2, 3, 18446744073709551615])[1]? == some 2

/-! Writing -/

#guard ((UInt64Array.mk #[1, 2, 3]).set 1 42 (by decide)).data == #[1, 42, 3]
#guard ((UInt64Array.mk #[1, 2, 3]).uset 2 42 (by simp)).data == #[1, 2, 42]
#guard ((UInt64Array.mk #[1, 2, 3]).set! 0 18446744073709551615).data == #[18446744073709551615, 2, 3]

-- Writing to a shared array must leave the original unchanged. The result is checked first so
-- that it is computed while the original is still live.
#guard
  let a := UInt64Array.mk #[1, 2, 3]
  let b := a.set! 1 42
  b.data == #[1, 42, 3] && a.data == #[1, 2, 3]

-- Repeated writes to an exclusive array.
#guard Id.run do
  let mut a := UInt64Array.mk (Array.replicate 1000 0)
  for i in [0:1000] do
    a := a.set! i (i * 3).toUInt64
  return a.data == (Array.range 1000).map fun i => (i * 3).toUInt64

/-! Pushing -/

#guard (UInt64Array.empty.push 5 |>.push 6).data == #[5, 6]
#guard ((UInt64Array.emptyWithCapacity 1).push 5 |>.push 6 |>.push 7).data == #[5, 6, 7]
#guard ((UInt64Array.mk #[1, 2]).push 3).data == #[1, 2, 3]

-- Pushing past the capacity many times.
#guard Id.run do
  let mut a := UInt64Array.empty
  for i in [0:10000] do
    a := a.push i.toUInt64
  return a.size == 10000 && a.data == (Array.range 10000).map Nat.toUInt64

-- Pushing to a shared array must leave the original unchanged. The results are checked first so
-- that they are computed while the original is still live.
#guard
  let a := (UInt64Array.emptyWithCapacity 10).push 1
  let b := a.push 2
  let c := a.push 3
  c.data == #[1, 3] && b.data == #[1, 2] && a.data == #[1]

/-! Printing -/

#guard toString (UInt64Array.mk #[1, 2]) == "UInt64Array.mk " ++ toString #[(1 : UInt64), 2]
#guard reprStr (UInt64Array.mk #[1, 2]) == "UInt64Array.mk " ++ reprStr #[(1 : UInt64), 2]

/-! Every index, through both `Nat` and `USize` indices -/

#guard
  let a := UInt64Array.mk ((Array.range 300).map Nat.toUInt64)
  (List.range 300).all fun i =>
    a[i]! == i.toUInt64 && a.getD i 0 == i.toUInt64 && a.get! i == i.toUInt64 &&
      (if h : i.toUSize.toNat < a.size then a[i.toUSize] == i.toUInt64 else false)

/-! Writes don't touch neighbouring elements -/

#guard ((UInt64Array.mk #[0, 0, 0]).set! 1 18446744073709551615).data == #[0, 18446744073709551615, 0]
#guard ((UInt64Array.mk #[18446744073709551615, 18446744073709551615, 18446744073709551615]).set! 1 0).data == #[18446744073709551615, 0, 18446744073709551615]
#guard ((UInt64Array.mk #[0, 0, 0]).push 18446744073709551615 |>.push 0).data == #[0, 0, 0, 18446744073709551615, 0]

/-! Indices beyond 16 bits, and huge `Nat` indices -/

#guard
  let a := (UInt64Array.mk (Array.replicate 100000 0)).set! 99999 18446744073709551615 |>.set! 70000 1
  a.size == 100000 && a[99999]! == 18446744073709551615 && a[70000]! == 1 && a[99998]! == 0 &&
    a[70000 % 65536]! == 0 && a.data[99999]! == 18446744073709551615 && a.data[70000]! == 1 &&
    (if h : (70000 : USize).toNat < a.size then a[(70000 : USize)] == 1 else false)

#guard (UInt64Array.mk #[1, 2, 3])[2 ^ 70]? == none
#guard (UInt64Array.mk #[1, 2, 3]).getD (2 ^ 70) 7 == 7

/-! Pushing onto a shared array that is at full capacity -/

#guard
  let a := UInt64Array.mk #[1]
  let b := a.push 2
  b.data == #[1, 2] && a.data == #[1]

#guard
  let a := UInt64Array.mk #[]
  let b := a.push 2
  b.data == #[2] && a.data == #[]

/-! Conversions don't alias -/

#guard
  let a := #[(1 : UInt64), 2, 3]
  let b := (UInt64Array.mk a).set! 0 18446744073709551615
  b.data == #[18446744073709551615, 2, 3] && a == #[1, 2, 3]

#guard
  let a := UInt64Array.mk #[1, 2, 3]
  let d := a.data.set! 0 18446744073709551615
  d == #[18446744073709551615, 2, 3] && a.data == #[1, 2, 3]

/-! Runtime representation -/

#guard rawElemSize (UInt64Array.mk #[1, 2, 3]) == (8 : UInt32)
#guard rawElemSize (UInt64Array.emptyWithCapacity 10) == (8 : UInt32)
#guard rawElemSize (UInt64Array.empty.push 1) == (8 : UInt32)
#guard rawElemSize ((UInt64Array.mk #[1]).push 2) == (8 : UInt32)
#guard rawCapacity (UInt64Array.emptyWithCapacity 100) ≥ 100
#guard rawCapacity (UInt64Array.mk #[1, 2, 3]) ≥ 3
-- Growth is geometric, so pushing is amortized constant time.
#guard rawCapacity ((UInt64Array.mk #[1, 2, 3, 4]).push 5) ≥ 8


/-! Appending -/

#guard (UInt64Array.mk #[1, 2] ++ UInt64Array.mk #[3, 18446744073709551615]).data == #[1, 2, 3, 18446744073709551615]
#guard ((UInt64Array.mk #[1, 2]).append (UInt64Array.mk #[3])).data == #[1, 2, 3]
#guard (UInt64Array.mk #[1, 2] ++ UInt64Array.empty).data == #[1, 2]
#guard (UInt64Array.empty ++ UInt64Array.mk #[1, 2]).data == #[1, 2]
#guard (UInt64Array.empty ++ UInt64Array.empty).data == #[]
#guard (UInt64Array.mk #[0, 0] ++ UInt64Array.mk #[18446744073709551615] ++ UInt64Array.mk #[0]).data ==
  #[0, 0, 18446744073709551615, 0]

-- Appending an array to itself, with and without room.
#guard
  let a := UInt64Array.mk #[1, 2, 3]
  (a ++ a).data == #[1, 2, 3, 1, 2, 3]

#guard
  let a := (UInt64Array.emptyWithCapacity 10).push 1 |>.push 2
  (a ++ a).data == #[1, 2, 1, 2]

-- Appending to a shared array must leave the original unchanged, with and without room. The
-- results are checked first so that they are computed while the original is still live.
#guard
  let a := (UInt64Array.emptyWithCapacity 10).push 1
  let b := a ++ UInt64Array.mk #[2, 3]
  let c := a ++ UInt64Array.mk #[4]
  c.data == #[1, 4] && b.data == #[1, 2, 3] && a.data == #[1]

#guard
  let a := UInt64Array.mk #[1]
  let b := a ++ UInt64Array.mk #[2, 3]
  b.data == #[1, 2, 3] && a.data == #[1]

-- The right operand is never modified.
#guard
  let b := UInt64Array.mk #[2, 3]
  let c := UInt64Array.mk #[1] ++ b
  c.data == #[1, 2, 3] && b.data == #[2, 3]

-- Many appends to an exclusive array.
#guard Id.run do
  let mut a := UInt64Array.empty
  let mut r : Array UInt64 := #[]
  for i in [0:1000] do
    a := a ++ UInt64Array.mk #[i.toUInt64, (i * 7).toUInt64, 18446744073709551615]
    r := r ++ #[i.toUInt64, (i * 7).toUInt64, 18446744073709551615]
  return a.data == r

-- Large arrays on both sides.
#guard
  let xs := (Array.range 50000).map Nat.toUInt64
  let ys := (Array.range 50000).map fun i => (i * 3).toUInt64
  (UInt64Array.mk xs ++ UInt64Array.mk ys).data == xs ++ ys

-- An exclusive array with room is appended to in place, and growth is geometric.
-- The array is built from a parameter so that it isn't extracted as a shared closed term.
@[noinline] def UInt64Array.appendsInPlace (x : UInt64) : Bool :=
  let a := (UInt64Array.emptyWithCapacity 10).push x
  let p := rawAddr a
  let a := a ++ UInt64Array.mk #[2, 3]
  rawAddr a == p && a.data == #[x, 2, 3]

@[noinline] def UInt64Array.appendsToCopyWhenShared (x : UInt64) : Bool :=
  let a := (UInt64Array.emptyWithCapacity 10).push x
  let p := rawAddr a
  let b := a ++ UInt64Array.mk #[2, 3]
  rawAddr b != p && b.data == #[x, 2, 3] && a.data == #[x]

#guard UInt64Array.appendsInPlace 1
#guard UInt64Array.appendsToCopyWhenShared 1

#guard rawCapacity ((UInt64Array.emptyWithCapacity 10).push 1 ++ UInt64Array.mk #[2, 3]) ≥ 10
#guard rawCapacity (UInt64Array.mk #[1, 2, 3, 4] ++ UInt64Array.mk #[5]) ≥ 8
#guard rawCapacity (UInt64Array.mk #[1] ++ UInt64Array.mk (Array.replicate 10 0)) ≥ 11
#guard rawElemSize (UInt64Array.mk #[1] ++ UInt64Array.mk #[2]) == (8 : UInt32)
