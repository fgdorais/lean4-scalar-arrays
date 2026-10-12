/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ScalarArray.ISize
import ScalarArrayTest.Util

open ScalarArray ScalarArrayTest

/-! Construction and conversion -/

#guard (ISizeArray.mk #[1, 2, 3, (-9223372036854775808)]).data == #[1, 2, 3, (-9223372036854775808)]
#guard (ISizeArray.mk #[1, 2, 3, (-9223372036854775808)]).toList == [1, 2, 3, (-9223372036854775808)]
#guard (ISizeArray.mk #[]).data == #[]
#guard ISizeArray.empty.data == #[]
#guard (∅ : ISizeArray).data == #[]
#guard (default : ISizeArray).data == #[]
#guard (ISizeArray.emptyWithCapacity 100).data == #[]
#guard (ISizeArray.mk (Array.range 1000 |>.map Nat.toISize)).data == (Array.range 1000).map Nat.toISize

/-! Size -/

#guard (ISizeArray.mk #[1, 2, 3, (-9223372036854775808)]).size == 4
#guard (ISizeArray.mk #[1, 2, 3, (-9223372036854775808)]).usize == 4
#guard ISizeArray.empty.size == 0
#guard (ISizeArray.emptyWithCapacity 100).size == 0

/-! Reading -/

#guard (ISizeArray.mk #[1, 2, 3, (-9223372036854775808)])[0] == 1
#guard (ISizeArray.mk #[1, 2, 3, (-9223372036854775808)])[3] == (-9223372036854775808)
#guard (ISizeArray.mk #[1, 2, 3, (-9223372036854775808)])[(2 : USize)] == 3
#guard (ISizeArray.mk #[1, 2, 3, (-9223372036854775808)]).get! 1 == 2
#guard (ISizeArray.mk #[1, 2, 3, (-9223372036854775808)]).getD 2 7 == 3
#guard (ISizeArray.mk #[1, 2, 3, (-9223372036854775808)]).getD 4 7 == 7
#guard (ISizeArray.mk #[1, 2, 3, (-9223372036854775808)])[4]? == none
#guard (ISizeArray.mk #[1, 2, 3, (-9223372036854775808)])[1]? == some 2

/-! Writing -/

#guard ((ISizeArray.mk #[1, 2, 3]).set 1 42 (by decide)).data == #[1, 42, 3]
#guard ((ISizeArray.mk #[1, 2, 3]).uset 2 42 (by simp)).data == #[1, 2, 42]
#guard ((ISizeArray.mk #[1, 2, 3]).set! 0 (-9223372036854775808)).data == #[(-9223372036854775808), 2, 3]
#guard ((ISizeArray.mk #[1, 2, 3]).setD 0 0).data == #[0, 2, 3]
#guard ((ISizeArray.mk #[1, 2, 3]).setD 3 42).data == #[1, 2, 3]

-- Writing to a shared array must leave the original unchanged. The result is checked first so
-- that it is computed while the original is still live.
#guard
  let a := ISizeArray.mk #[1, 2, 3]
  let b := a.set! 1 42
  b.data == #[1, 42, 3] && a.data == #[1, 2, 3]

-- Repeated writes to an exclusive array.
#guard Id.run do
  let mut a := ISizeArray.mk (Array.replicate 1000 0)
  for i in [0:1000] do
    a := a.set! i (i * 3).toISize
  return a.data == (Array.range 1000).map fun i => (i * 3).toISize

/-! Pushing -/

#guard (ISizeArray.empty.push 5 |>.push 6).data == #[5, 6]
#guard ((ISizeArray.emptyWithCapacity 1).push 5 |>.push 6 |>.push 7).data == #[5, 6, 7]
#guard ((ISizeArray.mk #[1, 2]).push 3).data == #[1, 2, 3]

-- Pushing past the capacity many times.
#guard Id.run do
  let mut a := ISizeArray.empty
  for i in [0:10000] do
    a := a.push i.toISize
  return a.size == 10000 && a.data == (Array.range 10000).map Nat.toISize

-- Pushing to a shared array must leave the original unchanged. The results are checked first so
-- that they are computed while the original is still live.
#guard
  let a := (ISizeArray.emptyWithCapacity 10).push 1
  let b := a.push 2
  let c := a.push 3
  c.data == #[1, 3] && b.data == #[1, 2] && a.data == #[1]

/-! Printing -/

#guard toString (ISizeArray.mk #[1, 2]) == "ISizeArray.mk " ++ toString #[(1 : ISize), 2]
#guard reprStr (ISizeArray.mk #[1, 2]) == "ISizeArray.mk " ++ reprStr #[(1 : ISize), 2]

/-! Every index, through both `Nat` and `USize` indices -/

#guard
  let a := ISizeArray.mk ((Array.range 300).map Nat.toISize)
  (List.range 300).all fun i =>
    a[i]! == i.toISize && a.getD i 0 == i.toISize && a.get! i == i.toISize &&
      (if h : i.toUSize.toNat < a.size then a[i.toUSize] == i.toISize else false)

/-! Writes don't touch neighbouring elements -/

#guard ((ISizeArray.mk #[0, 0, 0]).set! 1 (-9223372036854775808)).data == #[0, (-9223372036854775808), 0]
#guard ((ISizeArray.mk #[(-9223372036854775808), (-9223372036854775808), (-9223372036854775808)]).set! 1 0).data == #[(-9223372036854775808), 0, (-9223372036854775808)]
#guard ((ISizeArray.mk #[0, 0, 0]).push (-9223372036854775808) |>.push 0).data == #[0, 0, 0, (-9223372036854775808), 0]

/-! Indices beyond 16 bits, and huge `Nat` indices -/

#guard
  let a := (ISizeArray.mk (Array.replicate 100000 0)).set! 99999 (-9223372036854775808) |>.set! 70000 1
  a.size == 100000 && a[99999]! == (-9223372036854775808) && a[70000]! == 1 && a[99998]! == 0 &&
    a[70000 % 65536]! == 0 && a.data[99999]! == (-9223372036854775808) && a.data[70000]! == 1 &&
    (if h : (70000 : USize).toNat < a.size then a[(70000 : USize)] == 1 else false)

#guard (ISizeArray.mk #[1, 2, 3])[2 ^ 70]? == none
#guard (ISizeArray.mk #[1, 2, 3]).getD (2 ^ 70) 7 == 7
#guard ((ISizeArray.mk #[1, 2, 3]).setD (2 ^ 70) 7).data == #[1, 2, 3]

/-! Pushing onto a shared array that is at full capacity -/

#guard
  let a := ISizeArray.mk #[1]
  let b := a.push 2
  b.data == #[1, 2] && a.data == #[1]

#guard
  let a := ISizeArray.mk #[]
  let b := a.push 2
  b.data == #[2] && a.data == #[]

/-! Conversions don't alias -/

#guard
  let a := #[(1 : ISize), 2, 3]
  let b := (ISizeArray.mk a).set! 0 (-9223372036854775808)
  b.data == #[(-9223372036854775808), 2, 3] && a == #[1, 2, 3]

#guard
  let a := ISizeArray.mk #[1, 2, 3]
  let d := a.data.set! 0 (-9223372036854775808)
  d == #[(-9223372036854775808), 2, 3] && a.data == #[1, 2, 3]

/-! Runtime representation -/

#guard rawElemSize (ISizeArray.mk #[1, 2, 3]) == ((System.Platform.numBits / 8).toUInt32 : UInt32)
#guard rawElemSize (ISizeArray.emptyWithCapacity 10) == ((System.Platform.numBits / 8).toUInt32 : UInt32)
#guard rawElemSize (ISizeArray.empty.push 1) == ((System.Platform.numBits / 8).toUInt32 : UInt32)
#guard rawElemSize ((ISizeArray.mk #[1]).push 2) == ((System.Platform.numBits / 8).toUInt32 : UInt32)
#guard rawCapacity (ISizeArray.emptyWithCapacity 100) ≥ 100
#guard rawCapacity (ISizeArray.mk #[1, 2, 3]) ≥ 3
-- Growth is geometric, so pushing is amortized constant time.
#guard rawCapacity ((ISizeArray.mk #[1, 2, 3, 4]).push 5) ≥ 8

