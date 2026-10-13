/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ScalarArray.UInt8
import ScalarArrayTest.Util

open ScalarArray ScalarArrayTest

/-! Construction and conversion -/

#guard (UInt8Array.mk #[1, 2, 3, 255]).data == #[1, 2, 3, 255]
#guard (UInt8Array.mk #[1, 2, 3, 255]).toList == [1, 2, 3, 255]
#guard (UInt8Array.mk #[]).data == #[]
#guard UInt8Array.empty.data == #[]
#guard (∅ : UInt8Array).data == #[]
#guard (default : UInt8Array).data == #[]
#guard (UInt8Array.emptyWithCapacity 100).data == #[]
#guard (UInt8Array.mk (Array.range 1000 |>.map Nat.toUInt8)).data == (Array.range 1000).map Nat.toUInt8

/-! Size -/

#guard (UInt8Array.mk #[1, 2, 3, 255]).size == 4
#guard (UInt8Array.mk #[1, 2, 3, 255]).usize == 4
#guard UInt8Array.empty.size == 0
#guard (UInt8Array.emptyWithCapacity 100).size == 0

/-! Reading -/

#guard (UInt8Array.mk #[1, 2, 3, 255])[0] == 1
#guard (UInt8Array.mk #[1, 2, 3, 255])[3] == 255
#guard (UInt8Array.mk #[1, 2, 3, 255])[(2 : USize)] == 3
#guard (UInt8Array.mk #[1, 2, 3, 255]).get! 1 == 2
#guard (UInt8Array.mk #[1, 2, 3, 255]).getD 2 7 == 3
#guard (UInt8Array.mk #[1, 2, 3, 255]).getD 4 7 == 7
#guard (UInt8Array.mk #[1, 2, 3, 255])[4]? == none
#guard (UInt8Array.mk #[1, 2, 3, 255])[1]? == some 2

/-! Writing -/

#guard ((UInt8Array.mk #[1, 2, 3]).set 1 42 (by decide)).data == #[1, 42, 3]
#guard ((UInt8Array.mk #[1, 2, 3]).uset 2 42 (by simp)).data == #[1, 2, 42]
#guard ((UInt8Array.mk #[1, 2, 3]).set! 0 255).data == #[255, 2, 3]

-- Writing to a shared array must leave the original unchanged. The result is checked first so
-- that it is computed while the original is still live.
#guard
  let a := UInt8Array.mk #[1, 2, 3]
  let b := a.set! 1 42
  b.data == #[1, 42, 3] && a.data == #[1, 2, 3]

-- Repeated writes to an exclusive array.
#guard Id.run do
  let mut a := UInt8Array.mk (Array.replicate 1000 0)
  for i in [0:1000] do
    a := a.set! i (i * 3).toUInt8
  return a.data == (Array.range 1000).map fun i => (i * 3).toUInt8

/-! Pushing -/

#guard (UInt8Array.empty.push 5 |>.push 6).data == #[5, 6]
#guard ((UInt8Array.emptyWithCapacity 1).push 5 |>.push 6 |>.push 7).data == #[5, 6, 7]
#guard ((UInt8Array.mk #[1, 2]).push 3).data == #[1, 2, 3]

-- Pushing past the capacity many times.
#guard Id.run do
  let mut a := UInt8Array.empty
  for i in [0:10000] do
    a := a.push i.toUInt8
  return a.size == 10000 && a.data == (Array.range 10000).map Nat.toUInt8

-- Pushing to a shared array must leave the original unchanged. The results are checked first so
-- that they are computed while the original is still live.
#guard
  let a := (UInt8Array.emptyWithCapacity 10).push 1
  let b := a.push 2
  let c := a.push 3
  c.data == #[1, 3] && b.data == #[1, 2] && a.data == #[1]

/-! Printing -/

#guard toString (UInt8Array.mk #[1, 2]) == "UInt8Array.mk " ++ toString #[(1 : UInt8), 2]
#guard reprStr (UInt8Array.mk #[1, 2]) == "UInt8Array.mk " ++ reprStr #[(1 : UInt8), 2]

/-! Every index, through both `Nat` and `USize` indices -/

#guard
  let a := UInt8Array.mk ((Array.range 300).map Nat.toUInt8)
  (List.range 300).all fun i =>
    a[i]! == i.toUInt8 && a.getD i 0 == i.toUInt8 && a.get! i == i.toUInt8 &&
      (if h : i.toUSize.toNat < a.size then a[i.toUSize] == i.toUInt8 else false)

/-! Writes don't touch neighbouring elements -/

#guard ((UInt8Array.mk #[0, 0, 0]).set! 1 255).data == #[0, 255, 0]
#guard ((UInt8Array.mk #[255, 255, 255]).set! 1 0).data == #[255, 0, 255]
#guard ((UInt8Array.mk #[0, 0, 0]).push 255 |>.push 0).data == #[0, 0, 0, 255, 0]

/-! Indices beyond 16 bits, and huge `Nat` indices -/

#guard
  let a := (UInt8Array.mk (Array.replicate 100000 0)).set! 99999 255 |>.set! 70000 1
  a.size == 100000 && a[99999]! == 255 && a[70000]! == 1 && a[99998]! == 0 &&
    a[70000 % 65536]! == 0 && a.data[99999]! == 255 && a.data[70000]! == 1 &&
    (if h : (70000 : USize).toNat < a.size then a[(70000 : USize)] == 1 else false)

#guard (UInt8Array.mk #[1, 2, 3])[2 ^ 70]? == none
#guard (UInt8Array.mk #[1, 2, 3]).getD (2 ^ 70) 7 == 7

/-! Pushing onto a shared array that is at full capacity -/

#guard
  let a := UInt8Array.mk #[1]
  let b := a.push 2
  b.data == #[1, 2] && a.data == #[1]

#guard
  let a := UInt8Array.mk #[]
  let b := a.push 2
  b.data == #[2] && a.data == #[]

/-! Conversions don't alias -/

#guard
  let a := #[(1 : UInt8), 2, 3]
  let b := (UInt8Array.mk a).set! 0 255
  b.data == #[255, 2, 3] && a == #[1, 2, 3]

#guard
  let a := UInt8Array.mk #[1, 2, 3]
  let d := a.data.set! 0 255
  d == #[255, 2, 3] && a.data == #[1, 2, 3]

/-! Runtime representation -/

#guard rawElemSize (UInt8Array.mk #[1, 2, 3]) == (1 : UInt32)
#guard rawElemSize (UInt8Array.emptyWithCapacity 10) == (1 : UInt32)
#guard rawElemSize (UInt8Array.empty.push 1) == (1 : UInt32)
#guard rawElemSize ((UInt8Array.mk #[1]).push 2) == (1 : UInt32)
#guard rawCapacity (UInt8Array.emptyWithCapacity 100) ≥ 100
#guard rawCapacity (UInt8Array.mk #[1, 2, 3]) ≥ 3
-- Growth is geometric, so pushing is amortized constant time.
#guard rawCapacity ((UInt8Array.mk #[1, 2, 3, 4]).push 5) ≥ 8

