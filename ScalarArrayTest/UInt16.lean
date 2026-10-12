/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ScalarArray.UInt16
import ScalarArrayTest.Util

open ScalarArray ScalarArrayTest

/-! Construction and conversion -/

#guard (UInt16Array.mk #[1, 2, 3, 65535]).data == #[1, 2, 3, 65535]
#guard (UInt16Array.mk #[1, 2, 3, 65535]).toList == [1, 2, 3, 65535]
#guard (UInt16Array.mk #[]).data == #[]
#guard UInt16Array.empty.data == #[]
#guard (∅ : UInt16Array).data == #[]
#guard (default : UInt16Array).data == #[]
#guard (UInt16Array.emptyWithCapacity 100).data == #[]
#guard (UInt16Array.mk (Array.range 1000 |>.map Nat.toUInt16)).data == (Array.range 1000).map Nat.toUInt16

/-! Size -/

#guard (UInt16Array.mk #[1, 2, 3, 65535]).size == 4
#guard (UInt16Array.mk #[1, 2, 3, 65535]).usize == 4
#guard UInt16Array.empty.size == 0
#guard (UInt16Array.emptyWithCapacity 100).size == 0

/-! Reading -/

#guard (UInt16Array.mk #[1, 2, 3, 65535])[0] == 1
#guard (UInt16Array.mk #[1, 2, 3, 65535])[3] == 65535
#guard (UInt16Array.mk #[1, 2, 3, 65535])[(2 : USize)] == 3
#guard (UInt16Array.mk #[1, 2, 3, 65535]).get! 1 == 2
#guard (UInt16Array.mk #[1, 2, 3, 65535]).getD 2 7 == 3
#guard (UInt16Array.mk #[1, 2, 3, 65535]).getD 4 7 == 7
#guard (UInt16Array.mk #[1, 2, 3, 65535])[4]? == none
#guard (UInt16Array.mk #[1, 2, 3, 65535])[1]? == some 2

/-! Writing -/

#guard ((UInt16Array.mk #[1, 2, 3]).set 1 42 (by decide)).data == #[1, 42, 3]
#guard ((UInt16Array.mk #[1, 2, 3]).uset 2 42 (by simp)).data == #[1, 2, 42]
#guard ((UInt16Array.mk #[1, 2, 3]).set! 0 65535).data == #[65535, 2, 3]
#guard ((UInt16Array.mk #[1, 2, 3]).setD 0 0).data == #[0, 2, 3]
#guard ((UInt16Array.mk #[1, 2, 3]).setD 3 42).data == #[1, 2, 3]

-- Writing to a shared array must leave the original unchanged. The result is checked first so
-- that it is computed while the original is still live.
#guard
  let a := UInt16Array.mk #[1, 2, 3]
  let b := a.set! 1 42
  b.data == #[1, 42, 3] && a.data == #[1, 2, 3]

-- Repeated writes to an exclusive array.
#guard Id.run do
  let mut a := UInt16Array.mk (Array.replicate 1000 0)
  for i in [0:1000] do
    a := a.set! i (i * 3).toUInt16
  return a.data == (Array.range 1000).map fun i => (i * 3).toUInt16

/-! Pushing -/

#guard (UInt16Array.empty.push 5 |>.push 6).data == #[5, 6]
#guard ((UInt16Array.emptyWithCapacity 1).push 5 |>.push 6 |>.push 7).data == #[5, 6, 7]
#guard ((UInt16Array.mk #[1, 2]).push 3).data == #[1, 2, 3]

-- Pushing past the capacity many times.
#guard Id.run do
  let mut a := UInt16Array.empty
  for i in [0:10000] do
    a := a.push i.toUInt16
  return a.size == 10000 && a.data == (Array.range 10000).map Nat.toUInt16

-- Pushing to a shared array must leave the original unchanged. The results are checked first so
-- that they are computed while the original is still live.
#guard
  let a := (UInt16Array.emptyWithCapacity 10).push 1
  let b := a.push 2
  let c := a.push 3
  c.data == #[1, 3] && b.data == #[1, 2] && a.data == #[1]

/-! Printing -/

#guard toString (UInt16Array.mk #[1, 2]) == "UInt16Array.mk " ++ toString #[(1 : UInt16), 2]
#guard reprStr (UInt16Array.mk #[1, 2]) == "UInt16Array.mk " ++ reprStr #[(1 : UInt16), 2]

/-! Every index, through both `Nat` and `USize` indices -/

#guard
  let a := UInt16Array.mk ((Array.range 300).map Nat.toUInt16)
  (List.range 300).all fun i =>
    a[i]! == i.toUInt16 && a.getD i 0 == i.toUInt16 && a.get! i == i.toUInt16 &&
      (if h : i.toUSize.toNat < a.size then a[i.toUSize] == i.toUInt16 else false)

/-! Writes don't touch neighbouring elements -/

#guard ((UInt16Array.mk #[0, 0, 0]).set! 1 65535).data == #[0, 65535, 0]
#guard ((UInt16Array.mk #[65535, 65535, 65535]).set! 1 0).data == #[65535, 0, 65535]
#guard ((UInt16Array.mk #[0, 0, 0]).push 65535 |>.push 0).data == #[0, 0, 0, 65535, 0]

/-! Indices beyond 16 bits, and huge `Nat` indices -/

#guard
  let a := (UInt16Array.mk (Array.replicate 100000 0)).set! 99999 65535 |>.set! 70000 1
  a.size == 100000 && a[99999]! == 65535 && a[70000]! == 1 && a[99998]! == 0 &&
    a[70000 % 65536]! == 0 && a.data[99999]! == 65535 && a.data[70000]! == 1 &&
    (if h : (70000 : USize).toNat < a.size then a[(70000 : USize)] == 1 else false)

#guard (UInt16Array.mk #[1, 2, 3])[2 ^ 70]? == none
#guard (UInt16Array.mk #[1, 2, 3]).getD (2 ^ 70) 7 == 7
#guard ((UInt16Array.mk #[1, 2, 3]).setD (2 ^ 70) 7).data == #[1, 2, 3]

/-! Pushing onto a shared array that is at full capacity -/

#guard
  let a := UInt16Array.mk #[1]
  let b := a.push 2
  b.data == #[1, 2] && a.data == #[1]

#guard
  let a := UInt16Array.mk #[]
  let b := a.push 2
  b.data == #[2] && a.data == #[]

/-! Conversions don't alias -/

#guard
  let a := #[(1 : UInt16), 2, 3]
  let b := (UInt16Array.mk a).set! 0 65535
  b.data == #[65535, 2, 3] && a == #[1, 2, 3]

#guard
  let a := UInt16Array.mk #[1, 2, 3]
  let d := a.data.set! 0 65535
  d == #[65535, 2, 3] && a.data == #[1, 2, 3]

/-! Runtime representation -/

#guard rawElemSize (UInt16Array.mk #[1, 2, 3]) == (2 : UInt32)
#guard rawElemSize (UInt16Array.emptyWithCapacity 10) == (2 : UInt32)
#guard rawElemSize (UInt16Array.empty.push 1) == (2 : UInt32)
#guard rawElemSize ((UInt16Array.mk #[1]).push 2) == (2 : UInt32)
#guard rawCapacity (UInt16Array.emptyWithCapacity 100) ≥ 100
#guard rawCapacity (UInt16Array.mk #[1, 2, 3]) ≥ 3
-- Growth is geometric, so pushing is amortized constant time.
#guard rawCapacity ((UInt16Array.mk #[1, 2, 3, 4]).push 5) ≥ 8

