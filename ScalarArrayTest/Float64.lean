/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ScalarArray.Float64
import ScalarArrayTest.Util

open ScalarArray ScalarArrayTest

/-! Construction and conversion -/

#guard (Float64Array.mk #[1, 2, 3, (-1.5e300)]).data == #[1, 2, 3, (-1.5e300)]
#guard (Float64Array.mk #[1, 2, 3, (-1.5e300)]).toList == [1, 2, 3, (-1.5e300)]
#guard (Float64Array.mk #[]).data == #[]
#guard Float64Array.empty.data == #[]
#guard (∅ : Float64Array).data == #[]
#guard (default : Float64Array).data == #[]
#guard (Float64Array.emptyWithCapacity 100).data == #[]
#guard (Float64Array.mk (Array.range 1000 |>.map Nat.toFloat)).data == (Array.range 1000).map Nat.toFloat

/-! Size -/

#guard (Float64Array.mk #[1, 2, 3, (-1.5e300)]).size == 4
#guard (Float64Array.mk #[1, 2, 3, (-1.5e300)]).usize == 4
#guard Float64Array.empty.size == 0
#guard (Float64Array.emptyWithCapacity 100).size == 0

/-! Reading -/

#guard (Float64Array.mk #[1, 2, 3, (-1.5e300)])[0] == 1
#guard (Float64Array.mk #[1, 2, 3, (-1.5e300)])[3] == (-1.5e300)
#guard (Float64Array.mk #[1, 2, 3, (-1.5e300)])[(2 : USize)] == 3
#guard (Float64Array.mk #[1, 2, 3, (-1.5e300)]).get! 1 == 2
#guard (Float64Array.mk #[1, 2, 3, (-1.5e300)]).getD 2 7 == 3
#guard (Float64Array.mk #[1, 2, 3, (-1.5e300)]).getD 4 7 == 7
#guard (Float64Array.mk #[1, 2, 3, (-1.5e300)])[4]? == none
#guard (Float64Array.mk #[1, 2, 3, (-1.5e300)])[1]? == some 2

/-! Writing -/

#guard ((Float64Array.mk #[1, 2, 3]).set 1 42 (by decide)).data == #[1, 42, 3]
#guard ((Float64Array.mk #[1, 2, 3]).uset 2 42 (by simp)).data == #[1, 2, 42]
#guard ((Float64Array.mk #[1, 2, 3]).set! 0 (-1.5e300)).data == #[(-1.5e300), 2, 3]
#guard ((Float64Array.mk #[1, 2, 3]).setD 0 0).data == #[0, 2, 3]
#guard ((Float64Array.mk #[1, 2, 3]).setD 3 42).data == #[1, 2, 3]

-- Writing to a shared array must leave the original unchanged. The result is checked first so
-- that it is computed while the original is still live.
#guard
  let a := Float64Array.mk #[1, 2, 3]
  let b := a.set! 1 42
  b.data == #[1, 42, 3] && a.data == #[1, 2, 3]

-- Repeated writes to an exclusive array.
#guard Id.run do
  let mut a := Float64Array.mk (Array.replicate 1000 0)
  for i in [0:1000] do
    a := a.set! i (i * 3).toFloat
  return a.data == (Array.range 1000).map fun i => (i * 3).toFloat

/-! Pushing -/

#guard (Float64Array.empty.push 5 |>.push 6).data == #[5, 6]
#guard ((Float64Array.emptyWithCapacity 1).push 5 |>.push 6 |>.push 7).data == #[5, 6, 7]
#guard ((Float64Array.mk #[1, 2]).push 3).data == #[1, 2, 3]

-- Pushing past the capacity many times.
#guard Id.run do
  let mut a := Float64Array.empty
  for i in [0:10000] do
    a := a.push i.toFloat
  return a.size == 10000 && a.data == (Array.range 10000).map Nat.toFloat

-- Pushing to a shared array must leave the original unchanged. The results are checked first so
-- that they are computed while the original is still live.
#guard
  let a := (Float64Array.emptyWithCapacity 10).push 1
  let b := a.push 2
  let c := a.push 3
  c.data == #[1, 3] && b.data == #[1, 2] && a.data == #[1]

/-! Printing -/

#guard toString (Float64Array.mk #[1, 2]) == "Float64Array.mk " ++ toString #[(1 : Float), 2]
#guard reprStr (Float64Array.mk #[1, 2]) == "Float64Array.mk " ++ reprStr #[(1 : Float), 2]

/-! Every index, through both `Nat` and `USize` indices -/

#guard
  let a := Float64Array.mk ((Array.range 300).map Nat.toFloat)
  (List.range 300).all fun i =>
    a[i]! == i.toFloat && a.getD i 0 == i.toFloat && a.get! i == i.toFloat &&
      (if h : i.toUSize.toNat < a.size then a[i.toUSize] == i.toFloat else false)

/-! Writes don't touch neighbouring elements -/

#guard ((Float64Array.mk #[0, 0, 0]).set! 1 (-1.5e300)).data == #[0, (-1.5e300), 0]
#guard ((Float64Array.mk #[(-1.5e300), (-1.5e300), (-1.5e300)]).set! 1 0).data == #[(-1.5e300), 0, (-1.5e300)]
#guard ((Float64Array.mk #[0, 0, 0]).push (-1.5e300) |>.push 0).data == #[0, 0, 0, (-1.5e300), 0]

/-! Indices beyond 16 bits, and huge `Nat` indices -/

#guard
  let a := (Float64Array.mk (Array.replicate 100000 0)).set! 99999 (-1.5e300) |>.set! 70000 1
  a.size == 100000 && a[99999]! == (-1.5e300) && a[70000]! == 1 && a[99998]! == 0 &&
    a[70000 % 65536]! == 0 && a.data[99999]! == (-1.5e300) && a.data[70000]! == 1 &&
    (if h : (70000 : USize).toNat < a.size then a[(70000 : USize)] == 1 else false)

#guard (Float64Array.mk #[1, 2, 3])[2 ^ 70]? == none
#guard (Float64Array.mk #[1, 2, 3]).getD (2 ^ 70) 7 == 7
#guard ((Float64Array.mk #[1, 2, 3]).setD (2 ^ 70) 7).data == #[1, 2, 3]

/-! Pushing onto a shared array that is at full capacity -/

#guard
  let a := Float64Array.mk #[1]
  let b := a.push 2
  b.data == #[1, 2] && a.data == #[1]

#guard
  let a := Float64Array.mk #[]
  let b := a.push 2
  b.data == #[2] && a.data == #[]

/-! Conversions don't alias -/

#guard
  let a := #[(1 : Float), 2, 3]
  let b := (Float64Array.mk a).set! 0 (-1.5e300)
  b.data == #[(-1.5e300), 2, 3] && a == #[1, 2, 3]

#guard
  let a := Float64Array.mk #[1, 2, 3]
  let d := a.data.set! 0 (-1.5e300)
  d == #[(-1.5e300), 2, 3] && a.data == #[1, 2, 3]

/-! Runtime representation -/

#guard rawElemSize (Float64Array.mk #[1, 2, 3]) == (8 : UInt32)
#guard rawElemSize (Float64Array.emptyWithCapacity 10) == (8 : UInt32)
#guard rawElemSize (Float64Array.empty.push 1) == (8 : UInt32)
#guard rawElemSize ((Float64Array.mk #[1]).push 2) == (8 : UInt32)
#guard rawCapacity (Float64Array.emptyWithCapacity 100) ≥ 100
#guard rawCapacity (Float64Array.mk #[1, 2, 3]) ≥ 3
-- Growth is geometric, so pushing is amortized constant time.
#guard rawCapacity ((Float64Array.mk #[1, 2, 3, 4]).push 5) ≥ 8

