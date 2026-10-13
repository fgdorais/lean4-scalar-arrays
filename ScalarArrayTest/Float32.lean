/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ScalarArray.Float32
import ScalarArrayTest.Util

open ScalarArray ScalarArrayTest

/-! Construction and conversion -/

#guard (Float32Array.mk #[1, 2, 3, (-1.5e38)]).data == #[1, 2, 3, (-1.5e38)]
#guard (Float32Array.mk #[1, 2, 3, (-1.5e38)]).toList == [1, 2, 3, (-1.5e38)]
#guard (Float32Array.mk #[]).data == #[]
#guard Float32Array.empty.data == #[]
#guard (∅ : Float32Array).data == #[]
#guard (default : Float32Array).data == #[]
#guard (Float32Array.emptyWithCapacity 100).data == #[]
#guard (Float32Array.mk (Array.range 1000 |>.map Nat.toFloat32)).data == (Array.range 1000).map Nat.toFloat32

/-! Size -/

#guard (Float32Array.mk #[1, 2, 3, (-1.5e38)]).size == 4
#guard (Float32Array.mk #[1, 2, 3, (-1.5e38)]).usize == 4
#guard Float32Array.empty.size == 0
#guard (Float32Array.emptyWithCapacity 100).size == 0

/-! Reading -/

#guard (Float32Array.mk #[1, 2, 3, (-1.5e38)])[0] == 1
#guard (Float32Array.mk #[1, 2, 3, (-1.5e38)])[3] == (-1.5e38)
#guard (Float32Array.mk #[1, 2, 3, (-1.5e38)])[(2 : USize)] == 3
#guard (Float32Array.mk #[1, 2, 3, (-1.5e38)]).get! 1 == 2
#guard (Float32Array.mk #[1, 2, 3, (-1.5e38)]).getD 2 7 == 3
#guard (Float32Array.mk #[1, 2, 3, (-1.5e38)]).getD 4 7 == 7
#guard (Float32Array.mk #[1, 2, 3, (-1.5e38)])[4]? == none
#guard (Float32Array.mk #[1, 2, 3, (-1.5e38)])[1]? == some 2

/-! Writing -/

#guard ((Float32Array.mk #[1, 2, 3]).set 1 42 (by decide)).data == #[1, 42, 3]
#guard ((Float32Array.mk #[1, 2, 3]).uset 2 42 (by simp)).data == #[1, 2, 42]
#guard ((Float32Array.mk #[1, 2, 3]).set! 0 (-1.5e38)).data == #[(-1.5e38), 2, 3]

-- Writing to a shared array must leave the original unchanged. The result is checked first so
-- that it is computed while the original is still live.
#guard
  let a := Float32Array.mk #[1, 2, 3]
  let b := a.set! 1 42
  b.data == #[1, 42, 3] && a.data == #[1, 2, 3]

-- Repeated writes to an exclusive array.
#guard Id.run do
  let mut a := Float32Array.mk (Array.replicate 1000 0)
  for i in [0:1000] do
    a := a.set! i (i * 3).toFloat32
  return a.data == (Array.range 1000).map fun i => (i * 3).toFloat32

/-! Pushing -/

#guard (Float32Array.empty.push 5 |>.push 6).data == #[5, 6]
#guard ((Float32Array.emptyWithCapacity 1).push 5 |>.push 6 |>.push 7).data == #[5, 6, 7]
#guard ((Float32Array.mk #[1, 2]).push 3).data == #[1, 2, 3]

-- Pushing past the capacity many times.
#guard Id.run do
  let mut a := Float32Array.empty
  for i in [0:10000] do
    a := a.push i.toFloat32
  return a.size == 10000 && a.data == (Array.range 10000).map Nat.toFloat32

-- Pushing to a shared array must leave the original unchanged. The results are checked first so
-- that they are computed while the original is still live.
#guard
  let a := (Float32Array.emptyWithCapacity 10).push 1
  let b := a.push 2
  let c := a.push 3
  c.data == #[1, 3] && b.data == #[1, 2] && a.data == #[1]

/-! Printing -/

#guard toString (Float32Array.mk #[1, 2]) == "Float32Array.mk " ++ toString #[(1 : Float32), 2]
#guard reprStr (Float32Array.mk #[1, 2]) == "Float32Array.mk " ++ reprStr #[(1 : Float32), 2]

/-! Every index, through both `Nat` and `USize` indices -/

#guard
  let a := Float32Array.mk ((Array.range 300).map Nat.toFloat32)
  (List.range 300).all fun i =>
    a[i]! == i.toFloat32 && a.getD i 0 == i.toFloat32 && a.get! i == i.toFloat32 &&
      (if h : i.toUSize.toNat < a.size then a[i.toUSize] == i.toFloat32 else false)

/-! Writes don't touch neighbouring elements -/

#guard ((Float32Array.mk #[0, 0, 0]).set! 1 (-1.5e38)).data == #[0, (-1.5e38), 0]
#guard ((Float32Array.mk #[(-1.5e38), (-1.5e38), (-1.5e38)]).set! 1 0).data == #[(-1.5e38), 0, (-1.5e38)]
#guard ((Float32Array.mk #[0, 0, 0]).push (-1.5e38) |>.push 0).data == #[0, 0, 0, (-1.5e38), 0]

/-! Indices beyond 16 bits, and huge `Nat` indices -/

#guard
  let a := (Float32Array.mk (Array.replicate 100000 0)).set! 99999 (-1.5e38) |>.set! 70000 1
  a.size == 100000 && a[99999]! == (-1.5e38) && a[70000]! == 1 && a[99998]! == 0 &&
    a[70000 % 65536]! == 0 && a.data[99999]! == (-1.5e38) && a.data[70000]! == 1 &&
    (if h : (70000 : USize).toNat < a.size then a[(70000 : USize)] == 1 else false)

#guard (Float32Array.mk #[1, 2, 3])[2 ^ 70]? == none
#guard (Float32Array.mk #[1, 2, 3]).getD (2 ^ 70) 7 == 7

/-! Pushing onto a shared array that is at full capacity -/

#guard
  let a := Float32Array.mk #[1]
  let b := a.push 2
  b.data == #[1, 2] && a.data == #[1]

#guard
  let a := Float32Array.mk #[]
  let b := a.push 2
  b.data == #[2] && a.data == #[]

/-! Conversions don't alias -/

#guard
  let a := #[(1 : Float32), 2, 3]
  let b := (Float32Array.mk a).set! 0 (-1.5e38)
  b.data == #[(-1.5e38), 2, 3] && a == #[1, 2, 3]

#guard
  let a := Float32Array.mk #[1, 2, 3]
  let d := a.data.set! 0 (-1.5e38)
  d == #[(-1.5e38), 2, 3] && a.data == #[1, 2, 3]

/-! Runtime representation -/

#guard rawElemSize (Float32Array.mk #[1, 2, 3]) == (4 : UInt32)
#guard rawElemSize (Float32Array.emptyWithCapacity 10) == (4 : UInt32)
#guard rawElemSize (Float32Array.empty.push 1) == (4 : UInt32)
#guard rawElemSize ((Float32Array.mk #[1]).push 2) == (4 : UInt32)
#guard rawCapacity (Float32Array.emptyWithCapacity 100) ≥ 100
#guard rawCapacity (Float32Array.mk #[1, 2, 3]) ≥ 3
-- Growth is geometric, so pushing is amortized constant time.
#guard rawCapacity ((Float32Array.mk #[1, 2, 3, 4]).push 5) ≥ 8


/-! Appending -/

#guard (Float32Array.mk #[1, 2] ++ Float32Array.mk #[3, (-1.5e38)]).data == #[1, 2, 3, (-1.5e38)]
#guard ((Float32Array.mk #[1, 2]).append (Float32Array.mk #[3])).data == #[1, 2, 3]
#guard (Float32Array.mk #[1, 2] ++ Float32Array.empty).data == #[1, 2]
#guard (Float32Array.empty ++ Float32Array.mk #[1, 2]).data == #[1, 2]
#guard (Float32Array.empty ++ Float32Array.empty).data == #[]
#guard (Float32Array.mk #[0, 0] ++ Float32Array.mk #[(-1.5e38)] ++ Float32Array.mk #[0]).data ==
  #[0, 0, (-1.5e38), 0]

-- Appending an array to itself, with and without room.
#guard
  let a := Float32Array.mk #[1, 2, 3]
  (a ++ a).data == #[1, 2, 3, 1, 2, 3]

#guard
  let a := (Float32Array.emptyWithCapacity 10).push 1 |>.push 2
  (a ++ a).data == #[1, 2, 1, 2]

-- Appending to a shared array must leave the original unchanged, with and without room. The
-- results are checked first so that they are computed while the original is still live.
#guard
  let a := (Float32Array.emptyWithCapacity 10).push 1
  let b := a ++ Float32Array.mk #[2, 3]
  let c := a ++ Float32Array.mk #[4]
  c.data == #[1, 4] && b.data == #[1, 2, 3] && a.data == #[1]

#guard
  let a := Float32Array.mk #[1]
  let b := a ++ Float32Array.mk #[2, 3]
  b.data == #[1, 2, 3] && a.data == #[1]

-- The right operand is never modified.
#guard
  let b := Float32Array.mk #[2, 3]
  let c := Float32Array.mk #[1] ++ b
  c.data == #[1, 2, 3] && b.data == #[2, 3]

-- Many appends to an exclusive array.
#guard Id.run do
  let mut a := Float32Array.empty
  let mut r : Array Float32 := #[]
  for i in [0:1000] do
    a := a ++ Float32Array.mk #[i.toFloat32, (i * 7).toFloat32, (-1.5e38)]
    r := r ++ #[i.toFloat32, (i * 7).toFloat32, (-1.5e38)]
  return a.data == r

-- Large arrays on both sides.
#guard
  let xs := (Array.range 50000).map Nat.toFloat32
  let ys := (Array.range 50000).map fun i => (i * 3).toFloat32
  (Float32Array.mk xs ++ Float32Array.mk ys).data == xs ++ ys

-- An exclusive array with room is appended to in place, and growth is geometric.
-- The array is built from a parameter so that it isn't extracted as a shared closed term.
@[noinline] def Float32Array.appendsInPlace (x : Float32) : Bool :=
  let a := (Float32Array.emptyWithCapacity 10).push x
  let p := rawAddr a
  let a := a ++ Float32Array.mk #[2, 3]
  rawAddr a == p && a.data == #[x, 2, 3]

@[noinline] def Float32Array.appendsToCopyWhenShared (x : Float32) : Bool :=
  let a := (Float32Array.emptyWithCapacity 10).push x
  let p := rawAddr a
  let b := a ++ Float32Array.mk #[2, 3]
  rawAddr b != p && b.data == #[x, 2, 3] && a.data == #[x]

#guard Float32Array.appendsInPlace 1
#guard Float32Array.appendsToCopyWhenShared 1

#guard rawCapacity ((Float32Array.emptyWithCapacity 10).push 1 ++ Float32Array.mk #[2, 3]) ≥ 10
#guard rawCapacity (Float32Array.mk #[1, 2, 3, 4] ++ Float32Array.mk #[5]) ≥ 8
#guard rawCapacity (Float32Array.mk #[1] ++ Float32Array.mk (Array.replicate 10 0)) ≥ 11
#guard rawElemSize (Float32Array.mk #[1] ++ Float32Array.mk #[2]) == (4 : UInt32)
