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


/-! Appending -/

#guard (Float64Array.mk #[1, 2] ++ Float64Array.mk #[3, (-1.5e300)]).data == #[1, 2, 3, (-1.5e300)]
#guard ((Float64Array.mk #[1, 2]).append (Float64Array.mk #[3])).data == #[1, 2, 3]
#guard (Float64Array.mk #[1, 2] ++ Float64Array.empty).data == #[1, 2]
#guard (Float64Array.empty ++ Float64Array.mk #[1, 2]).data == #[1, 2]
#guard (Float64Array.empty ++ Float64Array.empty).data == #[]
#guard (Float64Array.mk #[0, 0] ++ Float64Array.mk #[(-1.5e300)] ++ Float64Array.mk #[0]).data ==
  #[0, 0, (-1.5e300), 0]

-- Appending an array to itself, with and without room.
#guard
  let a := Float64Array.mk #[1, 2, 3]
  (a ++ a).data == #[1, 2, 3, 1, 2, 3]

#guard
  let a := (Float64Array.emptyWithCapacity 10).push 1 |>.push 2
  (a ++ a).data == #[1, 2, 1, 2]

-- Appending to a shared array must leave the original unchanged, with and without room. The
-- results are checked first so that they are computed while the original is still live.
#guard
  let a := (Float64Array.emptyWithCapacity 10).push 1
  let b := a ++ Float64Array.mk #[2, 3]
  let c := a ++ Float64Array.mk #[4]
  c.data == #[1, 4] && b.data == #[1, 2, 3] && a.data == #[1]

#guard
  let a := Float64Array.mk #[1]
  let b := a ++ Float64Array.mk #[2, 3]
  b.data == #[1, 2, 3] && a.data == #[1]

-- The right operand is never modified.
#guard
  let b := Float64Array.mk #[2, 3]
  let c := Float64Array.mk #[1] ++ b
  c.data == #[1, 2, 3] && b.data == #[2, 3]

-- Many appends to an exclusive array.
#guard Id.run do
  let mut a := Float64Array.empty
  let mut r : Array Float := #[]
  for i in [0:1000] do
    a := a ++ Float64Array.mk #[i.toFloat, (i * 7).toFloat, (-1.5e300)]
    r := r ++ #[i.toFloat, (i * 7).toFloat, (-1.5e300)]
  return a.data == r

-- Large arrays on both sides.
#guard
  let xs := (Array.range 50000).map Nat.toFloat
  let ys := (Array.range 50000).map fun i => (i * 3).toFloat
  (Float64Array.mk xs ++ Float64Array.mk ys).data == xs ++ ys

-- An exclusive array with room is appended to in place, and growth is geometric.
-- The array is built from a parameter so that it isn't extracted as a shared closed term.
@[noinline] def Float64Array.appendsInPlace (x : Float) : Bool :=
  let a := (Float64Array.emptyWithCapacity 10).push x
  let p := rawAddr a
  let a := a ++ Float64Array.mk #[2, 3]
  rawAddr a == p && a.data == #[x, 2, 3]

@[noinline] def Float64Array.appendsToCopyWhenShared (x : Float) : Bool :=
  let a := (Float64Array.emptyWithCapacity 10).push x
  let p := rawAddr a
  let b := a ++ Float64Array.mk #[2, 3]
  rawAddr b != p && b.data == #[x, 2, 3] && a.data == #[x]

#guard Float64Array.appendsInPlace 1
#guard Float64Array.appendsToCopyWhenShared 1

#guard rawCapacity ((Float64Array.emptyWithCapacity 10).push 1 ++ Float64Array.mk #[2, 3]) ≥ 10
#guard rawCapacity (Float64Array.mk #[1, 2, 3, 4] ++ Float64Array.mk #[5]) ≥ 8
#guard rawCapacity (Float64Array.mk #[1] ++ Float64Array.mk (Array.replicate 10 0)) ≥ 11
#guard rawElemSize (Float64Array.mk #[1] ++ Float64Array.mk #[2]) == (8 : UInt32)

/-! Equality -/

#guard Float64Array.mk #[1, 2, (-1.5e300)] == Float64Array.mk #[1, 2, (-1.5e300)]
#guard Float64Array.mk #[1, 2, (-1.5e300)] != Float64Array.mk #[1, 2, 0]
#guard Float64Array.mk #[1, 2] != Float64Array.mk #[1, 2, 0]
#guard Float64Array.mk #[1, 2, 0] != Float64Array.mk #[1, 2]
#guard Float64Array.empty == Float64Array.emptyWithCapacity 10
#guard (Float64Array.mk #[1, 2] ++ Float64Array.mk #[(-1.5e300)]) == Float64Array.mk #[1, 2, (-1.5e300)]
-- Capacity and leftover memory past the size don't matter.
#guard (Float64Array.emptyWithCapacity 100).push 1 == Float64Array.mk #[1]
#guard (Float64Array.mk #[1, 2, 3]).pop == Float64Array.mk #[1, 2]
#guard (Float64Array.mk (Array.replicate 100000 0)).set! 99999 (-1.5e300) !=
  Float64Array.mk (Array.replicate 100000 0)

/-! Iteration -/

#guard (Float64Array.mk #[1, 2, (-1.5e300)]).foldl (fun acc x => x :: acc) [] == [(-1.5e300), 2, 1]
#guard (Float64Array.mk #[1, 2, (-1.5e300)]).foldr (fun x acc => x :: acc) [] == [1, 2, (-1.5e300)]
#guard Float64Array.empty.foldl (fun acc x => x :: acc) [] == []
#guard Float64Array.empty.foldr (fun x acc => x :: acc) [] == []
#guard (Float64Array.mk #[1, 2, (-1.5e300)]).foldlM (m := Option)
  (fun acc x => if x == 2 then none else some (x :: acc)) [] == none
#guard (Float64Array.mk #[1, (-1.5e300)]).foldrM (m := Option) (fun x acc => some (x :: acc)) [] ==
  some [1, (-1.5e300)]

#guard Id.run do
  let mut r : List Float := []
  for x in Float64Array.mk #[1, 2, (-1.5e300)] do
    r := x :: r
  return r == [(-1.5e300), 2, 1]

#guard Id.run do
  let mut r : List Float := []
  for x in Float64Array.mk #[1, 2, 3, 4] do
    if x == 3 then break
    r := x :: r
  return r == [2, 1]

#guard
  let r : StateM (List Float) Unit := (Float64Array.mk #[1, 2, (-1.5e300)]).forM fun x => modify (x :: ·)
  (r.run []).2 == [(-1.5e300), 2, 1]

#guard
  let xs := (Array.range 100000).map Nat.toFloat
  let f := fun (acc : List Float) x => if x == 0 then x :: acc else acc
  (Float64Array.mk xs).foldl f [] == xs.foldl f []

#guard (Float64Array.mk #[1, 2, (-1.5e300)]).any (· == (-1.5e300))
#guard !(Float64Array.mk #[1, 2, 3]).any (· == (-1.5e300))
#guard (Float64Array.mk #[1, 2, 3]).all (· != (-1.5e300))
#guard !(Float64Array.mk #[1, (-1.5e300), 3]).all (· != (-1.5e300))
#guard !Float64Array.empty.any (fun _ => true) && Float64Array.empty.all (fun _ => false)
#guard (Float64Array.mk #[1, 2, (-1.5e300)]).contains (-1.5e300)
#guard !(Float64Array.mk #[1, 2, 3]).contains (-1.5e300)
#guard (Float64Array.mk (Array.replicate 100000 0) |>.set! 99999 (-1.5e300)).contains (-1.5e300)

/-! Removing elements -/

#guard Float64Array.empty.isEmpty && !(Float64Array.mk #[1]).isEmpty
#guard (Float64Array.mk #[1]).pop.isEmpty
#guard (Float64Array.mk #[1, 2, (-1.5e300)]).pop.data == #[1, 2]
#guard Float64Array.empty.pop.data == #[]
#guard ((Float64Array.mk #[1, 2, 3]).pop.push (-1.5e300)).data == #[1, 2, (-1.5e300)]
#guard (Float64Array.mk #[1, 2, (-1.5e300)]).back? == some (-1.5e300)
#guard Float64Array.empty.back? == none
#guard (Float64Array.mk #[1, 2, (-1.5e300)]).back! == (-1.5e300)
#guard (Float64Array.mk #[1, 2, (-1.5e300)]).back (by decide) == (-1.5e300)

-- Popping from a shared array must leave the original unchanged.
#guard
  let a := Float64Array.mk #[1, 2, 3]
  let b := a.pop
  b.data == #[1, 2] && a.data == #[1, 2, 3]

-- The array is built from a parameter so that it isn't extracted as a shared closed term.
@[noinline] def Float64Array.popsInPlace (x : Float) : Bool :=
  let a := (Float64Array.mk #[x]).push x
  let p := rawAddr a
  let a := a.pop
  rawAddr a == p && a.data == #[x]

#guard Float64Array.popsInPlace 1

#guard ((Float64Array.mk #[1, 2, 3, (-1.5e300)]).extract 1 3).data == #[2, 3]
#guard ((Float64Array.mk #[1, 2, 3, (-1.5e300)]).extract 2 100).data == #[3, (-1.5e300)]
#guard ((Float64Array.mk #[1, 2, 3]).extract 0 3).data == #[1, 2, 3]
#guard ((Float64Array.mk #[1, 2, 3]).extract 2 1).data == #[]
#guard ((Float64Array.mk #[1, 2, 3]).extract 5 9).data == #[]
#guard ((Float64Array.mk #[1, 2, 3]).extract (2 ^ 70) (2 ^ 71)).data == #[]
#guard ((Float64Array.mk #[1, 2, 3]).extract 1 (2 ^ 70)).data == #[2, 3]
#guard
  let xs := (Array.range 100000).map Nat.toFloat
  ((Float64Array.mk xs).extract 70000 70010).data == xs.extract 70000 70010
#guard rawElemSize ((Float64Array.mk #[1, 2, 3]).extract 1 2) == (8 : UInt32)

-- The extracted array is independent of the original.
#guard
  let a := Float64Array.mk #[1, 2, 3]
  let b := (a.extract 0 2).set! 0 (-1.5e300)
  b.data == #[(-1.5e300), 2] && a.data == #[1, 2, 3]

/-! Building arrays -/

#guard (Float64Array.replicate 3 (-1.5e300)).data == #[(-1.5e300), (-1.5e300), (-1.5e300)]
#guard (Float64Array.replicate 0 1).data == #[]
#guard (Float64Array.replicate 100000 (-1.5e300)).data == Array.replicate 100000 (-1.5e300)
#guard (Float64Array.ofFn (n := 4) fun i => i.val.toFloat).data == #[0, 1, 2, 3]
#guard (Float64Array.ofFn (n := 0) fun i => i.val.toFloat).data == #[]
#guard rawElemSize (Float64Array.replicate 2 1) == (8 : UInt32)
#guard rawElemSize (Float64Array.ofFn (n := 2) fun _ => 1) == (8 : UInt32)

/-! Lemmas -/

example (a : Float64Array) (v : Float) : (a.push v).pop = a := by simp [Float64Array.ext_iff]
example : (Float64Array.replicate 3 (-1.5e300))[1] = (-1.5e300) := by simp
example (a b : Float64Array) (h : 0 < a.size) : (a ++ b)[0]'(by simp; omega) = a[0] := by simp [h]
example (a : Float64Array) (i : Nat) (v : Float) (h : i < a.size) :
    (a.set i v h)[i]'(by simpa) = v := by simp
example (a : Float64Array) : a.extract 0 a.size = a := by simp
example (a : Float64Array) (v : Float) : (a.push v).pop = a :=
  Float64Array.ext_getElem (by simp) (by simp_all)

/-! Default bounds proofs -/

#guard (Float64Array.mk #[1, 2, (-1.5e300)]).get 2 == (-1.5e300)
#guard (Float64Array.mk #[1, 2, (-1.5e300)]).uget 2 == (-1.5e300)
#guard ((Float64Array.mk #[1, 2, 3]).set 1 (-1.5e300)).data == #[1, (-1.5e300), 3]
#guard ((Float64Array.mk #[1, 2, 3]).uset 1 (-1.5e300)).data == #[1, (-1.5e300), 3]

/-! `set!` leaves the array unchanged when the index is out of bounds, like `ByteArray.set!`. -/

#guard ((Float64Array.mk #[1, 2, 3]).set! 3 (-1.5e300)).data == #[1, 2, 3]
#guard ((Float64Array.mk #[1, 2, 3]).set! (2 ^ 70) (-1.5e300)).data == #[1, 2, 3]

/-! Folds over part of an array -/

#guard (Float64Array.mk #[1, 2, 3, (-1.5e300)]).foldl (fun acc x => x :: acc) [] 1 3 == [3, 2]
#guard (Float64Array.mk #[1, 2, 3, (-1.5e300)]).foldl (fun acc x => x :: acc) [] 2 == [(-1.5e300), 3]
#guard (Float64Array.mk #[1, 2, 3, (-1.5e300)]).foldl (fun acc x => x :: acc) [] 1 100 == [(-1.5e300), 3, 2]
#guard (Float64Array.mk #[1, 2, 3, (-1.5e300)]).foldl (fun acc x => x :: acc) [] 3 1 == []
#guard (Float64Array.mk #[1, 2, 3, (-1.5e300)]).foldl (fun acc x => x :: acc) [] 9 12 == []
#guard (Float64Array.mk #[1, 2, 3]).foldlM (m := Option)
  (fun acc x => if x == 1 then none else some (x :: acc)) [] 1 == some [3, 2]

/-! Copying slices -/

#guard
  let src := Float64Array.mk #[10, 11, 12, (-1.5e300)]
  let dest := Float64Array.mk #[1, 2, 3, 4, 5]
  (src.copySlice 1 dest 2 2).data == #[1, 2, 11, 12, 5] &&
  (src.copySlice 1 dest 4 3).data == #[1, 2, 3, 4, 11, 12, (-1.5e300)] &&
  (src.copySlice 0 dest 9 2).data == #[1, 2, 3, 4, 5, 10, 11] &&
  (src.copySlice 9 dest 1 2).data == #[1, 2, 3, 4, 5] &&
  (src.copySlice 2 dest 0 10).data == #[12, (-1.5e300), 3, 4, 5] &&
  (src.copySlice 0 dest 0 0).data == #[1, 2, 3, 4, 5] &&
  (src.copySlice 0 Float64Array.empty 0 4).data == #[10, 11, 12, (-1.5e300)] &&
  dest.data == #[1, 2, 3, 4, 5] && src.data == #[10, 11, 12, (-1.5e300)]

-- Copying from an array into itself.
#guard
  let a := Float64Array.mk #[1, 2, 3, (-1.5e300)]
  (a.copySlice 0 a 2 4).data == #[1, 2, 1, 2, 3, (-1.5e300)]

#guard
  let xs := (Array.range 100000).map Nat.toFloat
  let a := Float64Array.mk xs
  (a.copySlice 70000 (Float64Array.replicate 10 0) 5 10).data ==
    Array.replicate 5 0 ++ xs.extract 70000 70010

#guard rawElemSize ((Float64Array.mk #[1]).copySlice 0 Float64Array.empty 0 1) == (8 : UInt32)

@[noinline] def Float64Array.copiesSliceInPlace (x : Float) : Bool :=
  let dest := (Float64Array.emptyWithCapacity 10).push x |>.push x |>.push x
  let p := rawAddr dest
  let dest := (Float64Array.mk #[(-1.5e300), (-1.5e300)]).copySlice 0 dest 1 2
  rawAddr dest == p && dest.data == #[x, (-1.5e300), (-1.5e300)]

@[noinline] def Float64Array.copySliceGrowth (x : Float) : Bool :=
  let dest := (Float64Array.mk #[x, x, x, x])
  rawCapacity ((Float64Array.mk #[x]).copySlice 0 dest 4 1 (exact := false)) ≥ 8 &&
    rawCapacity ((Float64Array.mk #[x]).copySlice 0 dest 4 1) == 5

#guard Float64Array.copiesSliceInPlace 1
#guard Float64Array.copySliceGrowth 1

/-! Linearity markers -/

#guard ((Float64Array.mk #[1, 2]).markLinear.push (-1.5e300)).data == #[1, 2, (-1.5e300)]
#guard ((Float64Array.mk #[1]).propagateMark (Float64Array.mk #[2, (-1.5e300)])).data == #[2, (-1.5e300)]

/-! Search -/

#guard (Float64Array.mk #[1, 2, (-1.5e300), 2]).findIdx? (· == 2) == some 1
#guard (Float64Array.mk #[1, 2, (-1.5e300), 2]).findIdx? (· == 2) 2 == some 3
#guard (Float64Array.mk #[1, 2, (-1.5e300), 2]).findIdx? (· == 3) == none
#guard (Float64Array.mk #[1, 2, (-1.5e300), 2]).findIdx? (· == 1) 9 == none
#guard ((Float64Array.mk #[1, 2, (-1.5e300), 2]).findFinIdx? (· == (-1.5e300))).map (·.val) == some 2

/-! Lists -/

#guard (Float64Array.ofList [1, 2, (-1.5e300)]).data == #[1, 2, (-1.5e300)]
#guard (Float64Array.ofList []).data == #[]
#guard [1, 2, (-1.5e300)].toFloat64Array == Float64Array.mk #[1, 2, (-1.5e300)]
#guard (Float64Array.ofList ((List.range 100000).map Nat.toFloat)).data ==
  (Array.range 100000).map Nat.toFloat
#guard rawElemSize (Float64Array.ofList [1, 2]) == (8 : UInt32)

/-! More lemmas -/

example (a b c : Float64Array) : a ++ b ++ c = a ++ (b ++ c) := Float64Array.append_assoc ..
example (a : Float64Array) : a ++ ∅ = a := by simp
example (a b : Float64Array) : (a ++ b).extract 0 a.size = a := by simp
example (a : Float64Array) (i : Nat) (v : Float) : (a.set! i v).size = a.size := by simp
example (l : List Float) : (Float64Array.ofList l).toList = l := by simp
example (a : Float64Array) : Float64Array.ofList a.toList = a := by simp

/-! Slices -/

#guard
  let a := Float64Array.mk #[1, 2, 3, (-1.5e300)]
  let s := a[1...3]
  s.size == 2 && s[0]! == 2 && s[1]! == 3 && s.getD 2 7 == 7 && s.copy == Float64Array.mk #[2, 3] &&
    s.toList == [2, 3] && s.toArray == #[2, 3]

#guard
  let a := Float64Array.mk #[1, 2, 3, (-1.5e300)]
  a[1...=3].toList == [2, 3, (-1.5e300)] && a[*...2].toList == [1, 2] && a[2...*].toList == [3, (-1.5e300)] &&
    a[*...*].toList == [1, 2, 3, (-1.5e300)] && a[0<...2].toList == [2] &&
    a[0<...=2].toList == [2, 3] && a[*...=1].toList == [1, 2] && a[1<...*].toList == [3, (-1.5e300)]

-- Bounds are clamped.
#guard
  let a := Float64Array.mk #[1, 2, 3, (-1.5e300)]
  a[2...100].toList == [3, (-1.5e300)] && a[3...1].size == 0 && a[9...12].size == 0 &&
    (a.toSlice 1 (2 ^ 70)).toList == [2, 3, (-1.5e300)]

-- Slices of slices.
#guard
  let s := (Float64Array.mk #[1, 2, 3, (-1.5e300)])[1...4]
  s[1...2].toList == [3] && s[0...100].toList == [2, 3, (-1.5e300)] && s[*...*].toList == [2, 3, (-1.5e300)] &&
    s[2...*].toList == [(-1.5e300)] && s[5...6].size == 0

#guard
  let s := (Float64Array.mk #[1, 2, 3, (-1.5e300)])[1...4]
  s.popFront.toList == [3, (-1.5e300)] && s.popFront.popFront.popFront.popFront.size == 0

#guard (∅ : Float64Array.Slice).size == 0 && (default : Float64Array.Slice).toList == []

#guard Id.run do
  let mut r : List Float := []
  for x in (Float64Array.mk #[1, 2, 3, (-1.5e300)])[1...*] do
    r := x :: r
  return r == [(-1.5e300), 3, 2]

#guard (Float64Array.mk #[1, 2, 3, (-1.5e300)])[1...*].foldl (fun acc x => x :: acc) [] == [(-1.5e300), 3, 2]

#guard
  let xs := (Array.range 100000).map Nat.toFloat
  let s := (Float64Array.mk xs)[70000...70010]
  s.toArray == xs.extract 70000 70010 && s.copy.data == xs.extract 70000 70010

#guard toString (Float64Array.mk #[1, 2, 3])[1...*] == toString (Float64Array.mk #[2, 3])

-- Taking a slice doesn't copy the array.
@[noinline] def Float64Array.slicesWithoutCopying (x : Float) : Bool :=
  let a := Float64Array.mk #[x, 2, 3]
  let p := rawAddr a
  rawAddr a[1...2].array == p

#guard Float64Array.slicesWithoutCopying 1

example (s : Float64Array.Slice) : s.copy.size = s.size := by simp

/-! Slice API -/

#guard
  let s := (Float64Array.mk #[1, 2, 3, (-1.5e300), 2])[1...5]
  s.foldr (fun x acc => x :: acc) [] == [2, 3, (-1.5e300), 2] &&
    s.foldl (fun acc x => x :: acc) [] == [2, (-1.5e300), 3, 2] &&
    s.any (· == (-1.5e300)) && !s.any (· == 1) && s.all (· != 1) && !s.all (· == 2) &&
    s.contains (-1.5e300) && !s.contains 1 && s.count (· == 2) == 2 &&
    s.find? (· > 2) == some 3 && s.findRev? (· != (-1.5e300)) == some 2 && s.findRev? (· == 1) == none

#guard (Float64Array.mk #[1, 2, 3])[1...1].foldr (fun x acc => x :: acc) [] == []
#guard (Float64Array.mk #[1, 2, 3])[3...*].find? (fun _ => true) == none

#guard
  let s := (Float64Array.mk #[1, 2, 3, (-1.5e300)])[1...*]
  let r : StateM (List Float) Unit := s.forRevM fun x => modify (x :: ·)
  (r.run []).2 == [2, 3, (-1.5e300)]

#guard Id.run ((Float64Array.mk #[1, 2, (-1.5e300)])[*...*].findSomeRevM?
  (fun x => pure (if x == 2 then some x else none))) == some 2

/-! The `Std.Iterators` API on arrays and slices -/

#guard (Float64Array.mk #[1, 2, 3]).iter.toList == [1, 2, 3]
#guard ((Float64Array.mk #[1, 2, 3]).iter.map (· * 2)).toFloat64Array == Float64Array.mk #[2, 4, 6]
#guard ((Float64Array.mk #[1, 2, 3, (-1.5e300)]).iter.filter (· != 2)).toFloat64Array ==
  Float64Array.mk #[1, 3, (-1.5e300)]
#guard ((Float64Array.mk #[1, 2, 3, (-1.5e300)]).iter.take 2).toFloat64Array == Float64Array.mk #[1, 2]
#guard ((Float64Array.mk #[1, 2, 3, (-1.5e300)]).iter.drop 2).toFloat64Array == Float64Array.mk #[3, (-1.5e300)]
#guard (((Float64Array.mk #[1, 2, 3]).iter.zip (Float64Array.mk #[(-1.5e300), 5]).iter).map
  fun (x, y) => x + y).toFloat64Array == Float64Array.mk #[1 + (-1.5e300), 7]
#guard ((Float64Array.mk #[1, 2, 3, (-1.5e300)])[1...3].iter.map (· + 1)).toFloat64Array ==
  Float64Array.mk #[3, 4]
#guard (Float64Array.mk #[1, 2, 3]).iter.length == 3
#guard Float64Array.empty.iter.toFloat64Array == Float64Array.empty
#guard
  let xs := (Array.range 100000).map Nat.toFloat
  ((Float64Array.mk xs).iter.map (· + 1)).toFloat64Array.data == xs.map (· + 1)
#guard rawElemSize ((Float64Array.mk #[1]).iter.toFloat64Array) == (8 : UInt32)
