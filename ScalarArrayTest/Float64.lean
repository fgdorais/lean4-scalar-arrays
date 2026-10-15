/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import ScalarArray.Float64
import ScalarArrayTest.Util
meta import ScalarArray.Float64
meta import ScalarArrayTest.Util

open ScalarArray ScalarArrayTest

/-- A test value at the edge of the element type's range. -/
private abbrev big : Float := -1.5e300

/-- The size of an element in bytes. -/
private abbrev elemSize : UInt32 := 8

/-! Construction and conversion -/

#guard (Float64Array.mk #[1, 2, 3, big]).data == #[1, 2, 3, big]
#guard (Float64Array.mk #[1, 2, 3, big]).toList == [1, 2, 3, big]
#guard (Float64Array.mk #[]).data == #[]
#guard Float64Array.empty.data == #[]
#guard (∅ : Float64Array).data == #[]
#guard (default : Float64Array).data == #[]
#guard (Float64Array.emptyWithCapacity 100).data == #[]
#guard (Float64Array.mk (Array.range 1000 |>.map Nat.toFloat)).data ==
  (Array.range 1000).map Nat.toFloat

/-! Size -/

#guard (Float64Array.mk #[1, 2, 3, big]).size == 4
#guard (Float64Array.mk #[1, 2, 3, big]).usize == 4
#guard Float64Array.empty.size == 0
#guard (Float64Array.emptyWithCapacity 100).size == 0

/-! Reading -/

#guard (Float64Array.mk #[1, 2, 3, big])[0] == 1
#guard (Float64Array.mk #[1, 2, 3, big])[3] == big
#guard (Float64Array.mk #[1, 2, 3, big])[(2 : USize)] == 3
#guard (Float64Array.mk #[1, 2, 3, big]).get! 1 == 2
#guard (Float64Array.mk #[1, 2, 3, big]).getD 2 7 == 3
#guard (Float64Array.mk #[1, 2, 3, big]).getD 4 7 == 7
#guard (Float64Array.mk #[1, 2, 3, big])[4]? == none
#guard (Float64Array.mk #[1, 2, 3, big])[1]? == some 2

/-! Writing -/

#guard ((Float64Array.mk #[1, 2, 3]).set 1 42 (by decide)).data == #[1, 42, 3]
#guard ((Float64Array.mk #[1, 2, 3]).uset 2 42 (by simp)).data == #[1, 2, 42]
#guard ((Float64Array.mk #[1, 2, 3]).set! 0 big).data == #[big, 2, 3]

-- Writing to a shared array must leave the original unchanged. The result is checked first so
-- that it is computed while the original is still live.
#guard
  let a := Float64Array.mk #[1, 2, 3]
  let b := a.set! 1 42
  b.data == #[1, 42, 3] && a.data == #[1, 2, 3]
#guard
  let a := Float64Array.mk #[1, 2, 3]
  let b := a.uset 0 big (by simp [a])
  b.data == #[big, 2, 3] && a.data == #[1, 2, 3]
#guard
  let a := Float64Array.mk #[1, 2, 3]
  let b := a.set 2 big (by simp [a])
  b.data == #[1, 2, big] && a.data == #[1, 2, 3]

-- `foldInPlace` shifts a range right by one, inserting the initial accumulator.
#guard
  let r := (Float64Array.mk #[1, 2, 3, 4]).foldInPlace 1 2 9 (fun _ _ x b => (b, x)) (by simp)
  r.1.data == #[1, 9, 2, 4] && r.2 == 3

-- `foldInPlace` on a shared array must leave the original unchanged, and `f` must see the
-- elements of the original even when it reads them from the array itself.
#guard
  let a := Float64Array.mk #[1, 2, 3, 4]
  let r := a.foldInPlace 0 4 9 (fun _ _ x b => (b, x)) (by simp [a])
  r.1.data == #[9, 1, 2, 3] && a.data == #[1, 2, 3, 4]
#guard
  let a := Float64Array.mk #[1, 2, 3, 4]
  let r := a.foldInPlace 1 3 0 (fun k _ _ b => (a[k.toNat]!, b)) (by simp [a])
  r.1.data == #[1, 1, 2, 3]

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

#guard ((Float64Array.mk #[0, 0, 0]).set! 1 big).data == #[0, big, 0]
#guard ((Float64Array.mk #[big, big, big]).set! 1 0).data == #[big, 0, big]
#guard ((Float64Array.mk #[0, 0, 0]).push big |>.push 0).data == #[0, 0, 0, big, 0]

/-! Indices beyond 16 bits, and huge `Nat` indices -/

#guard
  let a := (Float64Array.mk (Array.replicate 100000 0)).set! 99999 big |>.set! 70000 1
  a.size == 100000 && a[99999]! == big && a[70000]! == 1 && a[99998]! == 0 &&
    a[70000 % 65536]! == 0 && a.data[99999]! == big && a.data[70000]! == 1 &&
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
  let b := (Float64Array.mk a).set! 0 big
  b.data == #[big, 2, 3] && a == #[1, 2, 3]

#guard
  let a := Float64Array.mk #[1, 2, 3]
  let d := a.data.set! 0 big
  d == #[big, 2, 3] && a.data == #[1, 2, 3]

/-! Runtime representation -/

#guard rawElemSize (Float64Array.mk #[1, 2, 3]) == elemSize
#guard rawElemSize (Float64Array.emptyWithCapacity 10) == elemSize
#guard rawElemSize (Float64Array.empty.push 1) == elemSize
#guard rawElemSize ((Float64Array.mk #[1]).push 2) == elemSize
#guard rawCapacity (Float64Array.emptyWithCapacity 100) ≥ 100
#guard rawCapacity (Float64Array.mk #[1, 2, 3]) ≥ 3
-- Growth is geometric, so pushing is amortized constant time.
#guard rawCapacity ((Float64Array.mk #[1, 2, 3, 4]).push 5) ≥ 8


/-! Appending -/

#guard (Float64Array.mk #[1, 2] ++ Float64Array.mk #[3, big]).data == #[1, 2, 3, big]
#guard ((Float64Array.mk #[1, 2]).append (Float64Array.mk #[3])).data == #[1, 2, 3]
#guard (Float64Array.mk #[1, 2] ++ Float64Array.empty).data == #[1, 2]
#guard (Float64Array.empty ++ Float64Array.mk #[1, 2]).data == #[1, 2]
#guard (Float64Array.empty ++ Float64Array.empty).data == #[]
#guard (Float64Array.mk #[0, 0] ++ Float64Array.mk #[big] ++ Float64Array.mk #[0]).data ==
  #[0, 0, big, 0]

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
    a := a ++ Float64Array.mk #[i.toFloat, (i * 7).toFloat, big]
    r := r ++ #[i.toFloat, (i * 7).toFloat, big]
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
#guard rawElemSize (Float64Array.mk #[1] ++ Float64Array.mk #[2]) == elemSize

/-! Equality -/

#guard Float64Array.mk #[1, 2, big] == Float64Array.mk #[1, 2, big]
#guard Float64Array.mk #[1, 2, big] != Float64Array.mk #[1, 2, 0]
#guard Float64Array.mk #[1, 2] != Float64Array.mk #[1, 2, 0]
#guard Float64Array.mk #[1, 2, 0] != Float64Array.mk #[1, 2]
#guard Float64Array.empty == Float64Array.emptyWithCapacity 10
#guard (Float64Array.mk #[1, 2] ++ Float64Array.mk #[big]) == Float64Array.mk #[1, 2, big]
-- Capacity and leftover memory past the size don't matter.
#guard (Float64Array.emptyWithCapacity 100).push 1 == Float64Array.mk #[1]
#guard (Float64Array.mk #[1, 2, 3]).pop == Float64Array.mk #[1, 2]
#guard (Float64Array.mk (Array.replicate 100000 0)).set! 99999 big !=
  Float64Array.mk (Array.replicate 100000 0)

/-! Iteration -/

#guard (Float64Array.mk #[1, 2, big]).foldl (fun acc x => x :: acc) [] == [big, 2, 1]
#guard (Float64Array.mk #[1, 2, big]).foldr (fun x acc => x :: acc) [] == [1, 2, big]
#guard Float64Array.empty.foldl (fun acc x => x :: acc) [] == []
#guard Float64Array.empty.foldr (fun x acc => x :: acc) [] == []
#guard (Float64Array.mk #[1, 2, big]).foldlM (m := Option)
  (fun acc x => if x == 2 then none else some (x :: acc)) [] == none
#guard (Float64Array.mk #[1, big]).foldrM (m := Option) (fun x acc => some (x :: acc)) [] ==
  some [1, big]

#guard Id.run do
  let mut r : List Float := []
  for x in Float64Array.mk #[1, 2, big] do
    r := x :: r
  return r == [big, 2, 1]

#guard Id.run do
  let mut r : List Float := []
  for x in Float64Array.mk #[1, 2, 3, 4] do
    if x == 3 then break
    r := x :: r
  return r == [2, 1]

#guard
  let r : StateM (List Float) Unit := (Float64Array.mk #[1, 2, big]).forM fun x => modify (x :: ·)
  (r.run []).2 == [big, 2, 1]

#guard
  let xs := (Array.range 100000).map Nat.toFloat
  let f := fun (acc : List Float) x => if x == 0 then x :: acc else acc
  (Float64Array.mk xs).foldl f [] == xs.foldl f []

#guard (Float64Array.mk #[1, 2, big]).any (· == big)
#guard !(Float64Array.mk #[1, 2, 3]).any (· == big)
#guard (Float64Array.mk #[1, 2, 3]).all (· != big)
#guard !(Float64Array.mk #[1, big, 3]).all (· != big)
#guard !Float64Array.empty.any (fun _ => true) && Float64Array.empty.all (fun _ => false)
#guard (Float64Array.mk #[1, 2, big]).contains big
#guard !(Float64Array.mk #[1, 2, 3]).contains big && !Float64Array.empty.contains big

-- Early exits, and loops in a monad other than `Id`.
#guard (Float64Array.mk #[1, 2, big]).foldrM (m := Option)
  (fun x acc => if x == 1 then none else some (x :: acc)) [] == none
#guard (Float64Array.mk #[big, 2, 1]).foldrM (m := Option)
  (fun x acc => if x == big then none else some (x :: acc)) [] == none
#guard
  let r : StateM (List Float) Unit := do
    for x in Float64Array.mk #[1, 2, big, 3] do
      if x == big then break
      modify (x :: ·)
  (r.run []).2 == [2, 1]
#guard
  let r : StateM (List Float) Unit :=
    (Float64Array.mk #[1, 2, big]).foldrM (fun x _ => modify (x :: ·)) ⟨⟩
  (r.run []).2 == [1, 2, big]
#guard Id.run do
  let mut r : List Float := []
  for x in Float64Array.empty do
    r := x :: r
  return r == []
#guard !(Float64Array.mk #[1, 2, 3]).contains big
#guard (Float64Array.mk (Array.replicate 100000 0) |>.set! 99999 big).contains big

/-! Removing elements -/

#guard Float64Array.empty.isEmpty && !(Float64Array.mk #[1]).isEmpty
#guard (Float64Array.mk #[1]).pop.isEmpty
#guard (Float64Array.mk #[1, 2, big]).pop.data == #[1, 2]
#guard Float64Array.empty.pop.data == #[]
#guard ((Float64Array.mk #[1, 2, 3]).pop.push big).data == #[1, 2, big]
#guard (Float64Array.mk #[1, 2, big]).back? == some big
#guard Float64Array.empty.back? == none
#guard (Float64Array.mk #[1, 2, big]).back! == big
#guard (Float64Array.mk #[1, 2, big]).back (by decide) == big

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

#guard (Float64Array.mk #[1, 0, big, 0, 0]).popWhile (· == 0) == Float64Array.mk #[1, 0, big]
#guard (Float64Array.mk #[1, 0, big]).popWhile (· == 0) == Float64Array.mk #[1, 0, big]
#guard (Float64Array.mk #[0, 0]).popWhile (· == 0) == Float64Array.empty
#guard Float64Array.empty.popWhile (· == 0) == Float64Array.empty

-- Popping several elements from an exclusive array.
@[noinline] def Float64Array.popsWhileInPlace (x : Float) : Bool :=
  let a := (Float64Array.mk #[x]).push 0 |>.push 0
  let p := rawAddr a
  let a := a.popWhile (· == 0)
  rawAddr a == p && a.data == #[x]

#guard Float64Array.popsWhileInPlace 1

example (p : Float → Bool) (a : Float64Array) : (a.popWhile p).data = a.data.popWhile p := by simp

#guard ((Float64Array.mk #[1, 2, 3, big]).extract 1 3).data == #[2, 3]
#guard ((Float64Array.mk #[1, 2, 3, big]).extract 2 100).data == #[3, big]
#guard ((Float64Array.mk #[1, 2, 3]).extract 0 3).data == #[1, 2, 3]
#guard ((Float64Array.mk #[1, 2, 3]).extract 2 1).data == #[]
#guard ((Float64Array.mk #[1, 2, 3]).extract 5 9).data == #[]
#guard ((Float64Array.mk #[1, 2, 3]).extract (2 ^ 70) (2 ^ 71)).data == #[]
#guard ((Float64Array.mk #[1, 2, 3]).extract 1 (2 ^ 70)).data == #[2, 3]
#guard
  let xs := (Array.range 100000).map Nat.toFloat
  ((Float64Array.mk xs).extract 70000 70010).data == xs.extract 70000 70010
#guard rawElemSize ((Float64Array.mk #[1, 2, 3]).extract 1 2) == elemSize

-- The extracted array is independent of the original.
#guard
  let a := Float64Array.mk #[1, 2, 3]
  let b := (a.extract 0 2).set! 0 big
  b.data == #[big, 2] && a.data == #[1, 2, 3]

/-! Building arrays -/

#guard (Float64Array.replicate 3 big).data == #[big, big, big]
#guard (Float64Array.replicate 0 1).data == #[]
#guard (Float64Array.replicate 100000 big).data == Array.replicate 100000 big
#guard (Float64Array.ofFn (n := 4) fun i => i.val.toFloat).data == #[0, 1, 2, 3]
#guard (Float64Array.ofFn (n := 0) fun i => i.val.toFloat).data == #[]
#guard rawElemSize (Float64Array.replicate 2 1) == elemSize
#guard rawElemSize (Float64Array.ofFn (n := 2) fun _ => 1) == elemSize

/-! Lemmas -/

example (a : Float64Array) (v : Float) : (a.push v).pop = a := by simp [Float64Array.ext_iff]
example : (Float64Array.replicate 3 big)[1] = big := by simp
example (a b : Float64Array) (h : 0 < a.size) : (a ++ b)[0]'(by simp; omega) = a[0] := by simp [h]
example (a : Float64Array) (i : Nat) (v : Float) (h : i < a.size) :
    (a.set i v h)[i]'(by simpa) = v := by simp
example (a : Float64Array) : a.extract 0 a.size = a := by simp
example (a : Float64Array) (v : Float) : (a.push v).pop = a :=
  Float64Array.ext_getElem (by simp) (by simp_all)

/-! Default bounds proofs -/

#guard (Float64Array.mk #[1, 2, big]).get 2 == big
#guard (Float64Array.mk #[1, 2, big]).uget 2 == big
#guard ((Float64Array.mk #[1, 2, 3]).set 1 big).data == #[1, big, 3]
#guard ((Float64Array.mk #[1, 2, 3]).uset 1 big).data == #[1, big, 3]

/-! `set!` leaves the array unchanged when the index is out of bounds, like `ByteArray.set!`. -/

#guard ((Float64Array.mk #[1, 2, 3]).set! 3 big).data == #[1, 2, 3]
#guard ((Float64Array.mk #[1, 2, 3]).set! (2 ^ 70) big).data == #[1, 2, 3]

/-! Folds over part of an array -/

#guard (Float64Array.mk #[1, 2, 3, big]).foldl (fun acc x => x :: acc) [] 1 3 == [3, 2]
#guard (Float64Array.mk #[1, 2, 3, big]).foldl (fun acc x => x :: acc) [] 2 == [big, 3]
#guard (Float64Array.mk #[1, 2, 3, big]).foldl (fun acc x => x :: acc) [] 1 100 == [big, 3, 2]
#guard (Float64Array.mk #[1, 2, 3, big]).foldl (fun acc x => x :: acc) [] 3 1 == []
#guard (Float64Array.mk #[1, 2, 3, big]).foldl (fun acc x => x :: acc) [] 9 12 == []
#guard (Float64Array.mk #[1, 2, 3]).foldlM (m := Option)
  (fun acc x => if x == 1 then none else some (x :: acc)) [] 1 == some [3, 2]

/-! Copying slices -/

#guard
  let src := Float64Array.mk #[10, 11, 12, big]
  let dest := Float64Array.mk #[1, 2, 3, 4, 5]
  (src.copySlice 1 dest 2 2).data == #[1, 2, 11, 12, 5] &&
  (src.copySlice 1 dest 4 3).data == #[1, 2, 3, 4, 11, 12, big] &&
  (src.copySlice 0 dest 9 2).data == #[1, 2, 3, 4, 5, 10, 11] &&
  (src.copySlice 9 dest 1 2).data == #[1, 2, 3, 4, 5] &&
  (src.copySlice 2 dest 0 10).data == #[12, big, 3, 4, 5] &&
  (src.copySlice 0 dest 0 0).data == #[1, 2, 3, 4, 5] &&
  (src.copySlice 0 Float64Array.empty 0 4).data == #[10, 11, 12, big] &&
  dest.data == #[1, 2, 3, 4, 5] && src.data == #[10, 11, 12, big]

-- Copying from an array into itself.
#guard
  let a := Float64Array.mk #[1, 2, 3, big]
  (a.copySlice 0 a 2 4).data == #[1, 2, 1, 2, 3, big]

#guard
  let xs := (Array.range 100000).map Nat.toFloat
  let a := Float64Array.mk xs
  (a.copySlice 70000 (Float64Array.replicate 10 0) 5 10).data ==
    Array.replicate 5 0 ++ xs.extract 70000 70010

#guard rawElemSize ((Float64Array.mk #[1]).copySlice 0 Float64Array.empty 0 1) == elemSize

@[noinline] def Float64Array.copiesSliceInPlace (x : Float) : Bool :=
  let dest := (Float64Array.emptyWithCapacity 10).push x |>.push x |>.push x
  let p := rawAddr dest
  let dest := (Float64Array.mk #[big, big]).copySlice 0 dest 1 2
  rawAddr dest == p && dest.data == #[x, big, big]

@[noinline] def Float64Array.copySliceGrowth (x : Float) : Bool :=
  let dest := (Float64Array.mk #[x, x, x, x])
  rawCapacity ((Float64Array.mk #[x]).copySlice 0 dest 4 1 (exact := false)) ≥ 8 &&
    rawCapacity ((Float64Array.mk #[x]).copySlice 0 dest 4 1) == 5

#guard Float64Array.copiesSliceInPlace 1
#guard Float64Array.copySliceGrowth 1

/-! Linearity markers -/

#guard ((Float64Array.mk #[1, 2]).markLinear.push big).data == #[1, 2, big]
#guard ((Float64Array.mk #[1]).propagateMark (Float64Array.mk #[2, big])).data == #[2, big]

/-! Search -/

#guard (Float64Array.mk #[1, 2, big, 2]).findIdx? (· == 2) == some 1
#guard (Float64Array.mk #[1, 2, big, 2]).findIdx? (· == 2) 2 == some 3
#guard (Float64Array.mk #[1, 2, big, 2]).findIdx? (· == 3) == none
#guard (Float64Array.mk #[1, 2, big, 2]).findIdx? (· == 1) 9 == none
#guard ((Float64Array.mk #[1, 2, big, 2]).findFinIdx? (· == big)).map (·.val) == some 2

/-! Lists -/

#guard (Float64Array.ofList [1, 2, big]).data == #[1, 2, big]
#guard (Float64Array.ofList []).data == #[]
#guard [1, 2, big].toFloat64Array == Float64Array.mk #[1, 2, big]
#guard (Float64Array.ofList ((List.range 100000).map Nat.toFloat)).data ==
  (Array.range 100000).map Nat.toFloat
#guard rawElemSize (Float64Array.ofList [1, 2]) == elemSize

/-! More lemmas -/

example (a b c : Float64Array) : a ++ b ++ c = a ++ (b ++ c) := Float64Array.append_assoc ..
example (a : Float64Array) : a ++ ∅ = a := by simp
example (a b : Float64Array) : (a ++ b).extract 0 a.size = a := by simp
example (a : Float64Array) (i : Nat) (v : Float) : (a.set! i v).size = a.size := by simp
example (l : List Float) : (Float64Array.ofList l).toList = l := by simp
example (a : Float64Array) : Float64Array.ofList a.toList = a := by simp

/-! Slices -/

#guard
  let a := Float64Array.mk #[1, 2, 3, big]
  let s := a[1...3]
  s.size == 2 && s[0]! == 2 && s[1]! == 3 && s.getD 2 7 == 7 && s.copy == Float64Array.mk #[2, 3] &&
    s.toList == [2, 3] && s.toArray == #[2, 3]

#guard
  let a := Float64Array.mk #[1, 2, 3, big]
  a[1...=3].toList == [2, 3, big] && a[*...2].toList == [1, 2] && a[2...*].toList == [3, big] &&
    a[*...*].toList == [1, 2, 3, big] && a[0<...2].toList == [2] &&
    a[0<...=2].toList == [2, 3] && a[*...=1].toList == [1, 2] && a[1<...*].toList == [3, big]

-- Bounds are clamped.
#guard
  let a := Float64Array.mk #[1, 2, 3, big]
  a[2...100].toList == [3, big] && a[3...1].size == 0 && a[9...12].size == 0 &&
    (a.toSlice 1 (2 ^ 70)).toList == [2, 3, big]

-- Slices of slices.
#guard
  let s := (Float64Array.mk #[1, 2, 3, big])[1...4]
  s[1...2].toList == [3] && s[0...100].toList == [2, 3, big] && s[*...*].toList == [2, 3, big] &&
    s[2...*].toList == [big] && s[5...6].size == 0

#guard
  let s := (Float64Array.mk #[1, 2, 3, big])[1...4]
  s.popFront.toList == [3, big] && s.popFront.popFront.popFront.popFront.size == 0

#guard (∅ : Float64Array.Slice).size == 0 && (default : Float64Array.Slice).toList == []

-- An array coerces to the slice of all its elements.
#guard
  let s : Float64Array.Slice := Float64Array.mk #[1, 2, big]
  s.toList == [1, 2, big] && s.start == 0

-- A slice does not coerce back to an array, since that would copy.
example (s : Float64Array.Slice) : Float64Array := s.copy

#guard Id.run do
  let mut r : List Float := []
  for x in (Float64Array.mk #[1, 2, 3, big])[1...*] do
    r := x :: r
  return r == [big, 3, 2]

#guard (Float64Array.mk #[1, 2, 3, big])[1...*].foldl (fun acc x => x :: acc) [] == [big, 3, 2]

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
  let s := (Float64Array.mk #[1, 2, 3, big, 2])[1...5]
  s.foldr (fun x acc => x :: acc) [] == [2, 3, big, 2] &&
    s.foldl (fun acc x => x :: acc) [] == [2, big, 3, 2] &&
    s.any (· == big) && !s.any (· == 1) && s.all (· != 1) && !s.all (· == 2) &&
    s.contains big && !s.contains 1 && s.count (· == 2) == 2 &&
    s.find? (· > 2) == some 3 && s.findRev? (· != big) == some 2 && s.findRev? (· == 1) == none

#guard (Float64Array.mk #[1, 2, 3])[1...1].foldr (fun x acc => x :: acc) [] == []
#guard (Float64Array.mk #[1, 2, 3])[3...*].find? (fun _ => true) == none

#guard
  let s := (Float64Array.mk #[1, 2, 3, big])[1...*]
  let r : StateM (List Float) Unit := s.forRevM fun x => modify (x :: ·)
  (r.run []).2 == [2, 3, big]

#guard Id.run ((Float64Array.mk #[1, 2, big])[*...*].findSomeRevM?
  (fun x => pure (if x == 2 then some x else none))) == some 2

-- The loops over slices stay within the slice, both with `start > 0` and with `stop < size`.
#guard
  let s := (Float64Array.mk #[big, 1, 2, 3, big])[1...4]
  s.foldr (fun x acc => x :: acc) [] == [1, 2, 3] &&
    s.foldl (fun acc x => x :: acc) [] == [3, 2, 1] && s.toList == [1, 2, 3] &&
    !s.any (· == big) && s.all (· != big) && !s.contains big && s.count (· != big) == 3 &&
    s.find? (· == big) == none && s.findRev? (· == big) == none &&
    s.find? (· != 1) == some 2 && s.findRev? (· != 3) == some 2

#guard Id.run do
  let mut r : List Float := []
  for x in (Float64Array.mk #[big, 1, 2, 3, big])[1...4] do
    r := x :: r
  return r == [3, 2, 1]

-- Early exits.
#guard Id.run do
  let mut r : List Float := []
  for x in (Float64Array.mk #[big, 1, 2, 3, big])[1...5] do
    if x == 3 then break
    r := x :: r
  return r == [2, 1]

#guard
  let s := (Float64Array.mk #[1, 2, big, 3, big])[1...5]
  s.any (· == big) && !s.all (· != big) && s.find? (· == big) == some big &&
    s.find? (· != 2) == some big && s.findRev? (· == big) == some big &&
    s.findRev? (· != big) == some 3

-- Empty slices.
#guard
  let s := (Float64Array.mk #[1, 2, 3])[1...1]
  s.foldl (fun acc x => x :: acc) [] == [] && s.toList == [] && !s.any (fun _ => true) &&
    s.all (fun _ => false) && s.count (fun _ => true) == 0 && s.find? (fun _ => true) == none &&
    s.findRev? (fun _ => true) == none && Id.run do
      let mut r : List Float := []
      for x in s do
        r := x :: r
      return r == []
#guard
  let s := (∅ : Float64Array.Slice)
  s.foldr (fun x acc => x :: acc) [] == [] && s.foldl (fun acc x => x :: acc) [] == [] &&
    !s.any (fun _ => true)

-- Loops in a monad other than `Id`.
#guard
  let r : StateM (List Float) Unit := do
    for x in (Float64Array.mk #[big, 1, 2, 3, big])[1...5] do
      if x == 3 then break
      modify (x :: ·)
  (r.run []).2 == [2, 1]
#guard
  let s := (Float64Array.mk #[big, 1, 2, 3, big])[1...4]
  let r : StateM (List Float) Unit := s.foldrM (fun x _ => modify (x :: ·)) ⟨⟩
  (r.run []).2 == [1, 2, 3]
#guard
  let s := (Float64Array.mk #[big, 1, 2, 3, big])[1...4]
  let r : StateM (List Float) Unit := s.foldlM (fun _ x => modify (x :: ·)) ⟨⟩
  (r.run []).2 == [3, 2, 1]
#guard (Float64Array.mk #[big, 1, 2, 3, big])[1...4].foldlM (m := Option)
  (fun acc x => if x == 2 then none else some (x :: acc)) [] == none
#guard (Float64Array.mk #[big, 1, 2, 3, big])[1...4].foldrM (m := Option)
  (fun x acc => if x == 2 then none else some (x :: acc)) [] == none
#guard (Float64Array.mk #[big, 1, 2, 3, big])[1...4].foldlM (m := Option)
  (fun acc x => some (x :: acc)) [] == some [3, 2, 1]
#guard (Float64Array.mk #[big, 1, 2, 3, big])[1...4].findSomeRevM? (m := Option)
  (fun x => if x == 3 then some none else some (some x)) == some (some 2)
#guard
  let xs := (Array.range 100000).map Nat.toFloat
  let s := (Float64Array.mk xs)[100...99900]
  let f := fun (acc : List Float) x => if x == 0 then x :: acc else acc
  s.foldl f [] == (xs.extract 100 99900).foldl f [] &&
    s.foldr (fun x acc => f acc x) [] == (xs.extract 100 99900).foldr (fun x acc => f acc x) []

/-! The `Std.Iterators` API on arrays and slices -/

#guard (Float64Array.mk #[1, 2, 3]).iter.toList == [1, 2, 3]
#guard ((Float64Array.mk #[1, 2, 3]).iter.map (· * 2)).toFloat64Array == Float64Array.mk #[2, 4, 6]
#guard ((Float64Array.mk #[1, 2, 3, big]).iter.filter (· != 2)).toFloat64Array ==
  Float64Array.mk #[1, 3, big]
#guard ((Float64Array.mk #[1, 2, 3, big]).iter.take 2).toFloat64Array == Float64Array.mk #[1, 2]
#guard ((Float64Array.mk #[1, 2, 3, big]).iter.drop 2).toFloat64Array == Float64Array.mk #[3, big]
#guard (((Float64Array.mk #[1, 2, 3]).iter.zip (Float64Array.mk #[big, 5]).iter).map
  fun (x, y) => x + y).toFloat64Array == Float64Array.mk #[1 + big, 7]
#guard ((Float64Array.mk #[1, 2, 3, big])[1...3].iter.map (· + 1)).toFloat64Array ==
  Float64Array.mk #[3, 4]
#guard (Float64Array.mk #[1, 2, 3]).iter.length == 3
#guard Float64Array.empty.iter.toFloat64Array == Float64Array.empty
#guard
  let xs := (Array.range 100000).map Nat.toFloat
  ((Float64Array.mk xs).iter.map (· + 1)).toFloat64Array.data == xs.map (· + 1)
#guard rawElemSize ((Float64Array.mk #[1]).iter.toFloat64Array) == elemSize
#guard (Float64Array.mk #[1, 2, 3]).iter.toFloat64ArrayWithCapacity 100 ==
  Float64Array.mk #[1, 2, 3]
#guard rawCapacity ((Float64Array.mk #[1, 2, 3]).iter.toFloat64ArrayWithCapacity 100) ≥ 100

/-! Membership, `ForM` and slice equality -/

#guard
  let a := Float64Array.mk #[1, 2, big]
  let r : StateM (List Float) PUnit := forM a fun x => modify (x :: ·)
  (r.run []).2 == [big, 2, 1]
#guard
  let s := (Float64Array.mk #[0, 1, 2, big])[1...3]
  let r : StateM (List Float) PUnit := forM s fun x => modify (x :: ·)
  (r.run []).2 == [2, 1]
#guard
  let r : StateM (List Float) PUnit := forM Float64Array.empty fun x => modify (x :: ·)
  (r.run []).2 == []
#guard (Float64Array.mk #[0, 1, 2, big])[1...3] == (Float64Array.mk #[1, 2, 5])[0...2]
#guard (Float64Array.mk #[1, big, 1, big])[0...2] == (Float64Array.mk #[1, big, 1, big])[2...4]
#guard (Float64Array.mk #[0, 1, 2, big])[1...3] != (Float64Array.mk #[1, 2, 5])[0...3]
#guard (Float64Array.mk #[0, 1, 2, big])[1...3] != (Float64Array.mk #[1, big])[0...2]
#guard (Float64Array.mk #[0, 1, 2, big])[1...3] != (Float64Array.mk #[2, 1])[0...2]
#guard (∅ : Float64Array.Slice) == (Float64Array.mk #[1, 2])[1...1]
#guard (Float64Array.mk #[1, 2, big] : Float64Array.Slice) ==
  (Float64Array.mk #[0, 1, 2, big])[1...*]
#guard
  let xs := (Array.range 100000).map Nat.toFloat
  (Float64Array.mk (#[0] ++ xs))[1...*] == (Float64Array.mk (xs ++ #[0]))[0...100000] &&
    (Float64Array.mk (#[0] ++ xs))[1...*] != (Float64Array.mk (xs.set! 99999 0))[0...100000]

/-! Lemmas from another module -/

example (a : Float64Array) (i : USize) (v : Float) (h) (j : Nat) (hj) :
    (a.uset i v h)[j]'hj = if i.toNat = j then v else a[j]'(by simpa using hj) := by
  simp
example (a : Float64Array) (v : Float) :
    (a.set! 0 v)[0]? = if 0 < a.size then some v else none := by
  simp
example (a : Float64Array) (v : Float) (h : 1 < (a.set! 0 v).size) :
    (a.set! 0 v)[1] = a[1]'(by simpa using h) := by
  simp
example (a : Float64Array) (p : Float → Bool) : (a.popWhile p).size ≤ a.size :=
  Float64Array.size_popWhile_le p a
example (src dest : Float64Array) :
    (src.copySlice 0 dest 0 src.size).size = max dest.size src.size := by
  simp
example (a : Float64Array) (f : Nat → Float → Option Nat) :
    a.toList.foldlM f 0 = a.foldlM f 0 := by
  simp
example (a : Float64Array) (f : Float → Nat → Option Nat) :
    a.toList.foldrM f 0 = a.foldrM f 0 := by
  simp
example (a : Float64Array) (f : Float → StateM Nat PUnit) : forM a.toList f = forM a f := by
  simp
example (a b : Float64Array) (x : Float) (h : x ∈ a) : x ∈ (a ++ b).toList := by
  simp [h]
example (a : Float64Array) (x : Float) : x ∈ a.push x := by
  simp
example (a : Float64Array) (i : Nat) (h : i < a.size) : a[i] ∈ a.toList := by
  simpa using Float64Array.getElem_mem h
example (a : Float64Array) (start stop : Nat) (p : Float → Bool) :
    (a.toSlice start stop).any p = (a.extract start stop).any p := by
  simp
example (a : Float64Array) (start stop : Nat) :
    (a.toSlice start stop).toList = (a.toList.extract start stop) := by
  simp
example (s : Float64Array.Slice) (p : Float → Bool) : s.count p = s.copy.toList.countP p := by
  simp
example (s : Float64Array.Slice) (p : Float → Bool) :
    s.find? p = s.copy.toList.find? p ∧ s.findRev? p = s.copy.toList.reverse.find? p := by
  simp
example (s : Float64Array.Slice) (f : Nat → Float → Nat) :
    s.foldl f 0 = s.copy.toList.foldl f 0 := by
  simp
example (s : Float64Array.Slice) (f : Float → StateM Nat PUnit) :
    forM s f = forM s.copy.toList f := by
  simp
example (s : Float64Array.Slice) (x : Float) : x ∈ s ↔ x ∈ s.copy.toList := by
  simp
example (s t : Float64Array.Slice) : (s == t) = (s.copy == t.copy) := by
  simp
example (a : Float64Array) : a.iter.toFloat64Array = a := by
  simp
example (s : Float64Array.Slice) : s.iter.toFloat64Array = s.copy := by
  simp
example : (∅ : Float64Array.Slice).size = 0 := by
  simp
