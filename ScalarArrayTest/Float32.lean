/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import ScalarArray.Float32
import ScalarArrayTest.Util
meta import ScalarArray.Float32
meta import ScalarArrayTest.Util

open ScalarArray ScalarArrayTest

/-- A test value at the edge of the element type's range. -/
private abbrev big : Float32 := -1.5e38

/-- The size of an element in bytes. -/
private abbrev elemSize : UInt32 := 4

/-! Construction and conversion -/

#guard (Float32Array.mk #[1, 2, 3, big]).data == #[1, 2, 3, big]
#guard (Float32Array.mk #[1, 2, 3, big]).toList == [1, 2, 3, big]
#guard (Float32Array.mk #[]).data == #[]
#guard Float32Array.empty.data == #[]
#guard (∅ : Float32Array).data == #[]
#guard (default : Float32Array).data == #[]
#guard (Float32Array.emptyWithCapacity 100).data == #[]
#guard (Float32Array.mk (Array.range 1000 |>.map Nat.toFloat32)).data ==
  (Array.range 1000).map Nat.toFloat32

/-! Size -/

#guard (Float32Array.mk #[1, 2, 3, big]).size == 4
#guard (Float32Array.mk #[1, 2, 3, big]).usize == 4
#guard Float32Array.empty.size == 0
#guard (Float32Array.emptyWithCapacity 100).size == 0

/-! Reading -/

#guard (Float32Array.mk #[1, 2, 3, big])[0] == 1
#guard (Float32Array.mk #[1, 2, 3, big])[3] == big
#guard (Float32Array.mk #[1, 2, 3, big])[(2 : USize)] == 3
#guard (Float32Array.mk #[1, 2, 3, big]).get! 1 == 2
#guard (Float32Array.mk #[1, 2, 3, big]).getD 2 7 == 3
#guard (Float32Array.mk #[1, 2, 3, big]).getD 4 7 == 7
#guard (Float32Array.mk #[1, 2, 3, big])[4]? == none
#guard (Float32Array.mk #[1, 2, 3, big])[1]? == some 2

/-! Writing -/

#guard ((Float32Array.mk #[1, 2, 3]).set 1 42 (by decide)).data == #[1, 42, 3]
#guard ((Float32Array.mk #[1, 2, 3]).uset 2 42 (by simp)).data == #[1, 2, 42]
#guard ((Float32Array.mk #[1, 2, 3]).set! 0 big).data == #[big, 2, 3]

-- Writing to a shared array must leave the original unchanged. The result is checked first so
-- that it is computed while the original is still live.
#guard
  let a := Float32Array.mk #[1, 2, 3]
  let b := a.set! 1 42
  b.data == #[1, 42, 3] && a.data == #[1, 2, 3]
#guard
  let a := Float32Array.mk #[1, 2, 3]
  let b := a.uset 0 big (by simp [a])
  b.data == #[big, 2, 3] && a.data == #[1, 2, 3]
#guard
  let a := Float32Array.mk #[1, 2, 3]
  let b := a.set 2 big (by simp [a])
  b.data == #[1, 2, big] && a.data == #[1, 2, 3]

-- `foldInPlace` shifts a range right by one, inserting the initial accumulator.
#guard
  let r := (Float32Array.mk #[1, 2, 3, 4]).foldInPlace 1 2 9 (fun _ _ x b => (b, x)) (by simp)
  r.1.data == #[1, 9, 2, 4] && r.2 == 3

-- `foldInPlace` on a shared array must leave the original unchanged, and `f` must see the
-- elements of the original even when it reads them from the array itself.
#guard
  let a := Float32Array.mk #[1, 2, 3, 4]
  let r := a.foldInPlace 0 4 9 (fun _ _ x b => (b, x)) (by simp [a])
  r.1.data == #[9, 1, 2, 3] && a.data == #[1, 2, 3, 4]
#guard
  let a := Float32Array.mk #[1, 2, 3, 4]
  let r := a.foldInPlace 1 3 0 (fun k _ _ b => (a[k.toNat]!, b)) (by simp [a])
  r.1.data == #[1, 1, 2, 3]

-- `foldInPlaceThen` hands the array and the last accumulator to `g`, here to store it.
#guard
  let r := (Float32Array.mk #[1, 2, 3, 4]).foldInPlaceThen 0 3 9 (fun _ _ x b => (b, x))
    (fun a b => a.set! 3 b) (by simp)
  r.data == #[9, 1, 2, 3]
#guard
  let a := Float32Array.mk #[1, 2, 3, 4]
  let r := a.foldInPlaceThen 1 2 9 (fun _ _ x b => (b, x)) Prod.mk (by simp [a])
  r.1.data == #[1, 9, 2, 4] && r.2 == 3 && a.data == #[1, 2, 3, 4]

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

-- Inlined `push` and `uset` on a closed array must copy it on every call, not write into a shared
-- constant: a later call must not change an earlier result.
@[noinline] def Float32Array.pushOntoConstant (x : Float32) : Float32Array :=
  (Float32Array.emptyWithCapacity 10).push x

@[noinline] def Float32Array.usetConstant (x : Float32) : Float32Array :=
  (Float32Array.mk #[0, 0]).uset 0 x

#guard
  let a := Float32Array.pushOntoConstant 1
  let b := Float32Array.pushOntoConstant 2
  b.data == #[2] && a.data == #[1]

#guard
  let a := Float32Array.usetConstant 1
  let b := Float32Array.usetConstant 2
  b.data == #[2, 0] && a.data == #[1, 0]

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

#guard ((Float32Array.mk #[0, 0, 0]).set! 1 big).data == #[0, big, 0]
#guard ((Float32Array.mk #[big, big, big]).set! 1 0).data == #[big, 0, big]
#guard ((Float32Array.mk #[0, 0, 0]).push big |>.push 0).data == #[0, 0, 0, big, 0]

/-! Indices beyond 16 bits, and huge `Nat` indices -/

#guard
  let a := (Float32Array.mk (Array.replicate 100000 0)).set! 99999 big |>.set! 70000 1
  a.size == 100000 && a[99999]! == big && a[70000]! == 1 && a[99998]! == 0 &&
    a[70000 % 65536]! == 0 && a.data[99999]! == big && a.data[70000]! == 1 &&
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
  let b := (Float32Array.mk a).set! 0 big
  b.data == #[big, 2, 3] && a == #[1, 2, 3]

#guard
  let a := Float32Array.mk #[1, 2, 3]
  let d := a.data.set! 0 big
  d == #[big, 2, 3] && a.data == #[1, 2, 3]

/-! Runtime representation -/

#guard rawElemSize (Float32Array.mk #[1, 2, 3]) == elemSize
#guard rawElemSize (Float32Array.emptyWithCapacity 10) == elemSize
#guard rawElemSize (Float32Array.empty.push 1) == elemSize
#guard rawElemSize ((Float32Array.mk #[1]).push 2) == elemSize
#guard rawCapacity (Float32Array.emptyWithCapacity 100) ≥ 100
#guard rawCapacity (Float32Array.mk #[1, 2, 3]) ≥ 3
-- Growth is geometric, so pushing is amortized constant time.
#guard rawCapacity ((Float32Array.mk #[1, 2, 3, 4]).push 5) ≥ 8


/-! Appending -/

#guard (Float32Array.mk #[1, 2] ++ Float32Array.mk #[3, big]).data == #[1, 2, 3, big]
#guard ((Float32Array.mk #[1, 2]).append (Float32Array.mk #[3])).data == #[1, 2, 3]
#guard (Float32Array.mk #[1, 2] ++ Float32Array.empty).data == #[1, 2]
#guard (Float32Array.empty ++ Float32Array.mk #[1, 2]).data == #[1, 2]
#guard (Float32Array.empty ++ Float32Array.empty).data == #[]
#guard (Float32Array.mk #[0, 0] ++ Float32Array.mk #[big] ++ Float32Array.mk #[0]).data ==
  #[0, 0, big, 0]

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
    a := a ++ Float32Array.mk #[i.toFloat32, (i * 7).toFloat32, big]
    r := r ++ #[i.toFloat32, (i * 7).toFloat32, big]
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
#guard rawElemSize (Float32Array.mk #[1] ++ Float32Array.mk #[2]) == elemSize

/-! Equality -/

#guard Float32Array.mk #[1, 2, big] == Float32Array.mk #[1, 2, big]
#guard Float32Array.mk #[1, 2, big] != Float32Array.mk #[1, 2, 0]
#guard Float32Array.mk #[1, 2] != Float32Array.mk #[1, 2, 0]
#guard Float32Array.mk #[1, 2, 0] != Float32Array.mk #[1, 2]
#guard Float32Array.empty == Float32Array.emptyWithCapacity 10
#guard (Float32Array.mk #[1, 2] ++ Float32Array.mk #[big]) == Float32Array.mk #[1, 2, big]
-- Capacity and leftover memory past the size don't matter.
#guard (Float32Array.emptyWithCapacity 100).push 1 == Float32Array.mk #[1]
#guard (Float32Array.mk #[1, 2, 3]).pop == Float32Array.mk #[1, 2]
#guard (Float32Array.mk (Array.replicate 100000 0)).set! 99999 big !=
  Float32Array.mk (Array.replicate 100000 0)

/-! Iteration -/

#guard (Float32Array.mk #[1, 2, big]).foldl (fun acc x => x :: acc) [] == [big, 2, 1]
#guard (Float32Array.mk #[1, 2, big]).foldr (fun x acc => x :: acc) [] == [1, 2, big]
#guard Float32Array.empty.foldl (fun acc x => x :: acc) [] == []
#guard Float32Array.empty.foldr (fun x acc => x :: acc) [] == []
#guard (Float32Array.mk #[1, 2, big]).foldlM (m := Option)
  (fun acc x => if x == 2 then none else some (x :: acc)) [] == none
#guard (Float32Array.mk #[1, big]).foldrM (m := Option) (fun x acc => some (x :: acc)) [] ==
  some [1, big]

#guard Id.run do
  let mut r : List Float32 := []
  for x in Float32Array.mk #[1, 2, big] do
    r := x :: r
  return r == [big, 2, 1]

#guard Id.run do
  let mut r : List Float32 := []
  for x in Float32Array.mk #[1, 2, 3, 4] do
    if x == 3 then break
    r := x :: r
  return r == [2, 1]

#guard
  let r : StateM (List Float32) Unit := (Float32Array.mk #[1, 2, big]).forM fun x => modify (x :: ·)
  (r.run []).2 == [big, 2, 1]

#guard
  let xs := (Array.range 100000).map Nat.toFloat32
  let f := fun (acc : List Float32) x => if x == 0 then x :: acc else acc
  (Float32Array.mk xs).foldl f [] == xs.foldl f []

#guard (Float32Array.mk #[1, 2, big]).any (· == big)
#guard !(Float32Array.mk #[1, 2, 3]).any (· == big)
#guard (Float32Array.mk #[1, 2, 3]).all (· != big)
#guard !(Float32Array.mk #[1, big, 3]).all (· != big)
#guard !Float32Array.empty.any (fun _ => true) && Float32Array.empty.all (fun _ => false)
#guard (Float32Array.mk #[1, 2, big]).contains big
#guard !(Float32Array.mk #[1, 2, 3]).contains big && !Float32Array.empty.contains big

-- Early exits, and loops in a monad other than `Id`.
#guard (Float32Array.mk #[1, 2, big]).foldrM (m := Option)
  (fun x acc => if x == 1 then none else some (x :: acc)) [] == none
#guard (Float32Array.mk #[big, 2, 1]).foldrM (m := Option)
  (fun x acc => if x == big then none else some (x :: acc)) [] == none
#guard
  let r : StateM (List Float32) Unit := do
    for x in Float32Array.mk #[1, 2, big, 3] do
      if x == big then break
      modify (x :: ·)
  (r.run []).2 == [2, 1]
#guard
  let r : StateM (List Float32) Unit :=
    (Float32Array.mk #[1, 2, big]).foldrM (fun x _ => modify (x :: ·)) ⟨⟩
  (r.run []).2 == [1, 2, big]
#guard Id.run do
  let mut r : List Float32 := []
  for x in Float32Array.empty do
    r := x :: r
  return r == []
#guard !(Float32Array.mk #[1, 2, 3]).contains big
#guard (Float32Array.mk (Array.replicate 100000 0) |>.set! 99999 big).contains big

/-! Removing elements -/

#guard Float32Array.empty.isEmpty && !(Float32Array.mk #[1]).isEmpty
#guard (Float32Array.mk #[1]).pop.isEmpty
#guard (Float32Array.mk #[1, 2, big]).pop.data == #[1, 2]
#guard Float32Array.empty.pop.data == #[]
#guard ((Float32Array.mk #[1, 2, 3]).pop.push big).data == #[1, 2, big]
#guard (Float32Array.mk #[1, 2, big]).back? == some big
#guard Float32Array.empty.back? == none
#guard (Float32Array.mk #[1, 2, big]).back! == big
#guard (Float32Array.mk #[1, 2, big]).back (by decide) == big

-- Popping from a shared array must leave the original unchanged.
#guard
  let a := Float32Array.mk #[1, 2, 3]
  let b := a.pop
  b.data == #[1, 2] && a.data == #[1, 2, 3]

-- The array is built from a parameter so that it isn't extracted as a shared closed term.
@[noinline] def Float32Array.popsInPlace (x : Float32) : Bool :=
  let a := (Float32Array.mk #[x]).push x
  let p := rawAddr a
  let a := a.pop
  rawAddr a == p && a.data == #[x]

#guard Float32Array.popsInPlace 1

#guard (Float32Array.mk #[1, 0, big, 0, 0]).popWhile (· == 0) == Float32Array.mk #[1, 0, big]
#guard (Float32Array.mk #[1, 0, big]).popWhile (· == 0) == Float32Array.mk #[1, 0, big]
#guard (Float32Array.mk #[0, 0]).popWhile (· == 0) == Float32Array.empty
#guard Float32Array.empty.popWhile (· == 0) == Float32Array.empty

-- Popping several elements from an exclusive array.
@[noinline] def Float32Array.popsWhileInPlace (x : Float32) : Bool :=
  let a := (Float32Array.mk #[x]).push 0 |>.push 0
  let p := rawAddr a
  let a := a.popWhile (· == 0)
  rawAddr a == p && a.data == #[x]

#guard Float32Array.popsWhileInPlace 1

example (p : Float32 → Bool) (a : Float32Array) : (a.popWhile p).data = a.data.popWhile p := by simp

#guard ((Float32Array.mk #[1, 2, 3, big]).extract 1 3).data == #[2, 3]
#guard ((Float32Array.mk #[1, 2, 3, big]).extract 2 100).data == #[3, big]
#guard ((Float32Array.mk #[1, 2, 3]).extract 0 3).data == #[1, 2, 3]
#guard ((Float32Array.mk #[1, 2, 3]).extract 2 1).data == #[]
#guard ((Float32Array.mk #[1, 2, 3]).extract 5 9).data == #[]
#guard ((Float32Array.mk #[1, 2, 3]).extract (2 ^ 70) (2 ^ 71)).data == #[]
#guard ((Float32Array.mk #[1, 2, 3]).extract 1 (2 ^ 70)).data == #[2, 3]
#guard
  let xs := (Array.range 100000).map Nat.toFloat32
  ((Float32Array.mk xs).extract 70000 70010).data == xs.extract 70000 70010
#guard rawElemSize ((Float32Array.mk #[1, 2, 3]).extract 1 2) == elemSize

-- The extracted array is independent of the original.
#guard
  let a := Float32Array.mk #[1, 2, 3]
  let b := (a.extract 0 2).set! 0 big
  b.data == #[big, 2] && a.data == #[1, 2, 3]

/-! Building arrays -/

#guard (Float32Array.replicate 3 big).data == #[big, big, big]
#guard (Float32Array.replicate 0 1).data == #[]
#guard (Float32Array.replicate 100000 big).data == Array.replicate 100000 big
#guard (Float32Array.ofFn (n := 4) fun i => i.val.toFloat32).data == #[0, 1, 2, 3]
#guard (Float32Array.ofFn (n := 0) fun i => i.val.toFloat32).data == #[]
#guard rawElemSize (Float32Array.replicate 2 1) == elemSize
#guard rawElemSize (Float32Array.ofFn (n := 2) fun _ => 1) == elemSize

/-! Lemmas -/

example (a : Float32Array) (v : Float32) : (a.push v).pop = a := by simp [Float32Array.ext_iff]
example : (Float32Array.replicate 3 big)[1] = big := by simp
example (a b : Float32Array) (h : 0 < a.size) : (a ++ b)[0]'(by simp; omega) = a[0] := by simp [h]
example (a : Float32Array) (i : Nat) (v : Float32) (h : i < a.size) :
    (a.set i v h)[i]'(by simpa) = v := by simp
example (a : Float32Array) : a.extract 0 a.size = a := by simp
example (a : Float32Array) (v : Float32) : (a.push v).pop = a :=
  Float32Array.ext_getElem (by simp) (by simp_all)

/-! Default bounds proofs -/

#guard (Float32Array.mk #[1, 2, big]).get 2 == big
#guard (Float32Array.mk #[1, 2, big]).uget 2 == big
#guard ((Float32Array.mk #[1, 2, 3]).set 1 big).data == #[1, big, 3]
#guard ((Float32Array.mk #[1, 2, 3]).uset 1 big).data == #[1, big, 3]

/-! `set!` leaves the array unchanged when the index is out of bounds, like `ByteArray.set!`. -/

#guard ((Float32Array.mk #[1, 2, 3]).set! 3 big).data == #[1, 2, 3]
#guard ((Float32Array.mk #[1, 2, 3]).set! (2 ^ 70) big).data == #[1, 2, 3]

/-! Folds over part of an array -/

#guard (Float32Array.mk #[1, 2, 3, big]).foldl (fun acc x => x :: acc) [] 1 3 == [3, 2]
#guard (Float32Array.mk #[1, 2, 3, big]).foldl (fun acc x => x :: acc) [] 2 == [big, 3]
#guard (Float32Array.mk #[1, 2, 3, big]).foldl (fun acc x => x :: acc) [] 1 100 == [big, 3, 2]
#guard (Float32Array.mk #[1, 2, 3, big]).foldl (fun acc x => x :: acc) [] 3 1 == []
#guard (Float32Array.mk #[1, 2, 3, big]).foldl (fun acc x => x :: acc) [] 9 12 == []
#guard (Float32Array.mk #[1, 2, 3]).foldlM (m := Option)
  (fun acc x => if x == 1 then none else some (x :: acc)) [] 1 == some [3, 2]

/-! Copying slices -/

#guard
  let src := Float32Array.mk #[10, 11, 12, big]
  let dest := Float32Array.mk #[1, 2, 3, 4, 5]
  (src.copySlice 1 dest 2 2).data == #[1, 2, 11, 12, 5] &&
  (src.copySlice 1 dest 4 3).data == #[1, 2, 3, 4, 11, 12, big] &&
  (src.copySlice 0 dest 9 2).data == #[1, 2, 3, 4, 5, 10, 11] &&
  (src.copySlice 9 dest 1 2).data == #[1, 2, 3, 4, 5] &&
  (src.copySlice 2 dest 0 10).data == #[12, big, 3, 4, 5] &&
  (src.copySlice 0 dest 0 0).data == #[1, 2, 3, 4, 5] &&
  (src.copySlice 0 Float32Array.empty 0 4).data == #[10, 11, 12, big] &&
  dest.data == #[1, 2, 3, 4, 5] && src.data == #[10, 11, 12, big]

-- Copying from an array into itself.
#guard
  let a := Float32Array.mk #[1, 2, 3, big]
  (a.copySlice 0 a 2 4).data == #[1, 2, 1, 2, 3, big]

#guard
  let xs := (Array.range 100000).map Nat.toFloat32
  let a := Float32Array.mk xs
  (a.copySlice 70000 (Float32Array.replicate 10 0) 5 10).data ==
    Array.replicate 5 0 ++ xs.extract 70000 70010

#guard rawElemSize ((Float32Array.mk #[1]).copySlice 0 Float32Array.empty 0 1) == elemSize

@[noinline] def Float32Array.copiesSliceInPlace (x : Float32) : Bool :=
  let dest := (Float32Array.emptyWithCapacity 10).push x |>.push x |>.push x
  let p := rawAddr dest
  let dest := (Float32Array.mk #[big, big]).copySlice 0 dest 1 2
  rawAddr dest == p && dest.data == #[x, big, big]

@[noinline] def Float32Array.copySliceGrowth (x : Float32) : Bool :=
  let dest := (Float32Array.mk #[x, x, x, x])
  rawCapacity ((Float32Array.mk #[x]).copySlice 0 dest 4 1 (exact := false)) ≥ 8 &&
    rawCapacity ((Float32Array.mk #[x]).copySlice 0 dest 4 1) == 5

#guard Float32Array.copiesSliceInPlace 1
#guard Float32Array.copySliceGrowth 1

/-! Linearity markers -/

#guard ((Float32Array.mk #[1, 2]).markLinear.push big).data == #[1, 2, big]
#guard ((Float32Array.mk #[1]).propagateMark (Float32Array.mk #[2, big])).data == #[2, big]

/-! Search -/

#guard (Float32Array.mk #[1, 2, big, 2]).findIdx? (· == 2) == some 1
#guard (Float32Array.mk #[1, 2, big, 2]).findIdx? (· == 2) 2 == some 3
#guard (Float32Array.mk #[1, 2, big, 2]).findIdx? (· == 3) == none
#guard (Float32Array.mk #[1, 2, big, 2]).findIdx? (· == 1) 9 == none
#guard ((Float32Array.mk #[1, 2, big, 2]).findFinIdx? (· == big)).map (·.val) == some 2

/-! Lists -/

#guard (Float32Array.ofList [1, 2, big]).data == #[1, 2, big]
#guard (Float32Array.ofList []).data == #[]
#guard [1, 2, big].toFloat32Array == Float32Array.mk #[1, 2, big]
#guard (Float32Array.ofList ((List.range 100000).map Nat.toFloat32)).data ==
  (Array.range 100000).map Nat.toFloat32
#guard rawElemSize (Float32Array.ofList [1, 2]) == elemSize

/-! More lemmas -/

example (a b c : Float32Array) : a ++ b ++ c = a ++ (b ++ c) := Float32Array.append_assoc ..
example (a : Float32Array) : a ++ ∅ = a := by simp
example (a b : Float32Array) : (a ++ b).extract 0 a.size = a := by simp
example (a : Float32Array) (i : Nat) (v : Float32) : (a.set! i v).size = a.size := by simp
example (l : List Float32) : (Float32Array.ofList l).toList = l := by simp
example (a : Float32Array) : Float32Array.ofList a.toList = a := by simp

/-! Slices -/

#guard
  let a := Float32Array.mk #[1, 2, 3, big]
  let s := a[1...3]
  s.size == 2 && s[0]! == 2 && s[1]! == 3 && s.getD 2 7 == 7 && s.copy == Float32Array.mk #[2, 3] &&
    s.toList == [2, 3] && s.toArray == #[2, 3]

#guard
  let a := Float32Array.mk #[1, 2, 3, big]
  a[1...=3].toList == [2, 3, big] && a[*...2].toList == [1, 2] && a[2...*].toList == [3, big] &&
    a[*...*].toList == [1, 2, 3, big] && a[0<...2].toList == [2] &&
    a[0<...=2].toList == [2, 3] && a[*...=1].toList == [1, 2] && a[1<...*].toList == [3, big]

-- Bounds are clamped.
#guard
  let a := Float32Array.mk #[1, 2, 3, big]
  a[2...100].toList == [3, big] && a[3...1].size == 0 && a[9...12].size == 0 &&
    (a.toSlice 1 (2 ^ 70)).toList == [2, 3, big]

-- Slices of slices.
#guard
  let s := (Float32Array.mk #[1, 2, 3, big])[1...4]
  s[1...2].toList == [3] && s[0...100].toList == [2, 3, big] && s[*...*].toList == [2, 3, big] &&
    s[2...*].toList == [big] && s[5...6].size == 0

#guard
  let s := (Float32Array.mk #[1, 2, 3, big])[1...4]
  s.popFront.toList == [3, big] && s.popFront.popFront.popFront.popFront.size == 0

#guard (∅ : Float32Array.Slice).size == 0 && (default : Float32Array.Slice).toList == []

-- An array coerces to the slice of all its elements.
#guard
  let s : Float32Array.Slice := Float32Array.mk #[1, 2, big]
  s.toList == [1, 2, big] && s.start == 0

-- A slice does not coerce back to an array, since that would copy.
example (s : Float32Array.Slice) : Float32Array := s.copy

#guard Id.run do
  let mut r : List Float32 := []
  for x in (Float32Array.mk #[1, 2, 3, big])[1...*] do
    r := x :: r
  return r == [big, 3, 2]

#guard (Float32Array.mk #[1, 2, 3, big])[1...*].foldl (fun acc x => x :: acc) [] == [big, 3, 2]

#guard
  let xs := (Array.range 100000).map Nat.toFloat32
  let s := (Float32Array.mk xs)[70000...70010]
  s.toArray == xs.extract 70000 70010 && s.copy.data == xs.extract 70000 70010

#guard toString (Float32Array.mk #[1, 2, 3])[1...*] == toString (Float32Array.mk #[2, 3])

-- Taking a slice doesn't copy the array.
@[noinline] def Float32Array.slicesWithoutCopying (x : Float32) : Bool :=
  let a := Float32Array.mk #[x, 2, 3]
  let p := rawAddr a
  rawAddr a[1...2].array == p

#guard Float32Array.slicesWithoutCopying 1

example (s : Float32Array.Slice) : s.copy.size = s.size := by simp

/-! Slice API -/

#guard
  let s := (Float32Array.mk #[1, 2, 3, big, 2])[1...5]
  s.foldr (fun x acc => x :: acc) [] == [2, 3, big, 2] &&
    s.foldl (fun acc x => x :: acc) [] == [2, big, 3, 2] &&
    s.any (· == big) && !s.any (· == 1) && s.all (· != 1) && !s.all (· == 2) &&
    s.contains big && !s.contains 1 && s.count (· == 2) == 2 &&
    s.find? (· > 2) == some 3 && s.findRev? (· != big) == some 2 && s.findRev? (· == 1) == none

#guard (Float32Array.mk #[1, 2, 3])[1...1].foldr (fun x acc => x :: acc) [] == []
#guard (Float32Array.mk #[1, 2, 3])[3...*].find? (fun _ => true) == none

#guard
  let s := (Float32Array.mk #[1, 2, 3, big])[1...*]
  let r : StateM (List Float32) Unit := s.forRevM fun x => modify (x :: ·)
  (r.run []).2 == [2, 3, big]

#guard Id.run ((Float32Array.mk #[1, 2, big])[*...*].findSomeRevM?
  (fun x => pure (if x == 2 then some x else none))) == some 2

-- The loops over slices stay within the slice, both with `start > 0` and with `stop < size`.
#guard
  let s := (Float32Array.mk #[big, 1, 2, 3, big])[1...4]
  s.foldr (fun x acc => x :: acc) [] == [1, 2, 3] &&
    s.foldl (fun acc x => x :: acc) [] == [3, 2, 1] && s.toList == [1, 2, 3] &&
    !s.any (· == big) && s.all (· != big) && !s.contains big && s.count (· != big) == 3 &&
    s.find? (· == big) == none && s.findRev? (· == big) == none &&
    s.find? (· != 1) == some 2 && s.findRev? (· != 3) == some 2

#guard Id.run do
  let mut r : List Float32 := []
  for x in (Float32Array.mk #[big, 1, 2, 3, big])[1...4] do
    r := x :: r
  return r == [3, 2, 1]

-- Early exits.
#guard Id.run do
  let mut r : List Float32 := []
  for x in (Float32Array.mk #[big, 1, 2, 3, big])[1...5] do
    if x == 3 then break
    r := x :: r
  return r == [2, 1]

#guard
  let s := (Float32Array.mk #[1, 2, big, 3, big])[1...5]
  s.any (· == big) && !s.all (· != big) && s.find? (· == big) == some big &&
    s.find? (· != 2) == some big && s.findRev? (· == big) == some big &&
    s.findRev? (· != big) == some 3

-- Empty slices.
#guard
  let s := (Float32Array.mk #[1, 2, 3])[1...1]
  s.foldl (fun acc x => x :: acc) [] == [] && s.toList == [] && !s.any (fun _ => true) &&
    s.all (fun _ => false) && s.count (fun _ => true) == 0 && s.find? (fun _ => true) == none &&
    s.findRev? (fun _ => true) == none && Id.run do
      let mut r : List Float32 := []
      for x in s do
        r := x :: r
      return r == []
#guard
  let s := (∅ : Float32Array.Slice)
  s.foldr (fun x acc => x :: acc) [] == [] && s.foldl (fun acc x => x :: acc) [] == [] &&
    !s.any (fun _ => true)

-- Loops in a monad other than `Id`.
#guard
  let r : StateM (List Float32) Unit := do
    for x in (Float32Array.mk #[big, 1, 2, 3, big])[1...5] do
      if x == 3 then break
      modify (x :: ·)
  (r.run []).2 == [2, 1]
#guard
  let s := (Float32Array.mk #[big, 1, 2, 3, big])[1...4]
  let r : StateM (List Float32) Unit := s.foldrM (fun x _ => modify (x :: ·)) ⟨⟩
  (r.run []).2 == [1, 2, 3]
#guard
  let s := (Float32Array.mk #[big, 1, 2, 3, big])[1...4]
  let r : StateM (List Float32) Unit := s.foldlM (fun _ x => modify (x :: ·)) ⟨⟩
  (r.run []).2 == [3, 2, 1]
#guard (Float32Array.mk #[big, 1, 2, 3, big])[1...4].foldlM (m := Option)
  (fun acc x => if x == 2 then none else some (x :: acc)) [] == none
#guard (Float32Array.mk #[big, 1, 2, 3, big])[1...4].foldrM (m := Option)
  (fun x acc => if x == 2 then none else some (x :: acc)) [] == none
#guard (Float32Array.mk #[big, 1, 2, 3, big])[1...4].foldlM (m := Option)
  (fun acc x => some (x :: acc)) [] == some [3, 2, 1]
#guard (Float32Array.mk #[big, 1, 2, 3, big])[1...4].findSomeRevM? (m := Option)
  (fun x => if x == 3 then some none else some (some x)) == some (some 2)
#guard
  let xs := (Array.range 100000).map Nat.toFloat32
  let s := (Float32Array.mk xs)[100...99900]
  let f := fun (acc : List Float32) x => if x == 0 then x :: acc else acc
  s.foldl f [] == (xs.extract 100 99900).foldl f [] &&
    s.foldr (fun x acc => f acc x) [] == (xs.extract 100 99900).foldr (fun x acc => f acc x) []

/-! The `Std.Iterators` API on arrays and slices -/

#guard (Float32Array.mk #[1, 2, 3]).iter.toList == [1, 2, 3]
#guard ((Float32Array.mk #[1, 2, 3]).iter.map (· * 2)).toFloat32Array == Float32Array.mk #[2, 4, 6]
#guard ((Float32Array.mk #[1, 2, 3, big]).iter.filter (· != 2)).toFloat32Array ==
  Float32Array.mk #[1, 3, big]
#guard ((Float32Array.mk #[1, 2, 3, big]).iter.take 2).toFloat32Array == Float32Array.mk #[1, 2]
#guard ((Float32Array.mk #[1, 2, 3, big]).iter.drop 2).toFloat32Array == Float32Array.mk #[3, big]
#guard (((Float32Array.mk #[1, 2, 3]).iter.zip (Float32Array.mk #[big, 5]).iter).map
  fun (x, y) => x + y).toFloat32Array == Float32Array.mk #[1 + big, 7]
#guard ((Float32Array.mk #[1, 2, 3, big])[1...3].iter.map (· + 1)).toFloat32Array ==
  Float32Array.mk #[3, 4]
#guard (Float32Array.mk #[1, 2, 3]).iter.length == 3
#guard Float32Array.empty.iter.toFloat32Array == Float32Array.empty
#guard
  let xs := (Array.range 100000).map Nat.toFloat32
  ((Float32Array.mk xs).iter.map (· + 1)).toFloat32Array.data == xs.map (· + 1)
#guard rawElemSize ((Float32Array.mk #[1]).iter.toFloat32Array) == elemSize
#guard (Float32Array.mk #[1, 2, 3]).iter.toFloat32ArrayWithCapacity 100 ==
  Float32Array.mk #[1, 2, 3]
#guard rawCapacity ((Float32Array.mk #[1, 2, 3]).iter.toFloat32ArrayWithCapacity 100) ≥ 100

/-! Membership, `ForM` and slice equality -/

#guard
  let a := Float32Array.mk #[1, 2, big]
  let r : StateM (List Float32) PUnit := forM a fun x => modify (x :: ·)
  (r.run []).2 == [big, 2, 1]
#guard
  let s := (Float32Array.mk #[0, 1, 2, big])[1...3]
  let r : StateM (List Float32) PUnit := forM s fun x => modify (x :: ·)
  (r.run []).2 == [2, 1]
#guard
  let r : StateM (List Float32) PUnit := forM Float32Array.empty fun x => modify (x :: ·)
  (r.run []).2 == []
#guard (Float32Array.mk #[0, 1, 2, big])[1...3] == (Float32Array.mk #[1, 2, 5])[0...2]
#guard (Float32Array.mk #[1, big, 1, big])[0...2] == (Float32Array.mk #[1, big, 1, big])[2...4]
#guard (Float32Array.mk #[0, 1, 2, big])[1...3] != (Float32Array.mk #[1, 2, 5])[0...3]
#guard (Float32Array.mk #[0, 1, 2, big])[1...3] != (Float32Array.mk #[1, big])[0...2]
#guard (Float32Array.mk #[0, 1, 2, big])[1...3] != (Float32Array.mk #[2, 1])[0...2]
#guard (∅ : Float32Array.Slice) == (Float32Array.mk #[1, 2])[1...1]
#guard (Float32Array.mk #[1, 2, big] : Float32Array.Slice) ==
  (Float32Array.mk #[0, 1, 2, big])[1...*]
#guard
  let xs := (Array.range 100000).map Nat.toFloat32
  (Float32Array.mk (#[0] ++ xs))[1...*] == (Float32Array.mk (xs ++ #[0]))[0...100000] &&
    (Float32Array.mk (#[0] ++ xs))[1...*] != (Float32Array.mk (xs.set! 99999 0))[0...100000]

/-! Writing through slices -/

#guard ((Float32Array.mk #[1, 2, 3, 4])[1...3].set 1 big).array.data == #[1, 2, big, 4]
#guard ((Float32Array.mk #[1, 2, 3, 4])[1...3].set! 1 big).toList == [2, big]
#guard ((Float32Array.mk #[1, 2, 3, 4])[1...3].set! 2 big).array.data == #[1, 2, 3, 4]
#guard ((Float32Array.mk #[1, 2, 3, 4])[1...3].modify 0 (· * 10)).array.data == #[1, 20, 3, 4]
#guard ((Float32Array.mk #[1, 2, 3, 4])[1...3].modify 2 (· * 10)).array.data == #[1, 2, 3, 4]
#guard ((Float32Array.mk #[1, 2, 3, big])[1...4].swap 0 2).array.data == #[1, big, 3, 2]
#guard ((Float32Array.mk #[1, 2, 3, big])[1...4].swap 1 1).array.data == #[1, 2, 3, big]
#guard ((Float32Array.mk #[0, 1, 2, 3, 4, 0])[1...5].reverse).array.data == #[0, 4, 3, 2, 1, 0]
#guard ((Float32Array.mk #[0, 1, 2, 3, 0])[1...4].reverse).array.data == #[0, 3, 2, 1, 0]
#guard ((Float32Array.mk #[1, 2])[1...1].reverse).array.data == #[1, 2]
#guard (∅ : Float32Array.Slice).reverse.toList == []

-- `foldlInPlace` on a slice shifts its range right by one, inserting the initial accumulator.
#guard
  let r := (Float32Array.mk #[1, 2, 3, 4])[1...3].foldlInPlace 9 (fun _ _ x b => (b, x))
  r.1.array.data == #[1, 9, 2, 4] && r.2 == 3 && r.1.start == 1 && r.1.stop == 3
#guard
  let r := (Float32Array.mk #[1, 2, 3, 4])[2...2].foldlInPlace 9 (fun _ _ x b => (b, x))
  r.1.array.data == #[1, 2, 3, 4] && r.2 == 9

-- `foldrInPlace` shifts the range left by one, from the last element to the first.
#guard
  let r := (Float32Array.mk #[1, 2, 3, 4])[1...3].foldrInPlace 9 (fun _ _ x b => (b, x))
  r.1.array.data == #[1, 3, 9, 4] && r.2 == 2 && r.1.start == 1 && r.1.stop == 3
#guard
  let r := (Float32Array.mk #[1, 2, 3, 4])[2...2].foldrInPlace 9 (fun _ _ x b => (b, x))
  r.1.array.data == #[1, 2, 3, 4] && r.2 == 9

-- The `Then` versions hand the slice and the last accumulator to `g`, here to store it.
#guard
  let s := (Float32Array.mk #[1, 2, 3, 4])[0...4]
  (s.foldlInPlaceThen 9 (fun _ _ x b => (b, x)) (fun s b => s.set! 0 b)).toList == [4, 1, 2, 3] &&
    (s.foldrInPlaceThen 9 (fun _ _ x b => (b, x)) (fun s b => s.set! 3 b)).toList ==
      [2, 3, 4, 1]
#guard
  let a := Float32Array.mk #[1, 2, 3, 4]
  let r := a[1...3].foldlInPlaceThen 9 (fun _ _ x b => (b, x)) Prod.mk
  let r' := a[1...3].foldrInPlaceThen 9 (fun _ _ x b => (b, x)) Prod.mk
  r.1.array.data == #[1, 9, 2, 4] && r.2 == 3 && r'.1.array.data == #[1, 3, 9, 4] && r'.2 == 2 &&
    a.data == #[1, 2, 3, 4]

-- The indices passed to `f`, counted from the start of the slice, in the order of the visits.
#guard
  let s := (Float32Array.mk #[1, 2, 3, 4, 5])[1...4]
  (s.foldlInPlace [] (fun k _ x b => (x, k.toNat :: b))).2 == [2, 1, 0] &&
    (s.foldrInPlace [] (fun k _ x b => (x, k.toNat :: b))).2 == [0, 1, 2]

-- Writing through a slice of a shared array must leave the original unchanged.
#guard
  let a := Float32Array.mk #[1, 2, 3, 4]
  let s := a[1...4].set 0 big
  s.array.data == #[1, big, 3, 4] && a.data == #[1, 2, 3, 4]
#guard
  let a := Float32Array.mk #[1, 2, 3, 4]
  let s := a[0...4].reverse
  s.array.data == #[4, 3, 2, 1] && a.data == #[1, 2, 3, 4]
#guard
  let a := Float32Array.mk #[1, 2, 3, 4]
  let r := a[0...4].foldlInPlace 9 (fun _ _ x b => (b, x))
  r.1.array.data == #[9, 1, 2, 3] && a.data == #[1, 2, 3, 4]
#guard
  let a := Float32Array.mk #[1, 2, 3, 4]
  let r := a[0...4].foldrInPlace 9 (fun _ _ x b => (b, x))
  r.1.array.data == #[2, 3, 4, 9] && a.data == #[1, 2, 3, 4]
#guard
  let s := (Float32Array.mk #[1, 2, 3, 4])[0...4]
  let t := s.swap 0 3
  t.toList == [4, 2, 3, 1] && s.toList == [1, 2, 3, 4]

-- A slice of an array that is no longer used writes into that array, without copying it.
@[noinline] def Float32Array.writesThroughSliceInPlace (x : Float32) : Bool :=
  let a := (Float32Array.emptyWithCapacity 8).push x |>.push 2 |>.push 3 |>.push 4 |>.push x
  let p := rawAddr a
  let s := a[1...4]
  let s := s.set! 0 big
  let s := if h : 2 < s.size then s.swap 0 2 else s
  let s := s.modify 1 (· + 1)
  let s := s.reverse
  let (s, _) := s.foldlInPlace () (fun _ _ x b => (x + 1, b))
  let (s, _) := s.foldrInPlace () (fun _ _ x b => (x + 1, b))
  let s := s.foldlInPlaceThen () (fun _ _ x b => (x + 1, b)) (fun s _ => s)
  let s := s.foldrInPlaceThen () (fun _ _ x b => (x + 1, b)) (fun s _ => s)
  rawAddr s.array == p && s.array.data == #[x, big + 4, 8, 8, x]

#guard Float32Array.writesThroughSliceInPlace 1

-- Reversing a large slice takes linear time only when every swap writes in place.
#guard
  let n := 1000000
  let xs := (Array.range n).map Nat.toFloat32
  (Float32Array.mk xs)[0...n].reverse.array.data == xs.reverse

/-! Lemmas from another module -/

example (a : Float32Array) (i : USize) (v : Float32) (h) (j : Nat) (hj) :
    (a.uset i v h)[j]'hj = if i.toNat = j then v else a[j]'(by simpa using hj) := by
  simp
example (a : Float32Array) (v : Float32) :
    (a.set! 0 v)[0]? = if 0 < a.size then some v else none := by
  simp
example (a : Float32Array) (v : Float32) (h : 1 < (a.set! 0 v).size) :
    (a.set! 0 v)[1] = a[1]'(by simpa using h) := by
  simp
example (a : Float32Array) (p : Float32 → Bool) : (a.popWhile p).size ≤ a.size :=
  Float32Array.size_popWhile_le p a
example (src dest : Float32Array) :
    (src.copySlice 0 dest 0 src.size).size = max dest.size src.size := by
  simp
example (a : Float32Array) (f : Nat → Float32 → Option Nat) :
    a.toList.foldlM f 0 = a.foldlM f 0 := by
  simp
example (a : Float32Array) (f : Float32 → Nat → Option Nat) :
    a.toList.foldrM f 0 = a.foldrM f 0 := by
  simp
example (a : Float32Array) (f : Float32 → StateM Nat PUnit) : forM a.toList f = forM a f := by
  simp
example (a b : Float32Array) (x : Float32) (h : x ∈ a) : x ∈ (a ++ b).toList := by
  simp [h]
example (a : Float32Array) (x : Float32) : x ∈ a.push x := by
  simp
example (a : Float32Array) (i : Nat) (h : i < a.size) : a[i] ∈ a.toList := by
  simpa using Float32Array.getElem_mem h
example (a : Float32Array) (start stop : Nat) (p : Float32 → Bool) :
    (a.toSlice start stop).any p = (a.extract start stop).any p := by
  simp
example (a : Float32Array) (start stop : Nat) :
    (a.toSlice start stop).toList = (a.toList.extract start stop) := by
  simp
example (s : Float32Array.Slice) (p : Float32 → Bool) : s.count p = s.copy.toList.countP p := by
  simp
example (s : Float32Array.Slice) (p : Float32 → Bool) :
    s.find? p = s.copy.toList.find? p ∧ s.findRev? p = s.copy.toList.reverse.find? p := by
  simp
example (s : Float32Array.Slice) (f : Nat → Float32 → Nat) :
    s.foldl f 0 = s.copy.toList.foldl f 0 := by
  simp
example (s : Float32Array.Slice) (f : Float32 → StateM Nat PUnit) :
    forM s f = forM s.copy.toList f := by
  simp
example (s : Float32Array.Slice) (x : Float32) : x ∈ s ↔ x ∈ s.copy.toList := by
  simp
example (s t : Float32Array.Slice) : (s == t) = (s.copy == t.copy) := by
  simp
example (a : Float32Array) : a.iter.toFloat32Array = a := by
  simp
example (s : Float32Array.Slice) : s.iter.toFloat32Array = s.copy := by
  simp
example : (∅ : Float32Array.Slice).size = 0 := by
  simp
example (s : Float32Array.Slice) (i : Nat) (v : Float32) (h : i < s.size) :
    (s.set i v h).copy = s.copy.set i v (by simpa using h) := by
  simp
example (s : Float32Array.Slice) (i j : Nat) (hi : i < s.size) (hj : j < s.size) :
    (s.swap i j hi hj)[i]'(by simpa using hi) = s[j] := by
  simp; intro h; subst h; rfl
example (s : Float32Array.Slice) : s.reverse.copy.toList = s.copy.toList.reverse := by
  simp
example (s : Float32Array.Slice) (f : Float32 → Float32) : (s.modify 0 f).size = s.size := by
  simp
example (s : Float32Array.Slice) (f : (k : USize) → k.toNat < s.size → Float32 → Nat → Float32 × Nat) :
    (s.foldlInPlace 0 f).1.size = s.size := by
  simp
example (s : Float32Array.Slice) (f : (k : USize) → k.toNat < s.size → Float32 → Nat → Float32 × Nat) :
    (s.foldrInPlace 0 f).1.size = s.size := by
  simp
example (s : Float32Array.Slice) (f : (k : USize) → k.toNat < s.size → Float32 → Nat → Float32 × Nat) :
    (s.foldrInPlaceThen 0 f fun t _ => t).size = s.size := by
  simp
