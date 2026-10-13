/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import ScalarArray.Int16
import ScalarArrayTest.Util
meta import ScalarArray.Int16
meta import ScalarArrayTest.Util

open ScalarArray ScalarArrayTest

/-- A test value at the edge of the element type's range. -/
private abbrev big : Int16 := -32768

/-- The size of an element in bytes. -/
private abbrev elemSize : UInt32 := 2

/-! Construction and conversion -/

#guard (Int16Array.mk #[1, 2, 3, big]).data == #[1, 2, 3, big]
#guard (Int16Array.mk #[1, 2, 3, big]).toList == [1, 2, 3, big]
#guard (Int16Array.mk #[]).data == #[]
#guard Int16Array.empty.data == #[]
#guard (∅ : Int16Array).data == #[]
#guard (default : Int16Array).data == #[]
#guard (Int16Array.emptyWithCapacity 100).data == #[]
#guard (Int16Array.mk (Array.range 1000 |>.map Nat.toInt16)).data ==
  (Array.range 1000).map Nat.toInt16

/-! Size -/

#guard (Int16Array.mk #[1, 2, 3, big]).size == 4
#guard (Int16Array.mk #[1, 2, 3, big]).usize == 4
#guard Int16Array.empty.size == 0
#guard (Int16Array.emptyWithCapacity 100).size == 0

/-! Reading -/

#guard (Int16Array.mk #[1, 2, 3, big])[0] == 1
#guard (Int16Array.mk #[1, 2, 3, big])[3] == big
#guard (Int16Array.mk #[1, 2, 3, big])[(2 : USize)] == 3
#guard (Int16Array.mk #[1, 2, 3, big]).get! 1 == 2
#guard (Int16Array.mk #[1, 2, 3, big]).getD 2 7 == 3
#guard (Int16Array.mk #[1, 2, 3, big]).getD 4 7 == 7
#guard (Int16Array.mk #[1, 2, 3, big])[4]? == none
#guard (Int16Array.mk #[1, 2, 3, big])[1]? == some 2

/-! Writing -/

#guard ((Int16Array.mk #[1, 2, 3]).set 1 42 (by decide)).data == #[1, 42, 3]
#guard ((Int16Array.mk #[1, 2, 3]).uset 2 42 (by simp)).data == #[1, 2, 42]
#guard ((Int16Array.mk #[1, 2, 3]).set! 0 big).data == #[big, 2, 3]

-- Writing to a shared array must leave the original unchanged. The result is checked first so
-- that it is computed while the original is still live.
#guard
  let a := Int16Array.mk #[1, 2, 3]
  let b := a.set! 1 42
  b.data == #[1, 42, 3] && a.data == #[1, 2, 3]

-- Repeated writes to an exclusive array.
#guard Id.run do
  let mut a := Int16Array.mk (Array.replicate 1000 0)
  for i in [0:1000] do
    a := a.set! i (i * 3).toInt16
  return a.data == (Array.range 1000).map fun i => (i * 3).toInt16

/-! Pushing -/

#guard (Int16Array.empty.push 5 |>.push 6).data == #[5, 6]
#guard ((Int16Array.emptyWithCapacity 1).push 5 |>.push 6 |>.push 7).data == #[5, 6, 7]
#guard ((Int16Array.mk #[1, 2]).push 3).data == #[1, 2, 3]

-- Pushing past the capacity many times.
#guard Id.run do
  let mut a := Int16Array.empty
  for i in [0:10000] do
    a := a.push i.toInt16
  return a.size == 10000 && a.data == (Array.range 10000).map Nat.toInt16

-- Pushing to a shared array must leave the original unchanged. The results are checked first so
-- that they are computed while the original is still live.
#guard
  let a := (Int16Array.emptyWithCapacity 10).push 1
  let b := a.push 2
  let c := a.push 3
  c.data == #[1, 3] && b.data == #[1, 2] && a.data == #[1]

/-! Printing -/

#guard toString (Int16Array.mk #[1, 2]) == "Int16Array.mk " ++ toString #[(1 : Int16), 2]
#guard reprStr (Int16Array.mk #[1, 2]) == "Int16Array.mk " ++ reprStr #[(1 : Int16), 2]

/-! Every index, through both `Nat` and `USize` indices -/

#guard
  let a := Int16Array.mk ((Array.range 300).map Nat.toInt16)
  (List.range 300).all fun i =>
    a[i]! == i.toInt16 && a.getD i 0 == i.toInt16 && a.get! i == i.toInt16 &&
      (if h : i.toUSize.toNat < a.size then a[i.toUSize] == i.toInt16 else false)

/-! Writes don't touch neighbouring elements -/

#guard ((Int16Array.mk #[0, 0, 0]).set! 1 big).data == #[0, big, 0]
#guard ((Int16Array.mk #[big, big, big]).set! 1 0).data == #[big, 0, big]
#guard ((Int16Array.mk #[0, 0, 0]).push big |>.push 0).data == #[0, 0, 0, big, 0]

/-! Indices beyond 16 bits, and huge `Nat` indices -/

#guard
  let a := (Int16Array.mk (Array.replicate 100000 0)).set! 99999 big |>.set! 70000 1
  a.size == 100000 && a[99999]! == big && a[70000]! == 1 && a[99998]! == 0 &&
    a[70000 % 65536]! == 0 && a.data[99999]! == big && a.data[70000]! == 1 &&
    (if h : (70000 : USize).toNat < a.size then a[(70000 : USize)] == 1 else false)

#guard (Int16Array.mk #[1, 2, 3])[2 ^ 70]? == none
#guard (Int16Array.mk #[1, 2, 3]).getD (2 ^ 70) 7 == 7

/-! Pushing onto a shared array that is at full capacity -/

#guard
  let a := Int16Array.mk #[1]
  let b := a.push 2
  b.data == #[1, 2] && a.data == #[1]

#guard
  let a := Int16Array.mk #[]
  let b := a.push 2
  b.data == #[2] && a.data == #[]

/-! Conversions don't alias -/

#guard
  let a := #[(1 : Int16), 2, 3]
  let b := (Int16Array.mk a).set! 0 big
  b.data == #[big, 2, 3] && a == #[1, 2, 3]

#guard
  let a := Int16Array.mk #[1, 2, 3]
  let d := a.data.set! 0 big
  d == #[big, 2, 3] && a.data == #[1, 2, 3]

/-! Runtime representation -/

#guard rawElemSize (Int16Array.mk #[1, 2, 3]) == elemSize
#guard rawElemSize (Int16Array.emptyWithCapacity 10) == elemSize
#guard rawElemSize (Int16Array.empty.push 1) == elemSize
#guard rawElemSize ((Int16Array.mk #[1]).push 2) == elemSize
#guard rawCapacity (Int16Array.emptyWithCapacity 100) ≥ 100
#guard rawCapacity (Int16Array.mk #[1, 2, 3]) ≥ 3
-- Growth is geometric, so pushing is amortized constant time.
#guard rawCapacity ((Int16Array.mk #[1, 2, 3, 4]).push 5) ≥ 8


/-! Appending -/

#guard (Int16Array.mk #[1, 2] ++ Int16Array.mk #[3, big]).data == #[1, 2, 3, big]
#guard ((Int16Array.mk #[1, 2]).append (Int16Array.mk #[3])).data == #[1, 2, 3]
#guard (Int16Array.mk #[1, 2] ++ Int16Array.empty).data == #[1, 2]
#guard (Int16Array.empty ++ Int16Array.mk #[1, 2]).data == #[1, 2]
#guard (Int16Array.empty ++ Int16Array.empty).data == #[]
#guard (Int16Array.mk #[0, 0] ++ Int16Array.mk #[big] ++ Int16Array.mk #[0]).data ==
  #[0, 0, big, 0]

-- Appending an array to itself, with and without room.
#guard
  let a := Int16Array.mk #[1, 2, 3]
  (a ++ a).data == #[1, 2, 3, 1, 2, 3]

#guard
  let a := (Int16Array.emptyWithCapacity 10).push 1 |>.push 2
  (a ++ a).data == #[1, 2, 1, 2]

-- Appending to a shared array must leave the original unchanged, with and without room. The
-- results are checked first so that they are computed while the original is still live.
#guard
  let a := (Int16Array.emptyWithCapacity 10).push 1
  let b := a ++ Int16Array.mk #[2, 3]
  let c := a ++ Int16Array.mk #[4]
  c.data == #[1, 4] && b.data == #[1, 2, 3] && a.data == #[1]

#guard
  let a := Int16Array.mk #[1]
  let b := a ++ Int16Array.mk #[2, 3]
  b.data == #[1, 2, 3] && a.data == #[1]

-- The right operand is never modified.
#guard
  let b := Int16Array.mk #[2, 3]
  let c := Int16Array.mk #[1] ++ b
  c.data == #[1, 2, 3] && b.data == #[2, 3]

-- Many appends to an exclusive array.
#guard Id.run do
  let mut a := Int16Array.empty
  let mut r : Array Int16 := #[]
  for i in [0:1000] do
    a := a ++ Int16Array.mk #[i.toInt16, (i * 7).toInt16, big]
    r := r ++ #[i.toInt16, (i * 7).toInt16, big]
  return a.data == r

-- Large arrays on both sides.
#guard
  let xs := (Array.range 50000).map Nat.toInt16
  let ys := (Array.range 50000).map fun i => (i * 3).toInt16
  (Int16Array.mk xs ++ Int16Array.mk ys).data == xs ++ ys

-- An exclusive array with room is appended to in place, and growth is geometric.
-- The array is built from a parameter so that it isn't extracted as a shared closed term.
@[noinline] def Int16Array.appendsInPlace (x : Int16) : Bool :=
  let a := (Int16Array.emptyWithCapacity 10).push x
  let p := rawAddr a
  let a := a ++ Int16Array.mk #[2, 3]
  rawAddr a == p && a.data == #[x, 2, 3]

@[noinline] def Int16Array.appendsToCopyWhenShared (x : Int16) : Bool :=
  let a := (Int16Array.emptyWithCapacity 10).push x
  let p := rawAddr a
  let b := a ++ Int16Array.mk #[2, 3]
  rawAddr b != p && b.data == #[x, 2, 3] && a.data == #[x]

#guard Int16Array.appendsInPlace 1
#guard Int16Array.appendsToCopyWhenShared 1

#guard rawCapacity ((Int16Array.emptyWithCapacity 10).push 1 ++ Int16Array.mk #[2, 3]) ≥ 10
#guard rawCapacity (Int16Array.mk #[1, 2, 3, 4] ++ Int16Array.mk #[5]) ≥ 8
#guard rawCapacity (Int16Array.mk #[1] ++ Int16Array.mk (Array.replicate 10 0)) ≥ 11
#guard rawElemSize (Int16Array.mk #[1] ++ Int16Array.mk #[2]) == elemSize

/-! Equality -/

#guard Int16Array.mk #[1, 2, big] == Int16Array.mk #[1, 2, big]
#guard Int16Array.mk #[1, 2, big] != Int16Array.mk #[1, 2, 0]
#guard Int16Array.mk #[1, 2] != Int16Array.mk #[1, 2, 0]
#guard Int16Array.mk #[1, 2, 0] != Int16Array.mk #[1, 2]
#guard Int16Array.empty == Int16Array.emptyWithCapacity 10
#guard (Int16Array.mk #[1, 2] ++ Int16Array.mk #[big]) == Int16Array.mk #[1, 2, big]
-- Capacity and leftover memory past the size don't matter.
#guard (Int16Array.emptyWithCapacity 100).push 1 == Int16Array.mk #[1]
#guard (Int16Array.mk #[1, 2, 3]).pop == Int16Array.mk #[1, 2]
#guard (Int16Array.mk (Array.replicate 100000 0)).set! 99999 big !=
  Int16Array.mk (Array.replicate 100000 0)

/-! Decidable equality and hashing -/

#guard decide (Int16Array.mk #[1, 2, big] = Int16Array.mk #[1, 2, big])
#guard !decide (Int16Array.mk #[1, 2, big] = Int16Array.mk #[1, 2, 0])
#guard hash (Int16Array.mk #[1, 2, big]) == hash #[(1 : Int16), 2, big]
#guard hash (Int16Array.empty) == hash (#[] : Array Int16)
#guard hash ((Int16Array.emptyWithCapacity 100).push 1) == hash (Int16Array.mk #[1])

/-! Iteration -/

#guard (Int16Array.mk #[1, 2, big]).foldl (fun acc x => x :: acc) [] == [big, 2, 1]
#guard (Int16Array.mk #[1, 2, big]).foldr (fun x acc => x :: acc) [] == [1, 2, big]
#guard Int16Array.empty.foldl (fun acc x => x :: acc) [] == []
#guard Int16Array.empty.foldr (fun x acc => x :: acc) [] == []
#guard (Int16Array.mk #[1, 2, big]).foldlM (m := Option)
  (fun acc x => if x == 2 then none else some (x :: acc)) [] == none
#guard (Int16Array.mk #[1, big]).foldrM (m := Option) (fun x acc => some (x :: acc)) [] ==
  some [1, big]

#guard Id.run do
  let mut r : List Int16 := []
  for x in Int16Array.mk #[1, 2, big] do
    r := x :: r
  return r == [big, 2, 1]

#guard Id.run do
  let mut r : List Int16 := []
  for x in Int16Array.mk #[1, 2, 3, 4] do
    if x == 3 then break
    r := x :: r
  return r == [2, 1]

#guard
  let r : StateM (List Int16) Unit := (Int16Array.mk #[1, 2, big]).forM fun x => modify (x :: ·)
  (r.run []).2 == [big, 2, 1]

#guard
  let xs := (Array.range 100000).map Nat.toInt16
  let f := fun (acc : List Int16) x => if x == 0 then x :: acc else acc
  (Int16Array.mk xs).foldl f [] == xs.foldl f []

#guard (Int16Array.mk #[1, 2, big]).any (· == big)
#guard !(Int16Array.mk #[1, 2, 3]).any (· == big)
#guard (Int16Array.mk #[1, 2, 3]).all (· != big)
#guard !(Int16Array.mk #[1, big, 3]).all (· != big)
#guard !Int16Array.empty.any (fun _ => true) && Int16Array.empty.all (fun _ => false)
#guard (Int16Array.mk #[1, 2, big]).contains big
#guard !(Int16Array.mk #[1, 2, 3]).contains big
#guard (Int16Array.mk (Array.replicate 100000 0) |>.set! 99999 big).contains big

/-! Removing elements -/

#guard Int16Array.empty.isEmpty && !(Int16Array.mk #[1]).isEmpty
#guard (Int16Array.mk #[1]).pop.isEmpty
#guard (Int16Array.mk #[1, 2, big]).pop.data == #[1, 2]
#guard Int16Array.empty.pop.data == #[]
#guard ((Int16Array.mk #[1, 2, 3]).pop.push big).data == #[1, 2, big]
#guard (Int16Array.mk #[1, 2, big]).back? == some big
#guard Int16Array.empty.back? == none
#guard (Int16Array.mk #[1, 2, big]).back! == big
#guard (Int16Array.mk #[1, 2, big]).back (by decide) == big

-- Popping from a shared array must leave the original unchanged.
#guard
  let a := Int16Array.mk #[1, 2, 3]
  let b := a.pop
  b.data == #[1, 2] && a.data == #[1, 2, 3]

-- The array is built from a parameter so that it isn't extracted as a shared closed term.
@[noinline] def Int16Array.popsInPlace (x : Int16) : Bool :=
  let a := (Int16Array.mk #[x]).push x
  let p := rawAddr a
  let a := a.pop
  rawAddr a == p && a.data == #[x]

#guard Int16Array.popsInPlace 1

#guard (Int16Array.mk #[1, 0, big, 0, 0]).popWhile (· == 0) == Int16Array.mk #[1, 0, big]
#guard (Int16Array.mk #[1, 0, big]).popWhile (· == 0) == Int16Array.mk #[1, 0, big]
#guard (Int16Array.mk #[0, 0]).popWhile (· == 0) == Int16Array.empty
#guard Int16Array.empty.popWhile (· == 0) == Int16Array.empty

-- Popping several elements from an exclusive array.
@[noinline] def Int16Array.popsWhileInPlace (x : Int16) : Bool :=
  let a := (Int16Array.mk #[x]).push 0 |>.push 0
  let p := rawAddr a
  let a := a.popWhile (· == 0)
  rawAddr a == p && a.data == #[x]

#guard Int16Array.popsWhileInPlace 1

example (p : Int16 → Bool) (a : Int16Array) : (a.popWhile p).data = a.data.popWhile p := by simp

#guard ((Int16Array.mk #[1, 2, 3, big]).extract 1 3).data == #[2, 3]
#guard ((Int16Array.mk #[1, 2, 3, big]).extract 2 100).data == #[3, big]
#guard ((Int16Array.mk #[1, 2, 3]).extract 0 3).data == #[1, 2, 3]
#guard ((Int16Array.mk #[1, 2, 3]).extract 2 1).data == #[]
#guard ((Int16Array.mk #[1, 2, 3]).extract 5 9).data == #[]
#guard ((Int16Array.mk #[1, 2, 3]).extract (2 ^ 70) (2 ^ 71)).data == #[]
#guard ((Int16Array.mk #[1, 2, 3]).extract 1 (2 ^ 70)).data == #[2, 3]
#guard
  let xs := (Array.range 100000).map Nat.toInt16
  ((Int16Array.mk xs).extract 70000 70010).data == xs.extract 70000 70010
#guard rawElemSize ((Int16Array.mk #[1, 2, 3]).extract 1 2) == elemSize

-- The extracted array is independent of the original.
#guard
  let a := Int16Array.mk #[1, 2, 3]
  let b := (a.extract 0 2).set! 0 big
  b.data == #[big, 2] && a.data == #[1, 2, 3]

/-! Building arrays -/

#guard (Int16Array.replicate 3 big).data == #[big, big, big]
#guard (Int16Array.replicate 0 1).data == #[]
#guard (Int16Array.replicate 100000 big).data == Array.replicate 100000 big
#guard (Int16Array.ofFn (n := 4) fun i => i.val.toInt16).data == #[0, 1, 2, 3]
#guard (Int16Array.ofFn (n := 0) fun i => i.val.toInt16).data == #[]
#guard rawElemSize (Int16Array.replicate 2 1) == elemSize
#guard rawElemSize (Int16Array.ofFn (n := 2) fun _ => 1) == elemSize

/-! Lemmas -/

example (a : Int16Array) (v : Int16) : (a.push v).pop = a := by simp [Int16Array.ext_iff]
example : (Int16Array.replicate 3 big)[1] = big := by simp
example (a b : Int16Array) (h : 0 < a.size) : (a ++ b)[0]'(by simp; omega) = a[0] := by simp [h]
example (a : Int16Array) (i : Nat) (v : Int16) (h : i < a.size) :
    (a.set i v h)[i]'(by simpa) = v := by simp
example (a : Int16Array) : a.extract 0 a.size = a := by simp
example (a : Int16Array) (v : Int16) : (a.push v).pop = a :=
  Int16Array.ext_getElem (by simp) (by simp_all)

/-! Default bounds proofs -/

#guard (Int16Array.mk #[1, 2, big]).get 2 == big
#guard (Int16Array.mk #[1, 2, big]).uget 2 == big
#guard ((Int16Array.mk #[1, 2, 3]).set 1 big).data == #[1, big, 3]
#guard ((Int16Array.mk #[1, 2, 3]).uset 1 big).data == #[1, big, 3]

/-! `set!` leaves the array unchanged when the index is out of bounds, like `ByteArray.set!`. -/

#guard ((Int16Array.mk #[1, 2, 3]).set! 3 big).data == #[1, 2, 3]
#guard ((Int16Array.mk #[1, 2, 3]).set! (2 ^ 70) big).data == #[1, 2, 3]

/-! Folds over part of an array -/

#guard (Int16Array.mk #[1, 2, 3, big]).foldl (fun acc x => x :: acc) [] 1 3 == [3, 2]
#guard (Int16Array.mk #[1, 2, 3, big]).foldl (fun acc x => x :: acc) [] 2 == [big, 3]
#guard (Int16Array.mk #[1, 2, 3, big]).foldl (fun acc x => x :: acc) [] 1 100 == [big, 3, 2]
#guard (Int16Array.mk #[1, 2, 3, big]).foldl (fun acc x => x :: acc) [] 3 1 == []
#guard (Int16Array.mk #[1, 2, 3, big]).foldl (fun acc x => x :: acc) [] 9 12 == []
#guard (Int16Array.mk #[1, 2, 3]).foldlM (m := Option)
  (fun acc x => if x == 1 then none else some (x :: acc)) [] 1 == some [3, 2]

/-! Copying slices -/

#guard
  let src := Int16Array.mk #[10, 11, 12, big]
  let dest := Int16Array.mk #[1, 2, 3, 4, 5]
  (src.copySlice 1 dest 2 2).data == #[1, 2, 11, 12, 5] &&
  (src.copySlice 1 dest 4 3).data == #[1, 2, 3, 4, 11, 12, big] &&
  (src.copySlice 0 dest 9 2).data == #[1, 2, 3, 4, 5, 10, 11] &&
  (src.copySlice 9 dest 1 2).data == #[1, 2, 3, 4, 5] &&
  (src.copySlice 2 dest 0 10).data == #[12, big, 3, 4, 5] &&
  (src.copySlice 0 dest 0 0).data == #[1, 2, 3, 4, 5] &&
  (src.copySlice 0 Int16Array.empty 0 4).data == #[10, 11, 12, big] &&
  dest.data == #[1, 2, 3, 4, 5] && src.data == #[10, 11, 12, big]

-- Copying from an array into itself.
#guard
  let a := Int16Array.mk #[1, 2, 3, big]
  (a.copySlice 0 a 2 4).data == #[1, 2, 1, 2, 3, big]

#guard
  let xs := (Array.range 100000).map Nat.toInt16
  let a := Int16Array.mk xs
  (a.copySlice 70000 (Int16Array.replicate 10 0) 5 10).data ==
    Array.replicate 5 0 ++ xs.extract 70000 70010

#guard rawElemSize ((Int16Array.mk #[1]).copySlice 0 Int16Array.empty 0 1) == elemSize

@[noinline] def Int16Array.copiesSliceInPlace (x : Int16) : Bool :=
  let dest := (Int16Array.emptyWithCapacity 10).push x |>.push x |>.push x
  let p := rawAddr dest
  let dest := (Int16Array.mk #[big, big]).copySlice 0 dest 1 2
  rawAddr dest == p && dest.data == #[x, big, big]

@[noinline] def Int16Array.copySliceGrowth (x : Int16) : Bool :=
  let dest := (Int16Array.mk #[x, x, x, x])
  rawCapacity ((Int16Array.mk #[x]).copySlice 0 dest 4 1 (exact := false)) ≥ 8 &&
    rawCapacity ((Int16Array.mk #[x]).copySlice 0 dest 4 1) == 5

#guard Int16Array.copiesSliceInPlace 1
#guard Int16Array.copySliceGrowth 1

/-! Linearity markers -/

#guard ((Int16Array.mk #[1, 2]).markLinear.push big).data == #[1, 2, big]
#guard ((Int16Array.mk #[1]).propagateMark (Int16Array.mk #[2, big])).data == #[2, big]

/-! Search -/

#guard (Int16Array.mk #[1, 2, big, 2]).findIdx? (· == 2) == some 1
#guard (Int16Array.mk #[1, 2, big, 2]).findIdx? (· == 2) 2 == some 3
#guard (Int16Array.mk #[1, 2, big, 2]).findIdx? (· == 3) == none
#guard (Int16Array.mk #[1, 2, big, 2]).findIdx? (· == 1) 9 == none
#guard ((Int16Array.mk #[1, 2, big, 2]).findFinIdx? (· == big)).map (·.val) == some 2

/-! Lists -/

#guard (Int16Array.ofList [1, 2, big]).data == #[1, 2, big]
#guard (Int16Array.ofList []).data == #[]
#guard [1, 2, big].toInt16Array == Int16Array.mk #[1, 2, big]
#guard (Int16Array.ofList ((List.range 100000).map Nat.toInt16)).data ==
  (Array.range 100000).map Nat.toInt16
#guard rawElemSize (Int16Array.ofList [1, 2]) == elemSize

/-! More lemmas -/

example (a b c : Int16Array) : a ++ b ++ c = a ++ (b ++ c) := Int16Array.append_assoc ..
example (a : Int16Array) : a ++ ∅ = a := by simp
example (a b : Int16Array) : (a ++ b).extract 0 a.size = a := by simp
example (a : Int16Array) (i : Nat) (v : Int16) : (a.set! i v).size = a.size := by simp
example (l : List Int16) : (Int16Array.ofList l).toList = l := by simp
example (a : Int16Array) : Int16Array.ofList a.toList = a := by simp

/-! Slices -/

#guard
  let a := Int16Array.mk #[1, 2, 3, big]
  let s := a[1...3]
  s.size == 2 && s[0]! == 2 && s[1]! == 3 && s.getD 2 7 == 7 && s.copy == Int16Array.mk #[2, 3] &&
    s.toList == [2, 3] && s.toArray == #[2, 3]

#guard
  let a := Int16Array.mk #[1, 2, 3, big]
  a[1...=3].toList == [2, 3, big] && a[*...2].toList == [1, 2] && a[2...*].toList == [3, big] &&
    a[*...*].toList == [1, 2, 3, big] && a[0<...2].toList == [2] &&
    a[0<...=2].toList == [2, 3] && a[*...=1].toList == [1, 2] && a[1<...*].toList == [3, big]

-- Bounds are clamped.
#guard
  let a := Int16Array.mk #[1, 2, 3, big]
  a[2...100].toList == [3, big] && a[3...1].size == 0 && a[9...12].size == 0 &&
    (a.toSlice 1 (2 ^ 70)).toList == [2, 3, big]

-- Slices of slices.
#guard
  let s := (Int16Array.mk #[1, 2, 3, big])[1...4]
  s[1...2].toList == [3] && s[0...100].toList == [2, 3, big] && s[*...*].toList == [2, 3, big] &&
    s[2...*].toList == [big] && s[5...6].size == 0

#guard
  let s := (Int16Array.mk #[1, 2, 3, big])[1...4]
  s.popFront.toList == [3, big] && s.popFront.popFront.popFront.popFront.size == 0

#guard (∅ : Int16Array.Slice).size == 0 && (default : Int16Array.Slice).toList == []

-- An array coerces to the slice of all its elements.
#guard
  let s : Int16Array.Slice := Int16Array.mk #[1, 2, big]
  s.toList == [1, 2, big] && s.start == 0

-- A slice does not coerce back to an array, since that would copy.
example (s : Int16Array.Slice) : Int16Array := s.copy

#guard Id.run do
  let mut r : List Int16 := []
  for x in (Int16Array.mk #[1, 2, 3, big])[1...*] do
    r := x :: r
  return r == [big, 3, 2]

#guard (Int16Array.mk #[1, 2, 3, big])[1...*].foldl (fun acc x => x :: acc) [] == [big, 3, 2]

#guard
  let xs := (Array.range 100000).map Nat.toInt16
  let s := (Int16Array.mk xs)[70000...70010]
  s.toArray == xs.extract 70000 70010 && s.copy.data == xs.extract 70000 70010

#guard toString (Int16Array.mk #[1, 2, 3])[1...*] == toString (Int16Array.mk #[2, 3])

-- Taking a slice doesn't copy the array.
@[noinline] def Int16Array.slicesWithoutCopying (x : Int16) : Bool :=
  let a := Int16Array.mk #[x, 2, 3]
  let p := rawAddr a
  rawAddr a[1...2].array == p

#guard Int16Array.slicesWithoutCopying 1

example (s : Int16Array.Slice) : s.copy.size = s.size := by simp

/-! Slice API -/

#guard
  let s := (Int16Array.mk #[1, 2, 3, big, 2])[1...5]
  s.foldr (fun x acc => x :: acc) [] == [2, 3, big, 2] &&
    s.foldl (fun acc x => x :: acc) [] == [2, big, 3, 2] &&
    s.any (· == big) && !s.any (· == 1) && s.all (· != 1) && !s.all (· == 2) &&
    s.contains big && !s.contains 1 && s.count (· == 2) == 2 &&
    s.find? (· > 2) == some 3 && s.findRev? (· != big) == some 2 && s.findRev? (· == 1) == none

#guard (Int16Array.mk #[1, 2, 3])[1...1].foldr (fun x acc => x :: acc) [] == []
#guard (Int16Array.mk #[1, 2, 3])[3...*].find? (fun _ => true) == none

#guard
  let s := (Int16Array.mk #[1, 2, 3, big])[1...*]
  let r : StateM (List Int16) Unit := s.forRevM fun x => modify (x :: ·)
  (r.run []).2 == [2, 3, big]

#guard Id.run ((Int16Array.mk #[1, 2, big])[*...*].findSomeRevM?
  (fun x => pure (if x == 2 then some x else none))) == some 2

/-! The `Std.Iterators` API on arrays and slices -/

#guard (Int16Array.mk #[1, 2, 3]).iter.toList == [1, 2, 3]
#guard ((Int16Array.mk #[1, 2, 3]).iter.map (· * 2)).toInt16Array == Int16Array.mk #[2, 4, 6]
#guard ((Int16Array.mk #[1, 2, 3, big]).iter.filter (· != 2)).toInt16Array ==
  Int16Array.mk #[1, 3, big]
#guard ((Int16Array.mk #[1, 2, 3, big]).iter.take 2).toInt16Array == Int16Array.mk #[1, 2]
#guard ((Int16Array.mk #[1, 2, 3, big]).iter.drop 2).toInt16Array == Int16Array.mk #[3, big]
#guard (((Int16Array.mk #[1, 2, 3]).iter.zip (Int16Array.mk #[big, 5]).iter).map
  fun (x, y) => x + y).toInt16Array == Int16Array.mk #[1 + big, 7]
#guard ((Int16Array.mk #[1, 2, 3, big])[1...3].iter.map (· + 1)).toInt16Array ==
  Int16Array.mk #[3, 4]
#guard (Int16Array.mk #[1, 2, 3]).iter.length == 3
#guard Int16Array.empty.iter.toInt16Array == Int16Array.empty
#guard
  let xs := (Array.range 100000).map Nat.toInt16
  ((Int16Array.mk xs).iter.map (· + 1)).toInt16Array.data == xs.map (· + 1)
#guard rawElemSize ((Int16Array.mk #[1]).iter.toInt16Array) == elemSize
#guard (Int16Array.mk #[1, 2, 3]).iter.toInt16ArrayWithCapacity 100 ==
  Int16Array.mk #[1, 2, 3]
#guard rawCapacity ((Int16Array.mk #[1, 2, 3]).iter.toInt16ArrayWithCapacity 100) ≥ 100
