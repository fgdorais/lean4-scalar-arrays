/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import ScalarArray.UInt64
import ScalarArrayTest.Util
meta import ScalarArray.UInt64
meta import ScalarArrayTest.Util

open ScalarArray ScalarArrayTest

/-- A test value at the edge of the element type's range. -/
private abbrev big : UInt64 := 18446744073709551615

/-- The size of an element in bytes. -/
private abbrev elemSize : UInt32 := 8

/-! Construction and conversion -/

#guard (UInt64Array.mk #[1, 2, 3, big]).data == #[1, 2, 3, big]
#guard (UInt64Array.mk #[1, 2, 3, big]).toList == [1, 2, 3, big]
#guard (UInt64Array.mk #[]).data == #[]
#guard UInt64Array.empty.data == #[]
#guard (∅ : UInt64Array).data == #[]
#guard (default : UInt64Array).data == #[]
#guard (UInt64Array.emptyWithCapacity 100).data == #[]
#guard (UInt64Array.mk (Array.range 1000 |>.map Nat.toUInt64)).data ==
  (Array.range 1000).map Nat.toUInt64

/-! Size -/

#guard (UInt64Array.mk #[1, 2, 3, big]).size == 4
#guard (UInt64Array.mk #[1, 2, 3, big]).usize == 4
#guard UInt64Array.empty.size == 0
#guard (UInt64Array.emptyWithCapacity 100).size == 0

/-! Reading -/

#guard (UInt64Array.mk #[1, 2, 3, big])[0] == 1
#guard (UInt64Array.mk #[1, 2, 3, big])[3] == big
#guard (UInt64Array.mk #[1, 2, 3, big])[(2 : USize)] == 3
#guard (UInt64Array.mk #[1, 2, 3, big]).get! 1 == 2
#guard (UInt64Array.mk #[1, 2, 3, big]).getD 2 7 == 3
#guard (UInt64Array.mk #[1, 2, 3, big]).getD 4 7 == 7
#guard (UInt64Array.mk #[1, 2, 3, big])[4]? == none
#guard (UInt64Array.mk #[1, 2, 3, big])[1]? == some 2

/-! Writing -/

#guard ((UInt64Array.mk #[1, 2, 3]).set 1 42 (by decide)).data == #[1, 42, 3]
#guard ((UInt64Array.mk #[1, 2, 3]).uset 2 42 (by simp)).data == #[1, 2, 42]
#guard ((UInt64Array.mk #[1, 2, 3]).set! 0 big).data == #[big, 2, 3]

-- Writing to a shared array must leave the original unchanged. The result is checked first so
-- that it is computed while the original is still live.
#guard
  let a := UInt64Array.mk #[1, 2, 3]
  let b := a.set! 1 42
  b.data == #[1, 42, 3] && a.data == #[1, 2, 3]
#guard
  let a := UInt64Array.mk #[1, 2, 3]
  let b := a.uset 0 big (by simp [a])
  b.data == #[big, 2, 3] && a.data == #[1, 2, 3]
#guard
  let a := UInt64Array.mk #[1, 2, 3]
  let b := a.set 2 big (by simp [a])
  b.data == #[1, 2, big] && a.data == #[1, 2, 3]

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

#guard ((UInt64Array.mk #[0, 0, 0]).set! 1 big).data == #[0, big, 0]
#guard ((UInt64Array.mk #[big, big, big]).set! 1 0).data == #[big, 0, big]
#guard ((UInt64Array.mk #[0, 0, 0]).push big |>.push 0).data == #[0, 0, 0, big, 0]

/-! Indices beyond 16 bits, and huge `Nat` indices -/

#guard
  let a := (UInt64Array.mk (Array.replicate 100000 0)).set! 99999 big |>.set! 70000 1
  a.size == 100000 && a[99999]! == big && a[70000]! == 1 && a[99998]! == 0 &&
    a[70000 % 65536]! == 0 && a.data[99999]! == big && a.data[70000]! == 1 &&
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
  let b := (UInt64Array.mk a).set! 0 big
  b.data == #[big, 2, 3] && a == #[1, 2, 3]

#guard
  let a := UInt64Array.mk #[1, 2, 3]
  let d := a.data.set! 0 big
  d == #[big, 2, 3] && a.data == #[1, 2, 3]

/-! Runtime representation -/

#guard rawElemSize (UInt64Array.mk #[1, 2, 3]) == elemSize
#guard rawElemSize (UInt64Array.emptyWithCapacity 10) == elemSize
#guard rawElemSize (UInt64Array.empty.push 1) == elemSize
#guard rawElemSize ((UInt64Array.mk #[1]).push 2) == elemSize
#guard rawCapacity (UInt64Array.emptyWithCapacity 100) ≥ 100
#guard rawCapacity (UInt64Array.mk #[1, 2, 3]) ≥ 3
-- Growth is geometric, so pushing is amortized constant time.
#guard rawCapacity ((UInt64Array.mk #[1, 2, 3, 4]).push 5) ≥ 8


/-! Appending -/

#guard (UInt64Array.mk #[1, 2] ++ UInt64Array.mk #[3, big]).data == #[1, 2, 3, big]
#guard ((UInt64Array.mk #[1, 2]).append (UInt64Array.mk #[3])).data == #[1, 2, 3]
#guard (UInt64Array.mk #[1, 2] ++ UInt64Array.empty).data == #[1, 2]
#guard (UInt64Array.empty ++ UInt64Array.mk #[1, 2]).data == #[1, 2]
#guard (UInt64Array.empty ++ UInt64Array.empty).data == #[]
#guard (UInt64Array.mk #[0, 0] ++ UInt64Array.mk #[big] ++ UInt64Array.mk #[0]).data ==
  #[0, 0, big, 0]

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
    a := a ++ UInt64Array.mk #[i.toUInt64, (i * 7).toUInt64, big]
    r := r ++ #[i.toUInt64, (i * 7).toUInt64, big]
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
#guard rawElemSize (UInt64Array.mk #[1] ++ UInt64Array.mk #[2]) == elemSize

/-! Equality -/

#guard UInt64Array.mk #[1, 2, big] == UInt64Array.mk #[1, 2, big]
#guard UInt64Array.mk #[1, 2, big] != UInt64Array.mk #[1, 2, 0]
#guard UInt64Array.mk #[1, 2] != UInt64Array.mk #[1, 2, 0]
#guard UInt64Array.mk #[1, 2, 0] != UInt64Array.mk #[1, 2]
#guard UInt64Array.empty == UInt64Array.emptyWithCapacity 10
#guard (UInt64Array.mk #[1, 2] ++ UInt64Array.mk #[big]) == UInt64Array.mk #[1, 2, big]
-- Capacity and leftover memory past the size don't matter.
#guard (UInt64Array.emptyWithCapacity 100).push 1 == UInt64Array.mk #[1]
#guard (UInt64Array.mk #[1, 2, 3]).pop == UInt64Array.mk #[1, 2]
#guard (UInt64Array.mk (Array.replicate 100000 0)).set! 99999 big !=
  UInt64Array.mk (Array.replicate 100000 0)

/-! Decidable equality and hashing -/

#guard decide (UInt64Array.mk #[1, 2, big] = UInt64Array.mk #[1, 2, big])
#guard !decide (UInt64Array.mk #[1, 2, big] = UInt64Array.mk #[1, 2, 0])
#guard hash (UInt64Array.mk #[1, 2, big]) == hash #[(1 : UInt64), 2, big]
#guard hash (UInt64Array.empty) == hash (#[] : Array UInt64)
#guard hash ((UInt64Array.emptyWithCapacity 100).push 1) == hash (UInt64Array.mk #[1])

/-! Iteration -/

#guard (UInt64Array.mk #[1, 2, big]).foldl (fun acc x => x :: acc) [] == [big, 2, 1]
#guard (UInt64Array.mk #[1, 2, big]).foldr (fun x acc => x :: acc) [] == [1, 2, big]
#guard UInt64Array.empty.foldl (fun acc x => x :: acc) [] == []
#guard UInt64Array.empty.foldr (fun x acc => x :: acc) [] == []
#guard (UInt64Array.mk #[1, 2, big]).foldlM (m := Option)
  (fun acc x => if x == 2 then none else some (x :: acc)) [] == none
#guard (UInt64Array.mk #[1, big]).foldrM (m := Option) (fun x acc => some (x :: acc)) [] ==
  some [1, big]

#guard Id.run do
  let mut r : List UInt64 := []
  for x in UInt64Array.mk #[1, 2, big] do
    r := x :: r
  return r == [big, 2, 1]

#guard Id.run do
  let mut r : List UInt64 := []
  for x in UInt64Array.mk #[1, 2, 3, 4] do
    if x == 3 then break
    r := x :: r
  return r == [2, 1]

#guard
  let r : StateM (List UInt64) Unit := (UInt64Array.mk #[1, 2, big]).forM fun x => modify (x :: ·)
  (r.run []).2 == [big, 2, 1]

#guard
  let xs := (Array.range 100000).map Nat.toUInt64
  let f := fun (acc : List UInt64) x => if x == 0 then x :: acc else acc
  (UInt64Array.mk xs).foldl f [] == xs.foldl f []

#guard (UInt64Array.mk #[1, 2, big]).any (· == big)
#guard !(UInt64Array.mk #[1, 2, 3]).any (· == big)
#guard (UInt64Array.mk #[1, 2, 3]).all (· != big)
#guard !(UInt64Array.mk #[1, big, 3]).all (· != big)
#guard !UInt64Array.empty.any (fun _ => true) && UInt64Array.empty.all (fun _ => false)
#guard (UInt64Array.mk #[1, 2, big]).contains big
#guard !(UInt64Array.mk #[1, 2, 3]).contains big && !UInt64Array.empty.contains big

-- Early exits, and loops in a monad other than `Id`.
#guard (UInt64Array.mk #[1, 2, big]).foldrM (m := Option)
  (fun x acc => if x == 1 then none else some (x :: acc)) [] == none
#guard (UInt64Array.mk #[big, 2, 1]).foldrM (m := Option)
  (fun x acc => if x == big then none else some (x :: acc)) [] == none
#guard
  let r : StateM (List UInt64) Unit := do
    for x in UInt64Array.mk #[1, 2, big, 3] do
      if x == big then break
      modify (x :: ·)
  (r.run []).2 == [2, 1]
#guard
  let r : StateM (List UInt64) Unit :=
    (UInt64Array.mk #[1, 2, big]).foldrM (fun x _ => modify (x :: ·)) ⟨⟩
  (r.run []).2 == [1, 2, big]
#guard Id.run do
  let mut r : List UInt64 := []
  for x in UInt64Array.empty do
    r := x :: r
  return r == []
#guard !(UInt64Array.mk #[1, 2, 3]).contains big
#guard (UInt64Array.mk (Array.replicate 100000 0) |>.set! 99999 big).contains big

/-! Removing elements -/

#guard UInt64Array.empty.isEmpty && !(UInt64Array.mk #[1]).isEmpty
#guard (UInt64Array.mk #[1]).pop.isEmpty
#guard (UInt64Array.mk #[1, 2, big]).pop.data == #[1, 2]
#guard UInt64Array.empty.pop.data == #[]
#guard ((UInt64Array.mk #[1, 2, 3]).pop.push big).data == #[1, 2, big]
#guard (UInt64Array.mk #[1, 2, big]).back? == some big
#guard UInt64Array.empty.back? == none
#guard (UInt64Array.mk #[1, 2, big]).back! == big
#guard (UInt64Array.mk #[1, 2, big]).back (by decide) == big

-- Popping from a shared array must leave the original unchanged.
#guard
  let a := UInt64Array.mk #[1, 2, 3]
  let b := a.pop
  b.data == #[1, 2] && a.data == #[1, 2, 3]

-- The array is built from a parameter so that it isn't extracted as a shared closed term.
@[noinline] def UInt64Array.popsInPlace (x : UInt64) : Bool :=
  let a := (UInt64Array.mk #[x]).push x
  let p := rawAddr a
  let a := a.pop
  rawAddr a == p && a.data == #[x]

#guard UInt64Array.popsInPlace 1

#guard (UInt64Array.mk #[1, 0, big, 0, 0]).popWhile (· == 0) == UInt64Array.mk #[1, 0, big]
#guard (UInt64Array.mk #[1, 0, big]).popWhile (· == 0) == UInt64Array.mk #[1, 0, big]
#guard (UInt64Array.mk #[0, 0]).popWhile (· == 0) == UInt64Array.empty
#guard UInt64Array.empty.popWhile (· == 0) == UInt64Array.empty

-- Popping several elements from an exclusive array.
@[noinline] def UInt64Array.popsWhileInPlace (x : UInt64) : Bool :=
  let a := (UInt64Array.mk #[x]).push 0 |>.push 0
  let p := rawAddr a
  let a := a.popWhile (· == 0)
  rawAddr a == p && a.data == #[x]

#guard UInt64Array.popsWhileInPlace 1

example (p : UInt64 → Bool) (a : UInt64Array) : (a.popWhile p).data = a.data.popWhile p := by simp

#guard ((UInt64Array.mk #[1, 2, 3, big]).extract 1 3).data == #[2, 3]
#guard ((UInt64Array.mk #[1, 2, 3, big]).extract 2 100).data == #[3, big]
#guard ((UInt64Array.mk #[1, 2, 3]).extract 0 3).data == #[1, 2, 3]
#guard ((UInt64Array.mk #[1, 2, 3]).extract 2 1).data == #[]
#guard ((UInt64Array.mk #[1, 2, 3]).extract 5 9).data == #[]
#guard ((UInt64Array.mk #[1, 2, 3]).extract (2 ^ 70) (2 ^ 71)).data == #[]
#guard ((UInt64Array.mk #[1, 2, 3]).extract 1 (2 ^ 70)).data == #[2, 3]
#guard
  let xs := (Array.range 100000).map Nat.toUInt64
  ((UInt64Array.mk xs).extract 70000 70010).data == xs.extract 70000 70010
#guard rawElemSize ((UInt64Array.mk #[1, 2, 3]).extract 1 2) == elemSize

-- The extracted array is independent of the original.
#guard
  let a := UInt64Array.mk #[1, 2, 3]
  let b := (a.extract 0 2).set! 0 big
  b.data == #[big, 2] && a.data == #[1, 2, 3]

/-! Building arrays -/

#guard (UInt64Array.replicate 3 big).data == #[big, big, big]
#guard (UInt64Array.replicate 0 1).data == #[]
#guard (UInt64Array.replicate 100000 big).data == Array.replicate 100000 big
#guard (UInt64Array.ofFn (n := 4) fun i => i.val.toUInt64).data == #[0, 1, 2, 3]
#guard (UInt64Array.ofFn (n := 0) fun i => i.val.toUInt64).data == #[]
#guard rawElemSize (UInt64Array.replicate 2 1) == elemSize
#guard rawElemSize (UInt64Array.ofFn (n := 2) fun _ => 1) == elemSize

/-! Lemmas -/

example (a : UInt64Array) (v : UInt64) : (a.push v).pop = a := by simp [UInt64Array.ext_iff]
example : (UInt64Array.replicate 3 big)[1] = big := by simp
example (a b : UInt64Array) (h : 0 < a.size) : (a ++ b)[0]'(by simp; omega) = a[0] := by simp [h]
example (a : UInt64Array) (i : Nat) (v : UInt64) (h : i < a.size) :
    (a.set i v h)[i]'(by simpa) = v := by simp
example (a : UInt64Array) : a.extract 0 a.size = a := by simp
example (a : UInt64Array) (v : UInt64) : (a.push v).pop = a :=
  UInt64Array.ext_getElem (by simp) (by simp_all)

/-! Default bounds proofs -/

#guard (UInt64Array.mk #[1, 2, big]).get 2 == big
#guard (UInt64Array.mk #[1, 2, big]).uget 2 == big
#guard ((UInt64Array.mk #[1, 2, 3]).set 1 big).data == #[1, big, 3]
#guard ((UInt64Array.mk #[1, 2, 3]).uset 1 big).data == #[1, big, 3]

/-! `set!` leaves the array unchanged when the index is out of bounds, like `ByteArray.set!`. -/

#guard ((UInt64Array.mk #[1, 2, 3]).set! 3 big).data == #[1, 2, 3]
#guard ((UInt64Array.mk #[1, 2, 3]).set! (2 ^ 70) big).data == #[1, 2, 3]

/-! Folds over part of an array -/

#guard (UInt64Array.mk #[1, 2, 3, big]).foldl (fun acc x => x :: acc) [] 1 3 == [3, 2]
#guard (UInt64Array.mk #[1, 2, 3, big]).foldl (fun acc x => x :: acc) [] 2 == [big, 3]
#guard (UInt64Array.mk #[1, 2, 3, big]).foldl (fun acc x => x :: acc) [] 1 100 == [big, 3, 2]
#guard (UInt64Array.mk #[1, 2, 3, big]).foldl (fun acc x => x :: acc) [] 3 1 == []
#guard (UInt64Array.mk #[1, 2, 3, big]).foldl (fun acc x => x :: acc) [] 9 12 == []
#guard (UInt64Array.mk #[1, 2, 3]).foldlM (m := Option)
  (fun acc x => if x == 1 then none else some (x :: acc)) [] 1 == some [3, 2]

/-! Copying slices -/

#guard
  let src := UInt64Array.mk #[10, 11, 12, big]
  let dest := UInt64Array.mk #[1, 2, 3, 4, 5]
  (src.copySlice 1 dest 2 2).data == #[1, 2, 11, 12, 5] &&
  (src.copySlice 1 dest 4 3).data == #[1, 2, 3, 4, 11, 12, big] &&
  (src.copySlice 0 dest 9 2).data == #[1, 2, 3, 4, 5, 10, 11] &&
  (src.copySlice 9 dest 1 2).data == #[1, 2, 3, 4, 5] &&
  (src.copySlice 2 dest 0 10).data == #[12, big, 3, 4, 5] &&
  (src.copySlice 0 dest 0 0).data == #[1, 2, 3, 4, 5] &&
  (src.copySlice 0 UInt64Array.empty 0 4).data == #[10, 11, 12, big] &&
  dest.data == #[1, 2, 3, 4, 5] && src.data == #[10, 11, 12, big]

-- Copying from an array into itself.
#guard
  let a := UInt64Array.mk #[1, 2, 3, big]
  (a.copySlice 0 a 2 4).data == #[1, 2, 1, 2, 3, big]

#guard
  let xs := (Array.range 100000).map Nat.toUInt64
  let a := UInt64Array.mk xs
  (a.copySlice 70000 (UInt64Array.replicate 10 0) 5 10).data ==
    Array.replicate 5 0 ++ xs.extract 70000 70010

#guard rawElemSize ((UInt64Array.mk #[1]).copySlice 0 UInt64Array.empty 0 1) == elemSize

@[noinline] def UInt64Array.copiesSliceInPlace (x : UInt64) : Bool :=
  let dest := (UInt64Array.emptyWithCapacity 10).push x |>.push x |>.push x
  let p := rawAddr dest
  let dest := (UInt64Array.mk #[big, big]).copySlice 0 dest 1 2
  rawAddr dest == p && dest.data == #[x, big, big]

@[noinline] def UInt64Array.copySliceGrowth (x : UInt64) : Bool :=
  let dest := (UInt64Array.mk #[x, x, x, x])
  rawCapacity ((UInt64Array.mk #[x]).copySlice 0 dest 4 1 (exact := false)) ≥ 8 &&
    rawCapacity ((UInt64Array.mk #[x]).copySlice 0 dest 4 1) == 5

#guard UInt64Array.copiesSliceInPlace 1
#guard UInt64Array.copySliceGrowth 1

/-! Linearity markers -/

#guard ((UInt64Array.mk #[1, 2]).markLinear.push big).data == #[1, 2, big]
#guard ((UInt64Array.mk #[1]).propagateMark (UInt64Array.mk #[2, big])).data == #[2, big]

/-! Search -/

#guard (UInt64Array.mk #[1, 2, big, 2]).findIdx? (· == 2) == some 1
#guard (UInt64Array.mk #[1, 2, big, 2]).findIdx? (· == 2) 2 == some 3
#guard (UInt64Array.mk #[1, 2, big, 2]).findIdx? (· == 3) == none
#guard (UInt64Array.mk #[1, 2, big, 2]).findIdx? (· == 1) 9 == none
#guard ((UInt64Array.mk #[1, 2, big, 2]).findFinIdx? (· == big)).map (·.val) == some 2

/-! Lists -/

#guard (UInt64Array.ofList [1, 2, big]).data == #[1, 2, big]
#guard (UInt64Array.ofList []).data == #[]
#guard [1, 2, big].toUInt64Array == UInt64Array.mk #[1, 2, big]
#guard (UInt64Array.ofList ((List.range 100000).map Nat.toUInt64)).data ==
  (Array.range 100000).map Nat.toUInt64
#guard rawElemSize (UInt64Array.ofList [1, 2]) == elemSize

/-! More lemmas -/

example (a b c : UInt64Array) : a ++ b ++ c = a ++ (b ++ c) := UInt64Array.append_assoc ..
example (a : UInt64Array) : a ++ ∅ = a := by simp
example (a b : UInt64Array) : (a ++ b).extract 0 a.size = a := by simp
example (a : UInt64Array) (i : Nat) (v : UInt64) : (a.set! i v).size = a.size := by simp
example (l : List UInt64) : (UInt64Array.ofList l).toList = l := by simp
example (a : UInt64Array) : UInt64Array.ofList a.toList = a := by simp

/-! Slices -/

#guard
  let a := UInt64Array.mk #[1, 2, 3, big]
  let s := a[1...3]
  s.size == 2 && s[0]! == 2 && s[1]! == 3 && s.getD 2 7 == 7 && s.copy == UInt64Array.mk #[2, 3] &&
    s.toList == [2, 3] && s.toArray == #[2, 3]

#guard
  let a := UInt64Array.mk #[1, 2, 3, big]
  a[1...=3].toList == [2, 3, big] && a[*...2].toList == [1, 2] && a[2...*].toList == [3, big] &&
    a[*...*].toList == [1, 2, 3, big] && a[0<...2].toList == [2] &&
    a[0<...=2].toList == [2, 3] && a[*...=1].toList == [1, 2] && a[1<...*].toList == [3, big]

-- Bounds are clamped.
#guard
  let a := UInt64Array.mk #[1, 2, 3, big]
  a[2...100].toList == [3, big] && a[3...1].size == 0 && a[9...12].size == 0 &&
    (a.toSlice 1 (2 ^ 70)).toList == [2, 3, big]

-- Slices of slices.
#guard
  let s := (UInt64Array.mk #[1, 2, 3, big])[1...4]
  s[1...2].toList == [3] && s[0...100].toList == [2, 3, big] && s[*...*].toList == [2, 3, big] &&
    s[2...*].toList == [big] && s[5...6].size == 0

#guard
  let s := (UInt64Array.mk #[1, 2, 3, big])[1...4]
  s.popFront.toList == [3, big] && s.popFront.popFront.popFront.popFront.size == 0

#guard (∅ : UInt64Array.Slice).size == 0 && (default : UInt64Array.Slice).toList == []

-- An array coerces to the slice of all its elements.
#guard
  let s : UInt64Array.Slice := UInt64Array.mk #[1, 2, big]
  s.toList == [1, 2, big] && s.start == 0

-- A slice does not coerce back to an array, since that would copy.
example (s : UInt64Array.Slice) : UInt64Array := s.copy

#guard Id.run do
  let mut r : List UInt64 := []
  for x in (UInt64Array.mk #[1, 2, 3, big])[1...*] do
    r := x :: r
  return r == [big, 3, 2]

#guard (UInt64Array.mk #[1, 2, 3, big])[1...*].foldl (fun acc x => x :: acc) [] == [big, 3, 2]

#guard
  let xs := (Array.range 100000).map Nat.toUInt64
  let s := (UInt64Array.mk xs)[70000...70010]
  s.toArray == xs.extract 70000 70010 && s.copy.data == xs.extract 70000 70010

#guard toString (UInt64Array.mk #[1, 2, 3])[1...*] == toString (UInt64Array.mk #[2, 3])

-- Taking a slice doesn't copy the array.
@[noinline] def UInt64Array.slicesWithoutCopying (x : UInt64) : Bool :=
  let a := UInt64Array.mk #[x, 2, 3]
  let p := rawAddr a
  rawAddr a[1...2].array == p

#guard UInt64Array.slicesWithoutCopying 1

example (s : UInt64Array.Slice) : s.copy.size = s.size := by simp

/-! Slice API -/

#guard
  let s := (UInt64Array.mk #[1, 2, 3, big, 2])[1...5]
  s.foldr (fun x acc => x :: acc) [] == [2, 3, big, 2] &&
    s.foldl (fun acc x => x :: acc) [] == [2, big, 3, 2] &&
    s.any (· == big) && !s.any (· == 1) && s.all (· != 1) && !s.all (· == 2) &&
    s.contains big && !s.contains 1 && s.count (· == 2) == 2 &&
    s.find? (· > 2) == some 3 && s.findRev? (· != big) == some 2 && s.findRev? (· == 1) == none

#guard (UInt64Array.mk #[1, 2, 3])[1...1].foldr (fun x acc => x :: acc) [] == []
#guard (UInt64Array.mk #[1, 2, 3])[3...*].find? (fun _ => true) == none

#guard
  let s := (UInt64Array.mk #[1, 2, 3, big])[1...*]
  let r : StateM (List UInt64) Unit := s.forRevM fun x => modify (x :: ·)
  (r.run []).2 == [2, 3, big]

#guard Id.run ((UInt64Array.mk #[1, 2, big])[*...*].findSomeRevM?
  (fun x => pure (if x == 2 then some x else none))) == some 2

-- The loops over slices stay within the slice, both with `start > 0` and with `stop < size`.
#guard
  let s := (UInt64Array.mk #[big, 1, 2, 3, big])[1...4]
  s.foldr (fun x acc => x :: acc) [] == [1, 2, 3] &&
    s.foldl (fun acc x => x :: acc) [] == [3, 2, 1] && s.toList == [1, 2, 3] &&
    !s.any (· == big) && s.all (· != big) && !s.contains big && s.count (· != big) == 3 &&
    s.find? (· == big) == none && s.findRev? (· == big) == none &&
    s.find? (· != 1) == some 2 && s.findRev? (· != 3) == some 2

#guard Id.run do
  let mut r : List UInt64 := []
  for x in (UInt64Array.mk #[big, 1, 2, 3, big])[1...4] do
    r := x :: r
  return r == [3, 2, 1]

-- Early exits.
#guard Id.run do
  let mut r : List UInt64 := []
  for x in (UInt64Array.mk #[big, 1, 2, 3, big])[1...5] do
    if x == 3 then break
    r := x :: r
  return r == [2, 1]

#guard
  let s := (UInt64Array.mk #[1, 2, big, 3, big])[1...5]
  s.any (· == big) && !s.all (· != big) && s.find? (· == big) == some big &&
    s.find? (· != 2) == some big && s.findRev? (· == big) == some big &&
    s.findRev? (· != big) == some 3

-- Empty slices.
#guard
  let s := (UInt64Array.mk #[1, 2, 3])[1...1]
  s.foldl (fun acc x => x :: acc) [] == [] && s.toList == [] && !s.any (fun _ => true) &&
    s.all (fun _ => false) && s.count (fun _ => true) == 0 && s.find? (fun _ => true) == none &&
    s.findRev? (fun _ => true) == none && Id.run do
      let mut r : List UInt64 := []
      for x in s do
        r := x :: r
      return r == []
#guard
  let s := (∅ : UInt64Array.Slice)
  s.foldr (fun x acc => x :: acc) [] == [] && s.foldl (fun acc x => x :: acc) [] == [] &&
    !s.any (fun _ => true)

-- Loops in a monad other than `Id`.
#guard
  let r : StateM (List UInt64) Unit := do
    for x in (UInt64Array.mk #[big, 1, 2, 3, big])[1...5] do
      if x == 3 then break
      modify (x :: ·)
  (r.run []).2 == [2, 1]
#guard
  let s := (UInt64Array.mk #[big, 1, 2, 3, big])[1...4]
  let r : StateM (List UInt64) Unit := s.foldrM (fun x _ => modify (x :: ·)) ⟨⟩
  (r.run []).2 == [1, 2, 3]
#guard
  let s := (UInt64Array.mk #[big, 1, 2, 3, big])[1...4]
  let r : StateM (List UInt64) Unit := s.foldlM (fun _ x => modify (x :: ·)) ⟨⟩
  (r.run []).2 == [3, 2, 1]
#guard (UInt64Array.mk #[big, 1, 2, 3, big])[1...4].foldlM (m := Option)
  (fun acc x => if x == 2 then none else some (x :: acc)) [] == none
#guard (UInt64Array.mk #[big, 1, 2, 3, big])[1...4].foldrM (m := Option)
  (fun x acc => if x == 2 then none else some (x :: acc)) [] == none
#guard (UInt64Array.mk #[big, 1, 2, 3, big])[1...4].foldlM (m := Option)
  (fun acc x => some (x :: acc)) [] == some [3, 2, 1]
#guard (UInt64Array.mk #[big, 1, 2, 3, big])[1...4].findSomeRevM? (m := Option)
  (fun x => if x == 3 then some none else some (some x)) == some (some 2)
#guard
  let xs := (Array.range 100000).map Nat.toUInt64
  let s := (UInt64Array.mk xs)[100...99900]
  let f := fun (acc : List UInt64) x => if x == 0 then x :: acc else acc
  s.foldl f [] == (xs.extract 100 99900).foldl f [] &&
    s.foldr (fun x acc => f acc x) [] == (xs.extract 100 99900).foldr (fun x acc => f acc x) []

/-! The `Std.Iterators` API on arrays and slices -/

#guard (UInt64Array.mk #[1, 2, 3]).iter.toList == [1, 2, 3]
#guard ((UInt64Array.mk #[1, 2, 3]).iter.map (· * 2)).toUInt64Array == UInt64Array.mk #[2, 4, 6]
#guard ((UInt64Array.mk #[1, 2, 3, big]).iter.filter (· != 2)).toUInt64Array ==
  UInt64Array.mk #[1, 3, big]
#guard ((UInt64Array.mk #[1, 2, 3, big]).iter.take 2).toUInt64Array == UInt64Array.mk #[1, 2]
#guard ((UInt64Array.mk #[1, 2, 3, big]).iter.drop 2).toUInt64Array == UInt64Array.mk #[3, big]
#guard (((UInt64Array.mk #[1, 2, 3]).iter.zip (UInt64Array.mk #[big, 5]).iter).map
  fun (x, y) => x + y).toUInt64Array == UInt64Array.mk #[1 + big, 7]
#guard ((UInt64Array.mk #[1, 2, 3, big])[1...3].iter.map (· + 1)).toUInt64Array ==
  UInt64Array.mk #[3, 4]
#guard (UInt64Array.mk #[1, 2, 3]).iter.length == 3
#guard UInt64Array.empty.iter.toUInt64Array == UInt64Array.empty
#guard
  let xs := (Array.range 100000).map Nat.toUInt64
  ((UInt64Array.mk xs).iter.map (· + 1)).toUInt64Array.data == xs.map (· + 1)
#guard rawElemSize ((UInt64Array.mk #[1]).iter.toUInt64Array) == elemSize
#guard (UInt64Array.mk #[1, 2, 3]).iter.toUInt64ArrayWithCapacity 100 ==
  UInt64Array.mk #[1, 2, 3]
#guard rawCapacity ((UInt64Array.mk #[1, 2, 3]).iter.toUInt64ArrayWithCapacity 100) ≥ 100
