/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ScalarArray.UInt32
import ScalarArrayTest.Util

open ScalarArray ScalarArrayTest

/-! Construction and conversion -/

#guard (UInt32Array.mk #[1, 2, 3, 4294967295]).data == #[1, 2, 3, 4294967295]
#guard (UInt32Array.mk #[1, 2, 3, 4294967295]).toList == [1, 2, 3, 4294967295]
#guard (UInt32Array.mk #[]).data == #[]
#guard UInt32Array.empty.data == #[]
#guard (∅ : UInt32Array).data == #[]
#guard (default : UInt32Array).data == #[]
#guard (UInt32Array.emptyWithCapacity 100).data == #[]
#guard (UInt32Array.mk (Array.range 1000 |>.map Nat.toUInt32)).data == (Array.range 1000).map Nat.toUInt32

/-! Size -/

#guard (UInt32Array.mk #[1, 2, 3, 4294967295]).size == 4
#guard (UInt32Array.mk #[1, 2, 3, 4294967295]).usize == 4
#guard UInt32Array.empty.size == 0
#guard (UInt32Array.emptyWithCapacity 100).size == 0

/-! Reading -/

#guard (UInt32Array.mk #[1, 2, 3, 4294967295])[0] == 1
#guard (UInt32Array.mk #[1, 2, 3, 4294967295])[3] == 4294967295
#guard (UInt32Array.mk #[1, 2, 3, 4294967295])[(2 : USize)] == 3
#guard (UInt32Array.mk #[1, 2, 3, 4294967295]).get! 1 == 2
#guard (UInt32Array.mk #[1, 2, 3, 4294967295]).getD 2 7 == 3
#guard (UInt32Array.mk #[1, 2, 3, 4294967295]).getD 4 7 == 7
#guard (UInt32Array.mk #[1, 2, 3, 4294967295])[4]? == none
#guard (UInt32Array.mk #[1, 2, 3, 4294967295])[1]? == some 2

/-! Writing -/

#guard ((UInt32Array.mk #[1, 2, 3]).set 1 42 (by decide)).data == #[1, 42, 3]
#guard ((UInt32Array.mk #[1, 2, 3]).uset 2 42 (by simp)).data == #[1, 2, 42]
#guard ((UInt32Array.mk #[1, 2, 3]).set! 0 4294967295).data == #[4294967295, 2, 3]

-- Writing to a shared array must leave the original unchanged. The result is checked first so
-- that it is computed while the original is still live.
#guard
  let a := UInt32Array.mk #[1, 2, 3]
  let b := a.set! 1 42
  b.data == #[1, 42, 3] && a.data == #[1, 2, 3]

-- Repeated writes to an exclusive array.
#guard Id.run do
  let mut a := UInt32Array.mk (Array.replicate 1000 0)
  for i in [0:1000] do
    a := a.set! i (i * 3).toUInt32
  return a.data == (Array.range 1000).map fun i => (i * 3).toUInt32

/-! Pushing -/

#guard (UInt32Array.empty.push 5 |>.push 6).data == #[5, 6]
#guard ((UInt32Array.emptyWithCapacity 1).push 5 |>.push 6 |>.push 7).data == #[5, 6, 7]
#guard ((UInt32Array.mk #[1, 2]).push 3).data == #[1, 2, 3]

-- Pushing past the capacity many times.
#guard Id.run do
  let mut a := UInt32Array.empty
  for i in [0:10000] do
    a := a.push i.toUInt32
  return a.size == 10000 && a.data == (Array.range 10000).map Nat.toUInt32

-- Pushing to a shared array must leave the original unchanged. The results are checked first so
-- that they are computed while the original is still live.
#guard
  let a := (UInt32Array.emptyWithCapacity 10).push 1
  let b := a.push 2
  let c := a.push 3
  c.data == #[1, 3] && b.data == #[1, 2] && a.data == #[1]

/-! Printing -/

#guard toString (UInt32Array.mk #[1, 2]) == "UInt32Array.mk " ++ toString #[(1 : UInt32), 2]
#guard reprStr (UInt32Array.mk #[1, 2]) == "UInt32Array.mk " ++ reprStr #[(1 : UInt32), 2]

/-! Every index, through both `Nat` and `USize` indices -/

#guard
  let a := UInt32Array.mk ((Array.range 300).map Nat.toUInt32)
  (List.range 300).all fun i =>
    a[i]! == i.toUInt32 && a.getD i 0 == i.toUInt32 && a.get! i == i.toUInt32 &&
      (if h : i.toUSize.toNat < a.size then a[i.toUSize] == i.toUInt32 else false)

/-! Writes don't touch neighbouring elements -/

#guard ((UInt32Array.mk #[0, 0, 0]).set! 1 4294967295).data == #[0, 4294967295, 0]
#guard ((UInt32Array.mk #[4294967295, 4294967295, 4294967295]).set! 1 0).data == #[4294967295, 0, 4294967295]
#guard ((UInt32Array.mk #[0, 0, 0]).push 4294967295 |>.push 0).data == #[0, 0, 0, 4294967295, 0]

/-! Indices beyond 16 bits, and huge `Nat` indices -/

#guard
  let a := (UInt32Array.mk (Array.replicate 100000 0)).set! 99999 4294967295 |>.set! 70000 1
  a.size == 100000 && a[99999]! == 4294967295 && a[70000]! == 1 && a[99998]! == 0 &&
    a[70000 % 65536]! == 0 && a.data[99999]! == 4294967295 && a.data[70000]! == 1 &&
    (if h : (70000 : USize).toNat < a.size then a[(70000 : USize)] == 1 else false)

#guard (UInt32Array.mk #[1, 2, 3])[2 ^ 70]? == none
#guard (UInt32Array.mk #[1, 2, 3]).getD (2 ^ 70) 7 == 7

/-! Pushing onto a shared array that is at full capacity -/

#guard
  let a := UInt32Array.mk #[1]
  let b := a.push 2
  b.data == #[1, 2] && a.data == #[1]

#guard
  let a := UInt32Array.mk #[]
  let b := a.push 2
  b.data == #[2] && a.data == #[]

/-! Conversions don't alias -/

#guard
  let a := #[(1 : UInt32), 2, 3]
  let b := (UInt32Array.mk a).set! 0 4294967295
  b.data == #[4294967295, 2, 3] && a == #[1, 2, 3]

#guard
  let a := UInt32Array.mk #[1, 2, 3]
  let d := a.data.set! 0 4294967295
  d == #[4294967295, 2, 3] && a.data == #[1, 2, 3]

/-! Runtime representation -/

#guard rawElemSize (UInt32Array.mk #[1, 2, 3]) == (4 : UInt32)
#guard rawElemSize (UInt32Array.emptyWithCapacity 10) == (4 : UInt32)
#guard rawElemSize (UInt32Array.empty.push 1) == (4 : UInt32)
#guard rawElemSize ((UInt32Array.mk #[1]).push 2) == (4 : UInt32)
#guard rawCapacity (UInt32Array.emptyWithCapacity 100) ≥ 100
#guard rawCapacity (UInt32Array.mk #[1, 2, 3]) ≥ 3
-- Growth is geometric, so pushing is amortized constant time.
#guard rawCapacity ((UInt32Array.mk #[1, 2, 3, 4]).push 5) ≥ 8


/-! Appending -/

#guard (UInt32Array.mk #[1, 2] ++ UInt32Array.mk #[3, 4294967295]).data == #[1, 2, 3, 4294967295]
#guard ((UInt32Array.mk #[1, 2]).append (UInt32Array.mk #[3])).data == #[1, 2, 3]
#guard (UInt32Array.mk #[1, 2] ++ UInt32Array.empty).data == #[1, 2]
#guard (UInt32Array.empty ++ UInt32Array.mk #[1, 2]).data == #[1, 2]
#guard (UInt32Array.empty ++ UInt32Array.empty).data == #[]
#guard (UInt32Array.mk #[0, 0] ++ UInt32Array.mk #[4294967295] ++ UInt32Array.mk #[0]).data ==
  #[0, 0, 4294967295, 0]

-- Appending an array to itself, with and without room.
#guard
  let a := UInt32Array.mk #[1, 2, 3]
  (a ++ a).data == #[1, 2, 3, 1, 2, 3]

#guard
  let a := (UInt32Array.emptyWithCapacity 10).push 1 |>.push 2
  (a ++ a).data == #[1, 2, 1, 2]

-- Appending to a shared array must leave the original unchanged, with and without room. The
-- results are checked first so that they are computed while the original is still live.
#guard
  let a := (UInt32Array.emptyWithCapacity 10).push 1
  let b := a ++ UInt32Array.mk #[2, 3]
  let c := a ++ UInt32Array.mk #[4]
  c.data == #[1, 4] && b.data == #[1, 2, 3] && a.data == #[1]

#guard
  let a := UInt32Array.mk #[1]
  let b := a ++ UInt32Array.mk #[2, 3]
  b.data == #[1, 2, 3] && a.data == #[1]

-- The right operand is never modified.
#guard
  let b := UInt32Array.mk #[2, 3]
  let c := UInt32Array.mk #[1] ++ b
  c.data == #[1, 2, 3] && b.data == #[2, 3]

-- Many appends to an exclusive array.
#guard Id.run do
  let mut a := UInt32Array.empty
  let mut r : Array UInt32 := #[]
  for i in [0:1000] do
    a := a ++ UInt32Array.mk #[i.toUInt32, (i * 7).toUInt32, 4294967295]
    r := r ++ #[i.toUInt32, (i * 7).toUInt32, 4294967295]
  return a.data == r

-- Large arrays on both sides.
#guard
  let xs := (Array.range 50000).map Nat.toUInt32
  let ys := (Array.range 50000).map fun i => (i * 3).toUInt32
  (UInt32Array.mk xs ++ UInt32Array.mk ys).data == xs ++ ys

-- An exclusive array with room is appended to in place, and growth is geometric.
-- The array is built from a parameter so that it isn't extracted as a shared closed term.
@[noinline] def UInt32Array.appendsInPlace (x : UInt32) : Bool :=
  let a := (UInt32Array.emptyWithCapacity 10).push x
  let p := rawAddr a
  let a := a ++ UInt32Array.mk #[2, 3]
  rawAddr a == p && a.data == #[x, 2, 3]

@[noinline] def UInt32Array.appendsToCopyWhenShared (x : UInt32) : Bool :=
  let a := (UInt32Array.emptyWithCapacity 10).push x
  let p := rawAddr a
  let b := a ++ UInt32Array.mk #[2, 3]
  rawAddr b != p && b.data == #[x, 2, 3] && a.data == #[x]

#guard UInt32Array.appendsInPlace 1
#guard UInt32Array.appendsToCopyWhenShared 1

#guard rawCapacity ((UInt32Array.emptyWithCapacity 10).push 1 ++ UInt32Array.mk #[2, 3]) ≥ 10
#guard rawCapacity (UInt32Array.mk #[1, 2, 3, 4] ++ UInt32Array.mk #[5]) ≥ 8
#guard rawCapacity (UInt32Array.mk #[1] ++ UInt32Array.mk (Array.replicate 10 0)) ≥ 11
#guard rawElemSize (UInt32Array.mk #[1] ++ UInt32Array.mk #[2]) == (4 : UInt32)

/-! Equality -/

#guard UInt32Array.mk #[1, 2, 4294967295] == UInt32Array.mk #[1, 2, 4294967295]
#guard UInt32Array.mk #[1, 2, 4294967295] != UInt32Array.mk #[1, 2, 0]
#guard UInt32Array.mk #[1, 2] != UInt32Array.mk #[1, 2, 0]
#guard UInt32Array.mk #[1, 2, 0] != UInt32Array.mk #[1, 2]
#guard UInt32Array.empty == UInt32Array.emptyWithCapacity 10
#guard (UInt32Array.mk #[1, 2] ++ UInt32Array.mk #[4294967295]) == UInt32Array.mk #[1, 2, 4294967295]
-- Capacity and leftover memory past the size don't matter.
#guard (UInt32Array.emptyWithCapacity 100).push 1 == UInt32Array.mk #[1]
#guard (UInt32Array.mk #[1, 2, 3]).pop == UInt32Array.mk #[1, 2]
#guard (UInt32Array.mk (Array.replicate 100000 0)).set! 99999 4294967295 !=
  UInt32Array.mk (Array.replicate 100000 0)

/-! Decidable equality and hashing -/

#guard decide (UInt32Array.mk #[1, 2, 4294967295] = UInt32Array.mk #[1, 2, 4294967295])
#guard !decide (UInt32Array.mk #[1, 2, 4294967295] = UInt32Array.mk #[1, 2, 0])
#guard hash (UInt32Array.mk #[1, 2, 4294967295]) == hash #[(1 : UInt32), 2, 4294967295]
#guard hash (UInt32Array.empty) == hash (#[] : Array UInt32)
#guard hash ((UInt32Array.emptyWithCapacity 100).push 1) == hash (UInt32Array.mk #[1])

/-! Iteration -/

#guard (UInt32Array.mk #[1, 2, 4294967295]).foldl (fun acc x => x :: acc) [] == [4294967295, 2, 1]
#guard (UInt32Array.mk #[1, 2, 4294967295]).foldr (fun x acc => x :: acc) [] == [1, 2, 4294967295]
#guard UInt32Array.empty.foldl (fun acc x => x :: acc) [] == []
#guard UInt32Array.empty.foldr (fun x acc => x :: acc) [] == []
#guard (UInt32Array.mk #[1, 2, 4294967295]).foldlM (m := Option)
  (fun acc x => if x == 2 then none else some (x :: acc)) [] == none
#guard (UInt32Array.mk #[1, 4294967295]).foldrM (m := Option) (fun x acc => some (x :: acc)) [] ==
  some [1, 4294967295]

#guard Id.run do
  let mut r : List UInt32 := []
  for x in UInt32Array.mk #[1, 2, 4294967295] do
    r := x :: r
  return r == [4294967295, 2, 1]

#guard Id.run do
  let mut r : List UInt32 := []
  for x in UInt32Array.mk #[1, 2, 3, 4] do
    if x == 3 then break
    r := x :: r
  return r == [2, 1]

#guard
  let r : StateM (List UInt32) Unit := (UInt32Array.mk #[1, 2, 4294967295]).forM fun x => modify (x :: ·)
  (r.run []).2 == [4294967295, 2, 1]

#guard
  let xs := (Array.range 100000).map Nat.toUInt32
  let f := fun (acc : List UInt32) x => if x == 0 then x :: acc else acc
  (UInt32Array.mk xs).foldl f [] == xs.foldl f []

#guard (UInt32Array.mk #[1, 2, 4294967295]).any (· == 4294967295)
#guard !(UInt32Array.mk #[1, 2, 3]).any (· == 4294967295)
#guard (UInt32Array.mk #[1, 2, 3]).all (· != 4294967295)
#guard !(UInt32Array.mk #[1, 4294967295, 3]).all (· != 4294967295)
#guard !UInt32Array.empty.any (fun _ => true) && UInt32Array.empty.all (fun _ => false)
#guard (UInt32Array.mk #[1, 2, 4294967295]).contains 4294967295
#guard !(UInt32Array.mk #[1, 2, 3]).contains 4294967295
#guard (UInt32Array.mk (Array.replicate 100000 0) |>.set! 99999 4294967295).contains 4294967295

/-! Removing elements -/

#guard UInt32Array.empty.isEmpty && !(UInt32Array.mk #[1]).isEmpty
#guard (UInt32Array.mk #[1]).pop.isEmpty
#guard (UInt32Array.mk #[1, 2, 4294967295]).pop.data == #[1, 2]
#guard UInt32Array.empty.pop.data == #[]
#guard ((UInt32Array.mk #[1, 2, 3]).pop.push 4294967295).data == #[1, 2, 4294967295]
#guard (UInt32Array.mk #[1, 2, 4294967295]).back? == some 4294967295
#guard UInt32Array.empty.back? == none
#guard (UInt32Array.mk #[1, 2, 4294967295]).back! == 4294967295
#guard (UInt32Array.mk #[1, 2, 4294967295]).back (by decide) == 4294967295

-- Popping from a shared array must leave the original unchanged.
#guard
  let a := UInt32Array.mk #[1, 2, 3]
  let b := a.pop
  b.data == #[1, 2] && a.data == #[1, 2, 3]

-- The array is built from a parameter so that it isn't extracted as a shared closed term.
@[noinline] def UInt32Array.popsInPlace (x : UInt32) : Bool :=
  let a := (UInt32Array.mk #[x]).push x
  let p := rawAddr a
  let a := a.pop
  rawAddr a == p && a.data == #[x]

#guard UInt32Array.popsInPlace 1

#guard (UInt32Array.mk #[1, 0, 4294967295, 0, 0]).popWhile (· == 0) == UInt32Array.mk #[1, 0, 4294967295]
#guard (UInt32Array.mk #[1, 0, 4294967295]).popWhile (· == 0) == UInt32Array.mk #[1, 0, 4294967295]
#guard (UInt32Array.mk #[0, 0]).popWhile (· == 0) == UInt32Array.empty
#guard UInt32Array.empty.popWhile (· == 0) == UInt32Array.empty

-- Popping several elements from an exclusive array.
@[noinline] def UInt32Array.popsWhileInPlace (x : UInt32) : Bool :=
  let a := (UInt32Array.mk #[x]).push 0 |>.push 0
  let p := rawAddr a
  let a := a.popWhile (· == 0)
  rawAddr a == p && a.data == #[x]

#guard UInt32Array.popsWhileInPlace 1

example (p : UInt32 → Bool) (a : UInt32Array) : (a.popWhile p).data = a.data.popWhile p := by simp

#guard ((UInt32Array.mk #[1, 2, 3, 4294967295]).extract 1 3).data == #[2, 3]
#guard ((UInt32Array.mk #[1, 2, 3, 4294967295]).extract 2 100).data == #[3, 4294967295]
#guard ((UInt32Array.mk #[1, 2, 3]).extract 0 3).data == #[1, 2, 3]
#guard ((UInt32Array.mk #[1, 2, 3]).extract 2 1).data == #[]
#guard ((UInt32Array.mk #[1, 2, 3]).extract 5 9).data == #[]
#guard ((UInt32Array.mk #[1, 2, 3]).extract (2 ^ 70) (2 ^ 71)).data == #[]
#guard ((UInt32Array.mk #[1, 2, 3]).extract 1 (2 ^ 70)).data == #[2, 3]
#guard
  let xs := (Array.range 100000).map Nat.toUInt32
  ((UInt32Array.mk xs).extract 70000 70010).data == xs.extract 70000 70010
#guard rawElemSize ((UInt32Array.mk #[1, 2, 3]).extract 1 2) == (4 : UInt32)

-- The extracted array is independent of the original.
#guard
  let a := UInt32Array.mk #[1, 2, 3]
  let b := (a.extract 0 2).set! 0 4294967295
  b.data == #[4294967295, 2] && a.data == #[1, 2, 3]

/-! Building arrays -/

#guard (UInt32Array.replicate 3 4294967295).data == #[4294967295, 4294967295, 4294967295]
#guard (UInt32Array.replicate 0 1).data == #[]
#guard (UInt32Array.replicate 100000 4294967295).data == Array.replicate 100000 4294967295
#guard (UInt32Array.ofFn (n := 4) fun i => i.val.toUInt32).data == #[0, 1, 2, 3]
#guard (UInt32Array.ofFn (n := 0) fun i => i.val.toUInt32).data == #[]
#guard rawElemSize (UInt32Array.replicate 2 1) == (4 : UInt32)
#guard rawElemSize (UInt32Array.ofFn (n := 2) fun _ => 1) == (4 : UInt32)

/-! Lemmas -/

example (a : UInt32Array) (v : UInt32) : (a.push v).pop = a := by simp [UInt32Array.ext_iff]
example : (UInt32Array.replicate 3 4294967295)[1] = 4294967295 := by simp
example (a b : UInt32Array) (h : 0 < a.size) : (a ++ b)[0]'(by simp; omega) = a[0] := by simp [h]
example (a : UInt32Array) (i : Nat) (v : UInt32) (h : i < a.size) :
    (a.set i v h)[i]'(by simpa) = v := by simp
example (a : UInt32Array) : a.extract 0 a.size = a := by simp
example (a : UInt32Array) (v : UInt32) : (a.push v).pop = a :=
  UInt32Array.ext_getElem (by simp) (by simp_all)

/-! Default bounds proofs -/

#guard (UInt32Array.mk #[1, 2, 4294967295]).get 2 == 4294967295
#guard (UInt32Array.mk #[1, 2, 4294967295]).uget 2 == 4294967295
#guard ((UInt32Array.mk #[1, 2, 3]).set 1 4294967295).data == #[1, 4294967295, 3]
#guard ((UInt32Array.mk #[1, 2, 3]).uset 1 4294967295).data == #[1, 4294967295, 3]

/-! `set!` leaves the array unchanged when the index is out of bounds, like `ByteArray.set!`. -/

#guard ((UInt32Array.mk #[1, 2, 3]).set! 3 4294967295).data == #[1, 2, 3]
#guard ((UInt32Array.mk #[1, 2, 3]).set! (2 ^ 70) 4294967295).data == #[1, 2, 3]

/-! Folds over part of an array -/

#guard (UInt32Array.mk #[1, 2, 3, 4294967295]).foldl (fun acc x => x :: acc) [] 1 3 == [3, 2]
#guard (UInt32Array.mk #[1, 2, 3, 4294967295]).foldl (fun acc x => x :: acc) [] 2 == [4294967295, 3]
#guard (UInt32Array.mk #[1, 2, 3, 4294967295]).foldl (fun acc x => x :: acc) [] 1 100 == [4294967295, 3, 2]
#guard (UInt32Array.mk #[1, 2, 3, 4294967295]).foldl (fun acc x => x :: acc) [] 3 1 == []
#guard (UInt32Array.mk #[1, 2, 3, 4294967295]).foldl (fun acc x => x :: acc) [] 9 12 == []
#guard (UInt32Array.mk #[1, 2, 3]).foldlM (m := Option)
  (fun acc x => if x == 1 then none else some (x :: acc)) [] 1 == some [3, 2]

/-! Copying slices -/

#guard
  let src := UInt32Array.mk #[10, 11, 12, 4294967295]
  let dest := UInt32Array.mk #[1, 2, 3, 4, 5]
  (src.copySlice 1 dest 2 2).data == #[1, 2, 11, 12, 5] &&
  (src.copySlice 1 dest 4 3).data == #[1, 2, 3, 4, 11, 12, 4294967295] &&
  (src.copySlice 0 dest 9 2).data == #[1, 2, 3, 4, 5, 10, 11] &&
  (src.copySlice 9 dest 1 2).data == #[1, 2, 3, 4, 5] &&
  (src.copySlice 2 dest 0 10).data == #[12, 4294967295, 3, 4, 5] &&
  (src.copySlice 0 dest 0 0).data == #[1, 2, 3, 4, 5] &&
  (src.copySlice 0 UInt32Array.empty 0 4).data == #[10, 11, 12, 4294967295] &&
  dest.data == #[1, 2, 3, 4, 5] && src.data == #[10, 11, 12, 4294967295]

-- Copying from an array into itself.
#guard
  let a := UInt32Array.mk #[1, 2, 3, 4294967295]
  (a.copySlice 0 a 2 4).data == #[1, 2, 1, 2, 3, 4294967295]

#guard
  let xs := (Array.range 100000).map Nat.toUInt32
  let a := UInt32Array.mk xs
  (a.copySlice 70000 (UInt32Array.replicate 10 0) 5 10).data ==
    Array.replicate 5 0 ++ xs.extract 70000 70010

#guard rawElemSize ((UInt32Array.mk #[1]).copySlice 0 UInt32Array.empty 0 1) == (4 : UInt32)

@[noinline] def UInt32Array.copiesSliceInPlace (x : UInt32) : Bool :=
  let dest := (UInt32Array.emptyWithCapacity 10).push x |>.push x |>.push x
  let p := rawAddr dest
  let dest := (UInt32Array.mk #[4294967295, 4294967295]).copySlice 0 dest 1 2
  rawAddr dest == p && dest.data == #[x, 4294967295, 4294967295]

@[noinline] def UInt32Array.copySliceGrowth (x : UInt32) : Bool :=
  let dest := (UInt32Array.mk #[x, x, x, x])
  rawCapacity ((UInt32Array.mk #[x]).copySlice 0 dest 4 1 (exact := false)) ≥ 8 &&
    rawCapacity ((UInt32Array.mk #[x]).copySlice 0 dest 4 1) == 5

#guard UInt32Array.copiesSliceInPlace 1
#guard UInt32Array.copySliceGrowth 1

/-! Linearity markers -/

#guard ((UInt32Array.mk #[1, 2]).markLinear.push 4294967295).data == #[1, 2, 4294967295]
#guard ((UInt32Array.mk #[1]).propagateMark (UInt32Array.mk #[2, 4294967295])).data == #[2, 4294967295]

/-! Search -/

#guard (UInt32Array.mk #[1, 2, 4294967295, 2]).findIdx? (· == 2) == some 1
#guard (UInt32Array.mk #[1, 2, 4294967295, 2]).findIdx? (· == 2) 2 == some 3
#guard (UInt32Array.mk #[1, 2, 4294967295, 2]).findIdx? (· == 3) == none
#guard (UInt32Array.mk #[1, 2, 4294967295, 2]).findIdx? (· == 1) 9 == none
#guard ((UInt32Array.mk #[1, 2, 4294967295, 2]).findFinIdx? (· == 4294967295)).map (·.val) == some 2

/-! Lists -/

#guard (UInt32Array.ofList [1, 2, 4294967295]).data == #[1, 2, 4294967295]
#guard (UInt32Array.ofList []).data == #[]
#guard [1, 2, 4294967295].toUInt32Array == UInt32Array.mk #[1, 2, 4294967295]
#guard (UInt32Array.ofList ((List.range 100000).map Nat.toUInt32)).data ==
  (Array.range 100000).map Nat.toUInt32
#guard rawElemSize (UInt32Array.ofList [1, 2]) == (4 : UInt32)

/-! More lemmas -/

example (a b c : UInt32Array) : a ++ b ++ c = a ++ (b ++ c) := UInt32Array.append_assoc ..
example (a : UInt32Array) : a ++ ∅ = a := by simp
example (a b : UInt32Array) : (a ++ b).extract 0 a.size = a := by simp
example (a : UInt32Array) (i : Nat) (v : UInt32) : (a.set! i v).size = a.size := by simp
example (l : List UInt32) : (UInt32Array.ofList l).toList = l := by simp
example (a : UInt32Array) : UInt32Array.ofList a.toList = a := by simp

/-! Slices -/

#guard
  let a := UInt32Array.mk #[1, 2, 3, 4294967295]
  let s := a[1...3]
  s.size == 2 && s[0]! == 2 && s[1]! == 3 && s.getD 2 7 == 7 && s.copy == UInt32Array.mk #[2, 3] &&
    s.toList == [2, 3] && s.toArray == #[2, 3]

#guard
  let a := UInt32Array.mk #[1, 2, 3, 4294967295]
  a[1...=3].toList == [2, 3, 4294967295] && a[*...2].toList == [1, 2] && a[2...*].toList == [3, 4294967295] &&
    a[*...*].toList == [1, 2, 3, 4294967295] && a[0<...2].toList == [2] &&
    a[0<...=2].toList == [2, 3] && a[*...=1].toList == [1, 2] && a[1<...*].toList == [3, 4294967295]

-- Bounds are clamped.
#guard
  let a := UInt32Array.mk #[1, 2, 3, 4294967295]
  a[2...100].toList == [3, 4294967295] && a[3...1].size == 0 && a[9...12].size == 0 &&
    (a.toSlice 1 (2 ^ 70)).toList == [2, 3, 4294967295]

-- Slices of slices.
#guard
  let s := (UInt32Array.mk #[1, 2, 3, 4294967295])[1...4]
  s[1...2].toList == [3] && s[0...100].toList == [2, 3, 4294967295] && s[*...*].toList == [2, 3, 4294967295] &&
    s[2...*].toList == [4294967295] && s[5...6].size == 0

#guard
  let s := (UInt32Array.mk #[1, 2, 3, 4294967295])[1...4]
  s.popFront.toList == [3, 4294967295] && s.popFront.popFront.popFront.popFront.size == 0

#guard (∅ : UInt32Array.Slice).size == 0 && (default : UInt32Array.Slice).toList == []

-- An array coerces to the slice of all its elements.
#guard
  let s : UInt32Array.Slice := UInt32Array.mk #[1, 2, 4294967295]
  s.toList == [1, 2, 4294967295] && s.start == 0

-- A slice does not coerce back to an array, since that would copy.
example (s : UInt32Array.Slice) : UInt32Array := s.copy

#guard Id.run do
  let mut r : List UInt32 := []
  for x in (UInt32Array.mk #[1, 2, 3, 4294967295])[1...*] do
    r := x :: r
  return r == [4294967295, 3, 2]

#guard (UInt32Array.mk #[1, 2, 3, 4294967295])[1...*].foldl (fun acc x => x :: acc) [] == [4294967295, 3, 2]

#guard
  let xs := (Array.range 100000).map Nat.toUInt32
  let s := (UInt32Array.mk xs)[70000...70010]
  s.toArray == xs.extract 70000 70010 && s.copy.data == xs.extract 70000 70010

#guard toString (UInt32Array.mk #[1, 2, 3])[1...*] == toString (UInt32Array.mk #[2, 3])

-- Taking a slice doesn't copy the array.
@[noinline] def UInt32Array.slicesWithoutCopying (x : UInt32) : Bool :=
  let a := UInt32Array.mk #[x, 2, 3]
  let p := rawAddr a
  rawAddr a[1...2].array == p

#guard UInt32Array.slicesWithoutCopying 1

example (s : UInt32Array.Slice) : s.copy.size = s.size := by simp

/-! Slice API -/

#guard
  let s := (UInt32Array.mk #[1, 2, 3, 4294967295, 2])[1...5]
  s.foldr (fun x acc => x :: acc) [] == [2, 3, 4294967295, 2] &&
    s.foldl (fun acc x => x :: acc) [] == [2, 4294967295, 3, 2] &&
    s.any (· == 4294967295) && !s.any (· == 1) && s.all (· != 1) && !s.all (· == 2) &&
    s.contains 4294967295 && !s.contains 1 && s.count (· == 2) == 2 &&
    s.find? (· > 2) == some 3 && s.findRev? (· != 4294967295) == some 2 && s.findRev? (· == 1) == none

#guard (UInt32Array.mk #[1, 2, 3])[1...1].foldr (fun x acc => x :: acc) [] == []
#guard (UInt32Array.mk #[1, 2, 3])[3...*].find? (fun _ => true) == none

#guard
  let s := (UInt32Array.mk #[1, 2, 3, 4294967295])[1...*]
  let r : StateM (List UInt32) Unit := s.forRevM fun x => modify (x :: ·)
  (r.run []).2 == [2, 3, 4294967295]

#guard Id.run ((UInt32Array.mk #[1, 2, 4294967295])[*...*].findSomeRevM?
  (fun x => pure (if x == 2 then some x else none))) == some 2

/-! The `Std.Iterators` API on arrays and slices -/

#guard (UInt32Array.mk #[1, 2, 3]).iter.toList == [1, 2, 3]
#guard ((UInt32Array.mk #[1, 2, 3]).iter.map (· * 2)).toUInt32Array == UInt32Array.mk #[2, 4, 6]
#guard ((UInt32Array.mk #[1, 2, 3, 4294967295]).iter.filter (· != 2)).toUInt32Array ==
  UInt32Array.mk #[1, 3, 4294967295]
#guard ((UInt32Array.mk #[1, 2, 3, 4294967295]).iter.take 2).toUInt32Array == UInt32Array.mk #[1, 2]
#guard ((UInt32Array.mk #[1, 2, 3, 4294967295]).iter.drop 2).toUInt32Array == UInt32Array.mk #[3, 4294967295]
#guard (((UInt32Array.mk #[1, 2, 3]).iter.zip (UInt32Array.mk #[4294967295, 5]).iter).map
  fun (x, y) => x + y).toUInt32Array == UInt32Array.mk #[1 + 4294967295, 7]
#guard ((UInt32Array.mk #[1, 2, 3, 4294967295])[1...3].iter.map (· + 1)).toUInt32Array ==
  UInt32Array.mk #[3, 4]
#guard (UInt32Array.mk #[1, 2, 3]).iter.length == 3
#guard UInt32Array.empty.iter.toUInt32Array == UInt32Array.empty
#guard
  let xs := (Array.range 100000).map Nat.toUInt32
  ((UInt32Array.mk xs).iter.map (· + 1)).toUInt32Array.data == xs.map (· + 1)
#guard rawElemSize ((UInt32Array.mk #[1]).iter.toUInt32Array) == (4 : UInt32)
#guard ((UInt32Array.mk #[1, 2, 3]).iter.toUInt32Array (capacity := 100)) == UInt32Array.mk #[1, 2, 3]
#guard rawCapacity ((UInt32Array.mk #[1, 2, 3]).iter.toUInt32Array (capacity := 100)) ≥ 100
