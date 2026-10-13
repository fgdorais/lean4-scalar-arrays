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
example (a : UInt32Array) : a.extract 0 a.size = a := by simp [UInt32Array.ext_iff]
example (a : UInt32Array) (v : UInt32) : (a.push v).pop = a :=
  UInt32Array.ext_getElem (by simp) (by simp_all)
