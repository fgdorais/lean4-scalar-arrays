/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ScalarArray.ISize
import ScalarArrayTest.Util

open ScalarArray ScalarArrayTest

/-! Construction and conversion -/

#guard (ISizeArray.mk #[1, 2, 3, (-9223372036854775808)]).data == #[1, 2, 3, (-9223372036854775808)]
#guard (ISizeArray.mk #[1, 2, 3, (-9223372036854775808)]).toList == [1, 2, 3, (-9223372036854775808)]
#guard (ISizeArray.mk #[]).data == #[]
#guard ISizeArray.empty.data == #[]
#guard (∅ : ISizeArray).data == #[]
#guard (default : ISizeArray).data == #[]
#guard (ISizeArray.emptyWithCapacity 100).data == #[]
#guard (ISizeArray.mk (Array.range 1000 |>.map Nat.toISize)).data == (Array.range 1000).map Nat.toISize

/-! Size -/

#guard (ISizeArray.mk #[1, 2, 3, (-9223372036854775808)]).size == 4
#guard (ISizeArray.mk #[1, 2, 3, (-9223372036854775808)]).usize == 4
#guard ISizeArray.empty.size == 0
#guard (ISizeArray.emptyWithCapacity 100).size == 0

/-! Reading -/

#guard (ISizeArray.mk #[1, 2, 3, (-9223372036854775808)])[0] == 1
#guard (ISizeArray.mk #[1, 2, 3, (-9223372036854775808)])[3] == (-9223372036854775808)
#guard (ISizeArray.mk #[1, 2, 3, (-9223372036854775808)])[(2 : USize)] == 3
#guard (ISizeArray.mk #[1, 2, 3, (-9223372036854775808)]).get! 1 == 2
#guard (ISizeArray.mk #[1, 2, 3, (-9223372036854775808)]).getD 2 7 == 3
#guard (ISizeArray.mk #[1, 2, 3, (-9223372036854775808)]).getD 4 7 == 7
#guard (ISizeArray.mk #[1, 2, 3, (-9223372036854775808)])[4]? == none
#guard (ISizeArray.mk #[1, 2, 3, (-9223372036854775808)])[1]? == some 2

/-! Writing -/

#guard ((ISizeArray.mk #[1, 2, 3]).set 1 42 (by decide)).data == #[1, 42, 3]
#guard ((ISizeArray.mk #[1, 2, 3]).uset 2 42 (by simp)).data == #[1, 2, 42]
#guard ((ISizeArray.mk #[1, 2, 3]).set! 0 (-9223372036854775808)).data == #[(-9223372036854775808), 2, 3]

-- Writing to a shared array must leave the original unchanged. The result is checked first so
-- that it is computed while the original is still live.
#guard
  let a := ISizeArray.mk #[1, 2, 3]
  let b := a.set! 1 42
  b.data == #[1, 42, 3] && a.data == #[1, 2, 3]

-- Repeated writes to an exclusive array.
#guard Id.run do
  let mut a := ISizeArray.mk (Array.replicate 1000 0)
  for i in [0:1000] do
    a := a.set! i (i * 3).toISize
  return a.data == (Array.range 1000).map fun i => (i * 3).toISize

/-! Pushing -/

#guard (ISizeArray.empty.push 5 |>.push 6).data == #[5, 6]
#guard ((ISizeArray.emptyWithCapacity 1).push 5 |>.push 6 |>.push 7).data == #[5, 6, 7]
#guard ((ISizeArray.mk #[1, 2]).push 3).data == #[1, 2, 3]

-- Pushing past the capacity many times.
#guard Id.run do
  let mut a := ISizeArray.empty
  for i in [0:10000] do
    a := a.push i.toISize
  return a.size == 10000 && a.data == (Array.range 10000).map Nat.toISize

-- Pushing to a shared array must leave the original unchanged. The results are checked first so
-- that they are computed while the original is still live.
#guard
  let a := (ISizeArray.emptyWithCapacity 10).push 1
  let b := a.push 2
  let c := a.push 3
  c.data == #[1, 3] && b.data == #[1, 2] && a.data == #[1]

/-! Printing -/

#guard toString (ISizeArray.mk #[1, 2]) == "ISizeArray.mk " ++ toString #[(1 : ISize), 2]
#guard reprStr (ISizeArray.mk #[1, 2]) == "ISizeArray.mk " ++ reprStr #[(1 : ISize), 2]

/-! Every index, through both `Nat` and `USize` indices -/

#guard
  let a := ISizeArray.mk ((Array.range 300).map Nat.toISize)
  (List.range 300).all fun i =>
    a[i]! == i.toISize && a.getD i 0 == i.toISize && a.get! i == i.toISize &&
      (if h : i.toUSize.toNat < a.size then a[i.toUSize] == i.toISize else false)

/-! Writes don't touch neighbouring elements -/

#guard ((ISizeArray.mk #[0, 0, 0]).set! 1 (-9223372036854775808)).data == #[0, (-9223372036854775808), 0]
#guard ((ISizeArray.mk #[(-9223372036854775808), (-9223372036854775808), (-9223372036854775808)]).set! 1 0).data == #[(-9223372036854775808), 0, (-9223372036854775808)]
#guard ((ISizeArray.mk #[0, 0, 0]).push (-9223372036854775808) |>.push 0).data == #[0, 0, 0, (-9223372036854775808), 0]

/-! Indices beyond 16 bits, and huge `Nat` indices -/

#guard
  let a := (ISizeArray.mk (Array.replicate 100000 0)).set! 99999 (-9223372036854775808) |>.set! 70000 1
  a.size == 100000 && a[99999]! == (-9223372036854775808) && a[70000]! == 1 && a[99998]! == 0 &&
    a[70000 % 65536]! == 0 && a.data[99999]! == (-9223372036854775808) && a.data[70000]! == 1 &&
    (if h : (70000 : USize).toNat < a.size then a[(70000 : USize)] == 1 else false)

#guard (ISizeArray.mk #[1, 2, 3])[2 ^ 70]? == none
#guard (ISizeArray.mk #[1, 2, 3]).getD (2 ^ 70) 7 == 7

/-! Pushing onto a shared array that is at full capacity -/

#guard
  let a := ISizeArray.mk #[1]
  let b := a.push 2
  b.data == #[1, 2] && a.data == #[1]

#guard
  let a := ISizeArray.mk #[]
  let b := a.push 2
  b.data == #[2] && a.data == #[]

/-! Conversions don't alias -/

#guard
  let a := #[(1 : ISize), 2, 3]
  let b := (ISizeArray.mk a).set! 0 (-9223372036854775808)
  b.data == #[(-9223372036854775808), 2, 3] && a == #[1, 2, 3]

#guard
  let a := ISizeArray.mk #[1, 2, 3]
  let d := a.data.set! 0 (-9223372036854775808)
  d == #[(-9223372036854775808), 2, 3] && a.data == #[1, 2, 3]

/-! Runtime representation -/

#guard rawElemSize (ISizeArray.mk #[1, 2, 3]) == ((System.Platform.numBits / 8).toUInt32 : UInt32)
#guard rawElemSize (ISizeArray.emptyWithCapacity 10) == ((System.Platform.numBits / 8).toUInt32 : UInt32)
#guard rawElemSize (ISizeArray.empty.push 1) == ((System.Platform.numBits / 8).toUInt32 : UInt32)
#guard rawElemSize ((ISizeArray.mk #[1]).push 2) == ((System.Platform.numBits / 8).toUInt32 : UInt32)
#guard rawCapacity (ISizeArray.emptyWithCapacity 100) ≥ 100
#guard rawCapacity (ISizeArray.mk #[1, 2, 3]) ≥ 3
-- Growth is geometric, so pushing is amortized constant time.
#guard rawCapacity ((ISizeArray.mk #[1, 2, 3, 4]).push 5) ≥ 8


/-! Appending -/

#guard (ISizeArray.mk #[1, 2] ++ ISizeArray.mk #[3, (-9223372036854775808)]).data == #[1, 2, 3, (-9223372036854775808)]
#guard ((ISizeArray.mk #[1, 2]).append (ISizeArray.mk #[3])).data == #[1, 2, 3]
#guard (ISizeArray.mk #[1, 2] ++ ISizeArray.empty).data == #[1, 2]
#guard (ISizeArray.empty ++ ISizeArray.mk #[1, 2]).data == #[1, 2]
#guard (ISizeArray.empty ++ ISizeArray.empty).data == #[]
#guard (ISizeArray.mk #[0, 0] ++ ISizeArray.mk #[(-9223372036854775808)] ++ ISizeArray.mk #[0]).data ==
  #[0, 0, (-9223372036854775808), 0]

-- Appending an array to itself, with and without room.
#guard
  let a := ISizeArray.mk #[1, 2, 3]
  (a ++ a).data == #[1, 2, 3, 1, 2, 3]

#guard
  let a := (ISizeArray.emptyWithCapacity 10).push 1 |>.push 2
  (a ++ a).data == #[1, 2, 1, 2]

-- Appending to a shared array must leave the original unchanged, with and without room. The
-- results are checked first so that they are computed while the original is still live.
#guard
  let a := (ISizeArray.emptyWithCapacity 10).push 1
  let b := a ++ ISizeArray.mk #[2, 3]
  let c := a ++ ISizeArray.mk #[4]
  c.data == #[1, 4] && b.data == #[1, 2, 3] && a.data == #[1]

#guard
  let a := ISizeArray.mk #[1]
  let b := a ++ ISizeArray.mk #[2, 3]
  b.data == #[1, 2, 3] && a.data == #[1]

-- The right operand is never modified.
#guard
  let b := ISizeArray.mk #[2, 3]
  let c := ISizeArray.mk #[1] ++ b
  c.data == #[1, 2, 3] && b.data == #[2, 3]

-- Many appends to an exclusive array.
#guard Id.run do
  let mut a := ISizeArray.empty
  let mut r : Array ISize := #[]
  for i in [0:1000] do
    a := a ++ ISizeArray.mk #[i.toISize, (i * 7).toISize, (-9223372036854775808)]
    r := r ++ #[i.toISize, (i * 7).toISize, (-9223372036854775808)]
  return a.data == r

-- Large arrays on both sides.
#guard
  let xs := (Array.range 50000).map Nat.toISize
  let ys := (Array.range 50000).map fun i => (i * 3).toISize
  (ISizeArray.mk xs ++ ISizeArray.mk ys).data == xs ++ ys

-- An exclusive array with room is appended to in place, and growth is geometric.
-- The array is built from a parameter so that it isn't extracted as a shared closed term.
@[noinline] def ISizeArray.appendsInPlace (x : ISize) : Bool :=
  let a := (ISizeArray.emptyWithCapacity 10).push x
  let p := rawAddr a
  let a := a ++ ISizeArray.mk #[2, 3]
  rawAddr a == p && a.data == #[x, 2, 3]

@[noinline] def ISizeArray.appendsToCopyWhenShared (x : ISize) : Bool :=
  let a := (ISizeArray.emptyWithCapacity 10).push x
  let p := rawAddr a
  let b := a ++ ISizeArray.mk #[2, 3]
  rawAddr b != p && b.data == #[x, 2, 3] && a.data == #[x]

#guard ISizeArray.appendsInPlace 1
#guard ISizeArray.appendsToCopyWhenShared 1

#guard rawCapacity ((ISizeArray.emptyWithCapacity 10).push 1 ++ ISizeArray.mk #[2, 3]) ≥ 10
#guard rawCapacity (ISizeArray.mk #[1, 2, 3, 4] ++ ISizeArray.mk #[5]) ≥ 8
#guard rawCapacity (ISizeArray.mk #[1] ++ ISizeArray.mk (Array.replicate 10 0)) ≥ 11
#guard rawElemSize (ISizeArray.mk #[1] ++ ISizeArray.mk #[2]) == ((System.Platform.numBits / 8).toUInt32 : UInt32)

/-! Equality -/

#guard ISizeArray.mk #[1, 2, (-9223372036854775808)] == ISizeArray.mk #[1, 2, (-9223372036854775808)]
#guard ISizeArray.mk #[1, 2, (-9223372036854775808)] != ISizeArray.mk #[1, 2, 0]
#guard ISizeArray.mk #[1, 2] != ISizeArray.mk #[1, 2, 0]
#guard ISizeArray.mk #[1, 2, 0] != ISizeArray.mk #[1, 2]
#guard ISizeArray.empty == ISizeArray.emptyWithCapacity 10
#guard (ISizeArray.mk #[1, 2] ++ ISizeArray.mk #[(-9223372036854775808)]) == ISizeArray.mk #[1, 2, (-9223372036854775808)]
-- Capacity and leftover memory past the size don't matter.
#guard (ISizeArray.emptyWithCapacity 100).push 1 == ISizeArray.mk #[1]
#guard (ISizeArray.mk #[1, 2, 3]).pop == ISizeArray.mk #[1, 2]
#guard (ISizeArray.mk (Array.replicate 100000 0)).set! 99999 (-9223372036854775808) !=
  ISizeArray.mk (Array.replicate 100000 0)

/-! Decidable equality and hashing -/

#guard decide (ISizeArray.mk #[1, 2, (-9223372036854775808)] = ISizeArray.mk #[1, 2, (-9223372036854775808)])
#guard !decide (ISizeArray.mk #[1, 2, (-9223372036854775808)] = ISizeArray.mk #[1, 2, 0])
#guard hash (ISizeArray.mk #[1, 2, (-9223372036854775808)]) == hash #[(1 : ISize), 2, (-9223372036854775808)]
#guard hash (ISizeArray.empty) == hash (#[] : Array ISize)
#guard hash ((ISizeArray.emptyWithCapacity 100).push 1) == hash (ISizeArray.mk #[1])

/-! Iteration -/

#guard (ISizeArray.mk #[1, 2, (-9223372036854775808)]).foldl (fun acc x => x :: acc) [] == [(-9223372036854775808), 2, 1]
#guard (ISizeArray.mk #[1, 2, (-9223372036854775808)]).foldr (fun x acc => x :: acc) [] == [1, 2, (-9223372036854775808)]
#guard ISizeArray.empty.foldl (fun acc x => x :: acc) [] == []
#guard ISizeArray.empty.foldr (fun x acc => x :: acc) [] == []
#guard (ISizeArray.mk #[1, 2, (-9223372036854775808)]).foldlM (m := Option)
  (fun acc x => if x == 2 then none else some (x :: acc)) [] == none
#guard (ISizeArray.mk #[1, (-9223372036854775808)]).foldrM (m := Option) (fun x acc => some (x :: acc)) [] ==
  some [1, (-9223372036854775808)]

#guard Id.run do
  let mut r : List ISize := []
  for x in ISizeArray.mk #[1, 2, (-9223372036854775808)] do
    r := x :: r
  return r == [(-9223372036854775808), 2, 1]

#guard Id.run do
  let mut r : List ISize := []
  for x in ISizeArray.mk #[1, 2, 3, 4] do
    if x == 3 then break
    r := x :: r
  return r == [2, 1]

#guard
  let r : StateM (List ISize) Unit := (ISizeArray.mk #[1, 2, (-9223372036854775808)]).forM fun x => modify (x :: ·)
  (r.run []).2 == [(-9223372036854775808), 2, 1]

#guard
  let xs := (Array.range 100000).map Nat.toISize
  let f := fun (acc : List ISize) x => if x == 0 then x :: acc else acc
  (ISizeArray.mk xs).foldl f [] == xs.foldl f []

#guard (ISizeArray.mk #[1, 2, (-9223372036854775808)]).any (· == (-9223372036854775808))
#guard !(ISizeArray.mk #[1, 2, 3]).any (· == (-9223372036854775808))
#guard (ISizeArray.mk #[1, 2, 3]).all (· != (-9223372036854775808))
#guard !(ISizeArray.mk #[1, (-9223372036854775808), 3]).all (· != (-9223372036854775808))
#guard !ISizeArray.empty.any (fun _ => true) && ISizeArray.empty.all (fun _ => false)
#guard (ISizeArray.mk #[1, 2, (-9223372036854775808)]).contains (-9223372036854775808)
#guard !(ISizeArray.mk #[1, 2, 3]).contains (-9223372036854775808)
#guard (ISizeArray.mk (Array.replicate 100000 0) |>.set! 99999 (-9223372036854775808)).contains (-9223372036854775808)

/-! Removing elements -/

#guard ISizeArray.empty.isEmpty && !(ISizeArray.mk #[1]).isEmpty
#guard (ISizeArray.mk #[1]).pop.isEmpty
#guard (ISizeArray.mk #[1, 2, (-9223372036854775808)]).pop.data == #[1, 2]
#guard ISizeArray.empty.pop.data == #[]
#guard ((ISizeArray.mk #[1, 2, 3]).pop.push (-9223372036854775808)).data == #[1, 2, (-9223372036854775808)]
#guard (ISizeArray.mk #[1, 2, (-9223372036854775808)]).back? == some (-9223372036854775808)
#guard ISizeArray.empty.back? == none
#guard (ISizeArray.mk #[1, 2, (-9223372036854775808)]).back! == (-9223372036854775808)
#guard (ISizeArray.mk #[1, 2, (-9223372036854775808)]).back (by decide) == (-9223372036854775808)

-- Popping from a shared array must leave the original unchanged.
#guard
  let a := ISizeArray.mk #[1, 2, 3]
  let b := a.pop
  b.data == #[1, 2] && a.data == #[1, 2, 3]

-- The array is built from a parameter so that it isn't extracted as a shared closed term.
@[noinline] def ISizeArray.popsInPlace (x : ISize) : Bool :=
  let a := (ISizeArray.mk #[x]).push x
  let p := rawAddr a
  let a := a.pop
  rawAddr a == p && a.data == #[x]

#guard ISizeArray.popsInPlace 1

#guard ((ISizeArray.mk #[1, 2, 3, (-9223372036854775808)]).extract 1 3).data == #[2, 3]
#guard ((ISizeArray.mk #[1, 2, 3, (-9223372036854775808)]).extract 2 100).data == #[3, (-9223372036854775808)]
#guard ((ISizeArray.mk #[1, 2, 3]).extract 0 3).data == #[1, 2, 3]
#guard ((ISizeArray.mk #[1, 2, 3]).extract 2 1).data == #[]
#guard ((ISizeArray.mk #[1, 2, 3]).extract 5 9).data == #[]
#guard ((ISizeArray.mk #[1, 2, 3]).extract (2 ^ 70) (2 ^ 71)).data == #[]
#guard ((ISizeArray.mk #[1, 2, 3]).extract 1 (2 ^ 70)).data == #[2, 3]
#guard
  let xs := (Array.range 100000).map Nat.toISize
  ((ISizeArray.mk xs).extract 70000 70010).data == xs.extract 70000 70010
#guard rawElemSize ((ISizeArray.mk #[1, 2, 3]).extract 1 2) == ((System.Platform.numBits / 8).toUInt32 : UInt32)

-- The extracted array is independent of the original.
#guard
  let a := ISizeArray.mk #[1, 2, 3]
  let b := (a.extract 0 2).set! 0 (-9223372036854775808)
  b.data == #[(-9223372036854775808), 2] && a.data == #[1, 2, 3]

/-! Building arrays -/

#guard (ISizeArray.replicate 3 (-9223372036854775808)).data == #[(-9223372036854775808), (-9223372036854775808), (-9223372036854775808)]
#guard (ISizeArray.replicate 0 1).data == #[]
#guard (ISizeArray.replicate 100000 (-9223372036854775808)).data == Array.replicate 100000 (-9223372036854775808)
#guard (ISizeArray.ofFn (n := 4) fun i => i.val.toISize).data == #[0, 1, 2, 3]
#guard (ISizeArray.ofFn (n := 0) fun i => i.val.toISize).data == #[]
#guard rawElemSize (ISizeArray.replicate 2 1) == ((System.Platform.numBits / 8).toUInt32 : UInt32)
#guard rawElemSize (ISizeArray.ofFn (n := 2) fun _ => 1) == ((System.Platform.numBits / 8).toUInt32 : UInt32)

/-! Lemmas -/

example (a : ISizeArray) (v : ISize) : (a.push v).pop = a := by simp [ISizeArray.ext_iff]
example : (ISizeArray.replicate 3 (-9223372036854775808))[1] = (-9223372036854775808) := by simp
example (a b : ISizeArray) (h : 0 < a.size) : (a ++ b)[0]'(by simp; omega) = a[0] := by simp [h]
example (a : ISizeArray) (i : Nat) (v : ISize) (h : i < a.size) :
    (a.set i v h)[i]'(by simpa) = v := by simp
example (a : ISizeArray) : a.extract 0 a.size = a := by simp
example (a : ISizeArray) (v : ISize) : (a.push v).pop = a :=
  ISizeArray.ext_getElem (by simp) (by simp_all)

/-! Default bounds proofs -/

#guard (ISizeArray.mk #[1, 2, (-9223372036854775808)]).get 2 == (-9223372036854775808)
#guard (ISizeArray.mk #[1, 2, (-9223372036854775808)]).uget 2 == (-9223372036854775808)
#guard ((ISizeArray.mk #[1, 2, 3]).set 1 (-9223372036854775808)).data == #[1, (-9223372036854775808), 3]
#guard ((ISizeArray.mk #[1, 2, 3]).uset 1 (-9223372036854775808)).data == #[1, (-9223372036854775808), 3]

/-! `set!` leaves the array unchanged when the index is out of bounds, like `ByteArray.set!`. -/

#guard ((ISizeArray.mk #[1, 2, 3]).set! 3 (-9223372036854775808)).data == #[1, 2, 3]
#guard ((ISizeArray.mk #[1, 2, 3]).set! (2 ^ 70) (-9223372036854775808)).data == #[1, 2, 3]

/-! Folds over part of an array -/

#guard (ISizeArray.mk #[1, 2, 3, (-9223372036854775808)]).foldl (fun acc x => x :: acc) [] 1 3 == [3, 2]
#guard (ISizeArray.mk #[1, 2, 3, (-9223372036854775808)]).foldl (fun acc x => x :: acc) [] 2 == [(-9223372036854775808), 3]
#guard (ISizeArray.mk #[1, 2, 3, (-9223372036854775808)]).foldl (fun acc x => x :: acc) [] 1 100 == [(-9223372036854775808), 3, 2]
#guard (ISizeArray.mk #[1, 2, 3, (-9223372036854775808)]).foldl (fun acc x => x :: acc) [] 3 1 == []
#guard (ISizeArray.mk #[1, 2, 3, (-9223372036854775808)]).foldl (fun acc x => x :: acc) [] 9 12 == []
#guard (ISizeArray.mk #[1, 2, 3]).foldlM (m := Option)
  (fun acc x => if x == 1 then none else some (x :: acc)) [] 1 == some [3, 2]

/-! Copying slices -/

#guard
  let src := ISizeArray.mk #[10, 11, 12, (-9223372036854775808)]
  let dest := ISizeArray.mk #[1, 2, 3, 4, 5]
  (src.copySlice 1 dest 2 2).data == #[1, 2, 11, 12, 5] &&
  (src.copySlice 1 dest 4 3).data == #[1, 2, 3, 4, 11, 12, (-9223372036854775808)] &&
  (src.copySlice 0 dest 9 2).data == #[1, 2, 3, 4, 5, 10, 11] &&
  (src.copySlice 9 dest 1 2).data == #[1, 2, 3, 4, 5] &&
  (src.copySlice 2 dest 0 10).data == #[12, (-9223372036854775808), 3, 4, 5] &&
  (src.copySlice 0 dest 0 0).data == #[1, 2, 3, 4, 5] &&
  (src.copySlice 0 ISizeArray.empty 0 4).data == #[10, 11, 12, (-9223372036854775808)] &&
  dest.data == #[1, 2, 3, 4, 5] && src.data == #[10, 11, 12, (-9223372036854775808)]

-- Copying from an array into itself.
#guard
  let a := ISizeArray.mk #[1, 2, 3, (-9223372036854775808)]
  (a.copySlice 0 a 2 4).data == #[1, 2, 1, 2, 3, (-9223372036854775808)]

#guard
  let xs := (Array.range 100000).map Nat.toISize
  let a := ISizeArray.mk xs
  (a.copySlice 70000 (ISizeArray.replicate 10 0) 5 10).data ==
    Array.replicate 5 0 ++ xs.extract 70000 70010

#guard rawElemSize ((ISizeArray.mk #[1]).copySlice 0 ISizeArray.empty 0 1) == ((System.Platform.numBits / 8).toUInt32 : UInt32)

@[noinline] def ISizeArray.copiesSliceInPlace (x : ISize) : Bool :=
  let dest := (ISizeArray.emptyWithCapacity 10).push x |>.push x |>.push x
  let p := rawAddr dest
  let dest := (ISizeArray.mk #[(-9223372036854775808), (-9223372036854775808)]).copySlice 0 dest 1 2
  rawAddr dest == p && dest.data == #[x, (-9223372036854775808), (-9223372036854775808)]

@[noinline] def ISizeArray.copySliceGrowth (x : ISize) : Bool :=
  let dest := (ISizeArray.mk #[x, x, x, x])
  rawCapacity ((ISizeArray.mk #[x]).copySlice 0 dest 4 1 (exact := false)) ≥ 8 &&
    rawCapacity ((ISizeArray.mk #[x]).copySlice 0 dest 4 1) == 5

#guard ISizeArray.copiesSliceInPlace 1
#guard ISizeArray.copySliceGrowth 1

/-! Linearity markers -/

#guard ((ISizeArray.mk #[1, 2]).markLinear.push (-9223372036854775808)).data == #[1, 2, (-9223372036854775808)]
#guard ((ISizeArray.mk #[1]).propagateMark (ISizeArray.mk #[2, (-9223372036854775808)])).data == #[2, (-9223372036854775808)]

/-! Search -/

#guard (ISizeArray.mk #[1, 2, (-9223372036854775808), 2]).findIdx? (· == 2) == some 1
#guard (ISizeArray.mk #[1, 2, (-9223372036854775808), 2]).findIdx? (· == 2) 2 == some 3
#guard (ISizeArray.mk #[1, 2, (-9223372036854775808), 2]).findIdx? (· == 3) == none
#guard (ISizeArray.mk #[1, 2, (-9223372036854775808), 2]).findIdx? (· == 1) 9 == none
#guard ((ISizeArray.mk #[1, 2, (-9223372036854775808), 2]).findFinIdx? (· == (-9223372036854775808))).map (·.val) == some 2

/-! Lists -/

#guard (ISizeArray.ofList [1, 2, (-9223372036854775808)]).data == #[1, 2, (-9223372036854775808)]
#guard (ISizeArray.ofList []).data == #[]
#guard [1, 2, (-9223372036854775808)].toISizeArray == ISizeArray.mk #[1, 2, (-9223372036854775808)]
#guard (ISizeArray.ofList ((List.range 100000).map Nat.toISize)).data ==
  (Array.range 100000).map Nat.toISize
#guard rawElemSize (ISizeArray.ofList [1, 2]) == ((System.Platform.numBits / 8).toUInt32 : UInt32)

/-! More lemmas -/

example (a b c : ISizeArray) : a ++ b ++ c = a ++ (b ++ c) := ISizeArray.append_assoc ..
example (a : ISizeArray) : a ++ ∅ = a := by simp
example (a b : ISizeArray) : (a ++ b).extract 0 a.size = a := by simp
example (a : ISizeArray) (i : Nat) (v : ISize) : (a.set! i v).size = a.size := by simp
example (l : List ISize) : (ISizeArray.ofList l).toList = l := by simp
example (a : ISizeArray) : ISizeArray.ofList a.toList = a := by simp

/-! Iterators -/

#guard
  let it := (ISizeArray.mk #[1, 2, (-9223372036854775808)]).iter
  it.curr == 1 && it.pos == 0 && !it.atEnd && it.hasNext && !it.hasPrev && it.remaining == 3 &&
    it.next.curr == 2 && it.next.hasPrev && it.next.next.curr == (-9223372036854775808) &&
    it.next.next.next.atEnd && !it.next.next.next.hasNext && it.next.next.next.remaining == 0 &&
    it.toEnd.atEnd && it.toEnd.pos == 3 && it.toEnd.prev.curr == (-9223372036854775808) &&
    (it.forward 2).curr == (-9223372036854775808) && (it.nextn 1).curr == 2 && (it.toEnd.prevn 2).curr == 2 &&
    (it.toEnd.prevn 10).pos == 0 && it.prev.pos == 0

-- An invalid position gives the default element.
#guard (ISizeArray.mk #[1]).iter.next.curr == default
#guard ((ISizeArray.mk #[1, 2]).iter.forward 5).curr == default
#guard ISizeArray.empty.iter.atEnd && ISizeArray.empty.iter.curr == default

#guard (ISizeArray.mk #[1, (-9223372036854775808)]).iter.curr' (by decide) == 1
#guard ((ISizeArray.mk #[1, (-9223372036854775808)]).iter.next' (by decide)).curr == (-9223372036854775808)

#guard Id.run do
  let mut it := (ISizeArray.mk #[1, 2, (-9223372036854775808)]).iter
  let mut r : List ISize := []
  while it.hasNext do
    r := it.curr :: r
    it := it.next
  return r == [(-9223372036854775808), 2, 1]

#guard Id.run do
  let mut it := (ISizeArray.mk #[1, 2, (-9223372036854775808)]).iter.toEnd
  let mut r : List ISize := []
  while it.hasPrev do
    it := it.prev
    r := it.curr :: r
  return r == [1, 2, (-9223372036854775808)]

example (it : ISizeArray.Iterator) : sizeOf it = it.array.size - it.idx :=
  ISizeArray.Iterator.sizeOf_eq it
