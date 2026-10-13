/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ScalarArray.Int64
import ScalarArrayTest.Util

open ScalarArray ScalarArrayTest

/-! Construction and conversion -/

#guard (Int64Array.mk #[1, 2, 3, (-9223372036854775808)]).data == #[1, 2, 3, (-9223372036854775808)]
#guard (Int64Array.mk #[1, 2, 3, (-9223372036854775808)]).toList == [1, 2, 3, (-9223372036854775808)]
#guard (Int64Array.mk #[]).data == #[]
#guard Int64Array.empty.data == #[]
#guard (∅ : Int64Array).data == #[]
#guard (default : Int64Array).data == #[]
#guard (Int64Array.emptyWithCapacity 100).data == #[]
#guard (Int64Array.mk (Array.range 1000 |>.map Nat.toInt64)).data == (Array.range 1000).map Nat.toInt64

/-! Size -/

#guard (Int64Array.mk #[1, 2, 3, (-9223372036854775808)]).size == 4
#guard (Int64Array.mk #[1, 2, 3, (-9223372036854775808)]).usize == 4
#guard Int64Array.empty.size == 0
#guard (Int64Array.emptyWithCapacity 100).size == 0

/-! Reading -/

#guard (Int64Array.mk #[1, 2, 3, (-9223372036854775808)])[0] == 1
#guard (Int64Array.mk #[1, 2, 3, (-9223372036854775808)])[3] == (-9223372036854775808)
#guard (Int64Array.mk #[1, 2, 3, (-9223372036854775808)])[(2 : USize)] == 3
#guard (Int64Array.mk #[1, 2, 3, (-9223372036854775808)]).get! 1 == 2
#guard (Int64Array.mk #[1, 2, 3, (-9223372036854775808)]).getD 2 7 == 3
#guard (Int64Array.mk #[1, 2, 3, (-9223372036854775808)]).getD 4 7 == 7
#guard (Int64Array.mk #[1, 2, 3, (-9223372036854775808)])[4]? == none
#guard (Int64Array.mk #[1, 2, 3, (-9223372036854775808)])[1]? == some 2

/-! Writing -/

#guard ((Int64Array.mk #[1, 2, 3]).set 1 42 (by decide)).data == #[1, 42, 3]
#guard ((Int64Array.mk #[1, 2, 3]).uset 2 42 (by simp)).data == #[1, 2, 42]
#guard ((Int64Array.mk #[1, 2, 3]).set! 0 (-9223372036854775808)).data == #[(-9223372036854775808), 2, 3]

-- Writing to a shared array must leave the original unchanged. The result is checked first so
-- that it is computed while the original is still live.
#guard
  let a := Int64Array.mk #[1, 2, 3]
  let b := a.set! 1 42
  b.data == #[1, 42, 3] && a.data == #[1, 2, 3]

-- Repeated writes to an exclusive array.
#guard Id.run do
  let mut a := Int64Array.mk (Array.replicate 1000 0)
  for i in [0:1000] do
    a := a.set! i (i * 3).toInt64
  return a.data == (Array.range 1000).map fun i => (i * 3).toInt64

/-! Pushing -/

#guard (Int64Array.empty.push 5 |>.push 6).data == #[5, 6]
#guard ((Int64Array.emptyWithCapacity 1).push 5 |>.push 6 |>.push 7).data == #[5, 6, 7]
#guard ((Int64Array.mk #[1, 2]).push 3).data == #[1, 2, 3]

-- Pushing past the capacity many times.
#guard Id.run do
  let mut a := Int64Array.empty
  for i in [0:10000] do
    a := a.push i.toInt64
  return a.size == 10000 && a.data == (Array.range 10000).map Nat.toInt64

-- Pushing to a shared array must leave the original unchanged. The results are checked first so
-- that they are computed while the original is still live.
#guard
  let a := (Int64Array.emptyWithCapacity 10).push 1
  let b := a.push 2
  let c := a.push 3
  c.data == #[1, 3] && b.data == #[1, 2] && a.data == #[1]

/-! Printing -/

#guard toString (Int64Array.mk #[1, 2]) == "Int64Array.mk " ++ toString #[(1 : Int64), 2]
#guard reprStr (Int64Array.mk #[1, 2]) == "Int64Array.mk " ++ reprStr #[(1 : Int64), 2]

/-! Every index, through both `Nat` and `USize` indices -/

#guard
  let a := Int64Array.mk ((Array.range 300).map Nat.toInt64)
  (List.range 300).all fun i =>
    a[i]! == i.toInt64 && a.getD i 0 == i.toInt64 && a.get! i == i.toInt64 &&
      (if h : i.toUSize.toNat < a.size then a[i.toUSize] == i.toInt64 else false)

/-! Writes don't touch neighbouring elements -/

#guard ((Int64Array.mk #[0, 0, 0]).set! 1 (-9223372036854775808)).data == #[0, (-9223372036854775808), 0]
#guard ((Int64Array.mk #[(-9223372036854775808), (-9223372036854775808), (-9223372036854775808)]).set! 1 0).data == #[(-9223372036854775808), 0, (-9223372036854775808)]
#guard ((Int64Array.mk #[0, 0, 0]).push (-9223372036854775808) |>.push 0).data == #[0, 0, 0, (-9223372036854775808), 0]

/-! Indices beyond 16 bits, and huge `Nat` indices -/

#guard
  let a := (Int64Array.mk (Array.replicate 100000 0)).set! 99999 (-9223372036854775808) |>.set! 70000 1
  a.size == 100000 && a[99999]! == (-9223372036854775808) && a[70000]! == 1 && a[99998]! == 0 &&
    a[70000 % 65536]! == 0 && a.data[99999]! == (-9223372036854775808) && a.data[70000]! == 1 &&
    (if h : (70000 : USize).toNat < a.size then a[(70000 : USize)] == 1 else false)

#guard (Int64Array.mk #[1, 2, 3])[2 ^ 70]? == none
#guard (Int64Array.mk #[1, 2, 3]).getD (2 ^ 70) 7 == 7

/-! Pushing onto a shared array that is at full capacity -/

#guard
  let a := Int64Array.mk #[1]
  let b := a.push 2
  b.data == #[1, 2] && a.data == #[1]

#guard
  let a := Int64Array.mk #[]
  let b := a.push 2
  b.data == #[2] && a.data == #[]

/-! Conversions don't alias -/

#guard
  let a := #[(1 : Int64), 2, 3]
  let b := (Int64Array.mk a).set! 0 (-9223372036854775808)
  b.data == #[(-9223372036854775808), 2, 3] && a == #[1, 2, 3]

#guard
  let a := Int64Array.mk #[1, 2, 3]
  let d := a.data.set! 0 (-9223372036854775808)
  d == #[(-9223372036854775808), 2, 3] && a.data == #[1, 2, 3]

/-! Runtime representation -/

#guard rawElemSize (Int64Array.mk #[1, 2, 3]) == (8 : UInt32)
#guard rawElemSize (Int64Array.emptyWithCapacity 10) == (8 : UInt32)
#guard rawElemSize (Int64Array.empty.push 1) == (8 : UInt32)
#guard rawElemSize ((Int64Array.mk #[1]).push 2) == (8 : UInt32)
#guard rawCapacity (Int64Array.emptyWithCapacity 100) ≥ 100
#guard rawCapacity (Int64Array.mk #[1, 2, 3]) ≥ 3
-- Growth is geometric, so pushing is amortized constant time.
#guard rawCapacity ((Int64Array.mk #[1, 2, 3, 4]).push 5) ≥ 8


/-! Appending -/

#guard (Int64Array.mk #[1, 2] ++ Int64Array.mk #[3, (-9223372036854775808)]).data == #[1, 2, 3, (-9223372036854775808)]
#guard ((Int64Array.mk #[1, 2]).append (Int64Array.mk #[3])).data == #[1, 2, 3]
#guard (Int64Array.mk #[1, 2] ++ Int64Array.empty).data == #[1, 2]
#guard (Int64Array.empty ++ Int64Array.mk #[1, 2]).data == #[1, 2]
#guard (Int64Array.empty ++ Int64Array.empty).data == #[]
#guard (Int64Array.mk #[0, 0] ++ Int64Array.mk #[(-9223372036854775808)] ++ Int64Array.mk #[0]).data ==
  #[0, 0, (-9223372036854775808), 0]

-- Appending an array to itself, with and without room.
#guard
  let a := Int64Array.mk #[1, 2, 3]
  (a ++ a).data == #[1, 2, 3, 1, 2, 3]

#guard
  let a := (Int64Array.emptyWithCapacity 10).push 1 |>.push 2
  (a ++ a).data == #[1, 2, 1, 2]

-- Appending to a shared array must leave the original unchanged, with and without room. The
-- results are checked first so that they are computed while the original is still live.
#guard
  let a := (Int64Array.emptyWithCapacity 10).push 1
  let b := a ++ Int64Array.mk #[2, 3]
  let c := a ++ Int64Array.mk #[4]
  c.data == #[1, 4] && b.data == #[1, 2, 3] && a.data == #[1]

#guard
  let a := Int64Array.mk #[1]
  let b := a ++ Int64Array.mk #[2, 3]
  b.data == #[1, 2, 3] && a.data == #[1]

-- The right operand is never modified.
#guard
  let b := Int64Array.mk #[2, 3]
  let c := Int64Array.mk #[1] ++ b
  c.data == #[1, 2, 3] && b.data == #[2, 3]

-- Many appends to an exclusive array.
#guard Id.run do
  let mut a := Int64Array.empty
  let mut r : Array Int64 := #[]
  for i in [0:1000] do
    a := a ++ Int64Array.mk #[i.toInt64, (i * 7).toInt64, (-9223372036854775808)]
    r := r ++ #[i.toInt64, (i * 7).toInt64, (-9223372036854775808)]
  return a.data == r

-- Large arrays on both sides.
#guard
  let xs := (Array.range 50000).map Nat.toInt64
  let ys := (Array.range 50000).map fun i => (i * 3).toInt64
  (Int64Array.mk xs ++ Int64Array.mk ys).data == xs ++ ys

-- An exclusive array with room is appended to in place, and growth is geometric.
-- The array is built from a parameter so that it isn't extracted as a shared closed term.
@[noinline] def Int64Array.appendsInPlace (x : Int64) : Bool :=
  let a := (Int64Array.emptyWithCapacity 10).push x
  let p := rawAddr a
  let a := a ++ Int64Array.mk #[2, 3]
  rawAddr a == p && a.data == #[x, 2, 3]

@[noinline] def Int64Array.appendsToCopyWhenShared (x : Int64) : Bool :=
  let a := (Int64Array.emptyWithCapacity 10).push x
  let p := rawAddr a
  let b := a ++ Int64Array.mk #[2, 3]
  rawAddr b != p && b.data == #[x, 2, 3] && a.data == #[x]

#guard Int64Array.appendsInPlace 1
#guard Int64Array.appendsToCopyWhenShared 1

#guard rawCapacity ((Int64Array.emptyWithCapacity 10).push 1 ++ Int64Array.mk #[2, 3]) ≥ 10
#guard rawCapacity (Int64Array.mk #[1, 2, 3, 4] ++ Int64Array.mk #[5]) ≥ 8
#guard rawCapacity (Int64Array.mk #[1] ++ Int64Array.mk (Array.replicate 10 0)) ≥ 11
#guard rawElemSize (Int64Array.mk #[1] ++ Int64Array.mk #[2]) == (8 : UInt32)

/-! Equality -/

#guard Int64Array.mk #[1, 2, (-9223372036854775808)] == Int64Array.mk #[1, 2, (-9223372036854775808)]
#guard Int64Array.mk #[1, 2, (-9223372036854775808)] != Int64Array.mk #[1, 2, 0]
#guard Int64Array.mk #[1, 2] != Int64Array.mk #[1, 2, 0]
#guard Int64Array.mk #[1, 2, 0] != Int64Array.mk #[1, 2]
#guard Int64Array.empty == Int64Array.emptyWithCapacity 10
#guard (Int64Array.mk #[1, 2] ++ Int64Array.mk #[(-9223372036854775808)]) == Int64Array.mk #[1, 2, (-9223372036854775808)]
-- Capacity and leftover memory past the size don't matter.
#guard (Int64Array.emptyWithCapacity 100).push 1 == Int64Array.mk #[1]
#guard (Int64Array.mk #[1, 2, 3]).pop == Int64Array.mk #[1, 2]
#guard (Int64Array.mk (Array.replicate 100000 0)).set! 99999 (-9223372036854775808) !=
  Int64Array.mk (Array.replicate 100000 0)

/-! Decidable equality and hashing -/

#guard decide (Int64Array.mk #[1, 2, (-9223372036854775808)] = Int64Array.mk #[1, 2, (-9223372036854775808)])
#guard !decide (Int64Array.mk #[1, 2, (-9223372036854775808)] = Int64Array.mk #[1, 2, 0])
#guard hash (Int64Array.mk #[1, 2, (-9223372036854775808)]) == hash #[(1 : Int64), 2, (-9223372036854775808)]
#guard hash (Int64Array.empty) == hash (#[] : Array Int64)
#guard hash ((Int64Array.emptyWithCapacity 100).push 1) == hash (Int64Array.mk #[1])

/-! Iteration -/

#guard (Int64Array.mk #[1, 2, (-9223372036854775808)]).foldl (fun acc x => x :: acc) [] == [(-9223372036854775808), 2, 1]
#guard (Int64Array.mk #[1, 2, (-9223372036854775808)]).foldr (fun x acc => x :: acc) [] == [1, 2, (-9223372036854775808)]
#guard Int64Array.empty.foldl (fun acc x => x :: acc) [] == []
#guard Int64Array.empty.foldr (fun x acc => x :: acc) [] == []
#guard (Int64Array.mk #[1, 2, (-9223372036854775808)]).foldlM (m := Option)
  (fun acc x => if x == 2 then none else some (x :: acc)) [] == none
#guard (Int64Array.mk #[1, (-9223372036854775808)]).foldrM (m := Option) (fun x acc => some (x :: acc)) [] ==
  some [1, (-9223372036854775808)]

#guard Id.run do
  let mut r : List Int64 := []
  for x in Int64Array.mk #[1, 2, (-9223372036854775808)] do
    r := x :: r
  return r == [(-9223372036854775808), 2, 1]

#guard Id.run do
  let mut r : List Int64 := []
  for x in Int64Array.mk #[1, 2, 3, 4] do
    if x == 3 then break
    r := x :: r
  return r == [2, 1]

#guard
  let r : StateM (List Int64) Unit := (Int64Array.mk #[1, 2, (-9223372036854775808)]).forM fun x => modify (x :: ·)
  (r.run []).2 == [(-9223372036854775808), 2, 1]

#guard
  let xs := (Array.range 100000).map Nat.toInt64
  let f := fun (acc : List Int64) x => if x == 0 then x :: acc else acc
  (Int64Array.mk xs).foldl f [] == xs.foldl f []

#guard (Int64Array.mk #[1, 2, (-9223372036854775808)]).any (· == (-9223372036854775808))
#guard !(Int64Array.mk #[1, 2, 3]).any (· == (-9223372036854775808))
#guard (Int64Array.mk #[1, 2, 3]).all (· != (-9223372036854775808))
#guard !(Int64Array.mk #[1, (-9223372036854775808), 3]).all (· != (-9223372036854775808))
#guard !Int64Array.empty.any (fun _ => true) && Int64Array.empty.all (fun _ => false)
#guard (Int64Array.mk #[1, 2, (-9223372036854775808)]).contains (-9223372036854775808)
#guard !(Int64Array.mk #[1, 2, 3]).contains (-9223372036854775808)
#guard (Int64Array.mk (Array.replicate 100000 0) |>.set! 99999 (-9223372036854775808)).contains (-9223372036854775808)

/-! Removing elements -/

#guard Int64Array.empty.isEmpty && !(Int64Array.mk #[1]).isEmpty
#guard (Int64Array.mk #[1]).pop.isEmpty
#guard (Int64Array.mk #[1, 2, (-9223372036854775808)]).pop.data == #[1, 2]
#guard Int64Array.empty.pop.data == #[]
#guard ((Int64Array.mk #[1, 2, 3]).pop.push (-9223372036854775808)).data == #[1, 2, (-9223372036854775808)]
#guard (Int64Array.mk #[1, 2, (-9223372036854775808)]).back? == some (-9223372036854775808)
#guard Int64Array.empty.back? == none
#guard (Int64Array.mk #[1, 2, (-9223372036854775808)]).back! == (-9223372036854775808)
#guard (Int64Array.mk #[1, 2, (-9223372036854775808)]).back (by decide) == (-9223372036854775808)

-- Popping from a shared array must leave the original unchanged.
#guard
  let a := Int64Array.mk #[1, 2, 3]
  let b := a.pop
  b.data == #[1, 2] && a.data == #[1, 2, 3]

-- The array is built from a parameter so that it isn't extracted as a shared closed term.
@[noinline] def Int64Array.popsInPlace (x : Int64) : Bool :=
  let a := (Int64Array.mk #[x]).push x
  let p := rawAddr a
  let a := a.pop
  rawAddr a == p && a.data == #[x]

#guard Int64Array.popsInPlace 1

#guard ((Int64Array.mk #[1, 2, 3, (-9223372036854775808)]).extract 1 3).data == #[2, 3]
#guard ((Int64Array.mk #[1, 2, 3, (-9223372036854775808)]).extract 2 100).data == #[3, (-9223372036854775808)]
#guard ((Int64Array.mk #[1, 2, 3]).extract 0 3).data == #[1, 2, 3]
#guard ((Int64Array.mk #[1, 2, 3]).extract 2 1).data == #[]
#guard ((Int64Array.mk #[1, 2, 3]).extract 5 9).data == #[]
#guard ((Int64Array.mk #[1, 2, 3]).extract (2 ^ 70) (2 ^ 71)).data == #[]
#guard ((Int64Array.mk #[1, 2, 3]).extract 1 (2 ^ 70)).data == #[2, 3]
#guard
  let xs := (Array.range 100000).map Nat.toInt64
  ((Int64Array.mk xs).extract 70000 70010).data == xs.extract 70000 70010
#guard rawElemSize ((Int64Array.mk #[1, 2, 3]).extract 1 2) == (8 : UInt32)

-- The extracted array is independent of the original.
#guard
  let a := Int64Array.mk #[1, 2, 3]
  let b := (a.extract 0 2).set! 0 (-9223372036854775808)
  b.data == #[(-9223372036854775808), 2] && a.data == #[1, 2, 3]

/-! Building arrays -/

#guard (Int64Array.replicate 3 (-9223372036854775808)).data == #[(-9223372036854775808), (-9223372036854775808), (-9223372036854775808)]
#guard (Int64Array.replicate 0 1).data == #[]
#guard (Int64Array.replicate 100000 (-9223372036854775808)).data == Array.replicate 100000 (-9223372036854775808)
#guard (Int64Array.ofFn (n := 4) fun i => i.val.toInt64).data == #[0, 1, 2, 3]
#guard (Int64Array.ofFn (n := 0) fun i => i.val.toInt64).data == #[]
#guard rawElemSize (Int64Array.replicate 2 1) == (8 : UInt32)
#guard rawElemSize (Int64Array.ofFn (n := 2) fun _ => 1) == (8 : UInt32)

/-! Lemmas -/

example (a : Int64Array) (v : Int64) : (a.push v).pop = a := by simp [Int64Array.ext_iff]
example : (Int64Array.replicate 3 (-9223372036854775808))[1] = (-9223372036854775808) := by simp
example (a b : Int64Array) (h : 0 < a.size) : (a ++ b)[0]'(by simp; omega) = a[0] := by simp [h]
example (a : Int64Array) (i : Nat) (v : Int64) (h : i < a.size) :
    (a.set i v h)[i]'(by simpa) = v := by simp
example (a : Int64Array) : a.extract 0 a.size = a := by simp [Int64Array.ext_iff]
example (a : Int64Array) (v : Int64) : (a.push v).pop = a :=
  Int64Array.ext_getElem (by simp) (by simp_all)
