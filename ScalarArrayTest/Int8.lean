/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ScalarArray.Int8
import ScalarArrayTest.Util

open ScalarArray ScalarArrayTest

/-! Construction and conversion -/

#guard (Int8Array.mk #[1, 2, 3, (-128)]).data == #[1, 2, 3, (-128)]
#guard (Int8Array.mk #[1, 2, 3, (-128)]).toList == [1, 2, 3, (-128)]
#guard (Int8Array.mk #[]).data == #[]
#guard Int8Array.empty.data == #[]
#guard (∅ : Int8Array).data == #[]
#guard (default : Int8Array).data == #[]
#guard (Int8Array.emptyWithCapacity 100).data == #[]
#guard (Int8Array.mk (Array.range 1000 |>.map Nat.toInt8)).data == (Array.range 1000).map Nat.toInt8

/-! Size -/

#guard (Int8Array.mk #[1, 2, 3, (-128)]).size == 4
#guard (Int8Array.mk #[1, 2, 3, (-128)]).usize == 4
#guard Int8Array.empty.size == 0
#guard (Int8Array.emptyWithCapacity 100).size == 0

/-! Reading -/

#guard (Int8Array.mk #[1, 2, 3, (-128)])[0] == 1
#guard (Int8Array.mk #[1, 2, 3, (-128)])[3] == (-128)
#guard (Int8Array.mk #[1, 2, 3, (-128)])[(2 : USize)] == 3
#guard (Int8Array.mk #[1, 2, 3, (-128)]).get! 1 == 2
#guard (Int8Array.mk #[1, 2, 3, (-128)]).getD 2 7 == 3
#guard (Int8Array.mk #[1, 2, 3, (-128)]).getD 4 7 == 7
#guard (Int8Array.mk #[1, 2, 3, (-128)])[4]? == none
#guard (Int8Array.mk #[1, 2, 3, (-128)])[1]? == some 2

/-! Writing -/

#guard ((Int8Array.mk #[1, 2, 3]).set 1 42 (by decide)).data == #[1, 42, 3]
#guard ((Int8Array.mk #[1, 2, 3]).uset 2 42 (by simp)).data == #[1, 2, 42]
#guard ((Int8Array.mk #[1, 2, 3]).set! 0 (-128)).data == #[(-128), 2, 3]

-- Writing to a shared array must leave the original unchanged. The result is checked first so
-- that it is computed while the original is still live.
#guard
  let a := Int8Array.mk #[1, 2, 3]
  let b := a.set! 1 42
  b.data == #[1, 42, 3] && a.data == #[1, 2, 3]

-- Repeated writes to an exclusive array.
#guard Id.run do
  let mut a := Int8Array.mk (Array.replicate 1000 0)
  for i in [0:1000] do
    a := a.set! i (i * 3).toInt8
  return a.data == (Array.range 1000).map fun i => (i * 3).toInt8

/-! Pushing -/

#guard (Int8Array.empty.push 5 |>.push 6).data == #[5, 6]
#guard ((Int8Array.emptyWithCapacity 1).push 5 |>.push 6 |>.push 7).data == #[5, 6, 7]
#guard ((Int8Array.mk #[1, 2]).push 3).data == #[1, 2, 3]

-- Pushing past the capacity many times.
#guard Id.run do
  let mut a := Int8Array.empty
  for i in [0:10000] do
    a := a.push i.toInt8
  return a.size == 10000 && a.data == (Array.range 10000).map Nat.toInt8

-- Pushing to a shared array must leave the original unchanged. The results are checked first so
-- that they are computed while the original is still live.
#guard
  let a := (Int8Array.emptyWithCapacity 10).push 1
  let b := a.push 2
  let c := a.push 3
  c.data == #[1, 3] && b.data == #[1, 2] && a.data == #[1]

/-! Printing -/

#guard toString (Int8Array.mk #[1, 2]) == "Int8Array.mk " ++ toString #[(1 : Int8), 2]
#guard reprStr (Int8Array.mk #[1, 2]) == "Int8Array.mk " ++ reprStr #[(1 : Int8), 2]

/-! Every index, through both `Nat` and `USize` indices -/

#guard
  let a := Int8Array.mk ((Array.range 300).map Nat.toInt8)
  (List.range 300).all fun i =>
    a[i]! == i.toInt8 && a.getD i 0 == i.toInt8 && a.get! i == i.toInt8 &&
      (if h : i.toUSize.toNat < a.size then a[i.toUSize] == i.toInt8 else false)

/-! Writes don't touch neighbouring elements -/

#guard ((Int8Array.mk #[0, 0, 0]).set! 1 (-128)).data == #[0, (-128), 0]
#guard ((Int8Array.mk #[(-128), (-128), (-128)]).set! 1 0).data == #[(-128), 0, (-128)]
#guard ((Int8Array.mk #[0, 0, 0]).push (-128) |>.push 0).data == #[0, 0, 0, (-128), 0]

/-! Indices beyond 16 bits, and huge `Nat` indices -/

#guard
  let a := (Int8Array.mk (Array.replicate 100000 0)).set! 99999 (-128) |>.set! 70000 1
  a.size == 100000 && a[99999]! == (-128) && a[70000]! == 1 && a[99998]! == 0 &&
    a[70000 % 65536]! == 0 && a.data[99999]! == (-128) && a.data[70000]! == 1 &&
    (if h : (70000 : USize).toNat < a.size then a[(70000 : USize)] == 1 else false)

#guard (Int8Array.mk #[1, 2, 3])[2 ^ 70]? == none
#guard (Int8Array.mk #[1, 2, 3]).getD (2 ^ 70) 7 == 7

/-! Pushing onto a shared array that is at full capacity -/

#guard
  let a := Int8Array.mk #[1]
  let b := a.push 2
  b.data == #[1, 2] && a.data == #[1]

#guard
  let a := Int8Array.mk #[]
  let b := a.push 2
  b.data == #[2] && a.data == #[]

/-! Conversions don't alias -/

#guard
  let a := #[(1 : Int8), 2, 3]
  let b := (Int8Array.mk a).set! 0 (-128)
  b.data == #[(-128), 2, 3] && a == #[1, 2, 3]

#guard
  let a := Int8Array.mk #[1, 2, 3]
  let d := a.data.set! 0 (-128)
  d == #[(-128), 2, 3] && a.data == #[1, 2, 3]

/-! Runtime representation -/

#guard rawElemSize (Int8Array.mk #[1, 2, 3]) == (1 : UInt32)
#guard rawElemSize (Int8Array.emptyWithCapacity 10) == (1 : UInt32)
#guard rawElemSize (Int8Array.empty.push 1) == (1 : UInt32)
#guard rawElemSize ((Int8Array.mk #[1]).push 2) == (1 : UInt32)
#guard rawCapacity (Int8Array.emptyWithCapacity 100) ≥ 100
#guard rawCapacity (Int8Array.mk #[1, 2, 3]) ≥ 3
-- Growth is geometric, so pushing is amortized constant time.
#guard rawCapacity ((Int8Array.mk #[1, 2, 3, 4]).push 5) ≥ 8


/-! Appending -/

#guard (Int8Array.mk #[1, 2] ++ Int8Array.mk #[3, (-128)]).data == #[1, 2, 3, (-128)]
#guard ((Int8Array.mk #[1, 2]).append (Int8Array.mk #[3])).data == #[1, 2, 3]
#guard (Int8Array.mk #[1, 2] ++ Int8Array.empty).data == #[1, 2]
#guard (Int8Array.empty ++ Int8Array.mk #[1, 2]).data == #[1, 2]
#guard (Int8Array.empty ++ Int8Array.empty).data == #[]
#guard (Int8Array.mk #[0, 0] ++ Int8Array.mk #[(-128)] ++ Int8Array.mk #[0]).data ==
  #[0, 0, (-128), 0]

-- Appending an array to itself, with and without room.
#guard
  let a := Int8Array.mk #[1, 2, 3]
  (a ++ a).data == #[1, 2, 3, 1, 2, 3]

#guard
  let a := (Int8Array.emptyWithCapacity 10).push 1 |>.push 2
  (a ++ a).data == #[1, 2, 1, 2]

-- Appending to a shared array must leave the original unchanged, with and without room. The
-- results are checked first so that they are computed while the original is still live.
#guard
  let a := (Int8Array.emptyWithCapacity 10).push 1
  let b := a ++ Int8Array.mk #[2, 3]
  let c := a ++ Int8Array.mk #[4]
  c.data == #[1, 4] && b.data == #[1, 2, 3] && a.data == #[1]

#guard
  let a := Int8Array.mk #[1]
  let b := a ++ Int8Array.mk #[2, 3]
  b.data == #[1, 2, 3] && a.data == #[1]

-- The right operand is never modified.
#guard
  let b := Int8Array.mk #[2, 3]
  let c := Int8Array.mk #[1] ++ b
  c.data == #[1, 2, 3] && b.data == #[2, 3]

-- Many appends to an exclusive array.
#guard Id.run do
  let mut a := Int8Array.empty
  let mut r : Array Int8 := #[]
  for i in [0:1000] do
    a := a ++ Int8Array.mk #[i.toInt8, (i * 7).toInt8, (-128)]
    r := r ++ #[i.toInt8, (i * 7).toInt8, (-128)]
  return a.data == r

-- Large arrays on both sides.
#guard
  let xs := (Array.range 50000).map Nat.toInt8
  let ys := (Array.range 50000).map fun i => (i * 3).toInt8
  (Int8Array.mk xs ++ Int8Array.mk ys).data == xs ++ ys

-- An exclusive array with room is appended to in place, and growth is geometric.
-- The array is built from a parameter so that it isn't extracted as a shared closed term.
@[noinline] def Int8Array.appendsInPlace (x : Int8) : Bool :=
  let a := (Int8Array.emptyWithCapacity 10).push x
  let p := rawAddr a
  let a := a ++ Int8Array.mk #[2, 3]
  rawAddr a == p && a.data == #[x, 2, 3]

@[noinline] def Int8Array.appendsToCopyWhenShared (x : Int8) : Bool :=
  let a := (Int8Array.emptyWithCapacity 10).push x
  let p := rawAddr a
  let b := a ++ Int8Array.mk #[2, 3]
  rawAddr b != p && b.data == #[x, 2, 3] && a.data == #[x]

#guard Int8Array.appendsInPlace 1
#guard Int8Array.appendsToCopyWhenShared 1

#guard rawCapacity ((Int8Array.emptyWithCapacity 10).push 1 ++ Int8Array.mk #[2, 3]) ≥ 10
#guard rawCapacity (Int8Array.mk #[1, 2, 3, 4] ++ Int8Array.mk #[5]) ≥ 8
#guard rawCapacity (Int8Array.mk #[1] ++ Int8Array.mk (Array.replicate 10 0)) ≥ 11
#guard rawElemSize (Int8Array.mk #[1] ++ Int8Array.mk #[2]) == (1 : UInt32)

/-! Equality -/

#guard Int8Array.mk #[1, 2, (-128)] == Int8Array.mk #[1, 2, (-128)]
#guard Int8Array.mk #[1, 2, (-128)] != Int8Array.mk #[1, 2, 0]
#guard Int8Array.mk #[1, 2] != Int8Array.mk #[1, 2, 0]
#guard Int8Array.mk #[1, 2, 0] != Int8Array.mk #[1, 2]
#guard Int8Array.empty == Int8Array.emptyWithCapacity 10
#guard (Int8Array.mk #[1, 2] ++ Int8Array.mk #[(-128)]) == Int8Array.mk #[1, 2, (-128)]
-- Capacity and leftover memory past the size don't matter.
#guard (Int8Array.emptyWithCapacity 100).push 1 == Int8Array.mk #[1]
#guard (Int8Array.mk #[1, 2, 3]).pop == Int8Array.mk #[1, 2]
#guard (Int8Array.mk (Array.replicate 100000 0)).set! 99999 (-128) !=
  Int8Array.mk (Array.replicate 100000 0)

/-! Decidable equality and hashing -/

#guard decide (Int8Array.mk #[1, 2, (-128)] = Int8Array.mk #[1, 2, (-128)])
#guard !decide (Int8Array.mk #[1, 2, (-128)] = Int8Array.mk #[1, 2, 0])
#guard hash (Int8Array.mk #[1, 2, (-128)]) == hash #[(1 : Int8), 2, (-128)]
#guard hash (Int8Array.empty) == hash (#[] : Array Int8)
#guard hash ((Int8Array.emptyWithCapacity 100).push 1) == hash (Int8Array.mk #[1])

/-! Iteration -/

#guard (Int8Array.mk #[1, 2, (-128)]).foldl (fun acc x => x :: acc) [] == [(-128), 2, 1]
#guard (Int8Array.mk #[1, 2, (-128)]).foldr (fun x acc => x :: acc) [] == [1, 2, (-128)]
#guard Int8Array.empty.foldl (fun acc x => x :: acc) [] == []
#guard Int8Array.empty.foldr (fun x acc => x :: acc) [] == []
#guard (Int8Array.mk #[1, 2, (-128)]).foldlM (m := Option)
  (fun acc x => if x == 2 then none else some (x :: acc)) [] == none
#guard (Int8Array.mk #[1, (-128)]).foldrM (m := Option) (fun x acc => some (x :: acc)) [] ==
  some [1, (-128)]

#guard Id.run do
  let mut r : List Int8 := []
  for x in Int8Array.mk #[1, 2, (-128)] do
    r := x :: r
  return r == [(-128), 2, 1]

#guard Id.run do
  let mut r : List Int8 := []
  for x in Int8Array.mk #[1, 2, 3, 4] do
    if x == 3 then break
    r := x :: r
  return r == [2, 1]

#guard
  let r : StateM (List Int8) Unit := (Int8Array.mk #[1, 2, (-128)]).forM fun x => modify (x :: ·)
  (r.run []).2 == [(-128), 2, 1]

#guard
  let xs := (Array.range 100000).map Nat.toInt8
  let f := fun (acc : List Int8) x => if x == 0 then x :: acc else acc
  (Int8Array.mk xs).foldl f [] == xs.foldl f []

#guard (Int8Array.mk #[1, 2, (-128)]).any (· == (-128))
#guard !(Int8Array.mk #[1, 2, 3]).any (· == (-128))
#guard (Int8Array.mk #[1, 2, 3]).all (· != (-128))
#guard !(Int8Array.mk #[1, (-128), 3]).all (· != (-128))
#guard !Int8Array.empty.any (fun _ => true) && Int8Array.empty.all (fun _ => false)
#guard (Int8Array.mk #[1, 2, (-128)]).contains (-128)
#guard !(Int8Array.mk #[1, 2, 3]).contains (-128)
#guard (Int8Array.mk (Array.replicate 100000 0) |>.set! 99999 (-128)).contains (-128)

/-! Removing elements -/

#guard Int8Array.empty.isEmpty && !(Int8Array.mk #[1]).isEmpty
#guard (Int8Array.mk #[1]).pop.isEmpty
#guard (Int8Array.mk #[1, 2, (-128)]).pop.data == #[1, 2]
#guard Int8Array.empty.pop.data == #[]
#guard ((Int8Array.mk #[1, 2, 3]).pop.push (-128)).data == #[1, 2, (-128)]
#guard (Int8Array.mk #[1, 2, (-128)]).back? == some (-128)
#guard Int8Array.empty.back? == none
#guard (Int8Array.mk #[1, 2, (-128)]).back! == (-128)
#guard (Int8Array.mk #[1, 2, (-128)]).back (by decide) == (-128)

-- Popping from a shared array must leave the original unchanged.
#guard
  let a := Int8Array.mk #[1, 2, 3]
  let b := a.pop
  b.data == #[1, 2] && a.data == #[1, 2, 3]

-- The array is built from a parameter so that it isn't extracted as a shared closed term.
@[noinline] def Int8Array.popsInPlace (x : Int8) : Bool :=
  let a := (Int8Array.mk #[x]).push x
  let p := rawAddr a
  let a := a.pop
  rawAddr a == p && a.data == #[x]

#guard Int8Array.popsInPlace 1

#guard (Int8Array.mk #[1, 0, (-128), 0, 0]).popWhile (· == 0) == Int8Array.mk #[1, 0, (-128)]
#guard (Int8Array.mk #[1, 0, (-128)]).popWhile (· == 0) == Int8Array.mk #[1, 0, (-128)]
#guard (Int8Array.mk #[0, 0]).popWhile (· == 0) == Int8Array.empty
#guard Int8Array.empty.popWhile (· == 0) == Int8Array.empty

-- Popping several elements from an exclusive array.
@[noinline] def Int8Array.popsWhileInPlace (x : Int8) : Bool :=
  let a := (Int8Array.mk #[x]).push 0 |>.push 0
  let p := rawAddr a
  let a := a.popWhile (· == 0)
  rawAddr a == p && a.data == #[x]

#guard Int8Array.popsWhileInPlace 1

example (p : Int8 → Bool) (a : Int8Array) : (a.popWhile p).data = a.data.popWhile p := by simp

#guard ((Int8Array.mk #[1, 2, 3, (-128)]).extract 1 3).data == #[2, 3]
#guard ((Int8Array.mk #[1, 2, 3, (-128)]).extract 2 100).data == #[3, (-128)]
#guard ((Int8Array.mk #[1, 2, 3]).extract 0 3).data == #[1, 2, 3]
#guard ((Int8Array.mk #[1, 2, 3]).extract 2 1).data == #[]
#guard ((Int8Array.mk #[1, 2, 3]).extract 5 9).data == #[]
#guard ((Int8Array.mk #[1, 2, 3]).extract (2 ^ 70) (2 ^ 71)).data == #[]
#guard ((Int8Array.mk #[1, 2, 3]).extract 1 (2 ^ 70)).data == #[2, 3]
#guard
  let xs := (Array.range 100000).map Nat.toInt8
  ((Int8Array.mk xs).extract 70000 70010).data == xs.extract 70000 70010
#guard rawElemSize ((Int8Array.mk #[1, 2, 3]).extract 1 2) == (1 : UInt32)

-- The extracted array is independent of the original.
#guard
  let a := Int8Array.mk #[1, 2, 3]
  let b := (a.extract 0 2).set! 0 (-128)
  b.data == #[(-128), 2] && a.data == #[1, 2, 3]

/-! Building arrays -/

#guard (Int8Array.replicate 3 (-128)).data == #[(-128), (-128), (-128)]
#guard (Int8Array.replicate 0 1).data == #[]
#guard (Int8Array.replicate 100000 (-128)).data == Array.replicate 100000 (-128)
#guard (Int8Array.ofFn (n := 4) fun i => i.val.toInt8).data == #[0, 1, 2, 3]
#guard (Int8Array.ofFn (n := 0) fun i => i.val.toInt8).data == #[]
#guard rawElemSize (Int8Array.replicate 2 1) == (1 : UInt32)
#guard rawElemSize (Int8Array.ofFn (n := 2) fun _ => 1) == (1 : UInt32)

/-! Lemmas -/

example (a : Int8Array) (v : Int8) : (a.push v).pop = a := by simp [Int8Array.ext_iff]
example : (Int8Array.replicate 3 (-128))[1] = (-128) := by simp
example (a b : Int8Array) (h : 0 < a.size) : (a ++ b)[0]'(by simp; omega) = a[0] := by simp [h]
example (a : Int8Array) (i : Nat) (v : Int8) (h : i < a.size) :
    (a.set i v h)[i]'(by simpa) = v := by simp
example (a : Int8Array) : a.extract 0 a.size = a := by simp
example (a : Int8Array) (v : Int8) : (a.push v).pop = a :=
  Int8Array.ext_getElem (by simp) (by simp_all)

/-! Default bounds proofs -/

#guard (Int8Array.mk #[1, 2, (-128)]).get 2 == (-128)
#guard (Int8Array.mk #[1, 2, (-128)]).uget 2 == (-128)
#guard ((Int8Array.mk #[1, 2, 3]).set 1 (-128)).data == #[1, (-128), 3]
#guard ((Int8Array.mk #[1, 2, 3]).uset 1 (-128)).data == #[1, (-128), 3]

/-! `set!` leaves the array unchanged when the index is out of bounds, like `ByteArray.set!`. -/

#guard ((Int8Array.mk #[1, 2, 3]).set! 3 (-128)).data == #[1, 2, 3]
#guard ((Int8Array.mk #[1, 2, 3]).set! (2 ^ 70) (-128)).data == #[1, 2, 3]

/-! Folds over part of an array -/

#guard (Int8Array.mk #[1, 2, 3, (-128)]).foldl (fun acc x => x :: acc) [] 1 3 == [3, 2]
#guard (Int8Array.mk #[1, 2, 3, (-128)]).foldl (fun acc x => x :: acc) [] 2 == [(-128), 3]
#guard (Int8Array.mk #[1, 2, 3, (-128)]).foldl (fun acc x => x :: acc) [] 1 100 == [(-128), 3, 2]
#guard (Int8Array.mk #[1, 2, 3, (-128)]).foldl (fun acc x => x :: acc) [] 3 1 == []
#guard (Int8Array.mk #[1, 2, 3, (-128)]).foldl (fun acc x => x :: acc) [] 9 12 == []
#guard (Int8Array.mk #[1, 2, 3]).foldlM (m := Option)
  (fun acc x => if x == 1 then none else some (x :: acc)) [] 1 == some [3, 2]

/-! Copying slices -/

#guard
  let src := Int8Array.mk #[10, 11, 12, (-128)]
  let dest := Int8Array.mk #[1, 2, 3, 4, 5]
  (src.copySlice 1 dest 2 2).data == #[1, 2, 11, 12, 5] &&
  (src.copySlice 1 dest 4 3).data == #[1, 2, 3, 4, 11, 12, (-128)] &&
  (src.copySlice 0 dest 9 2).data == #[1, 2, 3, 4, 5, 10, 11] &&
  (src.copySlice 9 dest 1 2).data == #[1, 2, 3, 4, 5] &&
  (src.copySlice 2 dest 0 10).data == #[12, (-128), 3, 4, 5] &&
  (src.copySlice 0 dest 0 0).data == #[1, 2, 3, 4, 5] &&
  (src.copySlice 0 Int8Array.empty 0 4).data == #[10, 11, 12, (-128)] &&
  dest.data == #[1, 2, 3, 4, 5] && src.data == #[10, 11, 12, (-128)]

-- Copying from an array into itself.
#guard
  let a := Int8Array.mk #[1, 2, 3, (-128)]
  (a.copySlice 0 a 2 4).data == #[1, 2, 1, 2, 3, (-128)]

#guard
  let xs := (Array.range 100000).map Nat.toInt8
  let a := Int8Array.mk xs
  (a.copySlice 70000 (Int8Array.replicate 10 0) 5 10).data ==
    Array.replicate 5 0 ++ xs.extract 70000 70010

#guard rawElemSize ((Int8Array.mk #[1]).copySlice 0 Int8Array.empty 0 1) == (1 : UInt32)

@[noinline] def Int8Array.copiesSliceInPlace (x : Int8) : Bool :=
  let dest := (Int8Array.emptyWithCapacity 10).push x |>.push x |>.push x
  let p := rawAddr dest
  let dest := (Int8Array.mk #[(-128), (-128)]).copySlice 0 dest 1 2
  rawAddr dest == p && dest.data == #[x, (-128), (-128)]

@[noinline] def Int8Array.copySliceGrowth (x : Int8) : Bool :=
  let dest := (Int8Array.mk #[x, x, x, x])
  rawCapacity ((Int8Array.mk #[x]).copySlice 0 dest 4 1 (exact := false)) ≥ 8 &&
    rawCapacity ((Int8Array.mk #[x]).copySlice 0 dest 4 1) == 5

#guard Int8Array.copiesSliceInPlace 1
#guard Int8Array.copySliceGrowth 1

/-! Linearity markers -/

#guard ((Int8Array.mk #[1, 2]).markLinear.push (-128)).data == #[1, 2, (-128)]
#guard ((Int8Array.mk #[1]).propagateMark (Int8Array.mk #[2, (-128)])).data == #[2, (-128)]

/-! Search -/

#guard (Int8Array.mk #[1, 2, (-128), 2]).findIdx? (· == 2) == some 1
#guard (Int8Array.mk #[1, 2, (-128), 2]).findIdx? (· == 2) 2 == some 3
#guard (Int8Array.mk #[1, 2, (-128), 2]).findIdx? (· == 3) == none
#guard (Int8Array.mk #[1, 2, (-128), 2]).findIdx? (· == 1) 9 == none
#guard ((Int8Array.mk #[1, 2, (-128), 2]).findFinIdx? (· == (-128))).map (·.val) == some 2

/-! Lists -/

#guard (Int8Array.ofList [1, 2, (-128)]).data == #[1, 2, (-128)]
#guard (Int8Array.ofList []).data == #[]
#guard [1, 2, (-128)].toInt8Array == Int8Array.mk #[1, 2, (-128)]
#guard (Int8Array.ofList ((List.range 100000).map Nat.toInt8)).data ==
  (Array.range 100000).map Nat.toInt8
#guard rawElemSize (Int8Array.ofList [1, 2]) == (1 : UInt32)

/-! More lemmas -/

example (a b c : Int8Array) : a ++ b ++ c = a ++ (b ++ c) := Int8Array.append_assoc ..
example (a : Int8Array) : a ++ ∅ = a := by simp
example (a b : Int8Array) : (a ++ b).extract 0 a.size = a := by simp
example (a : Int8Array) (i : Nat) (v : Int8) : (a.set! i v).size = a.size := by simp
example (l : List Int8) : (Int8Array.ofList l).toList = l := by simp
example (a : Int8Array) : Int8Array.ofList a.toList = a := by simp

/-! Slices -/

#guard
  let a := Int8Array.mk #[1, 2, 3, (-128)]
  let s := a[1...3]
  s.size == 2 && s[0]! == 2 && s[1]! == 3 && s.getD 2 7 == 7 && s.copy == Int8Array.mk #[2, 3] &&
    s.toList == [2, 3] && s.toArray == #[2, 3]

#guard
  let a := Int8Array.mk #[1, 2, 3, (-128)]
  a[1...=3].toList == [2, 3, (-128)] && a[*...2].toList == [1, 2] && a[2...*].toList == [3, (-128)] &&
    a[*...*].toList == [1, 2, 3, (-128)] && a[0<...2].toList == [2] &&
    a[0<...=2].toList == [2, 3] && a[*...=1].toList == [1, 2] && a[1<...*].toList == [3, (-128)]

-- Bounds are clamped.
#guard
  let a := Int8Array.mk #[1, 2, 3, (-128)]
  a[2...100].toList == [3, (-128)] && a[3...1].size == 0 && a[9...12].size == 0 &&
    (a.toSlice 1 (2 ^ 70)).toList == [2, 3, (-128)]

-- Slices of slices.
#guard
  let s := (Int8Array.mk #[1, 2, 3, (-128)])[1...4]
  s[1...2].toList == [3] && s[0...100].toList == [2, 3, (-128)] && s[*...*].toList == [2, 3, (-128)] &&
    s[2...*].toList == [(-128)] && s[5...6].size == 0

#guard
  let s := (Int8Array.mk #[1, 2, 3, (-128)])[1...4]
  s.popFront.toList == [3, (-128)] && s.popFront.popFront.popFront.popFront.size == 0

#guard (∅ : Int8Array.Slice).size == 0 && (default : Int8Array.Slice).toList == []

-- An array coerces to the slice of all its elements.
#guard
  let s : Int8Array.Slice := Int8Array.mk #[1, 2, (-128)]
  s.toList == [1, 2, (-128)] && s.start == 0

-- A slice does not coerce back to an array, since that would copy.
example (s : Int8Array.Slice) : Int8Array := s.copy

#guard Id.run do
  let mut r : List Int8 := []
  for x in (Int8Array.mk #[1, 2, 3, (-128)])[1...*] do
    r := x :: r
  return r == [(-128), 3, 2]

#guard (Int8Array.mk #[1, 2, 3, (-128)])[1...*].foldl (fun acc x => x :: acc) [] == [(-128), 3, 2]

#guard
  let xs := (Array.range 100000).map Nat.toInt8
  let s := (Int8Array.mk xs)[70000...70010]
  s.toArray == xs.extract 70000 70010 && s.copy.data == xs.extract 70000 70010

#guard toString (Int8Array.mk #[1, 2, 3])[1...*] == toString (Int8Array.mk #[2, 3])

-- Taking a slice doesn't copy the array.
@[noinline] def Int8Array.slicesWithoutCopying (x : Int8) : Bool :=
  let a := Int8Array.mk #[x, 2, 3]
  let p := rawAddr a
  rawAddr a[1...2].array == p

#guard Int8Array.slicesWithoutCopying 1

example (s : Int8Array.Slice) : s.copy.size = s.size := by simp

/-! Slice API -/

#guard
  let s := (Int8Array.mk #[1, 2, 3, (-128), 2])[1...5]
  s.foldr (fun x acc => x :: acc) [] == [2, 3, (-128), 2] &&
    s.foldl (fun acc x => x :: acc) [] == [2, (-128), 3, 2] &&
    s.any (· == (-128)) && !s.any (· == 1) && s.all (· != 1) && !s.all (· == 2) &&
    s.contains (-128) && !s.contains 1 && s.count (· == 2) == 2 &&
    s.find? (· > 2) == some 3 && s.findRev? (· != (-128)) == some 2 && s.findRev? (· == 1) == none

#guard (Int8Array.mk #[1, 2, 3])[1...1].foldr (fun x acc => x :: acc) [] == []
#guard (Int8Array.mk #[1, 2, 3])[3...*].find? (fun _ => true) == none

#guard
  let s := (Int8Array.mk #[1, 2, 3, (-128)])[1...*]
  let r : StateM (List Int8) Unit := s.forRevM fun x => modify (x :: ·)
  (r.run []).2 == [2, 3, (-128)]

#guard Id.run ((Int8Array.mk #[1, 2, (-128)])[*...*].findSomeRevM?
  (fun x => pure (if x == 2 then some x else none))) == some 2

/-! The `Std.Iterators` API on arrays and slices -/

#guard (Int8Array.mk #[1, 2, 3]).iter.toList == [1, 2, 3]
#guard ((Int8Array.mk #[1, 2, 3]).iter.map (· * 2)).toInt8Array == Int8Array.mk #[2, 4, 6]
#guard ((Int8Array.mk #[1, 2, 3, (-128)]).iter.filter (· != 2)).toInt8Array ==
  Int8Array.mk #[1, 3, (-128)]
#guard ((Int8Array.mk #[1, 2, 3, (-128)]).iter.take 2).toInt8Array == Int8Array.mk #[1, 2]
#guard ((Int8Array.mk #[1, 2, 3, (-128)]).iter.drop 2).toInt8Array == Int8Array.mk #[3, (-128)]
#guard (((Int8Array.mk #[1, 2, 3]).iter.zip (Int8Array.mk #[(-128), 5]).iter).map
  fun (x, y) => x + y).toInt8Array == Int8Array.mk #[1 + (-128), 7]
#guard ((Int8Array.mk #[1, 2, 3, (-128)])[1...3].iter.map (· + 1)).toInt8Array ==
  Int8Array.mk #[3, 4]
#guard (Int8Array.mk #[1, 2, 3]).iter.length == 3
#guard Int8Array.empty.iter.toInt8Array == Int8Array.empty
#guard
  let xs := (Array.range 100000).map Nat.toInt8
  ((Int8Array.mk xs).iter.map (· + 1)).toInt8Array.data == xs.map (· + 1)
#guard rawElemSize ((Int8Array.mk #[1]).iter.toInt8Array) == (1 : UInt32)
#guard ((Int8Array.mk #[1, 2, 3]).iter.toInt8ArrayWithCapacity 100) == Int8Array.mk #[1, 2, 3]
#guard rawCapacity ((Int8Array.mk #[1, 2, 3]).iter.toInt8ArrayWithCapacity 100) ≥ 100
