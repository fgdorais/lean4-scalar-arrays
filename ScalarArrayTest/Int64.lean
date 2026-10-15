/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import ScalarArray.Int64
import ScalarArrayTest.Util
meta import ScalarArray.Int64
meta import ScalarArrayTest.Util

open ScalarArray ScalarArrayTest

/-- A test value at the edge of the element type's range. -/
private abbrev big : Int64 := -9223372036854775808

/-- The size of an element in bytes. -/
private abbrev elemSize : UInt32 := 8

/-! Construction and conversion -/

#guard (Int64Array.mk #[1, 2, 3, big]).data == #[1, 2, 3, big]
#guard (Int64Array.mk #[1, 2, 3, big]).toList == [1, 2, 3, big]
#guard (Int64Array.mk #[]).data == #[]
#guard Int64Array.empty.data == #[]
#guard (∅ : Int64Array).data == #[]
#guard (default : Int64Array).data == #[]
#guard (Int64Array.emptyWithCapacity 100).data == #[]
#guard (Int64Array.mk (Array.range 1000 |>.map Nat.toInt64)).data ==
  (Array.range 1000).map Nat.toInt64

/-! Size -/

#guard (Int64Array.mk #[1, 2, 3, big]).size == 4
#guard (Int64Array.mk #[1, 2, 3, big]).usize == 4
#guard Int64Array.empty.size == 0
#guard (Int64Array.emptyWithCapacity 100).size == 0

/-! Reading -/

#guard (Int64Array.mk #[1, 2, 3, big])[0] == 1
#guard (Int64Array.mk #[1, 2, 3, big])[3] == big
#guard (Int64Array.mk #[1, 2, 3, big])[(2 : USize)] == 3
#guard (Int64Array.mk #[1, 2, 3, big]).get! 1 == 2
#guard (Int64Array.mk #[1, 2, 3, big]).getD 2 7 == 3
#guard (Int64Array.mk #[1, 2, 3, big]).getD 4 7 == 7
#guard (Int64Array.mk #[1, 2, 3, big])[4]? == none
#guard (Int64Array.mk #[1, 2, 3, big])[1]? == some 2

/-! Writing -/

#guard ((Int64Array.mk #[1, 2, 3]).set 1 42 (by decide)).data == #[1, 42, 3]
#guard ((Int64Array.mk #[1, 2, 3]).uset 2 42 (by simp)).data == #[1, 2, 42]
#guard ((Int64Array.mk #[1, 2, 3]).set! 0 big).data == #[big, 2, 3]

-- Writing to a shared array must leave the original unchanged. The result is checked first so
-- that it is computed while the original is still live.
#guard
  let a := Int64Array.mk #[1, 2, 3]
  let b := a.set! 1 42
  b.data == #[1, 42, 3] && a.data == #[1, 2, 3]
#guard
  let a := Int64Array.mk #[1, 2, 3]
  let b := a.uset 0 big (by simp [a])
  b.data == #[big, 2, 3] && a.data == #[1, 2, 3]
#guard
  let a := Int64Array.mk #[1, 2, 3]
  let b := a.set 2 big (by simp [a])
  b.data == #[1, 2, big] && a.data == #[1, 2, 3]

-- `foldInPlace` shifts a range right by one, inserting the initial accumulator.
#guard
  let r := (Int64Array.mk #[1, 2, 3, 4]).foldInPlace 1 2 9 (fun _ _ x b => (b, x)) (by simp)
  r.1.data == #[1, 9, 2, 4] && r.2 == 3

-- `foldInPlace` on a shared array must leave the original unchanged, and `f` must see the
-- elements of the original even when it reads them from the array itself.
#guard
  let a := Int64Array.mk #[1, 2, 3, 4]
  let r := a.foldInPlace 0 4 9 (fun _ _ x b => (b, x)) (by simp [a])
  r.1.data == #[9, 1, 2, 3] && a.data == #[1, 2, 3, 4]
#guard
  let a := Int64Array.mk #[1, 2, 3, 4]
  let r := a.foldInPlace 1 3 0 (fun k _ _ b => (a[k.toNat]!, b)) (by simp [a])
  r.1.data == #[1, 1, 2, 3]

-- `foldInPlaceThen` hands the array and the last accumulator to `g`, here to store it.
#guard
  let r := (Int64Array.mk #[1, 2, 3, 4]).foldInPlaceThen 0 3 9 (fun _ _ x b => (b, x))
    (fun a b => a.set! 3 b) (by simp)
  r.data == #[9, 1, 2, 3]
#guard
  let a := Int64Array.mk #[1, 2, 3, 4]
  let r := a.foldInPlaceThen 1 2 9 (fun _ _ x b => (b, x)) Prod.mk (by simp [a])
  r.1.data == #[1, 9, 2, 4] && r.2 == 3 && a.data == #[1, 2, 3, 4]

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

#guard ((Int64Array.mk #[0, 0, 0]).set! 1 big).data == #[0, big, 0]
#guard ((Int64Array.mk #[big, big, big]).set! 1 0).data == #[big, 0, big]
#guard ((Int64Array.mk #[0, 0, 0]).push big |>.push 0).data == #[0, 0, 0, big, 0]

/-! Indices beyond 16 bits, and huge `Nat` indices -/

#guard
  let a := (Int64Array.mk (Array.replicate 100000 0)).set! 99999 big |>.set! 70000 1
  a.size == 100000 && a[99999]! == big && a[70000]! == 1 && a[99998]! == 0 &&
    a[70000 % 65536]! == 0 && a.data[99999]! == big && a.data[70000]! == 1 &&
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
  let b := (Int64Array.mk a).set! 0 big
  b.data == #[big, 2, 3] && a == #[1, 2, 3]

#guard
  let a := Int64Array.mk #[1, 2, 3]
  let d := a.data.set! 0 big
  d == #[big, 2, 3] && a.data == #[1, 2, 3]

/-! Runtime representation -/

#guard rawElemSize (Int64Array.mk #[1, 2, 3]) == elemSize
#guard rawElemSize (Int64Array.emptyWithCapacity 10) == elemSize
#guard rawElemSize (Int64Array.empty.push 1) == elemSize
#guard rawElemSize ((Int64Array.mk #[1]).push 2) == elemSize
#guard rawCapacity (Int64Array.emptyWithCapacity 100) ≥ 100
#guard rawCapacity (Int64Array.mk #[1, 2, 3]) ≥ 3
-- Growth is geometric, so pushing is amortized constant time.
#guard rawCapacity ((Int64Array.mk #[1, 2, 3, 4]).push 5) ≥ 8


/-! Appending -/

#guard (Int64Array.mk #[1, 2] ++ Int64Array.mk #[3, big]).data == #[1, 2, 3, big]
#guard ((Int64Array.mk #[1, 2]).append (Int64Array.mk #[3])).data == #[1, 2, 3]
#guard (Int64Array.mk #[1, 2] ++ Int64Array.empty).data == #[1, 2]
#guard (Int64Array.empty ++ Int64Array.mk #[1, 2]).data == #[1, 2]
#guard (Int64Array.empty ++ Int64Array.empty).data == #[]
#guard (Int64Array.mk #[0, 0] ++ Int64Array.mk #[big] ++ Int64Array.mk #[0]).data ==
  #[0, 0, big, 0]

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
    a := a ++ Int64Array.mk #[i.toInt64, (i * 7).toInt64, big]
    r := r ++ #[i.toInt64, (i * 7).toInt64, big]
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
#guard rawElemSize (Int64Array.mk #[1] ++ Int64Array.mk #[2]) == elemSize

/-! Equality -/

#guard Int64Array.mk #[1, 2, big] == Int64Array.mk #[1, 2, big]
#guard Int64Array.mk #[1, 2, big] != Int64Array.mk #[1, 2, 0]
#guard Int64Array.mk #[1, 2] != Int64Array.mk #[1, 2, 0]
#guard Int64Array.mk #[1, 2, 0] != Int64Array.mk #[1, 2]
#guard Int64Array.empty == Int64Array.emptyWithCapacity 10
#guard (Int64Array.mk #[1, 2] ++ Int64Array.mk #[big]) == Int64Array.mk #[1, 2, big]
-- Capacity and leftover memory past the size don't matter.
#guard (Int64Array.emptyWithCapacity 100).push 1 == Int64Array.mk #[1]
#guard (Int64Array.mk #[1, 2, 3]).pop == Int64Array.mk #[1, 2]
#guard (Int64Array.mk (Array.replicate 100000 0)).set! 99999 big !=
  Int64Array.mk (Array.replicate 100000 0)

/-! Decidable equality and hashing -/

#guard decide (Int64Array.mk #[1, 2, big] = Int64Array.mk #[1, 2, big])
#guard !decide (Int64Array.mk #[1, 2, big] = Int64Array.mk #[1, 2, 0])
#guard hash (Int64Array.mk #[1, 2, big]) == hash #[(1 : Int64), 2, big]
#guard hash (Int64Array.empty) == hash (#[] : Array Int64)
#guard hash ((Int64Array.emptyWithCapacity 100).push 1) == hash (Int64Array.mk #[1])

/-! Decidable membership and slice hashing -/

#guard (2 : Int64) ∈ Int64Array.mk #[1, 2, big]
#guard big ∈ Int64Array.mk #[1, 2, big]
#guard (3 : Int64) ∉ Int64Array.mk #[1, 2, big]
#guard (0 : Int64) ∉ Int64Array.empty
#guard big ∈ (Int64Array.mk #[0, 1, 2, big])[1...4]
#guard (0 : Int64) ∉ (Int64Array.mk #[0, 1, 2, big])[1...4]
#guard (2 : Int64) ∉ (Int64Array.mk #[0, 1, 2, big])[0...2]
#guard hash (Int64Array.mk #[0, 1, 2, big])[1...3] == hash (Int64Array.mk #[1, 2])
#guard hash (Int64Array.mk #[0, 1, 2, big])[1...3] == hash (Int64Array.mk #[big, 1, 2])[1...3]
#guard hash (∅ : Int64Array.Slice) == hash Int64Array.empty
#guard hash (Int64Array.mk #[1, 2])[1...1] == hash (∅ : Int64Array.Slice)

-- `decide` evaluates equality and membership for arrays and slices of literals.
example : Int64Array.mk #[1, 2] = Int64Array.mk #[1, 2] := by decide
example : Int64Array.mk #[1, 2] ≠ Int64Array.mk #[1, 3] := by decide
example : Int64Array.mk #[1, 2] ≠ Int64Array.mk #[1, 2, 3] := by decide
example : (2 : Int64) ∈ Int64Array.mk #[1, 2] := by decide
example : (3 : Int64) ∉ Int64Array.mk #[1, 2] := by decide
example : (2 : Int64) ∈ (Int64Array.mk #[1, 2, 3])[1...3] := by decide
example : (1 : Int64) ∉ (Int64Array.mk #[1, 2, 3])[1...3] := by decide

-- Lemmas that need decidable equality, used from another module.
example (a : Int64Array) (x : Int64) : a.contains x ↔ x ∈ a.toList := by simp
example (s : Int64Array.Slice) (x : Int64) : s.contains x ↔ x ∈ s.copy := by simp
example (s t : Int64Array.Slice) (h : s.copy = t.copy) : s == t := by simp [h]
example (s t : Int64Array.Slice) (h : s == t) : hash s = hash t :=
  LawfulHashable.hash_eq s t h

/-! Iteration -/

#guard (Int64Array.mk #[1, 2, big]).foldl (fun acc x => x :: acc) [] == [big, 2, 1]
#guard (Int64Array.mk #[1, 2, big]).foldr (fun x acc => x :: acc) [] == [1, 2, big]
#guard Int64Array.empty.foldl (fun acc x => x :: acc) [] == []
#guard Int64Array.empty.foldr (fun x acc => x :: acc) [] == []
#guard (Int64Array.mk #[1, 2, big]).foldlM (m := Option)
  (fun acc x => if x == 2 then none else some (x :: acc)) [] == none
#guard (Int64Array.mk #[1, big]).foldrM (m := Option) (fun x acc => some (x :: acc)) [] ==
  some [1, big]

#guard Id.run do
  let mut r : List Int64 := []
  for x in Int64Array.mk #[1, 2, big] do
    r := x :: r
  return r == [big, 2, 1]

#guard Id.run do
  let mut r : List Int64 := []
  for x in Int64Array.mk #[1, 2, 3, 4] do
    if x == 3 then break
    r := x :: r
  return r == [2, 1]

#guard
  let r : StateM (List Int64) Unit := (Int64Array.mk #[1, 2, big]).forM fun x => modify (x :: ·)
  (r.run []).2 == [big, 2, 1]

#guard
  let xs := (Array.range 100000).map Nat.toInt64
  let f := fun (acc : List Int64) x => if x == 0 then x :: acc else acc
  (Int64Array.mk xs).foldl f [] == xs.foldl f []

#guard (Int64Array.mk #[1, 2, big]).any (· == big)
#guard !(Int64Array.mk #[1, 2, 3]).any (· == big)
#guard (Int64Array.mk #[1, 2, 3]).all (· != big)
#guard !(Int64Array.mk #[1, big, 3]).all (· != big)
#guard !Int64Array.empty.any (fun _ => true) && Int64Array.empty.all (fun _ => false)
#guard (Int64Array.mk #[1, 2, big]).contains big
#guard !(Int64Array.mk #[1, 2, 3]).contains big && !Int64Array.empty.contains big

-- Early exits, and loops in a monad other than `Id`.
#guard (Int64Array.mk #[1, 2, big]).foldrM (m := Option)
  (fun x acc => if x == 1 then none else some (x :: acc)) [] == none
#guard (Int64Array.mk #[big, 2, 1]).foldrM (m := Option)
  (fun x acc => if x == big then none else some (x :: acc)) [] == none
#guard
  let r : StateM (List Int64) Unit := do
    for x in Int64Array.mk #[1, 2, big, 3] do
      if x == big then break
      modify (x :: ·)
  (r.run []).2 == [2, 1]
#guard
  let r : StateM (List Int64) Unit :=
    (Int64Array.mk #[1, 2, big]).foldrM (fun x _ => modify (x :: ·)) ⟨⟩
  (r.run []).2 == [1, 2, big]
#guard Id.run do
  let mut r : List Int64 := []
  for x in Int64Array.empty do
    r := x :: r
  return r == []
#guard !(Int64Array.mk #[1, 2, 3]).contains big
#guard (Int64Array.mk (Array.replicate 100000 0) |>.set! 99999 big).contains big

/-! Removing elements -/

#guard Int64Array.empty.isEmpty && !(Int64Array.mk #[1]).isEmpty
#guard (Int64Array.mk #[1]).pop.isEmpty
#guard (Int64Array.mk #[1, 2, big]).pop.data == #[1, 2]
#guard Int64Array.empty.pop.data == #[]
#guard ((Int64Array.mk #[1, 2, 3]).pop.push big).data == #[1, 2, big]
#guard (Int64Array.mk #[1, 2, big]).back? == some big
#guard Int64Array.empty.back? == none
#guard (Int64Array.mk #[1, 2, big]).back! == big
#guard (Int64Array.mk #[1, 2, big]).back (by decide) == big

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

#guard (Int64Array.mk #[1, 0, big, 0, 0]).popWhile (· == 0) == Int64Array.mk #[1, 0, big]
#guard (Int64Array.mk #[1, 0, big]).popWhile (· == 0) == Int64Array.mk #[1, 0, big]
#guard (Int64Array.mk #[0, 0]).popWhile (· == 0) == Int64Array.empty
#guard Int64Array.empty.popWhile (· == 0) == Int64Array.empty

-- Popping several elements from an exclusive array.
@[noinline] def Int64Array.popsWhileInPlace (x : Int64) : Bool :=
  let a := (Int64Array.mk #[x]).push 0 |>.push 0
  let p := rawAddr a
  let a := a.popWhile (· == 0)
  rawAddr a == p && a.data == #[x]

#guard Int64Array.popsWhileInPlace 1

example (p : Int64 → Bool) (a : Int64Array) : (a.popWhile p).data = a.data.popWhile p := by simp

#guard ((Int64Array.mk #[1, 2, 3, big]).extract 1 3).data == #[2, 3]
#guard ((Int64Array.mk #[1, 2, 3, big]).extract 2 100).data == #[3, big]
#guard ((Int64Array.mk #[1, 2, 3]).extract 0 3).data == #[1, 2, 3]
#guard ((Int64Array.mk #[1, 2, 3]).extract 2 1).data == #[]
#guard ((Int64Array.mk #[1, 2, 3]).extract 5 9).data == #[]
#guard ((Int64Array.mk #[1, 2, 3]).extract (2 ^ 70) (2 ^ 71)).data == #[]
#guard ((Int64Array.mk #[1, 2, 3]).extract 1 (2 ^ 70)).data == #[2, 3]
#guard
  let xs := (Array.range 100000).map Nat.toInt64
  ((Int64Array.mk xs).extract 70000 70010).data == xs.extract 70000 70010
#guard rawElemSize ((Int64Array.mk #[1, 2, 3]).extract 1 2) == elemSize

-- The extracted array is independent of the original.
#guard
  let a := Int64Array.mk #[1, 2, 3]
  let b := (a.extract 0 2).set! 0 big
  b.data == #[big, 2] && a.data == #[1, 2, 3]

/-! Building arrays -/

#guard (Int64Array.replicate 3 big).data == #[big, big, big]
#guard (Int64Array.replicate 0 1).data == #[]
#guard (Int64Array.replicate 100000 big).data == Array.replicate 100000 big
#guard (Int64Array.ofFn (n := 4) fun i => i.val.toInt64).data == #[0, 1, 2, 3]
#guard (Int64Array.ofFn (n := 0) fun i => i.val.toInt64).data == #[]
#guard rawElemSize (Int64Array.replicate 2 1) == elemSize
#guard rawElemSize (Int64Array.ofFn (n := 2) fun _ => 1) == elemSize

/-! Lemmas -/

example (a : Int64Array) (v : Int64) : (a.push v).pop = a := by simp [Int64Array.ext_iff]
example : (Int64Array.replicate 3 big)[1] = big := by simp
example (a b : Int64Array) (h : 0 < a.size) : (a ++ b)[0]'(by simp; omega) = a[0] := by simp [h]
example (a : Int64Array) (i : Nat) (v : Int64) (h : i < a.size) :
    (a.set i v h)[i]'(by simpa) = v := by simp
example (a : Int64Array) : a.extract 0 a.size = a := by simp
example (a : Int64Array) (v : Int64) : (a.push v).pop = a :=
  Int64Array.ext_getElem (by simp) (by simp_all)

/-! Default bounds proofs -/

#guard (Int64Array.mk #[1, 2, big]).get 2 == big
#guard (Int64Array.mk #[1, 2, big]).uget 2 == big
#guard ((Int64Array.mk #[1, 2, 3]).set 1 big).data == #[1, big, 3]
#guard ((Int64Array.mk #[1, 2, 3]).uset 1 big).data == #[1, big, 3]

/-! `set!` leaves the array unchanged when the index is out of bounds, like `ByteArray.set!`. -/

#guard ((Int64Array.mk #[1, 2, 3]).set! 3 big).data == #[1, 2, 3]
#guard ((Int64Array.mk #[1, 2, 3]).set! (2 ^ 70) big).data == #[1, 2, 3]

/-! Folds over part of an array -/

#guard (Int64Array.mk #[1, 2, 3, big]).foldl (fun acc x => x :: acc) [] 1 3 == [3, 2]
#guard (Int64Array.mk #[1, 2, 3, big]).foldl (fun acc x => x :: acc) [] 2 == [big, 3]
#guard (Int64Array.mk #[1, 2, 3, big]).foldl (fun acc x => x :: acc) [] 1 100 == [big, 3, 2]
#guard (Int64Array.mk #[1, 2, 3, big]).foldl (fun acc x => x :: acc) [] 3 1 == []
#guard (Int64Array.mk #[1, 2, 3, big]).foldl (fun acc x => x :: acc) [] 9 12 == []
#guard (Int64Array.mk #[1, 2, 3]).foldlM (m := Option)
  (fun acc x => if x == 1 then none else some (x :: acc)) [] 1 == some [3, 2]

/-! Copying slices -/

#guard
  let src := Int64Array.mk #[10, 11, 12, big]
  let dest := Int64Array.mk #[1, 2, 3, 4, 5]
  (src.copySlice 1 dest 2 2).data == #[1, 2, 11, 12, 5] &&
  (src.copySlice 1 dest 4 3).data == #[1, 2, 3, 4, 11, 12, big] &&
  (src.copySlice 0 dest 9 2).data == #[1, 2, 3, 4, 5, 10, 11] &&
  (src.copySlice 9 dest 1 2).data == #[1, 2, 3, 4, 5] &&
  (src.copySlice 2 dest 0 10).data == #[12, big, 3, 4, 5] &&
  (src.copySlice 0 dest 0 0).data == #[1, 2, 3, 4, 5] &&
  (src.copySlice 0 Int64Array.empty 0 4).data == #[10, 11, 12, big] &&
  dest.data == #[1, 2, 3, 4, 5] && src.data == #[10, 11, 12, big]

-- Copying from an array into itself.
#guard
  let a := Int64Array.mk #[1, 2, 3, big]
  (a.copySlice 0 a 2 4).data == #[1, 2, 1, 2, 3, big]

#guard
  let xs := (Array.range 100000).map Nat.toInt64
  let a := Int64Array.mk xs
  (a.copySlice 70000 (Int64Array.replicate 10 0) 5 10).data ==
    Array.replicate 5 0 ++ xs.extract 70000 70010

#guard rawElemSize ((Int64Array.mk #[1]).copySlice 0 Int64Array.empty 0 1) == elemSize

@[noinline] def Int64Array.copiesSliceInPlace (x : Int64) : Bool :=
  let dest := (Int64Array.emptyWithCapacity 10).push x |>.push x |>.push x
  let p := rawAddr dest
  let dest := (Int64Array.mk #[big, big]).copySlice 0 dest 1 2
  rawAddr dest == p && dest.data == #[x, big, big]

@[noinline] def Int64Array.copySliceGrowth (x : Int64) : Bool :=
  let dest := (Int64Array.mk #[x, x, x, x])
  rawCapacity ((Int64Array.mk #[x]).copySlice 0 dest 4 1 (exact := false)) ≥ 8 &&
    rawCapacity ((Int64Array.mk #[x]).copySlice 0 dest 4 1) == 5

#guard Int64Array.copiesSliceInPlace 1
#guard Int64Array.copySliceGrowth 1

/-! Linearity markers -/

#guard ((Int64Array.mk #[1, 2]).markLinear.push big).data == #[1, 2, big]
#guard ((Int64Array.mk #[1]).propagateMark (Int64Array.mk #[2, big])).data == #[2, big]

/-! Search -/

#guard (Int64Array.mk #[1, 2, big, 2]).findIdx? (· == 2) == some 1
#guard (Int64Array.mk #[1, 2, big, 2]).findIdx? (· == 2) 2 == some 3
#guard (Int64Array.mk #[1, 2, big, 2]).findIdx? (· == 3) == none
#guard (Int64Array.mk #[1, 2, big, 2]).findIdx? (· == 1) 9 == none
#guard ((Int64Array.mk #[1, 2, big, 2]).findFinIdx? (· == big)).map (·.val) == some 2

/-! Lists -/

#guard (Int64Array.ofList [1, 2, big]).data == #[1, 2, big]
#guard (Int64Array.ofList []).data == #[]
#guard [1, 2, big].toInt64Array == Int64Array.mk #[1, 2, big]
#guard (Int64Array.ofList ((List.range 100000).map Nat.toInt64)).data ==
  (Array.range 100000).map Nat.toInt64
#guard rawElemSize (Int64Array.ofList [1, 2]) == elemSize

/-! More lemmas -/

example (a b c : Int64Array) : a ++ b ++ c = a ++ (b ++ c) := Int64Array.append_assoc ..
example (a : Int64Array) : a ++ ∅ = a := by simp
example (a b : Int64Array) : (a ++ b).extract 0 a.size = a := by simp
example (a : Int64Array) (i : Nat) (v : Int64) : (a.set! i v).size = a.size := by simp
example (l : List Int64) : (Int64Array.ofList l).toList = l := by simp
example (a : Int64Array) : Int64Array.ofList a.toList = a := by simp

/-! Slices -/

#guard
  let a := Int64Array.mk #[1, 2, 3, big]
  let s := a[1...3]
  s.size == 2 && s[0]! == 2 && s[1]! == 3 && s.getD 2 7 == 7 && s.copy == Int64Array.mk #[2, 3] &&
    s.toList == [2, 3] && s.toArray == #[2, 3]

#guard
  let a := Int64Array.mk #[1, 2, 3, big]
  a[1...=3].toList == [2, 3, big] && a[*...2].toList == [1, 2] && a[2...*].toList == [3, big] &&
    a[*...*].toList == [1, 2, 3, big] && a[0<...2].toList == [2] &&
    a[0<...=2].toList == [2, 3] && a[*...=1].toList == [1, 2] && a[1<...*].toList == [3, big]

-- Bounds are clamped.
#guard
  let a := Int64Array.mk #[1, 2, 3, big]
  a[2...100].toList == [3, big] && a[3...1].size == 0 && a[9...12].size == 0 &&
    (a.toSlice 1 (2 ^ 70)).toList == [2, 3, big]

-- Slices of slices.
#guard
  let s := (Int64Array.mk #[1, 2, 3, big])[1...4]
  s[1...2].toList == [3] && s[0...100].toList == [2, 3, big] && s[*...*].toList == [2, 3, big] &&
    s[2...*].toList == [big] && s[5...6].size == 0

#guard
  let s := (Int64Array.mk #[1, 2, 3, big])[1...4]
  s.popFront.toList == [3, big] && s.popFront.popFront.popFront.popFront.size == 0

#guard (∅ : Int64Array.Slice).size == 0 && (default : Int64Array.Slice).toList == []

-- An array coerces to the slice of all its elements.
#guard
  let s : Int64Array.Slice := Int64Array.mk #[1, 2, big]
  s.toList == [1, 2, big] && s.start == 0

-- A slice does not coerce back to an array, since that would copy.
example (s : Int64Array.Slice) : Int64Array := s.copy

#guard Id.run do
  let mut r : List Int64 := []
  for x in (Int64Array.mk #[1, 2, 3, big])[1...*] do
    r := x :: r
  return r == [big, 3, 2]

#guard (Int64Array.mk #[1, 2, 3, big])[1...*].foldl (fun acc x => x :: acc) [] == [big, 3, 2]

#guard
  let xs := (Array.range 100000).map Nat.toInt64
  let s := (Int64Array.mk xs)[70000...70010]
  s.toArray == xs.extract 70000 70010 && s.copy.data == xs.extract 70000 70010

#guard toString (Int64Array.mk #[1, 2, 3])[1...*] == toString (Int64Array.mk #[2, 3])

-- Taking a slice doesn't copy the array.
@[noinline] def Int64Array.slicesWithoutCopying (x : Int64) : Bool :=
  let a := Int64Array.mk #[x, 2, 3]
  let p := rawAddr a
  rawAddr a[1...2].array == p

#guard Int64Array.slicesWithoutCopying 1

example (s : Int64Array.Slice) : s.copy.size = s.size := by simp

/-! Slice API -/

#guard
  let s := (Int64Array.mk #[1, 2, 3, big, 2])[1...5]
  s.foldr (fun x acc => x :: acc) [] == [2, 3, big, 2] &&
    s.foldl (fun acc x => x :: acc) [] == [2, big, 3, 2] &&
    s.any (· == big) && !s.any (· == 1) && s.all (· != 1) && !s.all (· == 2) &&
    s.contains big && !s.contains 1 && s.count (· == 2) == 2 &&
    s.find? (· > 2) == some 3 && s.findRev? (· != big) == some 2 && s.findRev? (· == 1) == none

#guard (Int64Array.mk #[1, 2, 3])[1...1].foldr (fun x acc => x :: acc) [] == []
#guard (Int64Array.mk #[1, 2, 3])[3...*].find? (fun _ => true) == none

#guard
  let s := (Int64Array.mk #[1, 2, 3, big])[1...*]
  let r : StateM (List Int64) Unit := s.forRevM fun x => modify (x :: ·)
  (r.run []).2 == [2, 3, big]

#guard Id.run ((Int64Array.mk #[1, 2, big])[*...*].findSomeRevM?
  (fun x => pure (if x == 2 then some x else none))) == some 2

-- The loops over slices stay within the slice, both with `start > 0` and with `stop < size`.
#guard
  let s := (Int64Array.mk #[big, 1, 2, 3, big])[1...4]
  s.foldr (fun x acc => x :: acc) [] == [1, 2, 3] &&
    s.foldl (fun acc x => x :: acc) [] == [3, 2, 1] && s.toList == [1, 2, 3] &&
    !s.any (· == big) && s.all (· != big) && !s.contains big && s.count (· != big) == 3 &&
    s.find? (· == big) == none && s.findRev? (· == big) == none &&
    s.find? (· != 1) == some 2 && s.findRev? (· != 3) == some 2

#guard Id.run do
  let mut r : List Int64 := []
  for x in (Int64Array.mk #[big, 1, 2, 3, big])[1...4] do
    r := x :: r
  return r == [3, 2, 1]

-- Early exits.
#guard Id.run do
  let mut r : List Int64 := []
  for x in (Int64Array.mk #[big, 1, 2, 3, big])[1...5] do
    if x == 3 then break
    r := x :: r
  return r == [2, 1]

#guard
  let s := (Int64Array.mk #[1, 2, big, 3, big])[1...5]
  s.any (· == big) && !s.all (· != big) && s.find? (· == big) == some big &&
    s.find? (· != 2) == some big && s.findRev? (· == big) == some big &&
    s.findRev? (· != big) == some 3

-- Empty slices.
#guard
  let s := (Int64Array.mk #[1, 2, 3])[1...1]
  s.foldl (fun acc x => x :: acc) [] == [] && s.toList == [] && !s.any (fun _ => true) &&
    s.all (fun _ => false) && s.count (fun _ => true) == 0 && s.find? (fun _ => true) == none &&
    s.findRev? (fun _ => true) == none && Id.run do
      let mut r : List Int64 := []
      for x in s do
        r := x :: r
      return r == []
#guard
  let s := (∅ : Int64Array.Slice)
  s.foldr (fun x acc => x :: acc) [] == [] && s.foldl (fun acc x => x :: acc) [] == [] &&
    !s.any (fun _ => true)

-- Loops in a monad other than `Id`.
#guard
  let r : StateM (List Int64) Unit := do
    for x in (Int64Array.mk #[big, 1, 2, 3, big])[1...5] do
      if x == 3 then break
      modify (x :: ·)
  (r.run []).2 == [2, 1]
#guard
  let s := (Int64Array.mk #[big, 1, 2, 3, big])[1...4]
  let r : StateM (List Int64) Unit := s.foldrM (fun x _ => modify (x :: ·)) ⟨⟩
  (r.run []).2 == [1, 2, 3]
#guard
  let s := (Int64Array.mk #[big, 1, 2, 3, big])[1...4]
  let r : StateM (List Int64) Unit := s.foldlM (fun _ x => modify (x :: ·)) ⟨⟩
  (r.run []).2 == [3, 2, 1]
#guard (Int64Array.mk #[big, 1, 2, 3, big])[1...4].foldlM (m := Option)
  (fun acc x => if x == 2 then none else some (x :: acc)) [] == none
#guard (Int64Array.mk #[big, 1, 2, 3, big])[1...4].foldrM (m := Option)
  (fun x acc => if x == 2 then none else some (x :: acc)) [] == none
#guard (Int64Array.mk #[big, 1, 2, 3, big])[1...4].foldlM (m := Option)
  (fun acc x => some (x :: acc)) [] == some [3, 2, 1]
#guard (Int64Array.mk #[big, 1, 2, 3, big])[1...4].findSomeRevM? (m := Option)
  (fun x => if x == 3 then some none else some (some x)) == some (some 2)
#guard
  let xs := (Array.range 100000).map Nat.toInt64
  let s := (Int64Array.mk xs)[100...99900]
  let f := fun (acc : List Int64) x => if x == 0 then x :: acc else acc
  s.foldl f [] == (xs.extract 100 99900).foldl f [] &&
    s.foldr (fun x acc => f acc x) [] == (xs.extract 100 99900).foldr (fun x acc => f acc x) []

/-! The `Std.Iterators` API on arrays and slices -/

#guard (Int64Array.mk #[1, 2, 3]).iter.toList == [1, 2, 3]
#guard ((Int64Array.mk #[1, 2, 3]).iter.map (· * 2)).toInt64Array == Int64Array.mk #[2, 4, 6]
#guard ((Int64Array.mk #[1, 2, 3, big]).iter.filter (· != 2)).toInt64Array ==
  Int64Array.mk #[1, 3, big]
#guard ((Int64Array.mk #[1, 2, 3, big]).iter.take 2).toInt64Array == Int64Array.mk #[1, 2]
#guard ((Int64Array.mk #[1, 2, 3, big]).iter.drop 2).toInt64Array == Int64Array.mk #[3, big]
#guard (((Int64Array.mk #[1, 2, 3]).iter.zip (Int64Array.mk #[big, 5]).iter).map
  fun (x, y) => x + y).toInt64Array == Int64Array.mk #[1 + big, 7]
#guard ((Int64Array.mk #[1, 2, 3, big])[1...3].iter.map (· + 1)).toInt64Array ==
  Int64Array.mk #[3, 4]
#guard (Int64Array.mk #[1, 2, 3]).iter.length == 3
#guard Int64Array.empty.iter.toInt64Array == Int64Array.empty
#guard
  let xs := (Array.range 100000).map Nat.toInt64
  ((Int64Array.mk xs).iter.map (· + 1)).toInt64Array.data == xs.map (· + 1)
#guard rawElemSize ((Int64Array.mk #[1]).iter.toInt64Array) == elemSize
#guard (Int64Array.mk #[1, 2, 3]).iter.toInt64ArrayWithCapacity 100 ==
  Int64Array.mk #[1, 2, 3]
#guard rawCapacity ((Int64Array.mk #[1, 2, 3]).iter.toInt64ArrayWithCapacity 100) ≥ 100

/-! Membership, `ForM` and slice equality -/

#guard
  let a := Int64Array.mk #[1, 2, big]
  let r : StateM (List Int64) PUnit := forM a fun x => modify (x :: ·)
  (r.run []).2 == [big, 2, 1]
#guard
  let s := (Int64Array.mk #[0, 1, 2, big])[1...3]
  let r : StateM (List Int64) PUnit := forM s fun x => modify (x :: ·)
  (r.run []).2 == [2, 1]
#guard
  let r : StateM (List Int64) PUnit := forM Int64Array.empty fun x => modify (x :: ·)
  (r.run []).2 == []
#guard (Int64Array.mk #[0, 1, 2, big])[1...3] == (Int64Array.mk #[1, 2, 5])[0...2]
#guard (Int64Array.mk #[1, big, 1, big])[0...2] == (Int64Array.mk #[1, big, 1, big])[2...4]
#guard (Int64Array.mk #[0, 1, 2, big])[1...3] != (Int64Array.mk #[1, 2, 5])[0...3]
#guard (Int64Array.mk #[0, 1, 2, big])[1...3] != (Int64Array.mk #[1, big])[0...2]
#guard (Int64Array.mk #[0, 1, 2, big])[1...3] != (Int64Array.mk #[2, 1])[0...2]
#guard (∅ : Int64Array.Slice) == (Int64Array.mk #[1, 2])[1...1]
#guard (Int64Array.mk #[1, 2, big] : Int64Array.Slice) ==
  (Int64Array.mk #[0, 1, 2, big])[1...*]
#guard
  let xs := (Array.range 100000).map Nat.toInt64
  (Int64Array.mk (#[0] ++ xs))[1...*] == (Int64Array.mk (xs ++ #[0]))[0...100000] &&
    (Int64Array.mk (#[0] ++ xs))[1...*] != (Int64Array.mk (xs.set! 99999 0))[0...100000]

/-! Lemmas from another module -/

example (a : Int64Array) (i : USize) (v : Int64) (h) (j : Nat) (hj) :
    (a.uset i v h)[j]'hj = if i.toNat = j then v else a[j]'(by simpa using hj) := by
  simp
example (a : Int64Array) (v : Int64) :
    (a.set! 0 v)[0]? = if 0 < a.size then some v else none := by
  simp
example (a : Int64Array) (v : Int64) (h : 1 < (a.set! 0 v).size) :
    (a.set! 0 v)[1] = a[1]'(by simpa using h) := by
  simp
example (a : Int64Array) (p : Int64 → Bool) : (a.popWhile p).size ≤ a.size :=
  Int64Array.size_popWhile_le p a
example (src dest : Int64Array) :
    (src.copySlice 0 dest 0 src.size).size = max dest.size src.size := by
  simp
example (a : Int64Array) (f : Nat → Int64 → Option Nat) :
    a.toList.foldlM f 0 = a.foldlM f 0 := by
  simp
example (a : Int64Array) (f : Int64 → Nat → Option Nat) :
    a.toList.foldrM f 0 = a.foldrM f 0 := by
  simp
example (a : Int64Array) (f : Int64 → StateM Nat PUnit) : forM a.toList f = forM a f := by
  simp
example (a b : Int64Array) (x : Int64) (h : x ∈ a) : x ∈ (a ++ b).toList := by
  simp [h]
example (a : Int64Array) (x : Int64) : x ∈ a.push x := by
  simp
example (a : Int64Array) (i : Nat) (h : i < a.size) : a[i] ∈ a.toList := by
  simpa using Int64Array.getElem_mem h
example (a : Int64Array) (start stop : Nat) (p : Int64 → Bool) :
    (a.toSlice start stop).any p = (a.extract start stop).any p := by
  simp
example (a : Int64Array) (start stop : Nat) :
    (a.toSlice start stop).toList = (a.toList.extract start stop) := by
  simp
example (s : Int64Array.Slice) (p : Int64 → Bool) : s.count p = s.copy.toList.countP p := by
  simp
example (s : Int64Array.Slice) (p : Int64 → Bool) :
    s.find? p = s.copy.toList.find? p ∧ s.findRev? p = s.copy.toList.reverse.find? p := by
  simp
example (s : Int64Array.Slice) (f : Nat → Int64 → Nat) :
    s.foldl f 0 = s.copy.toList.foldl f 0 := by
  simp
example (s : Int64Array.Slice) (f : Int64 → StateM Nat PUnit) :
    forM s f = forM s.copy.toList f := by
  simp
example (s : Int64Array.Slice) (x : Int64) : x ∈ s ↔ x ∈ s.copy.toList := by
  simp
example (s t : Int64Array.Slice) : (s == t) = (s.copy == t.copy) := by
  simp
example (a : Int64Array) : a.iter.toInt64Array = a := by
  simp
example (s : Int64Array.Slice) : s.iter.toInt64Array = s.copy := by
  simp
example : (∅ : Int64Array.Slice).size = 0 := by
  simp
