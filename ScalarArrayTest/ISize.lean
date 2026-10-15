/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import ScalarArray.ISize
import ScalarArrayTest.Util
meta import ScalarArray.ISize
meta import ScalarArrayTest.Util

open ScalarArray ScalarArrayTest

/-- A test value at the edge of the element type's range. -/
private abbrev big : ISize := -9223372036854775808

/-- The size of an element in bytes. -/
private abbrev elemSize : UInt32 := (System.Platform.numBits / 8).toUInt32

/-! Construction and conversion -/

#guard (ISizeArray.mk #[1, 2, 3, big]).data == #[1, 2, 3, big]
#guard (ISizeArray.mk #[1, 2, 3, big]).toList == [1, 2, 3, big]
#guard (ISizeArray.mk #[]).data == #[]
#guard ISizeArray.empty.data == #[]
#guard (∅ : ISizeArray).data == #[]
#guard (default : ISizeArray).data == #[]
#guard (ISizeArray.emptyWithCapacity 100).data == #[]
#guard (ISizeArray.mk (Array.range 1000 |>.map Nat.toISize)).data ==
  (Array.range 1000).map Nat.toISize

/-! Size -/

#guard (ISizeArray.mk #[1, 2, 3, big]).size == 4
#guard (ISizeArray.mk #[1, 2, 3, big]).usize == 4
#guard ISizeArray.empty.size == 0
#guard (ISizeArray.emptyWithCapacity 100).size == 0

/-! Reading -/

#guard (ISizeArray.mk #[1, 2, 3, big])[0] == 1
#guard (ISizeArray.mk #[1, 2, 3, big])[3] == big
#guard (ISizeArray.mk #[1, 2, 3, big])[(2 : USize)] == 3
#guard (ISizeArray.mk #[1, 2, 3, big]).get! 1 == 2
#guard (ISizeArray.mk #[1, 2, 3, big]).getD 2 7 == 3
#guard (ISizeArray.mk #[1, 2, 3, big]).getD 4 7 == 7
#guard (ISizeArray.mk #[1, 2, 3, big])[4]? == none
#guard (ISizeArray.mk #[1, 2, 3, big])[1]? == some 2

/-! Writing -/

#guard ((ISizeArray.mk #[1, 2, 3]).set 1 42 (by decide)).data == #[1, 42, 3]
#guard ((ISizeArray.mk #[1, 2, 3]).uset 2 42 (by simp)).data == #[1, 2, 42]
#guard ((ISizeArray.mk #[1, 2, 3]).set! 0 big).data == #[big, 2, 3]

-- Writing to a shared array must leave the original unchanged. The result is checked first so
-- that it is computed while the original is still live.
#guard
  let a := ISizeArray.mk #[1, 2, 3]
  let b := a.set! 1 42
  b.data == #[1, 42, 3] && a.data == #[1, 2, 3]
#guard
  let a := ISizeArray.mk #[1, 2, 3]
  let b := a.uset 0 big (by simp [a])
  b.data == #[big, 2, 3] && a.data == #[1, 2, 3]
#guard
  let a := ISizeArray.mk #[1, 2, 3]
  let b := a.set 2 big (by simp [a])
  b.data == #[1, 2, big] && a.data == #[1, 2, 3]

-- `foldInPlace` shifts a range right by one, inserting the initial accumulator.
#guard
  let r := (ISizeArray.mk #[1, 2, 3, 4]).foldInPlace 1 2 9 (fun _ _ x b => (b, x)) (by simp)
  r.1.data == #[1, 9, 2, 4] && r.2 == 3

-- `foldInPlace` on a shared array must leave the original unchanged, and `f` must see the
-- elements of the original even when it reads them from the array itself.
#guard
  let a := ISizeArray.mk #[1, 2, 3, 4]
  let r := a.foldInPlace 0 4 9 (fun _ _ x b => (b, x)) (by simp [a])
  r.1.data == #[9, 1, 2, 3] && a.data == #[1, 2, 3, 4]
#guard
  let a := ISizeArray.mk #[1, 2, 3, 4]
  let r := a.foldInPlace 1 3 0 (fun k _ _ b => (a[k.toNat]!, b)) (by simp [a])
  r.1.data == #[1, 1, 2, 3]

-- `foldInPlaceThen` hands the array and the last accumulator to `g`, here to store it.
#guard
  let r := (ISizeArray.mk #[1, 2, 3, 4]).foldInPlaceThen 0 3 9 (fun _ _ x b => (b, x))
    (fun a b => a.set! 3 b) (by simp)
  r.data == #[9, 1, 2, 3]
#guard
  let a := ISizeArray.mk #[1, 2, 3, 4]
  let r := a.foldInPlaceThen 1 2 9 (fun _ _ x b => (b, x)) Prod.mk (by simp [a])
  r.1.data == #[1, 9, 2, 4] && r.2 == 3 && a.data == #[1, 2, 3, 4]

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

#guard ((ISizeArray.mk #[0, 0, 0]).set! 1 big).data == #[0, big, 0]
#guard ((ISizeArray.mk #[big, big, big]).set! 1 0).data == #[big, 0, big]
#guard ((ISizeArray.mk #[0, 0, 0]).push big |>.push 0).data == #[0, 0, 0, big, 0]

/-! Indices beyond 16 bits, and huge `Nat` indices -/

#guard
  let a := (ISizeArray.mk (Array.replicate 100000 0)).set! 99999 big |>.set! 70000 1
  a.size == 100000 && a[99999]! == big && a[70000]! == 1 && a[99998]! == 0 &&
    a[70000 % 65536]! == 0 && a.data[99999]! == big && a.data[70000]! == 1 &&
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
  let b := (ISizeArray.mk a).set! 0 big
  b.data == #[big, 2, 3] && a == #[1, 2, 3]

#guard
  let a := ISizeArray.mk #[1, 2, 3]
  let d := a.data.set! 0 big
  d == #[big, 2, 3] && a.data == #[1, 2, 3]

/-! Runtime representation -/

#guard rawElemSize (ISizeArray.mk #[1, 2, 3]) == elemSize
#guard rawElemSize (ISizeArray.emptyWithCapacity 10) == elemSize
#guard rawElemSize (ISizeArray.empty.push 1) == elemSize
#guard rawElemSize ((ISizeArray.mk #[1]).push 2) == elemSize
#guard rawCapacity (ISizeArray.emptyWithCapacity 100) ≥ 100
#guard rawCapacity (ISizeArray.mk #[1, 2, 3]) ≥ 3
-- Growth is geometric, so pushing is amortized constant time.
#guard rawCapacity ((ISizeArray.mk #[1, 2, 3, 4]).push 5) ≥ 8


/-! Appending -/

#guard (ISizeArray.mk #[1, 2] ++ ISizeArray.mk #[3, big]).data == #[1, 2, 3, big]
#guard ((ISizeArray.mk #[1, 2]).append (ISizeArray.mk #[3])).data == #[1, 2, 3]
#guard (ISizeArray.mk #[1, 2] ++ ISizeArray.empty).data == #[1, 2]
#guard (ISizeArray.empty ++ ISizeArray.mk #[1, 2]).data == #[1, 2]
#guard (ISizeArray.empty ++ ISizeArray.empty).data == #[]
#guard (ISizeArray.mk #[0, 0] ++ ISizeArray.mk #[big] ++ ISizeArray.mk #[0]).data ==
  #[0, 0, big, 0]

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
    a := a ++ ISizeArray.mk #[i.toISize, (i * 7).toISize, big]
    r := r ++ #[i.toISize, (i * 7).toISize, big]
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
#guard rawElemSize (ISizeArray.mk #[1] ++ ISizeArray.mk #[2]) == elemSize

/-! Equality -/

#guard ISizeArray.mk #[1, 2, big] == ISizeArray.mk #[1, 2, big]
#guard ISizeArray.mk #[1, 2, big] != ISizeArray.mk #[1, 2, 0]
#guard ISizeArray.mk #[1, 2] != ISizeArray.mk #[1, 2, 0]
#guard ISizeArray.mk #[1, 2, 0] != ISizeArray.mk #[1, 2]
#guard ISizeArray.empty == ISizeArray.emptyWithCapacity 10
#guard (ISizeArray.mk #[1, 2] ++ ISizeArray.mk #[big]) == ISizeArray.mk #[1, 2, big]
-- Capacity and leftover memory past the size don't matter.
#guard (ISizeArray.emptyWithCapacity 100).push 1 == ISizeArray.mk #[1]
#guard (ISizeArray.mk #[1, 2, 3]).pop == ISizeArray.mk #[1, 2]
#guard (ISizeArray.mk (Array.replicate 100000 0)).set! 99999 big !=
  ISizeArray.mk (Array.replicate 100000 0)

/-! Decidable equality and hashing -/

#guard decide (ISizeArray.mk #[1, 2, big] = ISizeArray.mk #[1, 2, big])
#guard !decide (ISizeArray.mk #[1, 2, big] = ISizeArray.mk #[1, 2, 0])
#guard hash (ISizeArray.mk #[1, 2, big]) == hash #[(1 : ISize), 2, big]
#guard hash (ISizeArray.empty) == hash (#[] : Array ISize)
#guard hash ((ISizeArray.emptyWithCapacity 100).push 1) == hash (ISizeArray.mk #[1])

/-! Decidable membership and slice hashing -/

#guard (2 : ISize) ∈ ISizeArray.mk #[1, 2, big]
#guard big ∈ ISizeArray.mk #[1, 2, big]
#guard (3 : ISize) ∉ ISizeArray.mk #[1, 2, big]
#guard (0 : ISize) ∉ ISizeArray.empty
#guard big ∈ (ISizeArray.mk #[0, 1, 2, big])[1...4]
#guard (0 : ISize) ∉ (ISizeArray.mk #[0, 1, 2, big])[1...4]
#guard (2 : ISize) ∉ (ISizeArray.mk #[0, 1, 2, big])[0...2]
#guard hash (ISizeArray.mk #[0, 1, 2, big])[1...3] == hash (ISizeArray.mk #[1, 2])
#guard hash (ISizeArray.mk #[0, 1, 2, big])[1...3] == hash (ISizeArray.mk #[big, 1, 2])[1...3]
#guard hash (∅ : ISizeArray.Slice) == hash ISizeArray.empty
#guard hash (ISizeArray.mk #[1, 2])[1...1] == hash (∅ : ISizeArray.Slice)

-- Lemmas that need decidable equality, used from another module.
example (a : ISizeArray) (x : ISize) : a.contains x ↔ x ∈ a.toList := by simp
example (a : ISizeArray) (x : ISize) (h : x ∈ a) :
    (if a.contains x then 1 else 0) = 1 := by simp [h]
example (s : ISizeArray.Slice) (x : ISize) : s.contains x ↔ x ∈ s.copy := by simp
example (s t : ISizeArray.Slice) (h : s.copy = t.copy) : s == t := by simp [h]
example (s t : ISizeArray.Slice) (h : s == t) : hash s = hash t :=
  LawfulHashable.hash_eq s t h

/-! Iteration -/

#guard (ISizeArray.mk #[1, 2, big]).foldl (fun acc x => x :: acc) [] == [big, 2, 1]
#guard (ISizeArray.mk #[1, 2, big]).foldr (fun x acc => x :: acc) [] == [1, 2, big]
#guard ISizeArray.empty.foldl (fun acc x => x :: acc) [] == []
#guard ISizeArray.empty.foldr (fun x acc => x :: acc) [] == []
#guard (ISizeArray.mk #[1, 2, big]).foldlM (m := Option)
  (fun acc x => if x == 2 then none else some (x :: acc)) [] == none
#guard (ISizeArray.mk #[1, big]).foldrM (m := Option) (fun x acc => some (x :: acc)) [] ==
  some [1, big]

#guard Id.run do
  let mut r : List ISize := []
  for x in ISizeArray.mk #[1, 2, big] do
    r := x :: r
  return r == [big, 2, 1]

#guard Id.run do
  let mut r : List ISize := []
  for x in ISizeArray.mk #[1, 2, 3, 4] do
    if x == 3 then break
    r := x :: r
  return r == [2, 1]

#guard
  let r : StateM (List ISize) Unit := (ISizeArray.mk #[1, 2, big]).forM fun x => modify (x :: ·)
  (r.run []).2 == [big, 2, 1]

#guard
  let xs := (Array.range 100000).map Nat.toISize
  let f := fun (acc : List ISize) x => if x == 0 then x :: acc else acc
  (ISizeArray.mk xs).foldl f [] == xs.foldl f []

#guard (ISizeArray.mk #[1, 2, big]).any (· == big)
#guard !(ISizeArray.mk #[1, 2, 3]).any (· == big)
#guard (ISizeArray.mk #[1, 2, 3]).all (· != big)
#guard !(ISizeArray.mk #[1, big, 3]).all (· != big)
#guard !ISizeArray.empty.any (fun _ => true) && ISizeArray.empty.all (fun _ => false)
#guard (ISizeArray.mk #[1, 2, big]).contains big
#guard !(ISizeArray.mk #[1, 2, 3]).contains big && !ISizeArray.empty.contains big

-- Early exits, and loops in a monad other than `Id`.
#guard (ISizeArray.mk #[1, 2, big]).foldrM (m := Option)
  (fun x acc => if x == 1 then none else some (x :: acc)) [] == none
#guard (ISizeArray.mk #[big, 2, 1]).foldrM (m := Option)
  (fun x acc => if x == big then none else some (x :: acc)) [] == none
#guard
  let r : StateM (List ISize) Unit := do
    for x in ISizeArray.mk #[1, 2, big, 3] do
      if x == big then break
      modify (x :: ·)
  (r.run []).2 == [2, 1]
#guard
  let r : StateM (List ISize) Unit :=
    (ISizeArray.mk #[1, 2, big]).foldrM (fun x _ => modify (x :: ·)) ⟨⟩
  (r.run []).2 == [1, 2, big]
#guard Id.run do
  let mut r : List ISize := []
  for x in ISizeArray.empty do
    r := x :: r
  return r == []
#guard !(ISizeArray.mk #[1, 2, 3]).contains big
#guard (ISizeArray.mk (Array.replicate 100000 0) |>.set! 99999 big).contains big

/-! Removing elements -/

#guard ISizeArray.empty.isEmpty && !(ISizeArray.mk #[1]).isEmpty
#guard (ISizeArray.mk #[1]).pop.isEmpty
#guard (ISizeArray.mk #[1, 2, big]).pop.data == #[1, 2]
#guard ISizeArray.empty.pop.data == #[]
#guard ((ISizeArray.mk #[1, 2, 3]).pop.push big).data == #[1, 2, big]
#guard (ISizeArray.mk #[1, 2, big]).back? == some big
#guard ISizeArray.empty.back? == none
#guard (ISizeArray.mk #[1, 2, big]).back! == big
#guard (ISizeArray.mk #[1, 2, big]).back (by decide) == big

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

#guard (ISizeArray.mk #[1, 0, big, 0, 0]).popWhile (· == 0) == ISizeArray.mk #[1, 0, big]
#guard (ISizeArray.mk #[1, 0, big]).popWhile (· == 0) == ISizeArray.mk #[1, 0, big]
#guard (ISizeArray.mk #[0, 0]).popWhile (· == 0) == ISizeArray.empty
#guard ISizeArray.empty.popWhile (· == 0) == ISizeArray.empty

-- Popping several elements from an exclusive array.
@[noinline] def ISizeArray.popsWhileInPlace (x : ISize) : Bool :=
  let a := (ISizeArray.mk #[x]).push 0 |>.push 0
  let p := rawAddr a
  let a := a.popWhile (· == 0)
  rawAddr a == p && a.data == #[x]

#guard ISizeArray.popsWhileInPlace 1

example (p : ISize → Bool) (a : ISizeArray) : (a.popWhile p).data = a.data.popWhile p := by simp

#guard ((ISizeArray.mk #[1, 2, 3, big]).extract 1 3).data == #[2, 3]
#guard ((ISizeArray.mk #[1, 2, 3, big]).extract 2 100).data == #[3, big]
#guard ((ISizeArray.mk #[1, 2, 3]).extract 0 3).data == #[1, 2, 3]
#guard ((ISizeArray.mk #[1, 2, 3]).extract 2 1).data == #[]
#guard ((ISizeArray.mk #[1, 2, 3]).extract 5 9).data == #[]
#guard ((ISizeArray.mk #[1, 2, 3]).extract (2 ^ 70) (2 ^ 71)).data == #[]
#guard ((ISizeArray.mk #[1, 2, 3]).extract 1 (2 ^ 70)).data == #[2, 3]
#guard
  let xs := (Array.range 100000).map Nat.toISize
  ((ISizeArray.mk xs).extract 70000 70010).data == xs.extract 70000 70010
#guard rawElemSize ((ISizeArray.mk #[1, 2, 3]).extract 1 2) == elemSize

-- The extracted array is independent of the original.
#guard
  let a := ISizeArray.mk #[1, 2, 3]
  let b := (a.extract 0 2).set! 0 big
  b.data == #[big, 2] && a.data == #[1, 2, 3]

/-! Building arrays -/

#guard (ISizeArray.replicate 3 big).data == #[big, big, big]
#guard (ISizeArray.replicate 0 1).data == #[]
#guard (ISizeArray.replicate 100000 big).data == Array.replicate 100000 big
#guard (ISizeArray.ofFn (n := 4) fun i => i.val.toISize).data == #[0, 1, 2, 3]
#guard (ISizeArray.ofFn (n := 0) fun i => i.val.toISize).data == #[]
#guard rawElemSize (ISizeArray.replicate 2 1) == elemSize
#guard rawElemSize (ISizeArray.ofFn (n := 2) fun _ => 1) == elemSize

/-! Lemmas -/

example (a : ISizeArray) (v : ISize) : (a.push v).pop = a := by simp [ISizeArray.ext_iff]
example : (ISizeArray.replicate 3 big)[1] = big := by simp
example (a b : ISizeArray) (h : 0 < a.size) : (a ++ b)[0]'(by simp; omega) = a[0] := by simp [h]
example (a : ISizeArray) (i : Nat) (v : ISize) (h : i < a.size) :
    (a.set i v h)[i]'(by simpa) = v := by simp
example (a : ISizeArray) : a.extract 0 a.size = a := by simp
example (a : ISizeArray) (v : ISize) : (a.push v).pop = a :=
  ISizeArray.ext_getElem (by simp) (by simp_all)

/-! Default bounds proofs -/

#guard (ISizeArray.mk #[1, 2, big]).get 2 == big
#guard (ISizeArray.mk #[1, 2, big]).uget 2 == big
#guard ((ISizeArray.mk #[1, 2, 3]).set 1 big).data == #[1, big, 3]
#guard ((ISizeArray.mk #[1, 2, 3]).uset 1 big).data == #[1, big, 3]

/-! `set!` leaves the array unchanged when the index is out of bounds, like `ByteArray.set!`. -/

#guard ((ISizeArray.mk #[1, 2, 3]).set! 3 big).data == #[1, 2, 3]
#guard ((ISizeArray.mk #[1, 2, 3]).set! (2 ^ 70) big).data == #[1, 2, 3]

/-! Folds over part of an array -/

#guard (ISizeArray.mk #[1, 2, 3, big]).foldl (fun acc x => x :: acc) [] 1 3 == [3, 2]
#guard (ISizeArray.mk #[1, 2, 3, big]).foldl (fun acc x => x :: acc) [] 2 == [big, 3]
#guard (ISizeArray.mk #[1, 2, 3, big]).foldl (fun acc x => x :: acc) [] 1 100 == [big, 3, 2]
#guard (ISizeArray.mk #[1, 2, 3, big]).foldl (fun acc x => x :: acc) [] 3 1 == []
#guard (ISizeArray.mk #[1, 2, 3, big]).foldl (fun acc x => x :: acc) [] 9 12 == []
#guard (ISizeArray.mk #[1, 2, 3]).foldlM (m := Option)
  (fun acc x => if x == 1 then none else some (x :: acc)) [] 1 == some [3, 2]

/-! Copying slices -/

#guard
  let src := ISizeArray.mk #[10, 11, 12, big]
  let dest := ISizeArray.mk #[1, 2, 3, 4, 5]
  (src.copySlice 1 dest 2 2).data == #[1, 2, 11, 12, 5] &&
  (src.copySlice 1 dest 4 3).data == #[1, 2, 3, 4, 11, 12, big] &&
  (src.copySlice 0 dest 9 2).data == #[1, 2, 3, 4, 5, 10, 11] &&
  (src.copySlice 9 dest 1 2).data == #[1, 2, 3, 4, 5] &&
  (src.copySlice 2 dest 0 10).data == #[12, big, 3, 4, 5] &&
  (src.copySlice 0 dest 0 0).data == #[1, 2, 3, 4, 5] &&
  (src.copySlice 0 ISizeArray.empty 0 4).data == #[10, 11, 12, big] &&
  dest.data == #[1, 2, 3, 4, 5] && src.data == #[10, 11, 12, big]

-- Copying from an array into itself.
#guard
  let a := ISizeArray.mk #[1, 2, 3, big]
  (a.copySlice 0 a 2 4).data == #[1, 2, 1, 2, 3, big]

#guard
  let xs := (Array.range 100000).map Nat.toISize
  let a := ISizeArray.mk xs
  (a.copySlice 70000 (ISizeArray.replicate 10 0) 5 10).data ==
    Array.replicate 5 0 ++ xs.extract 70000 70010

#guard rawElemSize ((ISizeArray.mk #[1]).copySlice 0 ISizeArray.empty 0 1) == elemSize

@[noinline] def ISizeArray.copiesSliceInPlace (x : ISize) : Bool :=
  let dest := (ISizeArray.emptyWithCapacity 10).push x |>.push x |>.push x
  let p := rawAddr dest
  let dest := (ISizeArray.mk #[big, big]).copySlice 0 dest 1 2
  rawAddr dest == p && dest.data == #[x, big, big]

@[noinline] def ISizeArray.copySliceGrowth (x : ISize) : Bool :=
  let dest := (ISizeArray.mk #[x, x, x, x])
  rawCapacity ((ISizeArray.mk #[x]).copySlice 0 dest 4 1 (exact := false)) ≥ 8 &&
    rawCapacity ((ISizeArray.mk #[x]).copySlice 0 dest 4 1) == 5

#guard ISizeArray.copiesSliceInPlace 1
#guard ISizeArray.copySliceGrowth 1

/-! Linearity markers -/

#guard ((ISizeArray.mk #[1, 2]).markLinear.push big).data == #[1, 2, big]
#guard ((ISizeArray.mk #[1]).propagateMark (ISizeArray.mk #[2, big])).data == #[2, big]

/-! Search -/

#guard (ISizeArray.mk #[1, 2, big, 2]).findIdx? (· == 2) == some 1
#guard (ISizeArray.mk #[1, 2, big, 2]).findIdx? (· == 2) 2 == some 3
#guard (ISizeArray.mk #[1, 2, big, 2]).findIdx? (· == 3) == none
#guard (ISizeArray.mk #[1, 2, big, 2]).findIdx? (· == 1) 9 == none
#guard ((ISizeArray.mk #[1, 2, big, 2]).findFinIdx? (· == big)).map (·.val) == some 2

/-! Lists -/

#guard (ISizeArray.ofList [1, 2, big]).data == #[1, 2, big]
#guard (ISizeArray.ofList []).data == #[]
#guard [1, 2, big].toISizeArray == ISizeArray.mk #[1, 2, big]
#guard (ISizeArray.ofList ((List.range 100000).map Nat.toISize)).data ==
  (Array.range 100000).map Nat.toISize
#guard rawElemSize (ISizeArray.ofList [1, 2]) == elemSize

/-! More lemmas -/

example (a b c : ISizeArray) : a ++ b ++ c = a ++ (b ++ c) := ISizeArray.append_assoc ..
example (a : ISizeArray) : a ++ ∅ = a := by simp
example (a b : ISizeArray) : (a ++ b).extract 0 a.size = a := by simp
example (a : ISizeArray) (i : Nat) (v : ISize) : (a.set! i v).size = a.size := by simp
example (l : List ISize) : (ISizeArray.ofList l).toList = l := by simp
example (a : ISizeArray) : ISizeArray.ofList a.toList = a := by simp

/-! Slices -/

#guard
  let a := ISizeArray.mk #[1, 2, 3, big]
  let s := a[1...3]
  s.size == 2 && s[0]! == 2 && s[1]! == 3 && s.getD 2 7 == 7 && s.copy == ISizeArray.mk #[2, 3] &&
    s.toList == [2, 3] && s.toArray == #[2, 3]

#guard
  let a := ISizeArray.mk #[1, 2, 3, big]
  a[1...=3].toList == [2, 3, big] && a[*...2].toList == [1, 2] && a[2...*].toList == [3, big] &&
    a[*...*].toList == [1, 2, 3, big] && a[0<...2].toList == [2] &&
    a[0<...=2].toList == [2, 3] && a[*...=1].toList == [1, 2] && a[1<...*].toList == [3, big]

-- Bounds are clamped.
#guard
  let a := ISizeArray.mk #[1, 2, 3, big]
  a[2...100].toList == [3, big] && a[3...1].size == 0 && a[9...12].size == 0 &&
    (a.toSlice 1 (2 ^ 70)).toList == [2, 3, big]

-- Slices of slices.
#guard
  let s := (ISizeArray.mk #[1, 2, 3, big])[1...4]
  s[1...2].toList == [3] && s[0...100].toList == [2, 3, big] && s[*...*].toList == [2, 3, big] &&
    s[2...*].toList == [big] && s[5...6].size == 0

#guard
  let s := (ISizeArray.mk #[1, 2, 3, big])[1...4]
  s.popFront.toList == [3, big] && s.popFront.popFront.popFront.popFront.size == 0

#guard (∅ : ISizeArray.Slice).size == 0 && (default : ISizeArray.Slice).toList == []

-- An array coerces to the slice of all its elements.
#guard
  let s : ISizeArray.Slice := ISizeArray.mk #[1, 2, big]
  s.toList == [1, 2, big] && s.start == 0

-- A slice does not coerce back to an array, since that would copy.
example (s : ISizeArray.Slice) : ISizeArray := s.copy

#guard Id.run do
  let mut r : List ISize := []
  for x in (ISizeArray.mk #[1, 2, 3, big])[1...*] do
    r := x :: r
  return r == [big, 3, 2]

#guard (ISizeArray.mk #[1, 2, 3, big])[1...*].foldl (fun acc x => x :: acc) [] == [big, 3, 2]

#guard
  let xs := (Array.range 100000).map Nat.toISize
  let s := (ISizeArray.mk xs)[70000...70010]
  s.toArray == xs.extract 70000 70010 && s.copy.data == xs.extract 70000 70010

#guard toString (ISizeArray.mk #[1, 2, 3])[1...*] == toString (ISizeArray.mk #[2, 3])

-- Taking a slice doesn't copy the array.
@[noinline] def ISizeArray.slicesWithoutCopying (x : ISize) : Bool :=
  let a := ISizeArray.mk #[x, 2, 3]
  let p := rawAddr a
  rawAddr a[1...2].array == p

#guard ISizeArray.slicesWithoutCopying 1

example (s : ISizeArray.Slice) : s.copy.size = s.size := by simp

/-! Slice API -/

#guard
  let s := (ISizeArray.mk #[1, 2, 3, big, 2])[1...5]
  s.foldr (fun x acc => x :: acc) [] == [2, 3, big, 2] &&
    s.foldl (fun acc x => x :: acc) [] == [2, big, 3, 2] &&
    s.any (· == big) && !s.any (· == 1) && s.all (· != 1) && !s.all (· == 2) &&
    s.contains big && !s.contains 1 && s.count (· == 2) == 2 &&
    s.find? (· > 2) == some 3 && s.findRev? (· != big) == some 2 && s.findRev? (· == 1) == none

#guard (ISizeArray.mk #[1, 2, 3])[1...1].foldr (fun x acc => x :: acc) [] == []
#guard (ISizeArray.mk #[1, 2, 3])[3...*].find? (fun _ => true) == none

#guard
  let s := (ISizeArray.mk #[1, 2, 3, big])[1...*]
  let r : StateM (List ISize) Unit := s.forRevM fun x => modify (x :: ·)
  (r.run []).2 == [2, 3, big]

#guard Id.run ((ISizeArray.mk #[1, 2, big])[*...*].findSomeRevM?
  (fun x => pure (if x == 2 then some x else none))) == some 2

-- The loops over slices stay within the slice, both with `start > 0` and with `stop < size`.
#guard
  let s := (ISizeArray.mk #[big, 1, 2, 3, big])[1...4]
  s.foldr (fun x acc => x :: acc) [] == [1, 2, 3] &&
    s.foldl (fun acc x => x :: acc) [] == [3, 2, 1] && s.toList == [1, 2, 3] &&
    !s.any (· == big) && s.all (· != big) && !s.contains big && s.count (· != big) == 3 &&
    s.find? (· == big) == none && s.findRev? (· == big) == none &&
    s.find? (· != 1) == some 2 && s.findRev? (· != 3) == some 2

#guard Id.run do
  let mut r : List ISize := []
  for x in (ISizeArray.mk #[big, 1, 2, 3, big])[1...4] do
    r := x :: r
  return r == [3, 2, 1]

-- Early exits.
#guard Id.run do
  let mut r : List ISize := []
  for x in (ISizeArray.mk #[big, 1, 2, 3, big])[1...5] do
    if x == 3 then break
    r := x :: r
  return r == [2, 1]

#guard
  let s := (ISizeArray.mk #[1, 2, big, 3, big])[1...5]
  s.any (· == big) && !s.all (· != big) && s.find? (· == big) == some big &&
    s.find? (· != 2) == some big && s.findRev? (· == big) == some big &&
    s.findRev? (· != big) == some 3

-- Empty slices.
#guard
  let s := (ISizeArray.mk #[1, 2, 3])[1...1]
  s.foldl (fun acc x => x :: acc) [] == [] && s.toList == [] && !s.any (fun _ => true) &&
    s.all (fun _ => false) && s.count (fun _ => true) == 0 && s.find? (fun _ => true) == none &&
    s.findRev? (fun _ => true) == none && Id.run do
      let mut r : List ISize := []
      for x in s do
        r := x :: r
      return r == []
#guard
  let s := (∅ : ISizeArray.Slice)
  s.foldr (fun x acc => x :: acc) [] == [] && s.foldl (fun acc x => x :: acc) [] == [] &&
    !s.any (fun _ => true)

-- Loops in a monad other than `Id`.
#guard
  let r : StateM (List ISize) Unit := do
    for x in (ISizeArray.mk #[big, 1, 2, 3, big])[1...5] do
      if x == 3 then break
      modify (x :: ·)
  (r.run []).2 == [2, 1]
#guard
  let s := (ISizeArray.mk #[big, 1, 2, 3, big])[1...4]
  let r : StateM (List ISize) Unit := s.foldrM (fun x _ => modify (x :: ·)) ⟨⟩
  (r.run []).2 == [1, 2, 3]
#guard
  let s := (ISizeArray.mk #[big, 1, 2, 3, big])[1...4]
  let r : StateM (List ISize) Unit := s.foldlM (fun _ x => modify (x :: ·)) ⟨⟩
  (r.run []).2 == [3, 2, 1]
#guard (ISizeArray.mk #[big, 1, 2, 3, big])[1...4].foldlM (m := Option)
  (fun acc x => if x == 2 then none else some (x :: acc)) [] == none
#guard (ISizeArray.mk #[big, 1, 2, 3, big])[1...4].foldrM (m := Option)
  (fun x acc => if x == 2 then none else some (x :: acc)) [] == none
#guard (ISizeArray.mk #[big, 1, 2, 3, big])[1...4].foldlM (m := Option)
  (fun acc x => some (x :: acc)) [] == some [3, 2, 1]
#guard (ISizeArray.mk #[big, 1, 2, 3, big])[1...4].findSomeRevM? (m := Option)
  (fun x => if x == 3 then some none else some (some x)) == some (some 2)
#guard
  let xs := (Array.range 100000).map Nat.toISize
  let s := (ISizeArray.mk xs)[100...99900]
  let f := fun (acc : List ISize) x => if x == 0 then x :: acc else acc
  s.foldl f [] == (xs.extract 100 99900).foldl f [] &&
    s.foldr (fun x acc => f acc x) [] == (xs.extract 100 99900).foldr (fun x acc => f acc x) []

/-! The `Std.Iterators` API on arrays and slices -/

#guard (ISizeArray.mk #[1, 2, 3]).iter.toList == [1, 2, 3]
#guard ((ISizeArray.mk #[1, 2, 3]).iter.map (· * 2)).toISizeArray == ISizeArray.mk #[2, 4, 6]
#guard ((ISizeArray.mk #[1, 2, 3, big]).iter.filter (· != 2)).toISizeArray ==
  ISizeArray.mk #[1, 3, big]
#guard ((ISizeArray.mk #[1, 2, 3, big]).iter.take 2).toISizeArray == ISizeArray.mk #[1, 2]
#guard ((ISizeArray.mk #[1, 2, 3, big]).iter.drop 2).toISizeArray == ISizeArray.mk #[3, big]
#guard (((ISizeArray.mk #[1, 2, 3]).iter.zip (ISizeArray.mk #[big, 5]).iter).map
  fun (x, y) => x + y).toISizeArray == ISizeArray.mk #[1 + big, 7]
#guard ((ISizeArray.mk #[1, 2, 3, big])[1...3].iter.map (· + 1)).toISizeArray ==
  ISizeArray.mk #[3, 4]
#guard (ISizeArray.mk #[1, 2, 3]).iter.length == 3
#guard ISizeArray.empty.iter.toISizeArray == ISizeArray.empty
#guard
  let xs := (Array.range 100000).map Nat.toISize
  ((ISizeArray.mk xs).iter.map (· + 1)).toISizeArray.data == xs.map (· + 1)
#guard rawElemSize ((ISizeArray.mk #[1]).iter.toISizeArray) == elemSize
#guard (ISizeArray.mk #[1, 2, 3]).iter.toISizeArrayWithCapacity 100 ==
  ISizeArray.mk #[1, 2, 3]
#guard rawCapacity ((ISizeArray.mk #[1, 2, 3]).iter.toISizeArrayWithCapacity 100) ≥ 100

/-! Membership, `ForM` and slice equality -/

#guard
  let a := ISizeArray.mk #[1, 2, big]
  let r : StateM (List ISize) PUnit := forM a fun x => modify (x :: ·)
  (r.run []).2 == [big, 2, 1]
#guard
  let s := (ISizeArray.mk #[0, 1, 2, big])[1...3]
  let r : StateM (List ISize) PUnit := forM s fun x => modify (x :: ·)
  (r.run []).2 == [2, 1]
#guard
  let r : StateM (List ISize) PUnit := forM ISizeArray.empty fun x => modify (x :: ·)
  (r.run []).2 == []
#guard (ISizeArray.mk #[0, 1, 2, big])[1...3] == (ISizeArray.mk #[1, 2, 5])[0...2]
#guard (ISizeArray.mk #[1, big, 1, big])[0...2] == (ISizeArray.mk #[1, big, 1, big])[2...4]
#guard (ISizeArray.mk #[0, 1, 2, big])[1...3] != (ISizeArray.mk #[1, 2, 5])[0...3]
#guard (ISizeArray.mk #[0, 1, 2, big])[1...3] != (ISizeArray.mk #[1, big])[0...2]
#guard (ISizeArray.mk #[0, 1, 2, big])[1...3] != (ISizeArray.mk #[2, 1])[0...2]
#guard (∅ : ISizeArray.Slice) == (ISizeArray.mk #[1, 2])[1...1]
#guard (ISizeArray.mk #[1, 2, big] : ISizeArray.Slice) ==
  (ISizeArray.mk #[0, 1, 2, big])[1...*]
#guard
  let xs := (Array.range 100000).map Nat.toISize
  (ISizeArray.mk (#[0] ++ xs))[1...*] == (ISizeArray.mk (xs ++ #[0]))[0...100000] &&
    (ISizeArray.mk (#[0] ++ xs))[1...*] != (ISizeArray.mk (xs.set! 99999 0))[0...100000]

/-! Lemmas from another module -/

example (a : ISizeArray) (i : USize) (v : ISize) (h) (j : Nat) (hj) :
    (a.uset i v h)[j]'hj = if i.toNat = j then v else a[j]'(by simpa using hj) := by
  simp
example (a : ISizeArray) (v : ISize) :
    (a.set! 0 v)[0]? = if 0 < a.size then some v else none := by
  simp
example (a : ISizeArray) (v : ISize) (h : 1 < (a.set! 0 v).size) :
    (a.set! 0 v)[1] = a[1]'(by simpa using h) := by
  simp
example (a : ISizeArray) (p : ISize → Bool) : (a.popWhile p).size ≤ a.size :=
  ISizeArray.size_popWhile_le p a
example (src dest : ISizeArray) :
    (src.copySlice 0 dest 0 src.size).size = max dest.size src.size := by
  simp
example (a : ISizeArray) (f : Nat → ISize → Option Nat) :
    a.toList.foldlM f 0 = a.foldlM f 0 := by
  simp
example (a : ISizeArray) (f : ISize → Nat → Option Nat) :
    a.toList.foldrM f 0 = a.foldrM f 0 := by
  simp
example (a : ISizeArray) (f : ISize → StateM Nat PUnit) : forM a.toList f = forM a f := by
  simp
example (a b : ISizeArray) (x : ISize) (h : x ∈ a) : x ∈ (a ++ b).toList := by
  simp [h]
example (a : ISizeArray) (x : ISize) : x ∈ a.push x := by
  simp
example (a : ISizeArray) (i : Nat) (h : i < a.size) : a[i] ∈ a.toList := by
  simpa using ISizeArray.getElem_mem h
example (a : ISizeArray) (start stop : Nat) (p : ISize → Bool) :
    (a.toSlice start stop).any p = (a.extract start stop).any p := by
  simp
example (a : ISizeArray) (start stop : Nat) :
    (a.toSlice start stop).toList = (a.toList.extract start stop) := by
  simp
example (s : ISizeArray.Slice) (p : ISize → Bool) : s.count p = s.copy.toList.countP p := by
  simp
example (s : ISizeArray.Slice) (p : ISize → Bool) :
    s.find? p = s.copy.toList.find? p ∧ s.findRev? p = s.copy.toList.reverse.find? p := by
  simp
example (s : ISizeArray.Slice) (f : Nat → ISize → Nat) :
    s.foldl f 0 = s.copy.toList.foldl f 0 := by
  simp
example (s : ISizeArray.Slice) (f : ISize → StateM Nat PUnit) :
    forM s f = forM s.copy.toList f := by
  simp
example (s : ISizeArray.Slice) (x : ISize) : x ∈ s ↔ x ∈ s.copy.toList := by
  simp
example (s t : ISizeArray.Slice) : (s == t) = (s.copy == t.copy) := by
  simp
example (a : ISizeArray) : a.iter.toISizeArray = a := by
  simp
example (s : ISizeArray.Slice) : s.iter.toISizeArray = s.copy := by
  simp
example : (∅ : ISizeArray.Slice).size = 0 := by
  simp
