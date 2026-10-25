/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import ScalarArray.UInt32
import ScalarArrayTest.Util
meta import ScalarArray.UInt32
meta import ScalarArrayTest.Util

open ScalarArray ScalarArrayTest

/-- A test value at the edge of the element type's range. -/
private abbrev big : UInt32 := 4294967295

/-- The size of an element in bytes. -/
private abbrev elemSize : UInt32 := 4

/-! Construction and conversion -/

#guard (UInt32Array.mk #[1, 2, 3, big]).data == #[1, 2, 3, big]
#guard (UInt32Array.mk #[1, 2, 3, big]).toList == [1, 2, 3, big]
#guard (UInt32Array.mk #[]).data == #[]
#guard UInt32Array.empty.data == #[]
#guard (∅ : UInt32Array).data == #[]
#guard (default : UInt32Array).data == #[]
#guard (UInt32Array.emptyWithCapacity 100).data == #[]
#guard (UInt32Array.mk (Array.range 1000 |>.map Nat.toUInt32)).data ==
  (Array.range 1000).map Nat.toUInt32

/-! Case analysis -/

-- `cases` splits an array as `mk data`, also in compiled code.
private def headOrZero (a : UInt32Array) : UInt32 := by
  cases a with | mk data => exact data[0]?.getD 0

#guard headOrZero (UInt32Array.mk #[7, 8]) == 7
#guard headOrZero UInt32Array.empty == 0

-- There is no constructor to match on, which would run `Array` code on a scalar array.
/--
error: Invalid `⟨...⟩` notation: The expected type `Quot fun x x_1 => False` is not an inductive type

Note: This notation can only be used when the expected type is an inductive type with a single constructor
-/
#guard_msgs in
example (a : UInt32Array) : UInt32 := match a with | ⟨data⟩ => data[0]!

/-! Size -/

#guard (UInt32Array.mk #[1, 2, 3, big]).size == 4
#guard (UInt32Array.mk #[1, 2, 3, big]).usize == 4
#guard UInt32Array.empty.size == 0
#guard (UInt32Array.emptyWithCapacity 100).size == 0

/-! Reading -/

#guard (UInt32Array.mk #[1, 2, 3, big])[0] == 1
#guard (UInt32Array.mk #[1, 2, 3, big])[3] == big
#guard (UInt32Array.mk #[1, 2, 3, big])[(2 : USize)] == 3
#guard (UInt32Array.mk #[1, 2, 3, big]).get! 1 == 2
#guard (UInt32Array.mk #[1, 2, 3, big]).getD 2 7 == 3
#guard (UInt32Array.mk #[1, 2, 3, big]).getD 4 7 == 7
#guard (UInt32Array.mk #[1, 2, 3, big])[4]? == none
#guard (UInt32Array.mk #[1, 2, 3, big])[1]? == some 2

/-! Writing -/

#guard ((UInt32Array.mk #[1, 2, 3]).set 1 42 (by decide)).data == #[1, 42, 3]
#guard ((UInt32Array.mk #[1, 2, 3]).uset 2 42 (by simp)).data == #[1, 2, 42]
#guard ((UInt32Array.mk #[1, 2, 3]).set! 0 big).data == #[big, 2, 3]

-- Writing to a shared array must leave the original unchanged. The result is checked first so
-- that it is computed while the original is still live.
#guard
  let a := UInt32Array.mk #[1, 2, 3]
  let b := a.set! 1 42
  b.data == #[1, 42, 3] && a.data == #[1, 2, 3]
#guard
  let a := UInt32Array.mk #[1, 2, 3]
  let b := a.uset 0 big (by simp [a])
  b.data == #[big, 2, 3] && a.data == #[1, 2, 3]
#guard
  let a := UInt32Array.mk #[1, 2, 3]
  let b := a.set 2 big (by simp [a])
  b.data == #[1, 2, big] && a.data == #[1, 2, 3]

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

-- Inlined `push` and `uset` on a closed array must copy it on every call, not write into a shared
-- constant: a later call must not change an earlier result.
@[noinline] def UInt32Array.pushOntoConstant (x : UInt32) : UInt32Array :=
  (UInt32Array.emptyWithCapacity 10).push x

@[noinline] def UInt32Array.usetConstant (x : UInt32) : UInt32Array :=
  (UInt32Array.mk #[0, 0]).uset 0 x

#guard
  let a := UInt32Array.pushOntoConstant 1
  let b := UInt32Array.pushOntoConstant 2
  b.data == #[2] && a.data == #[1]

#guard
  let a := UInt32Array.usetConstant 1
  let b := UInt32Array.usetConstant 2
  b.data == #[2, 0] && a.data == #[1, 0]

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

#guard ((UInt32Array.mk #[0, 0, 0]).set! 1 big).data == #[0, big, 0]
#guard ((UInt32Array.mk #[big, big, big]).set! 1 0).data == #[big, 0, big]
#guard ((UInt32Array.mk #[0, 0, 0]).push big |>.push 0).data == #[0, 0, 0, big, 0]

/-! Indices beyond 16 bits, and huge `Nat` indices -/

#guard
  let a := (UInt32Array.mk (Array.replicate 100000 0)).set! 99999 big |>.set! 70000 1
  a.size == 100000 && a[99999]! == big && a[70000]! == 1 && a[99998]! == 0 &&
    a[70000 % 65536]! == 0 && a.data[99999]! == big && a.data[70000]! == 1 &&
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
  let b := (UInt32Array.mk a).set! 0 big
  b.data == #[big, 2, 3] && a == #[1, 2, 3]

#guard
  let a := UInt32Array.mk #[1, 2, 3]
  let d := a.data.set! 0 big
  d == #[big, 2, 3] && a.data == #[1, 2, 3]

/-! Runtime representation -/

#guard rawElemSize (UInt32Array.mk #[1, 2, 3]) == elemSize
#guard rawElemSize (UInt32Array.emptyWithCapacity 10) == elemSize
#guard rawElemSize (UInt32Array.empty.push 1) == elemSize
#guard rawElemSize ((UInt32Array.mk #[1]).push 2) == elemSize
#guard rawCapacity (UInt32Array.emptyWithCapacity 100) ≥ 100
#guard rawCapacity (UInt32Array.mk #[1, 2, 3]) ≥ 3
-- Growth is geometric, so pushing is amortized constant time.
#guard rawCapacity ((UInt32Array.mk #[1, 2, 3, 4]).push 5) ≥ 8


/-! Ensuring exclusivity and capacity -/

#guard (UInt32Array.mk #[1, 2, 3]).ensureExclusive.data == #[1, 2, 3]
#guard ((UInt32Array.mk #[1, 2, 3]).ensureCapacity 100).data == #[1, 2, 3]
#guard ((UInt32Array.mk #[1, 2, 3]).ensureCapacity 0).data == #[1, 2, 3]
#guard ((UInt32Array.mk #[1, 2, 3]).ensureExclusiveWithCapacity 100).data == #[1, 2, 3]
#guard ((UInt32Array.mk #[1, 2, 3]).ensureExclusiveWithCapacity 0).data == #[1, 2, 3]

#guard rawCapacity ((UInt32Array.mk #[1, 2, 3]).ensureCapacity 100) ≥ 100
#guard rawCapacity ((UInt32Array.mk #[1, 2, 3]).ensureExclusiveWithCapacity 100) ≥ 100
-- A copy never has less room than the size.
#guard rawCapacity ((UInt32Array.mk #[1, 2, 3]).ensureExclusiveWithCapacity 0) ≥ 3
#guard rawElemSize ((UInt32Array.mk #[1, 2, 3]).ensureCapacity 100) == elemSize

-- The array is built from a parameter so that it isn't extracted as a shared closed term.
@[noinline] def UInt32Array.ensuresInPlace (x : UInt32) : Bool :=
  let a := (UInt32Array.emptyWithCapacity 10).push x
  let p := rawAddr a
  let a := a.ensureExclusive.ensureCapacity 5 |>.ensureExclusiveWithCapacity 10
  rawAddr a == p && a.data == #[x]

-- Pushes after `ensureExclusiveWithCapacity` don't reallocate.
@[noinline] def UInt32Array.pushesInPlaceAfterEnsure (x : UInt32) : Bool :=
  let a := (UInt32Array.mk #[x]).ensureExclusiveWithCapacity 4
  let p := rawAddr a
  let a := a.push 2 |>.push 3 |>.push 4
  rawAddr a == p && a.data == #[x, 2, 3, 4]

-- `ensureCapacity` doesn't copy a shared array that has room.
@[noinline] def UInt32Array.ensureCapacityKeepsShared (x : UInt32) : Bool :=
  let a := (UInt32Array.emptyWithCapacity 10).push x
  let b := a.ensureCapacity 5
  rawAddr b == rawAddr a && b.data == #[x]

-- `ensureExclusiveWithCapacity` copies a shared array once, even when it also needs room.
@[noinline] def UInt32Array.ensureExclusiveWithCapacityCopiesShared (x : UInt32) : Bool :=
  let a := (UInt32Array.emptyWithCapacity 2).push x
  let b := a.ensureExclusiveWithCapacity 20
  rawAddr b != rawAddr a && rawCapacity b ≥ 20 && b.data == #[x] && a.data == #[x]

#guard UInt32Array.ensuresInPlace 1
#guard UInt32Array.pushesInPlaceAfterEnsure 1
#guard UInt32Array.ensureCapacityKeepsShared 1
#guard UInt32Array.ensureExclusiveWithCapacityCopiesShared 1

-- After any of them, a write to a shared array must leave the original unchanged. The results
-- are checked first so that they are computed while the original is still live.
#guard
  let a := UInt32Array.mk #[1, 2, 3]
  let b := a.ensureExclusive.set! 0 big
  b.data == #[big, 2, 3] && a.data == #[1, 2, 3]
#guard
  let a := UInt32Array.mk #[1, 2, 3]
  let b := (a.ensureCapacity 10).set! 0 big |>.push 4
  b.data == #[big, 2, 3, 4] && a.data == #[1, 2, 3]
#guard
  let a := UInt32Array.mk #[1, 2, 3]
  let b := (a.ensureExclusiveWithCapacity 10).set! 0 big |>.push 4
  b.data == #[big, 2, 3, 4] && a.data == #[1, 2, 3]

-- On a closed array, they must not hand out a shared constant: a later call must not change an
-- earlier result.
@[noinline] def UInt32Array.ensureExclusiveConstant (x : UInt32) : UInt32Array :=
  (UInt32Array.mk #[0, 0]).ensureExclusive.uset 0 x

@[noinline] def UInt32Array.ensureCapacityConstant (x : UInt32) : UInt32Array :=
  ((UInt32Array.mk #[0, 0]).ensureCapacity 10).uset 0 x |>.push x

@[noinline] def UInt32Array.ensureExclusiveWithCapacityConstant (x : UInt32) : UInt32Array :=
  ((UInt32Array.mk #[0, 0]).ensureExclusiveWithCapacity 10).uset 0 x |>.push x

#guard
  let a := UInt32Array.ensureExclusiveConstant 1
  let b := UInt32Array.ensureExclusiveConstant 2
  b.data == #[2, 0] && a.data == #[1, 0]

#guard
  let a := UInt32Array.ensureCapacityConstant 1
  let b := UInt32Array.ensureCapacityConstant 2
  b.data == #[2, 0, 2] && a.data == #[1, 0, 1]

#guard
  let a := UInt32Array.ensureExclusiveWithCapacityConstant 1
  let b := UInt32Array.ensureExclusiveWithCapacityConstant 2
  b.data == #[2, 0, 2] && a.data == #[1, 0, 1]


/-! Appending -/

#guard (UInt32Array.mk #[1, 2] ++ UInt32Array.mk #[3, big]).data == #[1, 2, 3, big]
#guard ((UInt32Array.mk #[1, 2]).append (UInt32Array.mk #[3])).data == #[1, 2, 3]
#guard (UInt32Array.mk #[1, 2] ++ UInt32Array.empty).data == #[1, 2]
#guard (UInt32Array.empty ++ UInt32Array.mk #[1, 2]).data == #[1, 2]
#guard (UInt32Array.empty ++ UInt32Array.empty).data == #[]
#guard (UInt32Array.mk #[0, 0] ++ UInt32Array.mk #[big] ++ UInt32Array.mk #[0]).data ==
  #[0, 0, big, 0]

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
    a := a ++ UInt32Array.mk #[i.toUInt32, (i * 7).toUInt32, big]
    r := r ++ #[i.toUInt32, (i * 7).toUInt32, big]
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
#guard rawElemSize (UInt32Array.mk #[1] ++ UInt32Array.mk #[2]) == elemSize

/-! Equality -/

#guard UInt32Array.mk #[1, 2, big] == UInt32Array.mk #[1, 2, big]
#guard UInt32Array.mk #[1, 2, big] != UInt32Array.mk #[1, 2, 0]
#guard UInt32Array.mk #[1, 2] != UInt32Array.mk #[1, 2, 0]
#guard UInt32Array.mk #[1, 2, 0] != UInt32Array.mk #[1, 2]
#guard UInt32Array.empty == UInt32Array.emptyWithCapacity 10
#guard (UInt32Array.mk #[1, 2] ++ UInt32Array.mk #[big]) == UInt32Array.mk #[1, 2, big]
-- Capacity and leftover memory past the size don't matter.
#guard (UInt32Array.emptyWithCapacity 100).push 1 == UInt32Array.mk #[1]
#guard (UInt32Array.mk #[1, 2, 3]).pop == UInt32Array.mk #[1, 2]
#guard (UInt32Array.mk (Array.replicate 100000 0)).set! 99999 big !=
  UInt32Array.mk (Array.replicate 100000 0)

/-! Decidable equality and hashing -/

#guard decide (UInt32Array.mk #[1, 2, big] = UInt32Array.mk #[1, 2, big])
#guard !decide (UInt32Array.mk #[1, 2, big] = UInt32Array.mk #[1, 2, 0])
#guard hash (UInt32Array.mk #[1, 2, big]) == hash #[(1 : UInt32), 2, big]
#guard hash (UInt32Array.empty) == hash (#[] : Array UInt32)
#guard hash ((UInt32Array.emptyWithCapacity 100).push 1) == hash (UInt32Array.mk #[1])

/-! Decidable membership and slice hashing -/

#guard (2 : UInt32) ∈ UInt32Array.mk #[1, 2, big]
#guard big ∈ UInt32Array.mk #[1, 2, big]
#guard (3 : UInt32) ∉ UInt32Array.mk #[1, 2, big]
#guard (0 : UInt32) ∉ UInt32Array.empty
#guard big ∈ (UInt32Array.mk #[0, 1, 2, big])[1...4]
#guard (0 : UInt32) ∉ (UInt32Array.mk #[0, 1, 2, big])[1...4]
#guard (2 : UInt32) ∉ (UInt32Array.mk #[0, 1, 2, big])[0...2]
#guard hash (UInt32Array.mk #[0, 1, 2, big])[1...3] == hash (UInt32Array.mk #[1, 2])
#guard hash (UInt32Array.mk #[0, 1, 2, big])[1...3] == hash (UInt32Array.mk #[big, 1, 2])[1...3]
#guard hash (∅ : UInt32Array.Slice) == hash UInt32Array.empty
#guard hash (UInt32Array.mk #[1, 2])[1...1] == hash (∅ : UInt32Array.Slice)

-- `decide` evaluates equality and membership for arrays and slices of literals.
example : UInt32Array.mk #[1, 2] = UInt32Array.mk #[1, 2] := by decide
example : UInt32Array.mk #[1, 2] ≠ UInt32Array.mk #[1, 3] := by decide
example : UInt32Array.mk #[1, 2] ≠ UInt32Array.mk #[1, 2, 3] := by decide
example : (2 : UInt32) ∈ UInt32Array.mk #[1, 2] := by decide
example : (3 : UInt32) ∉ UInt32Array.mk #[1, 2] := by decide
example : (2 : UInt32) ∈ (UInt32Array.mk #[1, 2, 3])[1...3] := by decide
example : (1 : UInt32) ∉ (UInt32Array.mk #[1, 2, 3])[1...3] := by decide

-- Lemmas that need decidable equality, used from another module.
example (a : UInt32Array) (x : UInt32) : a.contains x ↔ x ∈ a.toList := by simp
example (a : UInt32Array) (x : UInt32) (h : x ∈ a) :
    (if a.contains x then 1 else 0) = 1 := by simp [h]
example (s : UInt32Array.Slice) (x : UInt32) : s.contains x ↔ x ∈ s.copy := by simp
example (s t : UInt32Array.Slice) (h : s.copy = t.copy) : s == t := by simp [h]
example (s t : UInt32Array.Slice) (h : s == t) : hash s = hash t :=
  LawfulHashable.hash_eq s t h

/-! Iteration -/

#guard (UInt32Array.mk #[1, 2, big]).foldl (fun acc x => x :: acc) [] == [big, 2, 1]
#guard (UInt32Array.mk #[1, 2, big]).foldr (fun x acc => x :: acc) [] == [1, 2, big]
#guard UInt32Array.empty.foldl (fun acc x => x :: acc) [] == []
#guard UInt32Array.empty.foldr (fun x acc => x :: acc) [] == []
#guard (UInt32Array.mk #[1, 2, big]).foldlM (m := Option)
  (fun acc x => if x == 2 then none else some (x :: acc)) [] == none
#guard (UInt32Array.mk #[1, big]).foldrM (m := Option) (fun x acc => some (x :: acc)) [] ==
  some [1, big]

#guard Id.run do
  let mut r : List UInt32 := []
  for x in UInt32Array.mk #[1, 2, big] do
    r := x :: r
  return r == [big, 2, 1]

#guard Id.run do
  let mut r : List UInt32 := []
  for x in UInt32Array.mk #[1, 2, 3, 4] do
    if x == 3 then break
    r := x :: r
  return r == [2, 1]

#guard
  let r : StateM (List UInt32) Unit := (UInt32Array.mk #[1, 2, big]).forM fun x => modify (x :: ·)
  (r.run []).2 == [big, 2, 1]

#guard
  let xs := (Array.range 100000).map Nat.toUInt32
  let f := fun (acc : List UInt32) x => if x == 0 then x :: acc else acc
  (UInt32Array.mk xs).foldl f [] == xs.foldl f []

#guard (UInt32Array.mk #[1, 2, big]).any (· == big)
#guard !(UInt32Array.mk #[1, 2, 3]).any (· == big)
#guard (UInt32Array.mk #[1, 2, 3]).all (· != big)
#guard !(UInt32Array.mk #[1, big, 3]).all (· != big)
#guard !UInt32Array.empty.any (fun _ => true) && UInt32Array.empty.all (fun _ => false)
#guard (UInt32Array.mk #[1, 2, big]).contains big
#guard !(UInt32Array.mk #[1, 2, 3]).contains big && !UInt32Array.empty.contains big

-- Early exits, and loops in a monad other than `Id`.
#guard (UInt32Array.mk #[1, 2, big]).foldrM (m := Option)
  (fun x acc => if x == 1 then none else some (x :: acc)) [] == none
#guard (UInt32Array.mk #[big, 2, 1]).foldrM (m := Option)
  (fun x acc => if x == big then none else some (x :: acc)) [] == none
#guard
  let r : StateM (List UInt32) Unit := do
    for x in UInt32Array.mk #[1, 2, big, 3] do
      if x == big then break
      modify (x :: ·)
  (r.run []).2 == [2, 1]
#guard
  let r : StateM (List UInt32) Unit :=
    (UInt32Array.mk #[1, 2, big]).foldrM (fun x _ => modify (x :: ·)) ⟨⟩
  (r.run []).2 == [1, 2, big]
#guard Id.run do
  let mut r : List UInt32 := []
  for x in UInt32Array.empty do
    r := x :: r
  return r == []
#guard !(UInt32Array.mk #[1, 2, 3]).contains big
#guard (UInt32Array.mk (Array.replicate 100000 0) |>.set! 99999 big).contains big

/-! Removing elements -/

#guard UInt32Array.empty.isEmpty && !(UInt32Array.mk #[1]).isEmpty
#guard (UInt32Array.mk #[1]).pop.isEmpty
#guard (UInt32Array.mk #[1, 2, big]).pop.data == #[1, 2]
#guard UInt32Array.empty.pop.data == #[]
#guard ((UInt32Array.mk #[1, 2, 3]).pop.push big).data == #[1, 2, big]
#guard (UInt32Array.mk #[1, 2, big]).back? == some big
#guard UInt32Array.empty.back? == none
#guard (UInt32Array.mk #[1, 2, big]).back! == big
#guard (UInt32Array.mk #[1, 2, big]).back (by decide) == big

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

#guard (UInt32Array.mk #[1, 0, big, 0, 0]).popWhile (· == 0) == UInt32Array.mk #[1, 0, big]
#guard (UInt32Array.mk #[1, 0, big]).popWhile (· == 0) == UInt32Array.mk #[1, 0, big]
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

#guard ((UInt32Array.mk #[1, 2, 3, big]).extract 1 3).data == #[2, 3]
#guard ((UInt32Array.mk #[1, 2, 3, big]).extract 2 100).data == #[3, big]
#guard ((UInt32Array.mk #[1, 2, 3]).extract 0 3).data == #[1, 2, 3]
#guard ((UInt32Array.mk #[1, 2, 3]).extract 2 1).data == #[]
#guard ((UInt32Array.mk #[1, 2, 3]).extract 5 9).data == #[]
#guard ((UInt32Array.mk #[1, 2, 3]).extract (2 ^ 70) (2 ^ 71)).data == #[]
#guard ((UInt32Array.mk #[1, 2, 3]).extract 1 (2 ^ 70)).data == #[2, 3]
#guard
  let xs := (Array.range 100000).map Nat.toUInt32
  ((UInt32Array.mk xs).extract 70000 70010).data == xs.extract 70000 70010
#guard rawElemSize ((UInt32Array.mk #[1, 2, 3]).extract 1 2) == elemSize

-- The extracted array is independent of the original.
#guard
  let a := UInt32Array.mk #[1, 2, 3]
  let b := (a.extract 0 2).set! 0 big
  b.data == #[big, 2] && a.data == #[1, 2, 3]

/-! Building arrays -/

#guard (UInt32Array.replicate 3 big).data == #[big, big, big]
#guard (UInt32Array.replicate 0 1).data == #[]
#guard (UInt32Array.replicate 100000 big).data == Array.replicate 100000 big
#guard (UInt32Array.ofFn (n := 4) fun i => i.val.toUInt32).data == #[0, 1, 2, 3]
#guard (UInt32Array.ofFn (n := 0) fun i => i.val.toUInt32).data == #[]
#guard rawElemSize (UInt32Array.replicate 2 1) == elemSize
#guard rawElemSize (UInt32Array.ofFn (n := 2) fun _ => 1) == elemSize

/-! Lemmas -/

example (a : UInt32Array) (v : UInt32) : (a.push v).pop = a := by simp [UInt32Array.ext_iff]
example : (UInt32Array.replicate 3 big)[1] = big := by simp
example (a b : UInt32Array) (h : 0 < a.size) : (a ++ b)[0]'(by simp; lia) = a[0] := by simp [h]
example (a : UInt32Array) (i : Nat) (v : UInt32) (h : i < a.size) :
    (a.set i v h)[i]'(by simpa) = v := by simp
example (a : UInt32Array) : a.extract 0 a.size = a := by simp
example (a : UInt32Array) (v : UInt32) : (a.push v).pop = a :=
  UInt32Array.ext_getElem (by simp) (by simp_all)

/-! Default bounds proofs -/

#guard (UInt32Array.mk #[1, 2, big]).get 2 == big
#guard (UInt32Array.mk #[1, 2, big]).uget 2 == big
#guard ((UInt32Array.mk #[1, 2, 3]).set 1 big).data == #[1, big, 3]
#guard ((UInt32Array.mk #[1, 2, 3]).uset 1 big).data == #[1, big, 3]

/-! `set!` leaves the array unchanged when the index is out of bounds, like `ByteArray.set!`. -/

#guard ((UInt32Array.mk #[1, 2, 3]).set! 3 big).data == #[1, 2, 3]
#guard ((UInt32Array.mk #[1, 2, 3]).set! (2 ^ 70) big).data == #[1, 2, 3]

/-! Folds over part of an array -/

#guard (UInt32Array.mk #[1, 2, 3, big]).foldl (fun acc x => x :: acc) [] 1 3 == [3, 2]
#guard (UInt32Array.mk #[1, 2, 3, big]).foldl (fun acc x => x :: acc) [] 2 == [big, 3]
#guard (UInt32Array.mk #[1, 2, 3, big]).foldl (fun acc x => x :: acc) [] 1 100 == [big, 3, 2]
#guard (UInt32Array.mk #[1, 2, 3, big]).foldl (fun acc x => x :: acc) [] 3 1 == []
#guard (UInt32Array.mk #[1, 2, 3, big]).foldl (fun acc x => x :: acc) [] 9 12 == []
#guard (UInt32Array.mk #[1, 2, 3]).foldlM (m := Option)
  (fun acc x => if x == 1 then none else some (x :: acc)) [] 1 == some [3, 2]

/-! Copying slices -/

#guard
  let src := UInt32Array.mk #[10, 11, 12, big]
  let dest := UInt32Array.mk #[1, 2, 3, 4, 5]
  (src.copySlice 1 dest 2 2).data == #[1, 2, 11, 12, 5] &&
  (src.copySlice 1 dest 4 3).data == #[1, 2, 3, 4, 11, 12, big] &&
  (src.copySlice 0 dest 9 2).data == #[1, 2, 3, 4, 5, 10, 11] &&
  (src.copySlice 9 dest 1 2).data == #[1, 2, 3, 4, 5] &&
  (src.copySlice 2 dest 0 10).data == #[12, big, 3, 4, 5] &&
  (src.copySlice 0 dest 0 0).data == #[1, 2, 3, 4, 5] &&
  (src.copySlice 0 UInt32Array.empty 0 4).data == #[10, 11, 12, big] &&
  dest.data == #[1, 2, 3, 4, 5] && src.data == #[10, 11, 12, big]

-- Copying from an array into itself.
#guard
  let a := UInt32Array.mk #[1, 2, 3, big]
  (a.copySlice 0 a 2 4).data == #[1, 2, 1, 2, 3, big]

#guard
  let xs := (Array.range 100000).map Nat.toUInt32
  let a := UInt32Array.mk xs
  (a.copySlice 70000 (UInt32Array.replicate 10 0) 5 10).data ==
    Array.replicate 5 0 ++ xs.extract 70000 70010

#guard rawElemSize ((UInt32Array.mk #[1]).copySlice 0 UInt32Array.empty 0 1) == elemSize

@[noinline] def UInt32Array.copiesSliceInPlace (x : UInt32) : Bool :=
  let dest := (UInt32Array.emptyWithCapacity 10).push x |>.push x |>.push x
  let p := rawAddr dest
  let dest := (UInt32Array.mk #[big, big]).copySlice 0 dest 1 2
  rawAddr dest == p && dest.data == #[x, big, big]

@[noinline] def UInt32Array.copySliceGrowth (x : UInt32) : Bool :=
  let dest := (UInt32Array.mk #[x, x, x, x])
  rawCapacity ((UInt32Array.mk #[x]).copySlice 0 dest 4 1 (exact := false)) ≥ 8 &&
    rawCapacity ((UInt32Array.mk #[x]).copySlice 0 dest 4 1) == 5

#guard UInt32Array.copiesSliceInPlace 1
#guard UInt32Array.copySliceGrowth 1

/-! Linearity markers -/

#guard ((UInt32Array.mk #[1, 2]).markLinear.push big).data == #[1, 2, big]
#guard ((UInt32Array.mk #[1]).propagateMark (UInt32Array.mk #[2, big])).data == #[2, big]

/-! Search -/

#guard (UInt32Array.mk #[1, 2, big, 2]).findIdx? (· == 2) == some 1
#guard (UInt32Array.mk #[1, 2, big, 2]).findIdx? (· == 2) 2 == some 3
#guard (UInt32Array.mk #[1, 2, big, 2]).findIdx? (· == 3) == none
#guard (UInt32Array.mk #[1, 2, big, 2]).findIdx? (· == 1) 9 == none
#guard ((UInt32Array.mk #[1, 2, big, 2]).findFinIdx? (· == big)).map (·.val) == some 2

/-! Lists -/

#guard (UInt32Array.ofList [1, 2, big]).data == #[1, 2, big]
#guard (UInt32Array.ofList []).data == #[]
#guard [1, 2, big].toUInt32Array == UInt32Array.mk #[1, 2, big]
#guard (UInt32Array.ofList ((List.range 100000).map Nat.toUInt32)).data ==
  (Array.range 100000).map Nat.toUInt32
#guard rawElemSize (UInt32Array.ofList [1, 2]) == elemSize

/-! More lemmas -/

example (a b c : UInt32Array) : a ++ b ++ c = a ++ (b ++ c) := UInt32Array.append_assoc ..
example (a : UInt32Array) : a ++ ∅ = a := by simp
example (a b : UInt32Array) : (a ++ b).extract 0 a.size = a := by simp
example (a : UInt32Array) (i : Nat) (v : UInt32) : (a.set! i v).size = a.size := by simp
example (l : List UInt32) : (UInt32Array.ofList l).toList = l := by simp
example (a : UInt32Array) : UInt32Array.ofList a.toList = a := by simp

/-! Slices -/

#guard
  let a := UInt32Array.mk #[1, 2, 3, big]
  let s := a[1...3]
  s.size == 2 && s[0]! == 2 && s[1]! == 3 && s.getD 2 7 == 7 && s.copy == UInt32Array.mk #[2, 3] &&
    s.toList == [2, 3] && s.toArray == #[2, 3]

#guard
  let a := UInt32Array.mk #[1, 2, 3, big]
  a[1...=3].toList == [2, 3, big] && a[*...2].toList == [1, 2] && a[2...*].toList == [3, big] &&
    a[*...*].toList == [1, 2, 3, big] && a[0<...2].toList == [2] &&
    a[0<...=2].toList == [2, 3] && a[*...=1].toList == [1, 2] && a[1<...*].toList == [3, big]

-- Bounds are clamped.
#guard
  let a := UInt32Array.mk #[1, 2, 3, big]
  a[2...100].toList == [3, big] && a[3...1].size == 0 && a[9...12].size == 0 &&
    (a.toSlice 1 (2 ^ 70)).toList == [2, 3, big]

-- Slices of slices.
#guard
  let s := (UInt32Array.mk #[1, 2, 3, big])[1...4]
  s[1...2].toList == [3] && s[0...100].toList == [2, 3, big] && s[*...*].toList == [2, 3, big] &&
    s[2...*].toList == [big] && s[5...6].size == 0

#guard
  let s := (UInt32Array.mk #[1, 2, 3, big])[1...4]
  s.popFront.toList == [3, big] && s.popFront.popFront.popFront.popFront.size == 0

#guard (∅ : UInt32Array.Slice).size == 0 && (default : UInt32Array.Slice).toList == []

-- An array coerces to the slice of all its elements.
#guard
  let s : UInt32Array.Slice := UInt32Array.mk #[1, 2, big]
  s.toList == [1, 2, big] && s.start == 0

-- A slice does not coerce back to an array, since that would copy.
example (s : UInt32Array.Slice) : UInt32Array := s.copy

#guard Id.run do
  let mut r : List UInt32 := []
  for x in (UInt32Array.mk #[1, 2, 3, big])[1...*] do
    r := x :: r
  return r == [big, 3, 2]

#guard (UInt32Array.mk #[1, 2, 3, big])[1...*].foldl (fun acc x => x :: acc) [] == [big, 3, 2]

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
  let s := (UInt32Array.mk #[1, 2, 3, big, 2])[1...5]
  s.foldr (fun x acc => x :: acc) [] == [2, 3, big, 2] &&
    s.foldl (fun acc x => x :: acc) [] == [2, big, 3, 2] &&
    s.any (· == big) && !s.any (· == 1) && s.all (· != 1) && !s.all (· == 2) &&
    s.contains big && !s.contains 1 && s.count (· == 2) == 2 &&
    s.find? (· > 2) == some 3 && s.findRev? (· != big) == some 2 && s.findRev? (· == 1) == none

#guard (UInt32Array.mk #[1, 2, 3])[1...1].foldr (fun x acc => x :: acc) [] == []
#guard (UInt32Array.mk #[1, 2, 3])[3...*].find? (fun _ => true) == none

#guard
  let s := (UInt32Array.mk #[1, 2, 3, big])[1...*]
  let r : StateM (List UInt32) Unit := s.forRevM fun x => modify (x :: ·)
  (r.run []).2 == [2, 3, big]

#guard Id.run ((UInt32Array.mk #[1, 2, big])[*...*].findSomeRevM?
  (fun x => pure (if x == 2 then some x else none))) == some 2

-- The loops over slices stay within the slice, both with `start > 0` and with `stop < size`.
#guard
  let s := (UInt32Array.mk #[big, 1, 2, 3, big])[1...4]
  s.foldr (fun x acc => x :: acc) [] == [1, 2, 3] &&
    s.foldl (fun acc x => x :: acc) [] == [3, 2, 1] && s.toList == [1, 2, 3] &&
    !s.any (· == big) && s.all (· != big) && !s.contains big && s.count (· != big) == 3 &&
    s.find? (· == big) == none && s.findRev? (· == big) == none &&
    s.find? (· != 1) == some 2 && s.findRev? (· != 3) == some 2

#guard Id.run do
  let mut r : List UInt32 := []
  for x in (UInt32Array.mk #[big, 1, 2, 3, big])[1...4] do
    r := x :: r
  return r == [3, 2, 1]

-- Early exits.
#guard Id.run do
  let mut r : List UInt32 := []
  for x in (UInt32Array.mk #[big, 1, 2, 3, big])[1...5] do
    if x == 3 then break
    r := x :: r
  return r == [2, 1]

#guard
  let s := (UInt32Array.mk #[1, 2, big, 3, big])[1...5]
  s.any (· == big) && !s.all (· != big) && s.find? (· == big) == some big &&
    s.find? (· != 2) == some big && s.findRev? (· == big) == some big &&
    s.findRev? (· != big) == some 3

-- Empty slices.
#guard
  let s := (UInt32Array.mk #[1, 2, 3])[1...1]
  s.foldl (fun acc x => x :: acc) [] == [] && s.toList == [] && !s.any (fun _ => true) &&
    s.all (fun _ => false) && s.count (fun _ => true) == 0 && s.find? (fun _ => true) == none &&
    s.findRev? (fun _ => true) == none && Id.run do
      let mut r : List UInt32 := []
      for x in s do
        r := x :: r
      return r == []
#guard
  let s := (∅ : UInt32Array.Slice)
  s.foldr (fun x acc => x :: acc) [] == [] && s.foldl (fun acc x => x :: acc) [] == [] &&
    !s.any (fun _ => true)

-- Loops in a monad other than `Id`.
#guard
  let r : StateM (List UInt32) Unit := do
    for x in (UInt32Array.mk #[big, 1, 2, 3, big])[1...5] do
      if x == 3 then break
      modify (x :: ·)
  (r.run []).2 == [2, 1]
#guard
  let s := (UInt32Array.mk #[big, 1, 2, 3, big])[1...4]
  let r : StateM (List UInt32) Unit := s.foldrM (fun x _ => modify (x :: ·)) ⟨⟩
  (r.run []).2 == [1, 2, 3]
#guard
  let s := (UInt32Array.mk #[big, 1, 2, 3, big])[1...4]
  let r : StateM (List UInt32) Unit := s.foldlM (fun _ x => modify (x :: ·)) ⟨⟩
  (r.run []).2 == [3, 2, 1]
#guard (UInt32Array.mk #[big, 1, 2, 3, big])[1...4].foldlM (m := Option)
  (fun acc x => if x == 2 then none else some (x :: acc)) [] == none
#guard (UInt32Array.mk #[big, 1, 2, 3, big])[1...4].foldrM (m := Option)
  (fun x acc => if x == 2 then none else some (x :: acc)) [] == none
#guard (UInt32Array.mk #[big, 1, 2, 3, big])[1...4].foldlM (m := Option)
  (fun acc x => some (x :: acc)) [] == some [3, 2, 1]
#guard (UInt32Array.mk #[big, 1, 2, 3, big])[1...4].findSomeRevM? (m := Option)
  (fun x => if x == 3 then some none else some (some x)) == some (some 2)
#guard
  let xs := (Array.range 100000).map Nat.toUInt32
  let s := (UInt32Array.mk xs)[100...99900]
  let f := fun (acc : List UInt32) x => if x == 0 then x :: acc else acc
  s.foldl f [] == (xs.extract 100 99900).foldl f [] &&
    s.foldr (fun x acc => f acc x) [] == (xs.extract 100 99900).foldr (fun x acc => f acc x) []

/-! The `Std.Iterators` API on arrays and slices -/

#guard (UInt32Array.mk #[1, 2, 3]).iter.toList == [1, 2, 3]
#guard ((UInt32Array.mk #[1, 2, 3]).iter.map (· * 2)).toUInt32Array == UInt32Array.mk #[2, 4, 6]
#guard ((UInt32Array.mk #[1, 2, 3, big]).iter.filter (· != 2)).toUInt32Array ==
  UInt32Array.mk #[1, 3, big]
#guard ((UInt32Array.mk #[1, 2, 3, big]).iter.take 2).toUInt32Array == UInt32Array.mk #[1, 2]
#guard ((UInt32Array.mk #[1, 2, 3, big]).iter.drop 2).toUInt32Array == UInt32Array.mk #[3, big]
#guard (((UInt32Array.mk #[1, 2, 3]).iter.zip (UInt32Array.mk #[big, 5]).iter).map
  fun (x, y) => x + y).toUInt32Array == UInt32Array.mk #[1 + big, 7]
#guard ((UInt32Array.mk #[1, 2, 3, big])[1...3].iter.map (· + 1)).toUInt32Array ==
  UInt32Array.mk #[3, 4]
#guard (UInt32Array.mk #[1, 2, 3]).iter.length == 3
#guard UInt32Array.empty.iter.toUInt32Array == UInt32Array.empty
#guard
  let xs := (Array.range 100000).map Nat.toUInt32
  ((UInt32Array.mk xs).iter.map (· + 1)).toUInt32Array.data == xs.map (· + 1)
#guard rawElemSize ((UInt32Array.mk #[1]).iter.toUInt32Array) == elemSize
#guard (UInt32Array.mk #[1, 2, 3]).iter.toUInt32ArrayWithCapacity 100 ==
  UInt32Array.mk #[1, 2, 3]
#guard rawCapacity ((UInt32Array.mk #[1, 2, 3]).iter.toUInt32ArrayWithCapacity 100) ≥ 100

/-! Membership, `ForM` and slice equality -/

#guard
  let a := UInt32Array.mk #[1, 2, big]
  let r : StateM (List UInt32) PUnit := forM a fun x => modify (x :: ·)
  (r.run []).2 == [big, 2, 1]
#guard
  let s := (UInt32Array.mk #[0, 1, 2, big])[1...3]
  let r : StateM (List UInt32) PUnit := forM s fun x => modify (x :: ·)
  (r.run []).2 == [2, 1]
#guard
  let r : StateM (List UInt32) PUnit := forM UInt32Array.empty fun x => modify (x :: ·)
  (r.run []).2 == []
#guard (UInt32Array.mk #[0, 1, 2, big])[1...3] == (UInt32Array.mk #[1, 2, 5])[0...2]
#guard (UInt32Array.mk #[1, big, 1, big])[0...2] == (UInt32Array.mk #[1, big, 1, big])[2...4]
#guard (UInt32Array.mk #[0, 1, 2, big])[1...3] != (UInt32Array.mk #[1, 2, 5])[0...3]
#guard (UInt32Array.mk #[0, 1, 2, big])[1...3] != (UInt32Array.mk #[1, big])[0...2]
#guard (UInt32Array.mk #[0, 1, 2, big])[1...3] != (UInt32Array.mk #[2, 1])[0...2]
#guard (∅ : UInt32Array.Slice) == (UInt32Array.mk #[1, 2])[1...1]
#guard (UInt32Array.mk #[1, 2, big] : UInt32Array.Slice) ==
  (UInt32Array.mk #[0, 1, 2, big])[1...*]
#guard
  let xs := (Array.range 100000).map Nat.toUInt32
  (UInt32Array.mk (#[0] ++ xs))[1...*] == (UInt32Array.mk (xs ++ #[0]))[0...100000] &&
    (UInt32Array.mk (#[0] ++ xs))[1...*] != (UInt32Array.mk (xs.set! 99999 0))[0...100000]

/-! Writing through slices -/

#guard ((UInt32Array.mk #[1, 2, 3, 4])[1...3].set 1 big).array.data == #[1, 2, big, 4]
#guard ((UInt32Array.mk #[1, 2, 3, 4])[1...3].set! 1 big).toList == [2, big]
#guard ((UInt32Array.mk #[1, 2, 3, 4])[1...3].set! 2 big).array.data == #[1, 2, 3, 4]
#guard ((UInt32Array.mk #[1, 2, 3, 4])[1...3].modify 0 (· * 10)).array.data == #[1, 20, 3, 4]
#guard ((UInt32Array.mk #[1, 2, 3, 4])[1...3].modify 2 (· * 10)).array.data == #[1, 2, 3, 4]
#guard ((UInt32Array.mk #[1, 2, 3, big])[1...4].swap 0 2).array.data == #[1, big, 3, 2]
#guard ((UInt32Array.mk #[1, 2, 3, big])[1...4].swap 1 1).array.data == #[1, 2, 3, big]
#guard ((UInt32Array.mk #[0, 1, 2, 3, 4, 0])[1...5].reverse).array.data == #[0, 4, 3, 2, 1, 0]
#guard ((UInt32Array.mk #[0, 1, 2, 3, 0])[1...4].reverse).array.data == #[0, 3, 2, 1, 0]
#guard ((UInt32Array.mk #[1, 2])[1...1].reverse).array.data == #[1, 2]
#guard (∅ : UInt32Array.Slice).reverse.toList == []

-- `foldlInPlace` on a slice shifts its range right by one, inserting the initial accumulator.
#guard
  let r := (UInt32Array.mk #[1, 2, 3, 4])[1...3].foldlInPlace 9 (fun _ _ x b => (b, x))
  r.1.array.data == #[1, 9, 2, 4] && r.2 == 3 && r.1.start == 1 && r.1.stop == 3
#guard
  let r := (UInt32Array.mk #[1, 2, 3, 4])[2...2].foldlInPlace 9 (fun _ _ x b => (b, x))
  r.1.array.data == #[1, 2, 3, 4] && r.2 == 9

-- `foldrInPlace` shifts the range left by one, from the last element to the first.
#guard
  let r := (UInt32Array.mk #[1, 2, 3, 4])[1...3].foldrInPlace 9 (fun _ _ x b => (b, x))
  r.1.array.data == #[1, 3, 9, 4] && r.2 == 2 && r.1.start == 1 && r.1.stop == 3
#guard
  let r := (UInt32Array.mk #[1, 2, 3, 4])[2...2].foldrInPlace 9 (fun _ _ x b => (b, x))
  r.1.array.data == #[1, 2, 3, 4] && r.2 == 9

-- The `Then` versions hand the slice and the last accumulator to `g`, here to store it.
#guard
  let s := (UInt32Array.mk #[1, 2, 3, 4])[0...4]
  (s.foldlInPlaceThen 9 (fun _ _ x b => (b, x)) (fun s b => s.set! 0 b)).toList == [4, 1, 2, 3] &&
    (s.foldrInPlaceThen 9 (fun _ _ x b => (b, x)) (fun s b => s.set! 3 b)).toList ==
      [2, 3, 4, 1]
#guard
  let r := (UInt32Array.mk #[1, 2, 3, 4])[0...3].foldlInPlaceThen 9 (fun _ _ x b => (b, x))
    (fun s b => s.array.set! 3 b)
  r.data == #[9, 1, 2, 3]
#guard
  let a := UInt32Array.mk #[1, 2, 3, 4]
  let r := a[1...3].foldlInPlaceThen 9 (fun _ _ x b => (b, x)) Prod.mk
  let r' := a[1...3].foldrInPlaceThen 9 (fun _ _ x b => (b, x)) Prod.mk
  r.1.array.data == #[1, 9, 2, 4] && r.2 == 3 && r'.1.array.data == #[1, 3, 9, 4] && r'.2 == 2 &&
    a.data == #[1, 2, 3, 4]

-- The indices passed to `f`, counted from the start of the slice, in the order of the visits.
#guard
  let s := (UInt32Array.mk #[1, 2, 3, 4, 5])[1...4]
  (s.foldlInPlace [] (fun k _ x b => (x, k.toNat :: b))).2 == [2, 1, 0] &&
    (s.foldrInPlace [] (fun k _ x b => (x, k.toNat :: b))).2 == [0, 1, 2]

-- The folds agree with the pure folds of `foldlInPlace_eq_foldl_finRange` and
-- `foldrInPlace_eq_foldr_finRange`, and leave the array outside the slice unchanged.
#guard
  let s := (UInt32Array.mk #[1, 2, 3, 4, 5])[1...4]
  let r := s.foldlInPlace 7 (fun _ _ x b => (x * 2 + b, x))
  let r' := s.foldrInPlace 7 (fun _ _ x b => (x * 2 + b, x))
  (r.1.copy.toList, r.2) == (List.finRange s.size).foldl
      (fun (acc : List UInt32 × UInt32) i => (acc.1 ++ [s[i] * 2 + acc.2], s[i])) ([], 7) &&
    (r'.1.copy.toList, r'.2) == (List.finRange s.size).foldr
      (fun i (acc : List UInt32 × UInt32) => ((s[i] * 2 + acc.2) :: acc.1, s[i])) ([], 7) &&
    r.1.array[0]! == 1 && r.1.array[4]! == 5 && r'.1.array[0]! == 1 && r'.1.array[4]! == 5 &&
    r.1.array.size == 5 && r'.1.array.size == 5

-- Writing through a slice of a shared array must leave the original unchanged.
#guard
  let a := UInt32Array.mk #[1, 2, 3, 4]
  let s := a[1...4].set 0 big
  s.array.data == #[1, big, 3, 4] && a.data == #[1, 2, 3, 4]
#guard
  let a := UInt32Array.mk #[1, 2, 3, 4]
  let s := a[0...4].reverse
  s.array.data == #[4, 3, 2, 1] && a.data == #[1, 2, 3, 4]
#guard
  let a := UInt32Array.mk #[1, 2, 3, 4]
  let r := a[0...4].foldlInPlace 9 (fun _ _ x b => (b, x))
  r.1.array.data == #[9, 1, 2, 3] && a.data == #[1, 2, 3, 4]
#guard
  let a := UInt32Array.mk #[1, 2, 3, 4]
  let r := a[0...4].foldrInPlace 9 (fun _ _ x b => (b, x))
  r.1.array.data == #[2, 3, 4, 9] && a.data == #[1, 2, 3, 4]

-- `f` must see the elements of the original even when it reads them from the shared array itself.
#guard
  let a := UInt32Array.mk #[1, 2, 3, 4]
  let r := a[1...4].foldlInPlace 0 (fun k _ _ b => (a[k.toNat]!, b))
  let r' := a[1...4].foldrInPlace 0 (fun k _ _ b => (a[k.toNat]!, b))
  r.1.array.data == #[1, 1, 2, 3] && r'.1.array.data == #[1, 1, 2, 3] && a.data == #[1, 2, 3, 4]
#guard
  let s := (UInt32Array.mk #[1, 2, 3, 4])[0...4]
  let t := s.swap 0 3
  t.toList == [4, 2, 3, 1] && s.toList == [1, 2, 3, 4]

-- A slice of an array that is no longer used writes into that array, without copying it.
@[noinline] def UInt32Array.writesThroughSliceInPlace (x : UInt32) : Bool :=
  let a := (UInt32Array.emptyWithCapacity 8).push x |>.push 2 |>.push 3 |>.push 4 |>.push x
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

#guard UInt32Array.writesThroughSliceInPlace 1

-- Reversing a large slice takes linear time only when every swap writes in place.
#guard
  let n := 1000000
  let xs := (Array.range n).map Nat.toUInt32
  (UInt32Array.mk xs)[0...n].reverse.array.data == xs.reverse

/-! Folding over windows of one array -/

-- `foldlInPlace2` and `foldlInPlace2Then` with the bounds checked at run time.
private def fold2 {β : Type} (a : UInt32Array) (xs ys rs len : USize) (init : β)
    (f : (j : USize) → j.toNat < len.toNat → UInt32 → UInt32 → β → UInt32 × β) :
    Option (UInt32Array × β) :=
  if h : xs.toNat + len.toNat ≤ a.size ∧ ys.toNat + len.toNat ≤ a.size ∧
      rs.toNat + len.toNat ≤ a.size then
    some (a.foldlInPlace2 xs ys rs len h.1 h.2.1 h.2.2 init f)
  else
    none

private def fold2Then {β γ : Type} (a : UInt32Array) (xs ys rs len : USize) (init : β)
    (f : (j : USize) → j.toNat < len.toNat → UInt32 → UInt32 → β → UInt32 × β)
    (g : UInt32Array → β → γ) : Option γ :=
  if h : xs.toNat + len.toNat ≤ a.size ∧ ys.toNat + len.toNat ≤ a.size ∧
      rs.toNat + len.toNat ≤ a.size then
    some (a.foldlInPlace2Then xs ys rs len h.1 h.2.1 h.2.2 init f fun a' _ b => g a' b)
  else
    none

-- Disjoint windows, and the accumulator.
#guard (fold2 (UInt32Array.mk #[1, 2, 3, 4, 5, 6, 0, 0, 0]) 0 3 6 3 0
  (fun _ _ x y c => (x + y, c + 1))).map (fun r => (r.1.data, r.2)) ==
    some (#[1, 2, 3, 4, 5, 6, 5, 7, 9], 3)

-- Overlapping windows: each step reads what the earlier steps wrote.
#guard (fold2 (UInt32Array.mk #[1, 0, 0, 0, 0]) 0 0 1 4 () (fun _ _ x y c => (x + y, c))).map
  (·.1.data) == some #[1, 2, 4, 8, 16]
#guard (fold2 (UInt32Array.mk #[0, 1, 2, 3, big]) 1 1 0 4 () (fun _ _ x _ c => (x, c))).map
  (·.1.data) == some #[1, 2, 3, big, big]
#guard (fold2 (UInt32Array.mk #[1, 2, 3, 4]) 0 1 0 3 () (fun _ _ x y c => (x + y, c))).map
  (·.1.data) == some #[3, 5, 7, 4]
#guard (fold2 (UInt32Array.mk #[1, 1, 1, 1, 1]) 0 1 1 4 () (fun _ _ x y c => (x + y, c))).map
  (·.1.data) == some #[1, 2, 3, 4, 5]

-- The indices passed to `f`, in the order of the visits, and the empty fold.
#guard (fold2 (UInt32Array.mk #[1, 2, 3]) 0 0 0 3 [] (fun j _ x _ c => (x, j.toNat :: c))).map
  (·.2) == some [2, 1, 0]
#guard (fold2 (UInt32Array.mk #[1, 2, 3]) 3 0 1 0 big (fun _ _ x _ c => (x, c))).map
  (fun r => (r.1.data, r.2)) == some (#[1, 2, 3], big)

-- The `Then` form hands the array and the last accumulator to `g`, here to store it.
#guard fold2Then (UInt32Array.mk #[1, 2, 3, 0]) 0 1 0 2 (0 : UInt32)
  (fun _ _ x y c => (x + y, c + x)) (fun a c => (a.set! 3 c).data) == some #[3, 5, 3, 3]
#guard (fold2Then (UInt32Array.mk #[1, 2]) 0 0 0 2 () (fun _ _ x _ c => (x + 1, c))
  Prod.mk).map (·.1.data) == some #[2, 3]

-- The size proof that `g` receives bounds its reads.
#guard
  let a := UInt32Array.mk #[1, 2, 3]
  if h : (0 : USize).toNat + (2 : USize).toNat ≤ a.size ∧
      (1 : USize).toNat + (2 : USize).toNat ≤ a.size ∧ 2 < a.size then
    a.foldlInPlace2Then 0 1 0 2 h.1 h.2.1 h.1 () (fun _ _ x y c => (x + y, c))
      (fun a' h' _ => a'[2]'(by rw [h']; exact h.2.2) + a'[0]'(by rw [h']; lia)) == 6
  else false

-- Folding over windows of a shared array must leave the original unchanged, and `f` must see the
-- elements of the original when it reads them from the shared array itself.
#guard
  let a := UInt32Array.mk #[1, 2, 3, 4]
  let r := fold2 a 0 1 0 3 () (fun _ _ x y c => (x + y, c))
  r.map (·.1.data) == some #[3, 5, 7, 4] && a.data == #[1, 2, 3, 4]
#guard
  let a := UInt32Array.mk #[1, 2, 3, 4]
  let r := fold2 a 0 0 1 3 () (fun j _ _ _ c => (a[j.toNat]!, c))
  r.map (·.1.data) == some #[1, 1, 2, 3] && a.data == #[1, 2, 3, 4]

-- An exclusive array is written in place, without copying it.
@[noinline] def UInt32Array.foldsWindowsInPlace (x : UInt32) : Bool :=
  let a := (UInt32Array.emptyWithCapacity 6).push x |>.push 2 |>.push 3 |>.push 0 |>.push 0
  let p := rawAddr a
  match fold2 a 0 1 2 3 () (fun _ _ x y c => (x + y, c)) with
  | some (a, _) => rawAddr a == p && a.data == #[x, 2, x + 2, x + 4, x + x + 6]
  | none => false

#guard UInt32Array.foldsWindowsInPlace 1

-- Prefix sums in place over a large array take linear time only when every write is in place.
#guard
  let n := 100000
  let r := Id.run do
    let mut r := Array.replicate n (1 : UInt32)
    for i in [1:n] do
      r := r.set! i (r[i - 1]! + r[i]!)
    return r
  (fold2 (UInt32Array.replicate n 1) 0 1 1 (n - 1).toUSize () (fun _ _ x y c => (x + y, c))).map
    (·.1.data) == some r

/-! In-place folds over a `USize` range -/

-- The range folds with the bounds checked at run time, and the slice folds they are specified as.
private def foldlRange? {β : Type} (a : UInt32Array) (start len : USize) (init : β)
    (f : (k : USize) → k.toNat < len.toNat → UInt32 → β → UInt32 × β) :
    Option (UInt32Array × β) :=
  if h : start.toNat + len.toNat ≤ a.size then some (a.foldlInPlaceRange start len h init f)
  else none

private def foldrRange? {β : Type} (a : UInt32Array) (start len : USize) (init : β)
    (f : (k : USize) → k.toNat < len.toNat → UInt32 → β → UInt32 × β) :
    Option (UInt32Array × β) :=
  if h : start.toNat + len.toNat ≤ a.size then some (a.foldrInPlaceRange start len h init f)
  else none

private def foldlSlice {β : Type} (a : UInt32Array) (start len : Nat) (init : β)
    (f : USize → UInt32 → β → UInt32 × β) : UInt32Array × β :=
  let r := a[start...start + len].foldlInPlace init fun k _ => f k
  (r.1.array, r.2)

private def foldrSlice {β : Type} (a : UInt32Array) (start len : Nat) (init : β)
    (f : USize → UInt32 → β → UInt32 × β) : UInt32Array × β :=
  let r := a[start...start + len].foldrInPlace init fun k _ => f k
  (r.1.array, r.2)

-- Shifts the range by one, inserting the initial accumulator, and records the indices visited.
private def shift (k : USize) (x : UInt32) (b : UInt32 × List Nat) :
    UInt32 × (UInt32 × List Nat) :=
  (b.1, (x, k.toNat :: b.2))

#guard
  let a := UInt32Array.mk #[1, 2, 3, 4, 5, big]
  [(0, 6), (1, 3), (2, 0), (0, 0), (6, 0), (5, 1), (0, 1)].all fun (start, len) =>
    let l := (foldlRange? a start.toUSize len.toUSize (big, []) fun k _ => shift k).map
      fun r => (r.1.data, r.2)
    let r := (foldrRange? a start.toUSize len.toUSize (big, []) fun k _ => shift k).map
      fun r => (r.1.data, r.2)
    let l' := foldlSlice a start len (big, []) shift
    let r' := foldrSlice a start len (big, []) shift
    l == some (l'.1.data, l'.2) && r == some (r'.1.data, r'.2)

#guard (foldlRange? (UInt32Array.mk #[1, 2, 3, 4]) 1 2 (9 : UInt32) fun _ _ x b => (b, x)).map
  (fun r => (r.1.data, r.2)) == some (#[1, 9, 2, 4], 3)
#guard (foldrRange? (UInt32Array.mk #[1, 2, 3, 4]) 1 2 (9 : UInt32) fun _ _ x b => (b, x)).map
  (fun r => (r.1.data, r.2)) == some (#[1, 3, 9, 4], 2)
#guard (foldlRange? (UInt32Array.mk #[1, 2, 3, 4]) 4 0 (9 : UInt32) fun _ _ x b => (b, x)).map
  (fun r => (r.1.data, r.2)) == some (#[1, 2, 3, 4], 9)

-- The `Then` versions hand the array and the last accumulator to `g`, here to store it.
#guard
  let a := UInt32Array.mk #[1, 2, 3, 4]
  if h : (0 : USize).toNat + (3 : USize).toNat ≤ a.size then
    (a.foldlInPlaceRangeThen 0 3 h (9 : UInt32) (fun _ _ x b => (b, x)) fun a _ b =>
        (a.set! 3 b).data) == #[9, 1, 2, 3] &&
      (a.foldrInPlaceRangeThen 0 3 h (9 : UInt32) (fun _ _ x b => (b, x)) fun a _ b =>
        (a.set! 3 b).data) == #[2, 3, 9, 1] && a.data == #[1, 2, 3, 4]
  else false

-- `g` gets the size of the new array, for a bounded write without a check.
#guard
  let a := UInt32Array.mk #[1, 2, 3, 4]
  if h : (0 : USize).toNat + (3 : USize).toNat ≤ a.size then
    (a.foldlInPlaceRangeThen 0 3 h (9 : UInt32) (fun _ _ x b => (b, x)) fun a' ha b =>
        (a'.set 2 b (by rw [ha]; simp at h; lia)).data) == #[9, 1, 3, 4] &&
      (a.foldrInPlaceRangeThen 0 3 h (9 : UInt32) (fun _ _ x b => (b, x)) fun a' ha b =>
        (a'.set 2 b (by rw [ha]; simp at h; lia)).data) == #[2, 3, 1, 4]
  else false

-- A shared array is left unchanged, and an exclusive one is written in place.
#guard
  let a := UInt32Array.mk #[1, 2, 3, 4]
  let r := foldlRange? a 0 4 (9 : UInt32) fun _ _ x b => (b, x)
  let r' := foldrRange? a 0 4 (9 : UInt32) fun _ _ x b => (b, x)
  r.map (·.1.data) == some #[9, 1, 2, 3] && r'.map (·.1.data) == some #[2, 3, 4, 9] &&
    a.data == #[1, 2, 3, 4]

@[noinline] def UInt32Array.foldsRangeInPlace (x : UInt32) : Bool :=
  let a := (UInt32Array.emptyWithCapacity 8).push x |>.push 2 |>.push 3 |>.push 4 |>.push x
  let p := rawAddr a
  match foldlRange? a 1 3 () (fun _ _ x b => (x + 1, b)) with
  | some (a, _) =>
    match foldrRange? a 1 3 () (fun _ _ x b => (x + 1, b)) with
    | some (a, _) => rawAddr a == p && a.data == #[x, 4, 5, 6, x]
    | none => false
  | none => false

#guard UInt32Array.foldsRangeInPlace 1

/-! Lemmas from another module -/

example (a : UInt32Array) (i : USize) (v : UInt32) (h) (j : Nat) (hj) :
    (a.uset i v h)[j]'hj = if i.toNat = j then v else a[j]'(by simpa using hj) := by
  simp
example (a : UInt32Array) (v : UInt32) :
    (a.set! 0 v)[0]? = if 0 < a.size then some v else none := by
  simp
example (a : UInt32Array) (v : UInt32) (h : 1 < (a.set! 0 v).size) :
    (a.set! 0 v)[1] = a[1]'(by simpa using h) := by
  simp
example (a : UInt32Array) (p : UInt32 → Bool) : (a.popWhile p).size ≤ a.size :=
  UInt32Array.size_popWhile_le p a
example (src dest : UInt32Array) :
    (src.copySlice 0 dest 0 src.size).size = max dest.size src.size := by
  simp
example (a : UInt32Array) (f : Nat → UInt32 → Option Nat) :
    a.toList.foldlM f 0 = a.foldlM f 0 := by
  simp
example (a : UInt32Array) (f : UInt32 → Nat → Option Nat) :
    a.toList.foldrM f 0 = a.foldrM f 0 := by
  simp
example (a : UInt32Array) (f : UInt32 → StateM Nat PUnit) : forM a.toList f = forM a f := by
  simp
example (a b : UInt32Array) (x : UInt32) (h : x ∈ a) : x ∈ (a ++ b).toList := by
  simp [h]
example (a : UInt32Array) (x : UInt32) : x ∈ a.push x := by
  simp
example (a : UInt32Array) (i : Nat) (h : i < a.size) : a[i] ∈ a.toList := by
  simpa using UInt32Array.getElem_mem h
example (a : UInt32Array) (start stop : Nat) (p : UInt32 → Bool) :
    (a.toSlice start stop).any p = (a.extract start stop).any p := by
  simp
example (a : UInt32Array) (start stop : Nat) :
    (a.toSlice start stop).toList = (a.toList.extract start stop) := by
  simp
example (s : UInt32Array.Slice) (p : UInt32 → Bool) : s.count p = s.copy.toList.countP p := by
  simp
example (s : UInt32Array.Slice) (p : UInt32 → Bool) :
    s.find? p = s.copy.toList.find? p ∧ s.findRev? p = s.copy.toList.reverse.find? p := by
  simp
example (s : UInt32Array.Slice) (f : Nat → UInt32 → Nat) :
    s.foldl f 0 = s.copy.toList.foldl f 0 := by
  simp
example (s : UInt32Array.Slice) (f : UInt32 → StateM Nat PUnit) :
    forM s f = forM s.copy.toList f := by
  simp
example (s : UInt32Array.Slice) (x : UInt32) : x ∈ s ↔ x ∈ s.copy.toList := by
  simp
example (s t : UInt32Array.Slice) : (s == t) = (s.copy == t.copy) := by
  simp
example (a : UInt32Array) : a.iter.toUInt32Array = a := by
  simp
example (s : UInt32Array.Slice) : s.iter.toUInt32Array = s.copy := by
  simp
example : (∅ : UInt32Array.Slice).size = 0 := by
  simp
example (s : UInt32Array.Slice) (i : Nat) (v : UInt32) (h : i < s.size) :
    (s.set i v h).copy = s.copy.set i v (by simpa using h) := by
  simp
example (s : UInt32Array.Slice) (i j : Nat) (hi : i < s.size) (hj : j < s.size) :
    (s.swap i j hi hj)[i]'(by simpa using hi) = s[j] := by
  simp; intro h; subst h; rfl
example (s : UInt32Array.Slice) : s.reverse.copy.toList = s.copy.toList.reverse := by
  simp
example (s : UInt32Array.Slice) (f : UInt32 → UInt32) : (s.modify 0 f).size = s.size := by
  simp
example (s : UInt32Array.Slice) (f : (k : USize) → k.toNat < s.size → UInt32 → Nat → UInt32 × Nat) :
    (s.foldlInPlace 0 f).1.size = s.size := by
  simp
example (s : UInt32Array.Slice) (f : (k : USize) → k.toNat < s.size → UInt32 → Nat → UInt32 × Nat) :
    (s.foldrInPlace 0 f).1.size = s.size := by
  simp
example (s : UInt32Array.Slice) (f : (k : USize) → k.toNat < s.size → UInt32 → Nat → UInt32 × Nat) :
    (s.foldrInPlaceThen 0 f fun t _ => t).size = s.size := by
  simp
example (s : UInt32Array.Slice) (f : (k : USize) → k.toNat < s.size → UInt32 → Nat → UInt32 × Nat) :
    (s.foldlInPlace 0 f).1.array.size = s.array.size ∧
      (s.foldrInPlace 0 f).1.array.size = s.array.size := by
  simp
example (s : UInt32Array.Slice) (f : (k : USize) → k.toNat < s.size → UInt32 → Nat → UInt32 × Nat)
    (h : 0 < s.start) : (s.foldlInPlace 0 f).1.array[0]? = s.array[0]? :=
  s.getElem?_array_foldlInPlace 0 f 0 (.inl h)
example (s : UInt32Array.Slice) (f : (k : USize) → k.toNat < s.size → UInt32 → Nat → UInt32 × Nat) :
    (s.foldrInPlace 0 f).1.array[s.stop]? = s.array[s.stop]? :=
  s.getElem?_array_foldrInPlace 0 f _ (.inr (Nat.le_refl _))

-- Mapping each element and counting, as a pure fold.
example (s : UInt32Array.Slice) :
    (s.foldlInPlace 0 fun _ _ x b => (x + 1, b + 1)).2 =
      ((List.finRange s.size).foldl (fun acc i => (acc.1 ++ [s[i] + 1], acc.2 + 1))
        ([], 0)).2 :=
  congrArg Prod.snd (s.foldlInPlace_eq_foldl_finRange _ _)
example (s : UInt32Array.Slice) :
    (s.foldrInPlace 0 fun _ _ x b => (x + 1, b + 1)).1.copy.toList =
      ((List.finRange s.size).foldr (fun i acc => ((s[i] + 1) :: acc.1, acc.2 + 1))
        ([], 0)).1 :=
  congrArg Prod.fst (s.foldrInPlace_eq_foldr_finRange _ _)
example (a : UInt32Array) (xs ys rs len : USize) (hx hy hr)
    (f : (j : USize) → j.toNat < len.toNat → UInt32 → UInt32 → Nat → UInt32 × Nat) :
    (a.foldlInPlace2Then xs ys rs len hx hy hr 0 f fun a' _ _ => a').size = a.size := by
  simp
example (a : UInt32Array) (start len : USize) (h : start.toNat + len.toNat ≤ a.size)
    (f : (k : USize) → k.toNat < len.toNat → UInt32 → Nat → UInt32 × Nat) :
    (a.foldlInPlaceRange start len h 0 f).2 =
      ((a.toSlice start.toNat (start.toNat + len.toNat)).foldlInPlace 0
        fun k hk => f k (by simp at hk; lia)).2 := by
  simp
example (a : UInt32Array) (start len : USize) (h : start.toNat + len.toNat ≤ a.size)
    (f : (k : USize) → k.toNat < len.toNat → UInt32 → Nat → UInt32 × Nat) :
    a.foldrInPlaceRangeThen start len h 0 f (fun a' _ b => (a', b)) =
      a.foldrInPlaceRange start len h 0 f := by
  simp
example (a : UInt32Array) (start len : USize) (h : start.toNat + len.toNat ≤ a.size)
    (f : (k : USize) → k.toNat < len.toNat → UInt32 → Nat → UInt32 × Nat) :
    (a.foldlInPlaceRange start len h 0 f).1.size = a.size ∧
      (a.foldrInPlaceRange start len h 0 f).1.size = a.size := by
  simp
