/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ScalarArray.UInt32

/-!
A small arbitrary-precision natural number type, built on `UInt32Array` to exercise the library
in a realistic setting. It is test code only: nothing here is exported by `ScalarArray`.

A number is stored as little-endian base 2³² limbs. The arithmetic works on slices of limbs, so it
accepts trailing zero limbs, and its results are trimmed so that the most significant limb is
nonzero. Addition and multiplication are the schoolbook algorithms, checked against `Nat`.
-/

open ScalarArray

namespace ScalarArrayTest.Bignum

/-- Removes the trailing zero limbs. -/
def trim (a : UInt32Array) : UInt32Array := a.popWhile (· == 0)

/-- Whether the most significant limb is nonzero. -/
def isTrimmed (a : UInt32Array) : Bool := a.back? != some 0

/-- The limbs of a natural number. -/
def ofNat (n : Nat) : UInt32Array := loop n .empty
where
  loop (n : Nat) (acc : UInt32Array) : UInt32Array :=
    if h : n = 0 then acc else loop (n / 2 ^ 32) (acc.push n.toUInt32)
  termination_by n
  decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)

/-- The natural number that a slice of limbs denotes. -/
def toNat (s : UInt32Array.Slice) : Nat := s.foldr (fun d n => n * 2 ^ 32 + d.toNat) 0

/-- Adds two numbers. -/
def add (a b : UInt32Array.Slice) : UInt32Array := Id.run do
  let n := max a.size b.size
  let mut r := UInt32Array.emptyWithCapacity (n + 1)
  let mut c : UInt64 := 0
  for i in [0:n] do
    let t := (a.getD i 0).toUInt64 + (b.getD i 0).toUInt64 + c
    r := r.push t.toUInt32
    c := t >>> 32
  return trim (r.push c.toUInt32)

/-- Multiplies two numbers. -/
def mul (a b : UInt32Array.Slice) : UInt32Array := Id.run do
  let mut r := UInt32Array.replicate (a.size + b.size) 0
  let mut i := 0
  for x in a do
    -- Adds `x * b`, shifted by `i` limbs. The sum fits in 64 bits since
    -- `(2³² - 1) + (2³² - 1) * (2³² - 1) + (2³² - 1) = 2⁶⁴ - 1`.
    let mut c : UInt64 := 0
    let mut j := i
    for y in b do
      let t := r[j]!.toUInt64 + x.toUInt64 * y.toUInt64 + c
      r := r.set! j t.toUInt32
      c := t >>> 32
      j := j + 1
    r := r.set! j c.toUInt32
    i := i + 1
  return trim r

/-- Shifts a number left by `k` limbs. -/
def shiftLimbs (a : UInt32Array) (k : Nat) : UInt32Array :=
  if a.isEmpty then a else .replicate k 0 ++ a

end ScalarArrayTest.Bignum

open ScalarArrayTest Bignum

/-! Conversion -/

#guard (ofNat 0).size == 0
#guard (ofNat 1).toList == [1]
#guard (ofNat (2 ^ 32)).toList == [0, 1]
#guard (ofNat (2 ^ 64 - 1)).toList == [4294967295, 4294967295]
#guard [0, 1, 2 ^ 32 - 1, 2 ^ 32, 2 ^ 100 + 7, 10 ^ 50].all fun n => toNat (ofNat n).toSlice == n
#guard trim (UInt32Array.mk #[1, 2, 0, 0]) == UInt32Array.mk #[1, 2]
#guard trim (UInt32Array.mk #[0, 0]) == .empty
#guard toNat (UInt32Array.mk #[5, 0, 0]).toSlice == 5

/-! Test values -/

/-- Pseudorandom numbers of up to `bits` bits from a linear congruential generator. -/
def samples (count bits : Nat) (seed : Nat := 2026) : List Nat := Id.run do
  let mut s := seed
  let mut l := []
  for _ in [0:count] do
    let mut n := 0
    s := (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64
    let len := s % (bits + 1)
    for _ in [0:(len + 31) / 32] do
      s := (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64
      n := n * 2 ^ 32 + s / 2 ^ 32
    l := (n % 2 ^ len) :: l
  return l

/-- Numbers whose limbs are all `2³² - 1` or all zero but one, where carries propagate the most. -/
def edges : List Nat :=
  [0, 1, 2, 2 ^ 31] ++ (List.range 5).flatMap fun k =>
    [2 ^ (32 * (k + 1)) - 1, 2 ^ (32 * (k + 1)), 2 ^ (32 * (k + 1)) + 1]

def values : List Nat := edges ++ samples 40 400

/-! Addition -/

#guard values.all fun m => values.all fun n =>
  let r := add (ofNat m).toSlice (ofNat n).toSlice
  toNat r.toSlice == m + n && isTrimmed r

#guard add (ofNat (2 ^ 128 - 1)).toSlice (ofNat 1).toSlice == ofNat (2 ^ 128)
#guard add UInt32Array.empty.toSlice UInt32Array.empty.toSlice == .empty

/-! Multiplication -/

#guard values.all fun m => values.all fun n =>
  let r := mul (ofNat m).toSlice (ofNat n).toSlice
  toNat r.toSlice == m * n && isTrimmed r

#guard mul (ofNat (2 ^ 128 - 1)).toSlice (ofNat (2 ^ 128 - 1)).toSlice ==
  ofNat ((2 ^ 128 - 1) * (2 ^ 128 - 1))
#guard mul (ofNat 0).toSlice (ofNat (2 ^ 100)).toSlice == .empty

-- A long computation that reuses each result: 200 factorial.
#guard
  let r := (List.range 200).foldl (fun a i => mul a.toSlice (ofNat (i + 1)).toSlice) (ofNat 1)
  toNat r.toSlice == (List.range 200).foldl (fun a i => a * (i + 1)) 1

-- Repeated squaring: 3 ^ (2 ^ 10).
#guard
  let r := (List.range 10).foldl (fun a _ => mul a.toSlice a.toSlice) (ofNat 3)
  toNat r.toSlice == 3 ^ 2 ^ 10

/-! Slices of limbs -/

-- Splitting a number into a low and a high part, with the slices of a single array.
#guard values.all fun n =>
  let a := ofNat n
  (List.range (a.size + 1)).all fun k =>
    let lo := a[*...k]
    let hi := a[k...*]
    toNat lo + toNat hi * 2 ^ (32 * k) == n &&
    add (shiftLimbs (trim hi) k).toSlice lo == a

-- One step of Karatsuba's algorithm, which multiplies the halves of each operand.
#guard (samples 20 600).all fun m => (samples 20 600 (seed := 7)).all fun n =>
  let a := ofNat m
  let b := ofNat n
  let k := (max a.size b.size + 1) / 2
  let z₀ := mul a[*...k] b[*...k]
  let z₂ := mul a[k...*] b[k...*]
  let z₁ := mul (add a[*...k] a[k...*]).toSlice (add b[*...k] b[k...*]).toSlice
  -- z₁ - z₀ - z₂ is computed with `Nat` since there is no subtraction here.
  let mid := ofNat (toNat z₁.toSlice - toNat z₀.toSlice - toNat z₂.toSlice)
  let r := add (add z₀.toSlice (shiftLimbs mid k).toSlice).toSlice (shiftLimbs z₂ (2 * k)).toSlice
  r == mul a.toSlice b.toSlice && toNat r.toSlice == m * n
