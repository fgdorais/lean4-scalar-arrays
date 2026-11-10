/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import ScalarArray.Int64
import ScalarArrayTest.Util
meta import ScalarArray.Int64
meta import ScalarArrayTest.Util

open ScalarArray ScalarArrayTest Int64Array.InPlace

/-!
Tests for `Int64Array.InPlace`: in-place programs.
-/

/-- A test value at the edge of the element type's range. -/
private abbrev big : Int64 := -9223372036854775808

/-- `read` with the bound checked at run time, reading `0` out of bounds. -/
private def rd (i : USize) : Int64Array.InPlace n Int64 :=
  if h : i.toNat < n then read i h else pure 0

/-- `write` with the bound checked at run time, doing nothing out of bounds. -/
private def wr (i : USize) (v : Int64) : Int64Array.InPlace n Unit :=
  if h : i.toNat < n then write i h v else pure ()

-- `pure`, `read` and `write`, in order: a read sees the earlier writes.
#guard
  let r := (Int64Array.mk #[1, 2, 3]).runInPlace do
    let x ← rd 0
    wr 0 big
    let y ← rd 0
    wr 2 (x + 10)
    pure (x, y)
  r.1 == (1, big) && r.2.toArray == #[big, 2, 11]

-- `forIn lo hi` visits `lo` to `hi - 1`, `forInRev lo hi` visits `hi - 1` down to `lo`.
#guard ((Int64Array.mk #[1, 2, 3]).runInPlace
  (forIn 0 3 [] fun j _ b => pure (j.toNat :: b))).1 == [2, 1, 0]
#guard ((Int64Array.mk #[1, 2, 3]).runInPlace
  (forInRev 0 3 [] fun j _ b => pure (j.toNat :: b))).1 == [0, 1, 2]
#guard ((Int64Array.mk #[1, 2, 3]).runInPlace
  (forIn2 0 3 [] 0 fun j _ b c => pure (j.toNat :: b, c + 1))).1 == ([2, 1, 0], 3)
#guard ((Int64Array.mk #[1, 2, 3]).runInPlace
  (forInRev2 0 3 [] 0 fun j _ b c => pure (j.toNat :: b, c + 1))).1 == ([0, 1, 2], 3)
#guard ((Int64Array.mk #[1, 2, 3]).runInPlace
  (forIn 0 0 [] fun j _ b => pure (j.toNat :: b))).1 == []
#guard ((Int64Array.mk #[1, 2, 3]).runInPlace
  (forInRev 0 0 [] fun j _ b => pure (j.toNat :: b))).1 == []
#guard ((Int64Array.mk #[1, 2, 3, 4, 5]).runInPlace
  (forIn 1 4 [] fun j _ b => pure (j.toNat :: b))).1 == [3, 2, 1]
#guard ((Int64Array.mk #[1, 2, 3, 4, 5]).runInPlace
  (forInRev 1 4 [] fun j _ b => pure (j.toNat :: b))).1 == [1, 2, 3]
#guard ((Int64Array.mk #[1, 2, 3, 4, 5]).runInPlace
  (forInRev2 2 4 [] 0 fun j _ b c => pure (j.toNat :: b, c + 1))).1 == ([2, 3], 2)
#guard ((Int64Array.mk #[1, 2, 3, 4, 5]).runInPlace
  (forIn 4 2 [] fun j _ b => pure (j.toNat :: b))).1 == []
#guard ((Int64Array.mk #[1, 2, 3, 4, 5]).runInPlace
  (forInRev 4 2 [] fun j _ b => pure (j.toNat :: b))).1 == []
#guard
  if h : (2 : USize).toNat ≤ (4 : USize).toNat then
    ((Int64Array.mk #[1, 2, 3, 4, 5]).runInPlace
      (forInRevFrom 0 4 2 h [] fun j _ b => pure (j.toNat :: b))).1 == [0, 1]
  else false

-- Shifting up by one needs the downward loop; the upward loop smears the first element.
#guard ((Int64Array.mk #[1, 2, 3, 4]).runInPlace
  (forInRev 0 3 () fun j _ _ => do wr (j + 1) (← rd j))).2.toArray == #[1, 1, 2, 3]
#guard ((Int64Array.mk #[1, 2, 3, 4]).runInPlace
  (forIn 0 3 () fun j _ _ => do wr (j + 1) (← rd j))).2.toArray == #[1, 1, 1, 1]

-- A butterfly over the windows `x = [0, 3)`, `y = [3, 6)` and `t = [6, 9)`: `x := x + y` and
-- `t := x - y` in one pass, with two accumulators.
#guard
  let a := Int64Array.mk #[5, 6, 7, 1, 2, 3, 0, 0, 0]
  let r := a.runInPlace <| forIn2 0 3 (0 : Int64) (0 : Int64) fun j _ c b => do
    let u ← rd j
    let v ← rd (3 + j)
    wr j (u + v)
    wr (6 + j) (u - v)
    pure (c + u, b + v)
  r.1 == (18, 6) && r.2.toArray == #[6, 8, 10, 1, 2, 3, 4, 4, 4]

-- Running on a shared array copies it once and leaves the original unchanged, and a program that
-- reads the original array itself sees its old elements.
#guard
  let a := Int64Array.mk #[1, 2, 3, 4]
  let r := a.runInPlace (forIn 0 4 () fun j _ _ => wr j (a[(j.toNat + 1) % 4]! * 10))
  r.2.toArray == #[20, 30, 40, 10] && a.toArray == #[1, 2, 3, 4]
#guard
  let a := Int64Array.mk #[1, 2, 3, 4]
  let r := Int64Array.InPlace.run (n := 4) (forIn 0 4 () fun j _ _ => wr j (j.toNat.toInt64 + 7)) a rfl
  r.2.toArray == #[7, 8, 9, 10] && a.toArray == #[1, 2, 3, 4]

-- An array that is no longer used is updated in place, without copying it.
@[noinline] def Int64Array.runsInPlace (x : Int64) : Bool :=
  let a := (Int64Array.emptyWithCapacity 8).push x |>.push 2 |>.push 3 |>.push 4
  let p := rawAddr a
  let r := a.runInPlace do
    forIn 0 4 () fun j _ _ => do wr j ((← rd j) + 1)
    forInRev2 0 4 () () fun j _ _ _ => do wr j ((← rd j) * 2); pure ((), ())
  rawAddr r.2 == p && r.2.toArray == #[(x + 1) * 2, 6, 8, 10]

#guard Int64Array.runsInPlace 1

-- A long loop runs in linear time, so every write is in place.
#guard
  let n := 1000000
  let a := Int64Array.mk ((Array.range n).map Nat.toInt64)
  let r := a.runInPlace (forIn 0 a.usize (0 : Int64) fun j _ c => do
    let x ← rd j
    wr j (x + 1)
    pure (c + x))
  r.2.toArray == (Array.range n).map (Nat.toInt64 · + 1) &&
    r.1 == ((Array.range n).map Nat.toInt64).foldl (· + ·) 0
