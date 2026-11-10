/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import ScalarArray.USize
import ScalarArrayTest.Util
meta import ScalarArray.USize
meta import ScalarArrayTest.Util

open ScalarArray ScalarArrayTest USizeArray.InPlace

/-!
Tests for `USizeArray.InPlace`: in-place programs.
-/

/-- A test value at the edge of the element type's range. -/
private abbrev big : USize := 18446744073709551615

/-- `read` with the bound checked at run time, reading `0` out of bounds. -/
private def rd (i : USize) : USizeArray.InPlace n USize :=
  if h : i.toNat < n then read i h else pure 0

/-- `write` with the bound checked at run time, doing nothing out of bounds. -/
private def wr (i : USize) (v : USize) : USizeArray.InPlace n Unit :=
  if h : i.toNat < n then write i h v else pure ()

-- `pure`, `read` and `write`, in order: a read sees the earlier writes.
#guard
  let r := (USizeArray.mk #[1, 2, 3]).runInPlace do
    let x ← rd 0
    wr 0 big
    let y ← rd 0
    wr 2 (x + 10)
    pure (x, y)
  r.1 == (1, big) && r.2.toArray == #[big, 2, 11]

-- `InPlace.ite` and `InPlace.dite` run the branch of the condition.
#guard ((USizeArray.mk #[1, 2, 3]).runInPlace (forUp 3 () fun j _ _ =>
  USizeArray.InPlace.ite (j.toNat % 2 = 0) (wr j big) (pure ()))).2.toArray == #[big, 2, big]
#guard ((USizeArray.mk #[1, 2, 3]).runInPlace
  (USizeArray.InPlace.dite (2 < 3) (fun _ => wr 1 big *> pure true) (fun _ => pure false))) ==
    (true, USizeArray.mk #[1, big, 3])

-- `forUp` visits `0` to `len - 1`, `forDown` visits `len - 1` to `0`.
#guard ((USizeArray.mk #[1, 2, 3]).runInPlace
  (forUp 3 [] fun j _ b => pure (j.toNat :: b))).1 == [2, 1, 0]
#guard ((USizeArray.mk #[1, 2, 3]).runInPlace
  (forDown 3 [] fun j _ b => pure (j.toNat :: b))).1 == [0, 1, 2]
#guard ((USizeArray.mk #[1, 2, 3]).runInPlace
  (forUp2 3 [] 0 fun j _ b c => pure (j.toNat :: b, c + 1))).1 == ([2, 1, 0], 3)
#guard ((USizeArray.mk #[1, 2, 3]).runInPlace
  (forDown2 3 [] 0 fun j _ b c => pure (j.toNat :: b, c + 1))).1 == ([0, 1, 2], 3)
#guard ((USizeArray.mk #[1, 2, 3]).runInPlace
  (forUp 0 [] fun j _ b => pure (j.toNat :: b))).1 == []
#guard ((USizeArray.mk #[1, 2, 3]).runInPlace
  (forDown 0 [] fun j _ b => pure (j.toNat :: b))).1 == []
#guard ((USizeArray.mk #[1, 2, 3, 4, 5]).runInPlace
  (forUpFrom 4 1 [] fun j _ b => pure (j.toNat :: b))).1 == [3, 2, 1]
#guard
  if h : (2 : USize).toNat ≤ (4 : USize).toNat then
    ((USizeArray.mk #[1, 2, 3, 4, 5]).runInPlace
      (forDownFrom 4 2 h [] fun j _ b => pure (j.toNat :: b))).1 == [0, 1]
  else false

-- Shifting up by one needs the downward loop; the upward loop smears the first element.
#guard ((USizeArray.mk #[1, 2, 3, 4]).runInPlace
  (forDown 3 () fun j _ _ => do wr (j + 1) (← rd j))).2.toArray == #[1, 1, 2, 3]
#guard ((USizeArray.mk #[1, 2, 3, 4]).runInPlace
  (forUp 3 () fun j _ _ => do wr (j + 1) (← rd j))).2.toArray == #[1, 1, 1, 1]

-- A butterfly over the windows `x = [0, 3)`, `y = [3, 6)` and `t = [6, 9)`: `x := x + y` and
-- `t := x - y` in one pass, with two accumulators.
#guard
  let a := USizeArray.mk #[5, 6, 7, 1, 2, 3, 0, 0, 0]
  let r := a.runInPlace <| forUp2 3 (0 : USize) (0 : USize) fun j _ c b => do
    let u ← rd j
    let v ← rd (3 + j)
    wr j (u + v)
    wr (6 + j) (u - v)
    pure (c + u, b + v)
  r.1 == (18, 6) && r.2.toArray == #[6, 8, 10, 1, 2, 3, 4, 4, 4]

-- Running on a shared array copies it once and leaves the original unchanged, and a program that
-- reads the original array itself sees its old elements.
#guard
  let a := USizeArray.mk #[1, 2, 3, 4]
  let r := a.runInPlace (forUp 4 () fun j _ _ => wr j (a[(j.toNat + 1) % 4]! * 10))
  r.2.toArray == #[20, 30, 40, 10] && a.toArray == #[1, 2, 3, 4]
#guard
  let a := USizeArray.mk #[1, 2, 3, 4]
  let r := USizeArray.InPlace.run (n := 4) (forUp 4 () fun j _ _ => wr j (j.toNat.toUSize + 7)) a rfl
  r.2.toArray == #[7, 8, 9, 10] && a.toArray == #[1, 2, 3, 4]

-- An array that is no longer used is updated in place, without copying it.
@[noinline] def USizeArray.runsInPlace (x : USize) : Bool :=
  let a := (USizeArray.emptyWithCapacity 8).push x |>.push 2 |>.push 3 |>.push 4
  let p := rawAddr a
  let r := a.runInPlace do
    forUp 4 () fun j _ _ => do wr j ((← rd j) + 1)
    forDown2 4 () () fun j _ _ _ => do wr j ((← rd j) * 2); pure ((), ())
  rawAddr r.2 == p && r.2.toArray == #[(x + 1) * 2, 6, 8, 10]

#guard USizeArray.runsInPlace 1

-- A long loop runs in linear time, so every write is in place.
#guard
  let n := 1000000
  let a := USizeArray.mk ((Array.range n).map Nat.toUSize)
  let r := a.runInPlace (forUp a.usize (0 : USize) fun j _ c => do
    let x ← rd j
    wr j (x + 1)
    pure (c + x))
  r.2.toArray == (Array.range n).map (Nat.toUSize · + 1) &&
    r.1 == ((Array.range n).map Nat.toUSize).foldl (· + ·) 0
