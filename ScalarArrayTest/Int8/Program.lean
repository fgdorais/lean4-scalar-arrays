/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import ScalarArray.Int8
import ScalarArrayTest.Util
meta import ScalarArray.Int8
meta import ScalarArrayTest.Util

open ScalarArray ScalarArrayTest Int8Array.InPlace

/-!
Tests for `Int8Array.InPlace`: in-place programs.
-/

/-- A test value at the edge of the element type's range. -/
private abbrev big : Int8 := -128

/-- `read` with the bound checked at run time, reading `0` out of bounds. -/
private def rd (i : USize) : Int8Array.InPlace n Int8 :=
  if h : i.toNat < n then read i h else pure 0

/-- `write` with the bound checked at run time, doing nothing out of bounds. -/
private def wr (i : USize) (v : Int8) : Int8Array.InPlace n Unit :=
  if h : i.toNat < n then write i h v else pure ()

-- `pure`, `read` and `write`, in order: a read sees the earlier writes.
#guard
  let r := (Int8Array.mk #[1, 2, 3]).runInPlace do
    let x ← rd 0
    wr 0 big
    let y ← rd 0
    wr 2 (x + 10)
    pure (x, y)
  r.1 == (1, big) && r.2.toArray == #[big, 2, 11]

-- `InPlace.ite` and `InPlace.dite` run the branch of the condition.
#guard ((Int8Array.mk #[1, 2, 3]).runInPlace (forIn 0 3 () fun j _ _ _ =>
  Int8Array.InPlace.ite (j.toNat % 2 = 0) (wr j big) (pure ()))).2.toArray == #[big, 2, big]
#guard ((Int8Array.mk #[1, 2, 3]).runInPlace
  (Int8Array.InPlace.dite (2 < 3) (fun _ => wr 1 big *> pure true) (fun _ => pure false))) ==
    (true, Int8Array.mk #[1, big, 3])

-- `forIn lo hi` visits `lo` to `hi - 1`, `forInRev lo hi` visits `hi - 1` down to `lo`.
#guard ((Int8Array.mk #[1, 2, 3]).runInPlace
  (forIn 0 3 [] fun j _ _ b => pure (j.toNat :: b))).1 == [2, 1, 0]
#guard ((Int8Array.mk #[1, 2, 3]).runInPlace
  (forInRev 0 3 [] fun j _ _ b => pure (j.toNat :: b))).1 == [0, 1, 2]
#guard ((Int8Array.mk #[1, 2, 3]).runInPlace
  (forIn2 0 3 [] 0 fun j _ _ b c => pure (j.toNat :: b, c + 1))).1 == ([2, 1, 0], 3)
#guard ((Int8Array.mk #[1, 2, 3]).runInPlace
  (forInRev2 0 3 [] 0 fun j _ _ b c => pure (j.toNat :: b, c + 1))).1 == ([0, 1, 2], 3)
#guard ((Int8Array.mk #[1, 2, 3]).runInPlace
  (forIn 0 0 [] fun j _ _ b => pure (j.toNat :: b))).1 == []
#guard ((Int8Array.mk #[1, 2, 3]).runInPlace
  (forInRev 0 0 [] fun j _ _ b => pure (j.toNat :: b))).1 == []
#guard ((Int8Array.mk #[1, 2, 3, 4, 5]).runInPlace
  (forIn 1 4 [] fun j _ _ b => pure (j.toNat :: b))).1 == [3, 2, 1]
#guard ((Int8Array.mk #[1, 2, 3, 4, 5]).runInPlace
  (forInRev 1 4 [] fun j _ _ b => pure (j.toNat :: b))).1 == [1, 2, 3]
#guard ((Int8Array.mk #[1, 2, 3, 4, 5]).runInPlace
  (forInRev2 2 4 [] 0 fun j _ _ b c => pure (j.toNat :: b, c + 1))).1 == ([2, 3], 2)
#guard ((Int8Array.mk #[1, 2, 3, 4, 5]).runInPlace
  (forIn 4 2 [] fun j _ _ b => pure (j.toNat :: b))).1 == []
#guard ((Int8Array.mk #[1, 2, 3, 4, 5]).runInPlace
  (forInRev 4 2 [] fun j _ _ b => pure (j.toNat :: b))).1 == []
#guard
  if h : (2 : USize).toNat ≤ (4 : USize).toNat then
    ((Int8Array.mk #[1, 2, 3, 4, 5]).runInPlace
      (forInRevFrom 0 4 2 h [] fun j _ _ b => pure (j.toNat :: b))).1 == [0, 1]
  else false

-- The `Bind` loops run the rest of the program on the loop's last accumulators.
#guard ((Int8Array.mk #[1, 2, 3]).runInPlace
  (forInBind 0 3 [] (fun j _ _ b => pure (j.toNat :: b)) fun b => pure (b, b.length))).1 ==
    ([2, 1, 0], 3)
#guard ((Int8Array.mk #[1, 2, 3]).runInPlace
  (forIn2Bind 0 3 [] 0 (fun j _ _ b c => pure (j.toNat :: b, c + 1)) fun b c => pure (c, b))).1 ==
    (3, [2, 1, 0])
#guard ((Int8Array.mk #[1, 2, 3]).runInPlace
  (forInRevBind 1 3 [] (fun j _ _ b => pure (j.toNat :: b)) fun b => pure b)).1 == [1, 2]
#guard ((Int8Array.mk #[1, 2, 3]).runInPlace
  (forInRev2Bind 0 3 [] 0 (fun j _ _ b c => pure (j.toNat :: b, c + 1))
    fun b c => pure (c, b))).1 ==
    (3, [0, 1, 2])
#guard ((Int8Array.mk #[1, 2, 3]).runInPlace
  (forInBind 0 3 () (fun j _ _ _ => wr j big) fun _ => rd 1)) ==
    (big, Int8Array.mk #[big, big, big])

-- `simp` turns `InPlace.bind` and `InPlace.pure` into `>>=` and `pure`, for the `run_*` lemmas.
example (m : Int8Array.InPlace n Nat) (a : Int8Array) (h : a.size = n) :
    (m.bind fun x => Int8Array.InPlace.pure (x + 1)).run a h =
      ((m.run a h).1 + 1, (m.run a h).2) := by
  simp only [Int8Array.InPlace.bind_eq, Int8Array.InPlace.pure_eq,
    Int8Array.InPlace.run_bind, Int8Array.InPlace.run_pure]

-- The body gets both bounds of `j`: with `lo = 1`, `j - 1` is in bounds without a check.
private def diffs (a : Int8Array) : Int8Array :=
  (a.runInPlace (forInRev 1 a.usize () fun j hlo hj _ => do
    have := a.toNat_usize_le
    have h1 : (1 : USize).toNat = 1 := USize.toNat_one
    have hp : (j - 1).toNat < a.size := by
      rw [USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.2 hlo)]; lia
    let x ← read j (by lia)
    let y ← read (j - 1) hp
    write j (by lia) (x - y))).2

#guard (diffs (Int8Array.mk #[1, 3, 6, 10])).toArray == #[1, 2, 3, 4]
#guard (diffs (Int8Array.mk #[])).toArray == #[]

-- Shifting up by one needs the downward loop; the upward loop smears the first element.
#guard ((Int8Array.mk #[1, 2, 3, 4]).runInPlace
  (forInRev 0 3 () fun j _ _ _ => do wr (j + 1) (← rd j))).2.toArray == #[1, 1, 2, 3]
#guard ((Int8Array.mk #[1, 2, 3, 4]).runInPlace
  (forIn 0 3 () fun j _ _ _ => do wr (j + 1) (← rd j))).2.toArray == #[1, 1, 1, 1]

-- A butterfly over the windows `x = [0, 3)`, `y = [3, 6)` and `t = [6, 9)`: `x := x + y` and
-- `t := x - y` in one pass, with two accumulators.
#guard
  let a := Int8Array.mk #[5, 6, 7, 1, 2, 3, 0, 0, 0]
  let r := a.runInPlace <| forIn2 0 3 (0 : Int8) (0 : Int8) fun j _ _ c b => do
    let u ← rd j
    let v ← rd (3 + j)
    wr j (u + v)
    wr (6 + j) (u - v)
    pure (c + u, b + v)
  r.1 == (18, 6) && r.2.toArray == #[6, 8, 10, 1, 2, 3, 4, 4, 4]

-- Running on a shared array copies it once and leaves the original unchanged, and a program that
-- reads the original array itself sees its old elements.
#guard
  let a := Int8Array.mk #[1, 2, 3, 4]
  let r := a.runInPlace (forIn 0 4 () fun j _ _ _ => wr j (a[(j.toNat + 1) % 4]! * 10))
  r.2.toArray == #[20, 30, 40, 10] && a.toArray == #[1, 2, 3, 4]
#guard
  let a := Int8Array.mk #[1, 2, 3, 4]
  let r := Int8Array.InPlace.run (n := 4)
    (forIn 0 4 () fun j _ _ _ => wr j (j.toNat.toInt8 + 7)) a rfl
  r.2.toArray == #[7, 8, 9, 10] && a.toArray == #[1, 2, 3, 4]

-- An array that is no longer used is updated in place, without copying it.
@[noinline] def Int8Array.runsInPlace (x : Int8) : Bool :=
  let a := (Int8Array.emptyWithCapacity 8).push x |>.push 2 |>.push 3 |>.push 4
  let p := rawAddr a
  let r := a.runInPlace do
    forIn 0 4 () fun j _ _ _ => do wr j ((← rd j) + 1)
    forInRev2 0 4 () () fun j _ _ _ _ => do wr j ((← rd j) * 2); pure ((), ())
  rawAddr r.2 == p && r.2.toArray == #[(x + 1) * 2, 6, 8, 10]

#guard Int8Array.runsInPlace 1

-- A long loop runs in linear time, so every write is in place.
#guard
  let n := 1000000
  let a := Int8Array.mk ((Array.range n).map Nat.toInt8)
  let r := a.runInPlace (forIn 0 a.usize (0 : Int8) fun j _ _ c => do
    let x ← rd j
    wr j (x + 1)
    pure (c + x))
  r.2.toArray == (Array.range n).map (Nat.toInt8 · + 1) &&
    r.1 == ((Array.range n).map Nat.toInt8).foldl (· + ·) 0
