/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import ScalarArray.Float32
import ScalarArrayTest.Util
meta import ScalarArray.Float32
meta import ScalarArrayTest.Util

open ScalarArray ScalarArrayTest Float32Array.InPlace

/-!
Tests for `Float32Array.InPlace`: in-place programs.
-/

/-- A test value at the edge of the element type's range. -/
private abbrev big : Float32 := -1.5e38

/-- `read` with the bound checked at run time, reading `0` out of bounds. -/
private def rd (i : USize) : Float32Array.InPlace n Float32 :=
  if h : i.toNat < n then read i h else pure 0

/-- `write` with the bound checked at run time, doing nothing out of bounds. -/
private def wr (i : USize) (v : Float32) : Float32Array.InPlace n Unit :=
  if h : i.toNat < n then write i h v else pure ()

-- `pure`, `read` and `write`, in order: a read sees the earlier writes.
#guard
  let r := (Float32Array.mk #[1, 2, 3]).runInPlace do
    let x ← rd 0
    wr 0 big
    let y ← rd 0
    wr 2 (x + 10)
    pure (x, y)
  r.1 == (1, big) && r.2.toArray == #[big, 2, 11]

-- `forIn lo hi` visits `lo` to `hi - 1`, `forInRev lo hi` visits `hi - 1` down to `lo`.
#guard ((Float32Array.mk #[1, 2, 3]).runInPlace
  (forIn 0 3 [] fun j _ _ b => pure (j.toNat :: b))).1 == [2, 1, 0]
#guard ((Float32Array.mk #[1, 2, 3]).runInPlace
  (forInRev 0 3 [] fun j _ _ b => pure (j.toNat :: b))).1 == [0, 1, 2]
#guard ((Float32Array.mk #[1, 2, 3]).runInPlace
  (forIn2 0 3 [] 0 fun j _ _ b c => pure (j.toNat :: b, c + 1))).1 == ([2, 1, 0], 3)
#guard ((Float32Array.mk #[1, 2, 3]).runInPlace
  (forInRev2 0 3 [] 0 fun j _ _ b c => pure (j.toNat :: b, c + 1))).1 == ([0, 1, 2], 3)
#guard ((Float32Array.mk #[1, 2, 3]).runInPlace
  (forIn 0 0 [] fun j _ _ b => pure (j.toNat :: b))).1 == []
#guard ((Float32Array.mk #[1, 2, 3]).runInPlace
  (forInRev 0 0 [] fun j _ _ b => pure (j.toNat :: b))).1 == []
#guard ((Float32Array.mk #[1, 2, 3, 4, 5]).runInPlace
  (forIn 1 4 [] fun j _ _ b => pure (j.toNat :: b))).1 == [3, 2, 1]
#guard ((Float32Array.mk #[1, 2, 3, 4, 5]).runInPlace
  (forInRev 1 4 [] fun j _ _ b => pure (j.toNat :: b))).1 == [1, 2, 3]
#guard ((Float32Array.mk #[1, 2, 3, 4, 5]).runInPlace
  (forInRev2 2 4 [] 0 fun j _ _ b c => pure (j.toNat :: b, c + 1))).1 == ([2, 3], 2)
#guard ((Float32Array.mk #[1, 2, 3, 4, 5]).runInPlace
  (forIn 4 2 [] fun j _ _ b => pure (j.toNat :: b))).1 == []
#guard ((Float32Array.mk #[1, 2, 3, 4, 5]).runInPlace
  (forInRev 4 2 [] fun j _ _ b => pure (j.toNat :: b))).1 == []
#guard
  if h : (2 : USize).toNat ≤ (4 : USize).toNat then
    ((Float32Array.mk #[1, 2, 3, 4, 5]).runInPlace
      (forInRevFrom 0 4 2 h [] fun j _ _ b => pure (j.toNat :: b))).1 == [0, 1]
  else false

-- The `Bind` loops run the rest of the program on the loop's last accumulators.
#guard ((Float32Array.mk #[1, 2, 3]).runInPlace
  (forInBind 0 3 [] (fun j _ _ b => pure (j.toNat :: b)) fun b => pure (b, b.length))).1 ==
    ([2, 1, 0], 3)
#guard ((Float32Array.mk #[1, 2, 3]).runInPlace
  (forIn2Bind 0 3 [] 0 (fun j _ _ b c => pure (j.toNat :: b, c + 1)) fun b c => pure (c, b))).1 ==
    (3, [2, 1, 0])
#guard ((Float32Array.mk #[1, 2, 3]).runInPlace
  (forInRevBind 1 3 [] (fun j _ _ b => pure (j.toNat :: b)) fun b => pure b)).1 == [1, 2]
#guard ((Float32Array.mk #[1, 2, 3]).runInPlace
  (forInRev2Bind 0 3 [] 0 (fun j _ _ b c => pure (j.toNat :: b, c + 1))
    fun b c => pure (c, b))).1 ==
    (3, [0, 1, 2])
#guard ((Float32Array.mk #[1, 2, 3]).runInPlace
  (forInBind 0 3 () (fun j _ _ _ => wr j big) fun _ => rd 1)) ==
    (big, Float32Array.mk #[big, big, big])

-- `simp` turns `InPlace.bind` and `InPlace.pure` into `>>=` and `pure`, for the `run_*` lemmas.
example (m : Float32Array.InPlace n Nat) (a : Float32Array) (h : a.size = n) :
    (m.bind fun x => Float32Array.InPlace.pure (x + 1)).run a h =
      ((m.run a h).1 + 1, (m.run a h).2) := by
  simp only [Float32Array.InPlace.bind_eq, Float32Array.InPlace.pure_eq,
    Float32Array.InPlace.run_bind, Float32Array.InPlace.run_pure]

-- The body gets both bounds of `j`: with `lo = 1`, `j - 1` is in bounds without a check.
private def diffs (a : Float32Array) : Float32Array :=
  (a.runInPlace (forInRev 1 a.usize () fun j hlo hj _ => do
    have := a.toNat_usize_le
    have h1 : (1 : USize).toNat = 1 := USize.toNat_one
    have hp : (j - 1).toNat < a.size := by
      rw [USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.2 hlo)]; lia
    let x ← read j (by lia)
    let y ← read (j - 1) hp
    write j (by lia) (x - y))).2

#guard (diffs (Float32Array.mk #[1, 3, 6, 10])).toArray == #[1, 2, 3, 4]
#guard (diffs (Float32Array.mk #[])).toArray == #[]

-- Shifting up by one needs the downward loop; the upward loop smears the first element.
#guard ((Float32Array.mk #[1, 2, 3, 4]).runInPlace
  (forInRev 0 3 () fun j _ _ _ => do wr (j + 1) (← rd j))).2.toArray == #[1, 1, 2, 3]
#guard ((Float32Array.mk #[1, 2, 3, 4]).runInPlace
  (forIn 0 3 () fun j _ _ _ => do wr (j + 1) (← rd j))).2.toArray == #[1, 1, 1, 1]

-- A butterfly over the windows `x = [0, 3)`, `y = [3, 6)` and `t = [6, 9)`: `x := x + y` and
-- `t := x - y` in one pass, with two accumulators.
#guard
  let a := Float32Array.mk #[5, 6, 7, 1, 2, 3, 0, 0, 0]
  let r := a.runInPlace <| forIn2 0 3 (0 : Float32) (0 : Float32) fun j _ _ c b => do
    let u ← rd j
    let v ← rd (3 + j)
    wr j (u + v)
    wr (6 + j) (u - v)
    pure (c + u, b + v)
  r.1 == (18, 6) && r.2.toArray == #[6, 8, 10, 1, 2, 3, 4, 4, 4]

-- Running on a shared array copies it once and leaves the original unchanged, and a program that
-- reads the original array itself sees its old elements.
#guard
  let a := Float32Array.mk #[1, 2, 3, 4]
  let r := a.runInPlace (forIn 0 4 () fun j _ _ _ => wr j (a[(j.toNat + 1) % 4]! * 10))
  r.2.toArray == #[20, 30, 40, 10] && a.toArray == #[1, 2, 3, 4]
#guard
  let a := Float32Array.mk #[1, 2, 3, 4]
  let r := Float32Array.InPlace.run (n := 4)
    (forIn 0 4 () fun j _ _ _ => wr j (j.toNat.toFloat32 + 7)) a rfl
  r.2.toArray == #[7, 8, 9, 10] && a.toArray == #[1, 2, 3, 4]

-- An array that is no longer used is updated in place, without copying it.
@[noinline] def Float32Array.runsInPlace (x : Float32) : Bool :=
  let a := (Float32Array.emptyWithCapacity 8).push x |>.push 2 |>.push 3 |>.push 4
  let p := rawAddr a
  let r := a.runInPlace do
    forIn 0 4 () fun j _ _ _ => do wr j ((← rd j) + 1)
    forInRev2 0 4 () () fun j _ _ _ _ => do wr j ((← rd j) * 2); pure ((), ())
  rawAddr r.2 == p && r.2.toArray == #[(x + 1) * 2, 6, 8, 10]

#guard Float32Array.runsInPlace 1

-- A long loop runs in linear time, so every write is in place.
#guard
  let n := 1000000
  let a := Float32Array.mk ((Array.range n).map Nat.toFloat32)
  let r := a.runInPlace (forIn 0 a.usize (0 : Float32) fun j _ _ c => do
    let x ← rd j
    wr j (x + 1)
    pure (c + x))
  r.2.toArray == (Array.range n).map (Nat.toFloat32 · + 1) &&
    r.1 == ((Array.range n).map Nat.toFloat32).foldl (· + ·) 0
