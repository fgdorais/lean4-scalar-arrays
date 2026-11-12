/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import ScalarArray.Float64
import ScalarArrayTest.Util
meta import ScalarArray.Float64
meta import ScalarArrayTest.Util

open ScalarArray ScalarArrayTest Float64Array

/-!
Tests for `Float64Array.modifyAt` and the whole-loop lemmas of `Float64Array.InPlace.Tail`.
-/

/-! `modifyAt` -/

-- A stride: every second element from index `1`.
#guard ((mk #[1, 2, 3, 4, 5, 6]).modifyAt (Stride.idx ⟨1, 2⟩) 0 3 fun _ v => 2 * v).toArray ==
  #[1, 4, 3, 8, 5, 12]

-- Only the steps from `lo` up to `hi - 1`.
#guard ((mk #[1, 2, 3, 4, 5, 6]).modifyAt (Stride.idx ⟨1, 2⟩) 1 2 fun _ v => 2 * v).toArray ==
  #[1, 2, 3, 8, 5, 6]

-- An empty range changes nothing.
#guard ((mk #[1, 2, 3]).modifyAt id 2 1 fun _ v => 2 * v).toArray == #[1, 2, 3]

-- Indices out of bounds are skipped.
#guard ((mk #[1, 2, 3]).modifyAt (· * 2) 0 3 fun _ v => v + 1).toArray == #[2, 2, 4]

-- The steps run in order, and each sees the earlier writes.
#guard ((mk #[1, 2]).modifyAt (fun _ => 0) 0 3 fun _ v => 2 * v + 1).toArray == #[15, 2]

-- The step `i` gets its own index.
#guard ((mk #[0, 0, 0]).modifyAt (2 - ·) 0 3 fun i v => if i = 0 then v + 1 else v).toArray ==
  #[0, 0, 1]

example (src dest : Float64Array) (h₁ : 1 + 2 ≤ src.size) (h₂ : 3 + 2 ≤ dest.size) :
    src.copySlice 1 dest 3 2 = dest.modifyAt (3 + ·) 0 2 fun i _ => src[1 + i]! :=
  copySlice_eq_modifyAt src 1 dest 3 2 true h₁ h₂

/-! Whole loops -/

/-- Doubles the elements at the first `n` steps of `s`, with a loop up. -/
private def double (a : Float64Array) (s : Stride) (n : USize) : Float64Array :=
  if h : s.Fits n.toNat a.size ∧ a.size < USize.size then
    (InPlace.Tail.forIn (n := a.size) 0 n () (fun j _ hj next _ =>
        InPlace.Tail.readThen (s.off.toUSize + s.inc.toUSize * j)
          (s.toNat_idx_toUSize_lt h.1 h.2 hj) fun v =>
        InPlace.Tail.writeThen (s.off.toUSize + s.inc.toUSize * j)
          (s.toNat_idx_toUSize_lt h.1 h.2 hj) (2 * v) (next ()))
      fun _ => InPlace.Tail.done () fun _ a _ => a).run a rfl
  else a

/-- Doubles the elements at the first `n` steps of `s`, with a loop down. -/
private def doubleRev (a : Float64Array) (s : Stride) (n : USize) : Float64Array :=
  if h : s.Fits n.toNat a.size ∧ a.size < USize.size then
    (InPlace.Tail.forInRev (n := a.size) 0 n () (fun j _ hj next _ =>
        InPlace.Tail.readThen (s.off.toUSize + s.inc.toUSize * j)
          (s.toNat_idx_toUSize_lt h.1 h.2 hj) fun v =>
        InPlace.Tail.writeThen (s.off.toUSize + s.inc.toUSize * j)
          (s.toNat_idx_toUSize_lt h.1 h.2 hj) (2 * v) (next ()))
      fun _ => InPlace.Tail.done () fun _ a _ => a).run a rfl
  else a

/-- Writes `v` at the first `n` steps of `s`, with a loop up. -/
private def fill (a : Float64Array) (s : Stride) (n : USize) (v : Float) : Float64Array :=
  if h : s.Fits n.toNat a.size ∧ a.size < USize.size then
    (InPlace.Tail.forIn (n := a.size) 0 n () (fun j _ hj next _ =>
        InPlace.Tail.writeThen (s.off.toUSize + s.inc.toUSize * j)
          (s.toNat_idx_toUSize_lt h.1 h.2 hj) v (next ()))
      fun _ => InPlace.Tail.done () fun _ a _ => a).run a rfl
  else a

#guard (double (mk #[1, 2, 3, 4, 5, 6]) ⟨1, 2⟩ 3).toArray == #[1, 4, 3, 8, 5, 12]
#guard (doubleRev (mk #[1, 2, 3, 4, 5, 6]) ⟨1, 2⟩ 3).toArray == #[1, 4, 3, 8, 5, 12]
#guard (fill (mk #[1, 2, 3, 4, 5, 6]) ⟨0, 3⟩ 2 7).toArray == #[7, 2, 3, 7, 5, 6]

example (a : Float64Array) (s : Stride) (n : USize) (h : s.Fits n.toNat a.size)
    (hs : a.size < USize.size) :
    double a s n = a.modifyAt s.idx 0 n.toNat fun _ v => 2 * v := by
  rw [double, dite_eq_left_of_eq_true (eq_true ⟨h, hs⟩), InPlace.Tail.forIn_eq,
    InPlace.Tail.run_forInFrom_modify (idx := s.idx) (G := fun _ v => 2 * v)
      (he := fun _ _ hj => s.toNat_idx_toUSize h hs hj) (hg := fun _ _ _ _ => rfl)]
  simp

example (a : Float64Array) (s : Stride) (n : USize) (h : s.Fits n.toNat a.size)
    (hs : a.size < USize.size) :
    doubleRev a s n = a.modifyAt s.idx 0 n.toNat fun _ v => 2 * v := by
  rw [doubleRev, dite_eq_left_of_eq_true (eq_true ⟨h, hs⟩), InPlace.Tail.forInRev_eq,
    InPlace.Tail.run_forInRevFrom_modify (idx := s.idx) (G := fun _ v => 2 * v)
      (he := fun _ _ hj => s.toNat_idx_toUSize h hs hj)
      (hinj := fun _ _ h₁ _ _ h₂ e => h.idx_inj h₁ h₂ e) (hg := fun _ _ _ _ => rfl)]
  simp

example (a : Float64Array) (s : Stride) (n : USize) (v : Float) (h : s.Fits n.toNat a.size)
    (hs : a.size < USize.size) :
    fill a s n v = a.modifyAt s.idx 0 n.toNat fun _ _ => v := by
  rw [fill, dite_eq_left_of_eq_true (eq_true ⟨h, hs⟩), InPlace.Tail.forIn_eq,
    InPlace.Tail.run_forInFrom_write (idx := s.idx) (G := fun _ => v)
      (he := fun _ _ hj => s.toNat_idx_toUSize h hs hj) (hg := fun _ _ _ => rfl)]
  simp

-- The elements of the stride are doubled, and the others unchanged.
example (a : Float64Array) (s : Stride) (n : Nat) (h : s.Fits n a.size) (i : Nat) (hi : i < n) :
    (a.modifyAt s.idx 0 n fun _ v => 2 * v)[s.idx i]'(by simpa using h.idx_lt hi) =
      2 * a[s.idx i]'(h.idx_lt hi) :=
  getElem_modifyAt_stride a h (Nat.le_refl _) _ (Nat.zero_le _) hi

example (a : Float64Array) (s : Stride) (n : Nat) (p : Nat) (hp : ∀ i < n, s.idx i ≠ p)
    (h : p < a.size) :
    (a.modifyAt s.idx 0 n fun _ v => 2 * v)[p]'(by simpa using h) = a[p] :=
  getElem_modifyAt_of_forall_ne a s.idx _ (fun i _ hi => hp i hi) _
