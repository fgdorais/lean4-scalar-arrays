/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import ScalarArray.Int8
import ScalarArrayTest.Util
meta import ScalarArray.Int8
meta import ScalarArrayTest.Util

open ScalarArray ScalarArrayTest Int8Array

/-!
Tests for `Int8Array.modifyAt` and the whole-loop lemmas of `Int8Array.InPlace.Tail`.
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

example (src dest : Int8Array) (h₁ : 1 + 2 ≤ src.size) (h₂ : 3 + 2 ≤ dest.size) :
    src.copySlice 1 dest 3 2 = dest.modifyAt (3 + ·) 0 2 fun i _ => src[1 + i]! :=
  copySlice_eq_modifyAt src 1 dest 3 2 true h₁ h₂

/-! Whole loops -/

/-- Doubles the elements at the first `n` steps of `s`, with a loop up. -/
private def double (a : Int8Array) (s : Stride) (n : USize) : Int8Array :=
  if h : s.Fits n.toNat a.size ∧ a.size < USize.size then
    (InPlace.Tail.forIn (n := a.size) 0 n () (fun j _ hj next _ =>
        InPlace.Tail.readThen (s.off.toUSize + s.inc.toUSize * j)
          (s.toNat_idx_toUSize_lt h.1 h.2 hj) fun v =>
        InPlace.Tail.writeThen (s.off.toUSize + s.inc.toUSize * j)
          (s.toNat_idx_toUSize_lt h.1 h.2 hj) (2 * v) (next ()))
      fun _ => InPlace.Tail.done () fun _ a _ => a).run a rfl
  else a

/-- Doubles the elements at the first `n` steps of `s`, with a loop down. -/
private def doubleRev (a : Int8Array) (s : Stride) (n : USize) : Int8Array :=
  if h : s.Fits n.toNat a.size ∧ a.size < USize.size then
    (InPlace.Tail.forInRev (n := a.size) 0 n () (fun j _ hj next _ =>
        InPlace.Tail.readThen (s.off.toUSize + s.inc.toUSize * j)
          (s.toNat_idx_toUSize_lt h.1 h.2 hj) fun v =>
        InPlace.Tail.writeThen (s.off.toUSize + s.inc.toUSize * j)
          (s.toNat_idx_toUSize_lt h.1 h.2 hj) (2 * v) (next ()))
      fun _ => InPlace.Tail.done () fun _ a _ => a).run a rfl
  else a

/-- Writes `v` at the first `n` steps of `s`, with a loop up. -/
private def fill (a : Int8Array) (s : Stride) (n : USize) (v : Int8) : Int8Array :=
  if h : s.Fits n.toNat a.size ∧ a.size < USize.size then
    (InPlace.Tail.forIn (n := a.size) 0 n () (fun j _ hj next _ =>
        InPlace.Tail.writeThen (s.off.toUSize + s.inc.toUSize * j)
          (s.toNat_idx_toUSize_lt h.1 h.2 hj) v (next ()))
      fun _ => InPlace.Tail.done () fun _ a _ => a).run a rfl
  else a

#guard (double (mk #[1, 2, 3, 4, 5, 6]) ⟨1, 2⟩ 3).toArray == #[1, 4, 3, 8, 5, 12]
#guard (doubleRev (mk #[1, 2, 3, 4, 5, 6]) ⟨1, 2⟩ 3).toArray == #[1, 4, 3, 8, 5, 12]
#guard (fill (mk #[1, 2, 3, 4, 5, 6]) ⟨0, 3⟩ 2 7).toArray == #[7, 2, 3, 7, 5, 6]

example (a : Int8Array) (s : Stride) (n : USize) (h : s.Fits n.toNat a.size)
    (hs : a.size < USize.size) :
    double a s n = a.modifyAt s.idx 0 n.toNat fun _ v => 2 * v := by
  rw [double, dite_eq_left_of_eq_true (eq_true ⟨h, hs⟩), InPlace.Tail.forIn_eq,
    InPlace.Tail.run_forInFrom_modify (idx := s.idx) (G := fun _ v => 2 * v)
      (he := fun _ _ hj => s.toNat_idx_toUSize h hs hj) (hg := fun _ _ _ _ => rfl)]
  simp

example (a : Int8Array) (s : Stride) (n : USize) (h : s.Fits n.toNat a.size)
    (hs : a.size < USize.size) :
    doubleRev a s n = a.modifyAt s.idx 0 n.toNat fun _ v => 2 * v := by
  rw [doubleRev, dite_eq_left_of_eq_true (eq_true ⟨h, hs⟩), InPlace.Tail.forInRev_eq,
    InPlace.Tail.run_forInRevFrom_modify (idx := s.idx) (G := fun _ v => 2 * v)
      (he := fun _ _ hj => s.toNat_idx_toUSize h hs hj)
      (hinj := fun _ _ h₁ _ _ h₂ e => h.idx_inj h₁ h₂ e) (hg := fun _ _ _ _ => rfl)]
  simp

example (a : Int8Array) (s : Stride) (n : USize) (v : Int8) (h : s.Fits n.toNat a.size)
    (hs : a.size < USize.size) :
    fill a s n v = a.modifyAt s.idx 0 n.toNat fun _ _ => v := by
  rw [fill, dite_eq_left_of_eq_true (eq_true ⟨h, hs⟩), InPlace.Tail.forIn_eq,
    InPlace.Tail.run_forInFrom_write (idx := s.idx) (G := fun _ => v)
      (he := fun _ _ hj => s.toNat_idx_toUSize h hs hj) (hg := fun _ _ _ => rfl)]
  simp

-- The elements of the stride are doubled, and the others unchanged.
example (a : Int8Array) (s : Stride) (n : Nat) (h : s.Fits n a.size) (i : Nat) (hi : i < n) :
    (a.modifyAt s.idx 0 n fun _ v => 2 * v)[s.idx i]'(by simpa using h.idx_lt hi) =
      2 * a[s.idx i]'(h.idx_lt hi) :=
  getElem_modifyAt_stride a h (Nat.le_refl _) _ (Nat.zero_le _) hi

example (a : Int8Array) (s : Stride) (n : Nat) (p : Nat) (hp : ∀ i < n, s.idx i ≠ p)
    (h : p < a.size) :
    (a.modifyAt s.idx 0 n fun _ v => 2 * v)[p]'(by simpa using h) = a[p] :=
  getElem_modifyAt_of_forall_ne a s.idx _ (fun i _ hi => hp i hi) _

/-! `modifyAt2` and `zipModifyAt` -/

-- Two strides of one array: every second element from index `0`, and from index `1`.
#guard ((mk #[1, 2, 3, 4, 5, 6]).modifyAt2 (Stride.idx ⟨0, 2⟩) (Stride.idx ⟨1, 2⟩) 0 3
  (fun _ u v => u + v) (fun _ u v => u * v)).toArray == #[3, 2, 7, 12, 11, 30]

-- Both elements are read before either is written, and the second write wins where they meet.
#guard ((mk #[3, 2]).modifyAt2 id id 0 1 (fun _ u v => u + v) (fun _ u v => u * v)).toArray ==
  #[9, 2]

-- The steps run in order, and each sees the earlier writes.
#guard ((mk #[1, 2]).modifyAt2 (fun _ => 0) (fun _ => 1) 0 2 (fun _ u v => u + v)
  (fun _ u v => u * v)).toArray == #[5, 6]

-- Indices out of bounds read `default` and are not written.
#guard ((mk #[1, 2, 3]).modifyAt2 id (· + 2) 0 2 (fun _ u v => u + v)
  (fun _ u v => u * v)).toArray == #[4, 2, 3]

-- Two arrays.
#guard (zipModifyAt (mk #[1, 2, 3]) (mk #[4, 5, 6, 7]) id (· + 1) 0 3 (fun _ u v => u + v)
  (fun _ u v => u * v)) |> fun r => r.1.toArray == #[6, 8, 10] && r.2.toArray == #[4, 5, 12, 21]

-- An empty range changes nothing.
#guard (zipModifyAt (mk #[1, 2]) (mk #[3]) id id 2 1 (fun _ u v => u + v)
  (fun _ u v => u * v)) |> fun r => r.1.toArray == #[1, 2] && r.2.toArray == #[3]

/-! Strided loops -/

/-- `modifyStride` on a stride that fits, and `a` itself otherwise. -/
private def stride1 (a : Int8Array) (s : Stride) (n : Nat) (f : Int8 → Int8) :
    Int8Array :=
  if h : s.Fits n a.size then a.modifyStride s n f h else a

/-- `modifyStride2` on strides that fit, and `a` itself otherwise. -/
private def stride2 (a : Int8Array) (sa sb : Stride) (n : Nat)
    (f g : Int8 → Int8 → Int8) : Int8Array :=
  if h : sa.Fits n a.size ∧ sb.Fits n a.size then a.modifyStride2 sa sb n f g h.1 h.2 else a

/-- `zipModifyStride` on strides that fit, and `(a, b)` otherwise. -/
private def strideZip (a b : Int8Array) (sa sb : Stride) (n : Nat)
    (f g : Int8 → Int8 → Int8) : Int8Array × Int8Array :=
  if h : sa.Fits n a.size ∧ sb.Fits n b.size then zipModifyStride a b sa sb n f g h.1 h.2
  else (a, b)

#guard (stride1 (mk #[1, 2, 3, 4, 5, 6]) ⟨1, 2⟩ 3 (2 * ·)).toArray == #[1, 4, 3, 8, 5, 12]
-- A stride of `0` with one step, no steps, and a stride ending at the last element.
#guard (stride1 (mk #[1, 2, 3]) ⟨2, 0⟩ 1 (2 * ·)).toArray == #[1, 2, 6]
#guard (stride1 (mk #[1, 2, 3]) ⟨5, 7⟩ 0 (2 * ·)).toArray == #[1, 2, 3]
#guard (stride1 (mk #[1, 2, 3, 4, 5]) ⟨1, 3⟩ 2 (2 * ·)).toArray == #[1, 4, 3, 4, 10]

-- Two rows of a 3 × 3 matrix stored by columns.
#guard (stride2 (mk #[1, 2, 3, 4, 5, 6, 7, 8, 9]) ⟨0, 3⟩ ⟨1, 3⟩ 3 (· + ·) (· * ·)).toArray ==
  #[3, 2, 3, 9, 20, 6, 15, 56, 9]
#guard (stride2 (mk #[1, 2, 3, 4, 5, 6, 7, 8, 9]) ⟨0, 3⟩ ⟨1, 3⟩ 3 (· + ·) (· * ·)).toArray ==
  ((mk #[1, 2, 3, 4, 5, 6, 7, 8, 9]).modifyAt2 (Stride.idx ⟨0, 3⟩) (Stride.idx ⟨1, 3⟩) 0 3
    (fun _ => (· + ·)) (fun _ => (· * ·))).toArray

#guard (strideZip (mk #[1, 2, 3]) (mk #[4, 5, 6, 7]) ⟨0, 1⟩ ⟨1, 1⟩ 3 (· + ·) (· * ·)) |>
  fun r => r.1.toArray == #[6, 8, 10] && r.2.toArray == #[4, 5, 12, 21]
#guard (strideZip (mk #[1, 2, 3, 4]) (mk #[5, 6]) ⟨0, 2⟩ ⟨1, 0⟩ 1 (· + ·) (· * ·)) |>
  fun r => r.1.toArray == #[7, 2, 3, 4] && r.2.toArray == #[5, 6]

/-- `strideZip` with the same array, fresh at runtime, as both arrays. -/
@[noinline] private def zipSelf (n : Nat) : Int8Array × Int8Array :=
  let v := Int8Array.ofFn (n := n) fun i => i.val.toInt8 + 1
  strideZip v v ⟨0, 1⟩ ⟨0, 1⟩ n (· + ·) (· * ·)

/-- `zipSelf` where the array also stays alive, and is unchanged. -/
@[noinline] private def zipSelfKept (n : Nat) : Int8Array × Int8Array × Int8Array :=
  let v := Int8Array.ofFn (n := n) fun i => i.val.toInt8 + 1
  let r := strideZip v v ⟨0, 1⟩ ⟨0, 1⟩ n (· + ·) (· * ·)
  (r.1, r.2, v)

-- The same array as both arrays: the loop writes two arrays, as the model does.
#guard zipSelf 3 |> fun r => r.1.toArray == #[2, 4, 6] && r.2.toArray == #[1, 4, 9]
#guard zipSelfKept 3 |> fun r =>
  r.1.toArray == #[2, 4, 6] && r.2.1.toArray == #[1, 4, 9] && r.2.2.toArray == #[1, 2, 3]

-- The elements of two rows of a matrix stored by columns, with leading dimension `ld`.
example (a : Int8Array) (ld r n : Nat) (hr : r + 1 < ld) (h₁ : Stride.Fits ⟨r, ld⟩ n a.size)
    (h₂ : Stride.Fits ⟨r + 1, ld⟩ n a.size) (f g : Int8 → Int8 → Int8) (i : Nat)
    (hi : i < n) :
    (a.modifyStride2 ⟨r, ld⟩ ⟨r + 1, ld⟩ n f g h₁ h₂)[Stride.idx ⟨r, ld⟩ i]'(by
        simpa using h₁.idx_lt hi) =
      f (a[Stride.idx ⟨r, ld⟩ i]'(h₁.idx_lt hi)) (a[Stride.idx ⟨r + 1, ld⟩ i]'(h₂.idx_lt hi)) := by
  simp only [modifyStride2_eq]
  exact getElem_modifyAt2_stride_left a h₁ h₂
    (fun i _ j _ => Stride.idx_ne_idx_of_same_inc (s := ⟨r, ld⟩) (t := ⟨r + 1, ld⟩) rfl
      (by simp) (by simp; lia) i j)
    (Nat.le_refl _) _ _ (Nat.zero_le _) hi

-- Two vectors, by `zipModifyAt_eq`.
example (a b : Int8Array) (sa sb : Stride) (n : Nat) (ha : sa.Fits n a.size)
    (hb : sb.Fits n b.size) (f g : Int8 → Int8 → Int8) :
    zipModifyStride a b sa sb n f g ha hb =
      (a.modifyAt sa.idx 0 n fun i u => f u b[sb.idx i]!,
        b.modifyAt sb.idx 0 n fun i v => g a[sa.idx i]! v) := by
  rw [zipModifyStride_eq]
  exact zipModifyAt_eq a b _ _ (fun _ _ h₁ _ _ h₂ e => ha.idx_inj h₁ h₂ e)
    (fun _ _ h₁ _ _ h₂ e => hb.idx_inj h₁ h₂ e)

/-- A loop with two reads and two writes per step. -/
private def addMul (a : Int8Array) (sa sb : Stride) (n : USize) : Int8Array :=
  if h : sa.Fits n.toNat a.size ∧ sb.Fits n.toNat a.size ∧ a.size < USize.size then
    (InPlace.Tail.forIn (n := a.size) 0 n () (fun j _ hj next _ =>
        InPlace.Tail.readThen (sa.off.toUSize + sa.inc.toUSize * j)
          (sa.toNat_idx_toUSize_lt h.1 h.2.2 hj) fun u =>
        InPlace.Tail.readThen (sb.off.toUSize + sb.inc.toUSize * j)
          (sb.toNat_idx_toUSize_lt h.2.1 h.2.2 hj) fun v =>
        InPlace.Tail.writeThen (sa.off.toUSize + sa.inc.toUSize * j)
          (sa.toNat_idx_toUSize_lt h.1 h.2.2 hj) (u + v)
          (InPlace.Tail.writeThen (sb.off.toUSize + sb.inc.toUSize * j)
            (sb.toNat_idx_toUSize_lt h.2.1 h.2.2 hj) (u * v) (next ())))
      fun _ => InPlace.Tail.done () fun _ a _ => a).run a rfl
  else a

#guard (addMul (mk #[1, 2, 3, 4, 5, 6]) ⟨0, 2⟩ ⟨1, 2⟩ 3).toArray == #[3, 2, 7, 12, 11, 30]

example (a : Int8Array) (sa sb : Stride) (n : USize) (ha : sa.Fits n.toNat a.size)
    (hb : sb.Fits n.toNat a.size) (hs : a.size < USize.size) :
    addMul a sa sb n =
      a.modifyAt2 sa.idx sb.idx 0 n.toNat (fun _ u v => u + v) (fun _ u v => u * v) := by
  rw [addMul, dite_eq_left_of_eq_true (eq_true ⟨ha, hb, hs⟩), InPlace.Tail.forIn_eq,
    InPlace.Tail.run_forInFrom_modify2 (ia := sa.idx) (ib := sb.idx)
      (F := fun _ u v => u + v) (G := fun _ u v => u * v)
      (hea := fun _ _ hj => sa.toNat_idx_toUSize ha hs hj)
      (heb := fun _ _ hj => sb.toNat_idx_toUSize hb hs hj)
      (hf := fun _ _ _ _ _ => rfl) (hg := fun _ _ _ _ _ => rfl)]
  simp
