/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import all ScalarArray.Internal

/-!
# Strides and the models of loops

The parts of the specification of loops that name no element type, shared by all the arrays:

* `iterRange f lo hi x` applies `f lo`, `f (lo + 1)`, …, `f (hi - 1)` to `x`, in this order, and
  `iterRangeRev f lo hi x` applies them in the opposite order. They are the models of a loop
  whose step `j` maps its state by `f j`; the `run_forInFrom` and `run_forInRevFrom` lemmas of each
  array's `InPlace.Tail` run a loop to them.
* `Stride` is the affine index map `i ↦ off + inc * i` of a strided vector, such as the `incx` of
  a BLAS routine, the diagonal of a matrix or a column of a matrix stored by columns, and
  `Stride.Fits s n size` says that its first `n` indices are distinct and less than `size`. The
  arrays' `modifyAt` updates the elements at any index map, so `a.modifyAt s.idx lo hi g` is the
  model of a strided loop.

A loop computes the `USize` copies of the offset and the stride once, before it starts:
`toNat_idx_toUSize` gives the `Nat` value of `s.off.toUSize + s.inc.toUSize * j` for a step `j`
of a stride that fits in an array in memory.
-/

namespace ScalarArray

/-! ## Iteration over a range -/

section iterRange

variable {α : Sort u} {β : Sort v}

/--
`iterRange f lo hi x` applies `f lo`, `f (lo + 1)`, …, `f (hi - 1)` to `x`, in this order: the
model of a loop from `lo` up to `hi - 1` whose step `j` maps its state by `f j`. It is `x` when
`hi ≤ lo`.
-/
public def iterRange (f : Nat → α → α) (lo hi : Nat) (x : α) : α :=
  if lo < hi then iterRange f (lo + 1) hi (f lo x) else x
termination_by hi - lo

public theorem iterRange_of_lt (f : Nat → α → α) {lo hi : Nat} (h : lo < hi) (x : α) :
    iterRange f lo hi x = iterRange f (lo + 1) hi (f lo x) := by
  rw [iterRange]; simp [h]

public theorem iterRange_of_le (f : Nat → α → α) {lo hi : Nat} (h : hi ≤ lo) (x : α) :
    iterRange f lo hi x = x := by
  rw [iterRange]; simp [show ¬lo < hi by lia]

@[simp] public theorem iterRange_self (f : Nat → α → α) (lo : Nat) (x : α) :
    iterRange f lo lo x = x :=
  iterRange_of_le f (Nat.le_refl _) x

/-- The last step of `iterRange` comes last. -/
public theorem iterRange_succ (f : Nat → α → α) {lo hi : Nat} (h : lo ≤ hi) (x : α) :
    iterRange f lo (hi + 1) x = f hi (iterRange f lo hi x) := by
  obtain ⟨d, hd⟩ : ∃ d, hi - lo = d := ⟨_, rfl⟩
  induction d generalizing lo x with
  | zero =>
    obtain rfl : lo = hi := by lia
    rw [iterRange_of_lt f (by lia), iterRange_self, iterRange_self]
  | succ d ih =>
    rw [iterRange_of_lt f (show lo < hi + 1 by lia), ih (by lia) _ (by lia),
      ← iterRange_of_lt f (show lo < hi by lia)]

/-- `iterRange` splits at any `mid` between its bounds. -/
public theorem iterRange_split (f : Nat → α → α) {lo mid hi : Nat} (h₁ : lo ≤ mid)
    (h₂ : mid ≤ hi) (x : α) :
    iterRange f lo hi x = iterRange f mid hi (iterRange f lo mid x) := by
  obtain ⟨d, hd⟩ : ∃ d, mid - lo = d := ⟨_, rfl⟩
  induction d generalizing lo x with
  | zero =>
    obtain rfl : lo = mid := by lia
    rw [iterRange_self]
  | succ d ih =>
    rw [iterRange_of_lt f (show lo < hi by lia), iterRange_of_lt f (show lo < mid by lia),
      ih (by lia) _ (by lia)]

/-- `iterRange` depends only on the steps in its range. -/
public theorem iterRange_congr {f g : Nat → α → α} {lo hi : Nat}
    (h : ∀ i, lo ≤ i → i < hi → f i = g i) (x : α) :
    iterRange f lo hi x = iterRange g lo hi x := by
  obtain ⟨d, hd⟩ : ∃ d, hi - lo = d := ⟨_, rfl⟩
  induction d generalizing lo x with
  | zero => rw [iterRange_of_le f (by lia), iterRange_of_le g (by lia)]
  | succ d ih =>
    rw [iterRange_of_lt f (by lia), iterRange_of_lt g (by lia), h lo (Nat.le_refl _) (by lia),
      ih (fun i h₁ h₂ => h i (by lia) h₂) _ (by lia)]

/-- A property that each step in the range preserves holds after `iterRange`. -/
public theorem iterRange_invariant (p : α → Prop) {f : Nat → α → α} {lo hi : Nat}
    (hf : ∀ i, lo ≤ i → i < hi → ∀ x, p x → p (f i x)) {x : α} (hx : p x) :
    p (iterRange f lo hi x) := by
  obtain ⟨d, hd⟩ : ∃ d, hi - lo = d := ⟨_, rfl⟩
  induction d generalizing lo x with
  | zero => rw [iterRange_of_le f (by lia)]; exact hx
  | succ d ih =>
    rw [iterRange_of_lt f (by lia)]
    exact ih (fun i h₁ h₂ => hf i (by lia) h₂) (hf lo (Nat.le_refl _) (by lia) x hx) (by lia)

/-- A map `φ` that takes each step `f i` to `g i` takes `iterRange f` to `iterRange g`. -/
public theorem apply_iterRange (φ : α → β) {f : Nat → α → α} {g : Nat → β → β} {lo hi : Nat}
    (h : ∀ i, lo ≤ i → i < hi → ∀ x, φ (f i x) = g i (φ x)) (x : α) :
    φ (iterRange f lo hi x) = iterRange g lo hi (φ x) := by
  obtain ⟨d, hd⟩ : ∃ d, hi - lo = d := ⟨_, rfl⟩
  induction d generalizing lo x with
  | zero => rw [iterRange_of_le f (by lia), iterRange_of_le g (by lia)]
  | succ d ih =>
    rw [iterRange_of_lt f (by lia), iterRange_of_lt g (by lia), ← h lo (Nat.le_refl _) (by lia),
      ih (fun i h₁ h₂ => h i (by lia) h₂) _ (by lia)]

/--
`iterRangeRev f lo hi x` applies `f (hi - 1)`, `f (hi - 2)`, …, `f lo` to `x`, in this order: the
model of a loop from `hi - 1` down to `lo` whose step `j` maps its state by `f j`. It is `x` when
`hi ≤ lo`.
-/
public def iterRangeRev (f : Nat → α → α) (lo hi : Nat) (x : α) : α :=
  if lo < hi then iterRangeRev f lo (hi - 1) (f (hi - 1) x) else x
termination_by hi - lo

public theorem iterRangeRev_of_lt (f : Nat → α → α) {lo hi : Nat} (h : lo < hi) (x : α) :
    iterRangeRev f lo hi x = iterRangeRev f lo (hi - 1) (f (hi - 1) x) := by
  rw [iterRangeRev]; simp [h]

public theorem iterRangeRev_of_le (f : Nat → α → α) {lo hi : Nat} (h : hi ≤ lo) (x : α) :
    iterRangeRev f lo hi x = x := by
  rw [iterRangeRev]; simp [show ¬lo < hi by lia]

@[simp] public theorem iterRangeRev_self (f : Nat → α → α) (lo : Nat) (x : α) :
    iterRangeRev f lo lo x = x :=
  iterRangeRev_of_le f (Nat.le_refl _) x

/-- The step `lo` of `iterRangeRev` comes last. -/
public theorem iterRangeRev_of_lt_left (f : Nat → α → α) {lo hi : Nat} (h : lo < hi) (x : α) :
    iterRangeRev f lo hi x = f lo (iterRangeRev f (lo + 1) hi x) := by
  obtain ⟨d, hd⟩ : ∃ d, hi - (lo + 1) = d := ⟨_, rfl⟩
  induction d generalizing hi x with
  | zero =>
    obtain rfl : hi = lo + 1 := by lia
    rw [iterRangeRev_of_lt f h, Nat.add_sub_cancel, iterRangeRev_self, iterRangeRev_self]
  | succ d ih =>
    rw [iterRangeRev_of_lt f h, ih (by lia) _ (by lia), ← iterRangeRev_of_lt f (by lia)]

/-- `iterRangeRev` splits at any `mid` between its bounds. -/
public theorem iterRangeRev_split (f : Nat → α → α) {lo mid hi : Nat} (h₁ : lo ≤ mid)
    (h₂ : mid ≤ hi) (x : α) :
    iterRangeRev f lo hi x = iterRangeRev f lo mid (iterRangeRev f mid hi x) := by
  obtain ⟨d, hd⟩ : ∃ d, hi - mid = d := ⟨_, rfl⟩
  induction d generalizing hi x with
  | zero =>
    obtain rfl : hi = mid := by lia
    rw [iterRangeRev_self]
  | succ d ih =>
    rw [iterRangeRev_of_lt f (show lo < hi by lia), iterRangeRev_of_lt f (show mid < hi by lia),
      ih (by lia) _ (by lia)]

/-- `iterRangeRev` depends only on the steps in its range. -/
public theorem iterRangeRev_congr {f g : Nat → α → α} {lo hi : Nat}
    (h : ∀ i, lo ≤ i → i < hi → f i = g i) (x : α) :
    iterRangeRev f lo hi x = iterRangeRev g lo hi x := by
  obtain ⟨d, hd⟩ : ∃ d, hi - lo = d := ⟨_, rfl⟩
  induction d generalizing hi x with
  | zero => rw [iterRangeRev_of_le f (by lia), iterRangeRev_of_le g (by lia)]
  | succ d ih =>
    rw [iterRangeRev_of_lt f (by lia), iterRangeRev_of_lt g (by lia),
      h (hi - 1) (by lia) (by lia), ih (fun i h₁ h₂ => h i h₁ (by lia)) _ (by lia)]

/-- A property that each step in the range preserves holds after `iterRangeRev`. -/
public theorem iterRangeRev_invariant (p : α → Prop) {f : Nat → α → α} {lo hi : Nat}
    (hf : ∀ i, lo ≤ i → i < hi → ∀ x, p x → p (f i x)) {x : α} (hx : p x) :
    p (iterRangeRev f lo hi x) := by
  obtain ⟨d, hd⟩ : ∃ d, hi - lo = d := ⟨_, rfl⟩
  induction d generalizing hi x with
  | zero => rw [iterRangeRev_of_le f (by lia)]; exact hx
  | succ d ih =>
    rw [iterRangeRev_of_lt f (by lia)]
    exact ih (fun i h₁ h₂ => hf i h₁ (by lia)) (hf (hi - 1) (by lia) (by lia) x hx) (by lia)

/-- A map `φ` that takes each step `f i` to `g i` takes `iterRangeRev f` to `iterRangeRev g`. -/
public theorem apply_iterRangeRev (φ : α → β) {f : Nat → α → α} {g : Nat → β → β}
    {lo hi : Nat} (h : ∀ i, lo ≤ i → i < hi → ∀ x, φ (f i x) = g i (φ x)) (x : α) :
    φ (iterRangeRev f lo hi x) = iterRangeRev g lo hi (φ x) := by
  obtain ⟨d, hd⟩ : ∃ d, hi - lo = d := ⟨_, rfl⟩
  induction d generalizing hi x with
  | zero => rw [iterRangeRev_of_le f (by lia), iterRangeRev_of_le g (by lia)]
  | succ d ih =>
    rw [iterRangeRev_of_lt f (by lia), iterRangeRev_of_lt g (by lia),
      ← h (hi - 1) (by lia) (by lia), ih (fun i h₁ h₂ => h i h₁ (by lia)) _ (by lia)]

end iterRange

/-! ## Strides -/

/--
The indices `off + inc * i` of a strided vector, such as the `incx` of a BLAS routine, the diagonal
of a matrix or a column of a matrix stored by columns. It is plain data: `Stride.Fits s n size`
says that its first `n` indices are distinct and less than `size`.
-/
public structure Stride where
  /-- The index of the step `0`. -/
  off : Nat
  /-- The distance between the indices of two consecutive steps. -/
  inc : Nat
deriving DecidableEq, Repr

namespace Stride

/-- The index `off + inc * i` of the step `i`. -/
@[expose] public def idx (s : Stride) (i : Nat) : Nat := s.off + s.inc * i

@[simp] public theorem idx_zero (s : Stride) : s.idx 0 = s.off := by
  simp [idx]

public theorem idx_succ (s : Stride) (i : Nat) : s.idx (i + 1) = s.idx i + s.inc := by
  simp only [idx, Nat.mul_succ, Nat.add_assoc]

/-- The stride from the step `k` of `s` on, with the same increment. -/
@[expose] public def shift (s : Stride) (k : Nat) : Stride := ⟨s.idx k, s.inc⟩

@[simp] public theorem off_shift (s : Stride) (k : Nat) : (s.shift k).off = s.idx k := rfl

@[simp] public theorem inc_shift (s : Stride) (k : Nat) : (s.shift k).inc = s.inc := rfl

@[simp] public theorem idx_shift (s : Stride) (k i : Nat) : (s.shift k).idx i = s.idx (k + i) := by
  simp only [shift, idx, Nat.mul_add, Nat.add_assoc]

/--
The first `n` steps of `s` are at distinct indices, less than `size`: the stride is positive,
unless there is at most one step, and the index of the last step is less than `size`.
-/
public structure Fits (s : Stride) (n size : Nat) : Prop where
  /-- The stride is positive, unless there is at most one step. -/
  inc_pos : 0 < s.inc ∨ n ≤ 1
  /-- The index of the last step is less than `size`. -/
  idx_last_lt : n = 0 ∨ s.idx (n - 1) < size

public instance (s : Stride) (n size : Nat) : Decidable (s.Fits n size) :=
  decidable_of_iff ((0 < s.inc ∨ n ≤ 1) ∧ (n = 0 ∨ s.idx (n - 1) < size))
    ⟨fun ⟨h₁, h₂⟩ => ⟨h₁, h₂⟩, fun ⟨h₁, h₂⟩ => ⟨h₁, h₂⟩⟩

variable {s : Stride} {n size : Nat}

/-- The index of each of the first `n` steps is less than `size`. -/
public theorem Fits.idx_lt (h : s.Fits n size) {i : Nat} (hi : i < n) : s.idx i < size := by
  have : s.inc * i ≤ s.inc * (n - 1) := Nat.mul_le_mul_left _ (by lia)
  rcases h.idx_last_lt with h' | h' <;> simp only [idx] at * <;> lia

/-- The first `n` steps are at distinct indices. -/
public theorem Fits.idx_inj (h : s.Fits n size) {i j : Nat} (hi : i < n) (hj : j < n)
    (e : s.idx i = s.idx j) : i = j := by
  simp only [idx] at e
  rcases h.inc_pos with h' | h'
  · exact Nat.eq_of_mul_eq_mul_left h' (by lia)
  · lia

/-- `n` steps that fit in `size` indices are at most `size` steps. -/
public theorem Fits.le_size (h : s.Fits n size) : n ≤ size := by
  rcases Nat.lt_or_ge n 2 with h₂ | h₂
  · rcases Nat.eq_zero_or_pos n with h₀ | h₀
    · lia
    · have := h.idx_lt (i := 0) h₀; simp at this; lia
  · have hinc : 0 < s.inc := by rcases h.inc_pos with h' | h' <;> lia
    have : n - 1 ≤ s.inc * (n - 1) := Nat.le_mul_of_pos_left _ hinc
    have := h.idx_lt (i := n - 1) (by lia)
    simp only [idx] at this
    lia

/-- Fewer steps fit too. -/
public theorem Fits.mono (h : s.Fits n size) {m : Nat} (hm : m ≤ n) : s.Fits m size where
  inc_pos := by rcases h.inc_pos with h' | h' <;> lia
  idx_last_lt := by
    rcases Nat.eq_zero_or_pos m with h' | h'
    · exact .inl h'
    · exact .inr (h.idx_lt (by lia))

/-- The steps of `s` from `k` on fit, as the steps of `s.shift k`. -/
public theorem Fits.shift (h : s.Fits n size) (k : Nat) : (s.shift k).Fits (n - k) size where
  inc_pos := by rcases h.inc_pos with h' | h' <;> simp only [inc_shift] <;> lia
  idx_last_lt := by
    rcases Nat.lt_or_ge k n with h' | h'
    · exact .inr (by rw [idx_shift]; exact h.idx_lt (by lia))
    · exact .inl (by lia)

/--
The `USize` index `s.off.toUSize + s.inc.toUSize * i` of a step `i < n` of a stride that fits in
an array of `USize` size, as every array in memory has, doesn't wrap around.
-/
public theorem toNat_idx_toUSize (h : s.Fits n size) (hs : size < USize.size) {i : USize}
    (hi : i.toNat < n) : (s.off.toUSize + s.inc.toUSize * i).toNat = s.idx i.toNat := by
  have h₁ := h.idx_lt hi
  simp only [idx] at h₁ ⊢
  have ho : s.off.toUSize.toNat = s.off := by
    simp [Nat.mod_eq_of_lt (show s.off < USize.size by lia)]
  rcases Nat.eq_zero_or_pos i.toNat with h₀ | h₀
  · have : i = 0 := USize.toNat_inj.mp (by simpa using h₀)
    subst this
    simp [ho]
  · have hinc : s.inc ≤ s.inc * i.toNat := Nat.le_mul_of_pos_right _ h₀
    have hc : s.inc.toUSize.toNat = s.inc := by
      simp [Nat.mod_eq_of_lt (show s.inc < USize.size by lia)]
    rw [toNat_add_mul_of_lt (by rw [ho, hc]; lia), ho, hc]

/-- The `USize` index of a step `i < n` is less than `size`. -/
public theorem toNat_idx_toUSize_lt (h : s.Fits n size) (hs : size < USize.size) {i : USize}
    (hi : i.toNat < n) : (s.off.toUSize + s.inc.toUSize * i).toNat < size := by
  rw [toNat_idx_toUSize h hs hi]; exact h.idx_lt hi

end Stride

end ScalarArray
