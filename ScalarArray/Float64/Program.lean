/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ScalarArray.Float64.Lemmas
import all ScalarArray.Float64.Basic
import all ScalarArray.Float64.Lemmas

/-!
# In-place programs on `Float64Array`

`Float64Array.InPlace n α` is a program that reads and writes an array of size `n` in place and
returns a value of type `α`. Programs are built from `read`, `write`, the monad operations and the
loops `forUp`, `forUp2`, `forDown` and `forDown2`, then run on an array with `runInPlace` or
`InPlace.run`, which make the array exclusive once, before the program runs.

The array is never visible to a program: `InPlace` and its state have private constructors, so the
only code that touches the state is the code in this module, which passes it on linearly. That is
what lets `write` store without checking that the array is exclusive, like the loops of the
in-place folds.

The loops must be the loops of this module. A program that calls itself recursively compiles to a
closure for each step, and `for` in `do` notation boxes its mutable variables at each step, so both
are much slower than `forUp`, whose step is inlined into one loop with unboxed accumulators.

Programs are specified by `InPlace.run`, whose behavior the `run_*` lemmas give.
-/

namespace ScalarArray

namespace Float64Array

/--
The state of an in-place program on arrays of size `n`: the array itself. Its constructor is
private, so that no code outside this module can hold a state, or run a program on one.
-/
public structure InPlace.State (n : Nat) where
  private mk ::
  private array : Float64Array
  private size_array : array.size = n

/--
A program that reads and writes an array of size `n` in place and returns a value of type `α`.
See the module documentation.
-/
public structure InPlace (n : Nat) (α : Type u) where
  private mk ::
  private fn : InPlace.State n → α × InPlace.State n

namespace InPlace

variable {n : Nat} {α β : Type u}

/-- The program that returns `x` and leaves the array alone. Use `pure`. -/
@[inline]
public protected def pure (x : α) : InPlace n α := ⟨fun s => (x, s)⟩

/-- Runs `m`, then `f` on its result. Use `>>=`. -/
@[inline]
public protected def bind (m : InPlace n α) (f : α → InPlace n β) : InPlace n β :=
  ⟨fun s => let p := m.fn s; (f p.1).fn p.2⟩

@[inline]
public instance : Monad (InPlace n) where
  pure := InPlace.pure
  bind := InPlace.bind

/-- The element at index `i`. -/
@[inline]
public def read (i : USize) (h : i.toNat < n) : InPlace n Float :=
  ⟨fun s => (s.array.uget i (by rw [s.size_array]; exact h), s)⟩

/--
The index `off + j` of the window of `len` elements at `off` is in bounds, for `j < len`. This is
the bound that `read` and `write` need in a loop over a window.
-/
public theorem toNat_add_lt_of_window {off len j : USize} (hw : off.toNat + len.toNat ≤ n)
    (hj : j.toNat < len.toNat) : (off + j).toNat < n := by
  rw [USize.toNat_add]
  exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (by lia)

@[inline]
private unsafe def writeImpl (i : USize) (_h : i.toNat < n) (v : Float) : InPlace n Unit :=
  ⟨fun s => ((), ⟨setUnsafe s.array i v, lcProof⟩)⟩

/--
Stores `v` at index `i`. It compiles to one store, without checking that the array is exclusive:
`run` made it exclusive, and only this module's code holds it since.
-/
@[implemented_by writeImpl]
public def write (i : USize) (h : i.toNat < n) (v : Float) : InPlace n Unit :=
  ⟨fun s => ((), ⟨s.array.uset i v (by rw [s.size_array]; exact h),
    by rw [size_uset]; exact s.size_array⟩)⟩

/--
Runs the program `m` on the array `a`, and returns its result and the new array. The array is made
exclusive first, so it is copied once if it is shared, and updated in place otherwise.
-/
@[inline]
public def run (m : InPlace n α) (a : Float64Array) (h : a.size = n) : α × Float64Array :=
  match m.fn ⟨a.ensureExclusive, by rw [ensureExclusive_eq]; exact h⟩ with
  | (x, s) => (x, s.array)

/-! ## Loops -/

private theorem toNat_succ_of_lt {j len : USize} (h : j < len) : (j + 1).toNat = j.toNat + 1 := by
  have h1 := USize.lt_iff_toNat_lt.1 h
  have h2 := USize.toNat_lt_size len
  rw [USize.toNat_add, USize.toNat_one]
  exact Nat.mod_eq_of_lt (by have : USize.size = 2 ^ System.Platform.numBits := rfl; lia)

private theorem lt_succ_of_lt {j len : USize} (h : j < len) :
    len.toNat - (j + 1).toNat < len.toNat - j.toNat := by
  have := USize.lt_iff_toNat_lt.1 h
  rw [toNat_succ_of_lt h]; lia

/-- The loop of `forUp`. -/
@[specialize]
private def forUp.loop (len : USize)
    (body : (j : USize) → j.toNat < len.toNat → β → InPlace n β)
    (j : USize) (b : β) (s : State n) : β × State n :=
  if hj : j < len then
    match (body j hj b).fn s with
    | (b, s) => forUp.loop len body (j + 1) b s
  else
    (b, s)
termination_by len.toNat - j.toNat
decreasing_by exact lt_succ_of_lt hj

/--
Runs `body j hj b` for each `j` from `j₀` up to `len - 1`, threading the accumulator `b` from
`init`. `forUp` is the case `j₀ = 0`. It is specified by `forUpFrom_eq`.
-/
@[inline]
public def forUpFrom (len : USize) (j₀ : USize) (init : β)
    (body : (j : USize) → j.toNat < len.toNat → β → InPlace n β) : InPlace n β :=
  ⟨forUp.loop len body j₀ init⟩

/--
Runs `body j hj b` for each `j < len`, from `0` up, threading the accumulator `b` from `init`, and
returns the last accumulator.
-/
@[inline]
public def forUp (len : USize) (init : β)
    (body : (j : USize) → j.toNat < len.toNat → β → InPlace n β) : InPlace n β :=
  forUpFrom len 0 init body

/-- The loop of `forUp2`, with the two accumulators as separate arguments. -/
@[specialize]
private def forUp2.loop {β₁ β₂ : Type u} (len : USize)
    (body : (j : USize) → j.toNat < len.toNat → β₁ → β₂ → InPlace n (β₁ × β₂))
    (j : USize) (b₁ : β₁) (b₂ : β₂) (s : State n) : (β₁ × β₂) × State n :=
  if hj : j < len then
    match (body j hj b₁ b₂).fn s with
    | ((b₁, b₂), s) => forUp2.loop len body (j + 1) b₁ b₂ s
  else
    ((b₁, b₂), s)
termination_by len.toNat - j.toNat
decreasing_by exact lt_succ_of_lt hj

/-- `forUpFrom` with two accumulators. It is specified by `forUp2From_eq`. -/
@[inline]
public def forUp2From {β₁ β₂ : Type u} (len : USize) (j₀ : USize) (init₁ : β₁) (init₂ : β₂)
    (body : (j : USize) → j.toNat < len.toNat → β₁ → β₂ → InPlace n (β₁ × β₂)) :
    InPlace n (β₁ × β₂) :=
  ⟨forUp2.loop len body j₀ init₁ init₂⟩

/--
`forUp` with two accumulators, which the loop keeps as two arguments, so that each one stays
unboxed when its type is a scalar, such as a carry and a borrow. A pair accumulator in `forUp`
would be allocated at every step.
-/
@[inline]
public def forUp2 {β₁ β₂ : Type u} (len : USize) (init₁ : β₁) (init₂ : β₂)
    (body : (j : USize) → j.toNat < len.toNat → β₁ → β₂ → InPlace n (β₁ × β₂)) :
    InPlace n (β₁ × β₂) :=
  forUp2From len 0 init₁ init₂ body

/-- The index of a step of `forDown`: `j - 1 < len` when `0 < j ≤ len`. -/
public theorem forDown_pred_lt {len j : USize} (hj : j.toNat ≤ len.toNat) (h0 : ¬j = 0) :
    (j - 1).toNat < len.toNat := by
  have : j.toNat ≠ 0 := fun h => h0 (USize.toNat_inj.1 (by simpa using h))
  rw [USize.toNat_sub_of_le _ _ (by rw [USize.le_iff_toNat_le, USize.toNat_one]; lia),
    USize.toNat_one]
  lia

private theorem forDown_pred_lt_self {j : USize} (h0 : ¬j = 0) : (j - 1).toNat < j.toNat := by
  have : j.toNat ≠ 0 := fun h => h0 (USize.toNat_inj.1 (by simpa using h))
  rw [USize.toNat_sub_of_le _ _ (by rw [USize.le_iff_toNat_le, USize.toNat_one]; lia),
    USize.toNat_one]
  lia

/-- The loop of `forDown`: `j` is the number of steps left. -/
@[specialize]
private def forDown.loop (len : USize)
    (body : (j : USize) → j.toNat < len.toNat → β → InPlace n β)
    (j : USize) (hj : j.toNat ≤ len.toNat) (b : β) (s : State n) : β × State n :=
  if h0 : j = 0 then
    (b, s)
  else
    have hj' : (j - 1).toNat < len.toNat := forDown_pred_lt hj h0
    match (body (j - 1) hj' b).fn s with
    | (b, s) => forDown.loop len body (j - 1) (Nat.le_of_lt hj') b s
termination_by j.toNat
decreasing_by exact forDown_pred_lt_self h0

/--
Runs `body j hj b` for each `j` from `j₀ - 1` down to `0`, threading the accumulator `b` from
`init`. `forDown` is the case `j₀ = len`. It is specified by `forDownFrom_eq`.
-/
@[inline]
public def forDownFrom (len : USize) (j₀ : USize) (h : j₀.toNat ≤ len.toNat) (init : β)
    (body : (j : USize) → j.toNat < len.toNat → β → InPlace n β) : InPlace n β :=
  ⟨forDown.loop len body j₀ h init⟩

/--
Runs `body j hj b` for each `j < len`, from `len - 1` down to `0`, threading the accumulator `b`
from `init`, and returns the last accumulator.
-/
@[inline]
public def forDown (len : USize) (init : β)
    (body : (j : USize) → j.toNat < len.toNat → β → InPlace n β) : InPlace n β :=
  forDownFrom len len (Nat.le_refl _) init body

/-- The loop of `forDown2`, with the two accumulators as separate arguments. -/
@[specialize]
private def forDown2.loop {β₁ β₂ : Type u} (len : USize)
    (body : (j : USize) → j.toNat < len.toNat → β₁ → β₂ → InPlace n (β₁ × β₂))
    (j : USize) (hj : j.toNat ≤ len.toNat) (b₁ : β₁) (b₂ : β₂) (s : State n) :
    (β₁ × β₂) × State n :=
  if h0 : j = 0 then
    ((b₁, b₂), s)
  else
    have hj' : (j - 1).toNat < len.toNat := forDown_pred_lt hj h0
    match (body (j - 1) hj' b₁ b₂).fn s with
    | ((b₁, b₂), s) => forDown2.loop len body (j - 1) (Nat.le_of_lt hj') b₁ b₂ s
termination_by j.toNat
decreasing_by exact forDown_pred_lt_self h0

/-- `forDownFrom` with two accumulators. It is specified by `forDown2From_eq`. -/
@[inline]
public def forDown2From {β₁ β₂ : Type u} (len : USize) (j₀ : USize) (h : j₀.toNat ≤ len.toNat)
    (init₁ : β₁) (init₂ : β₂)
    (body : (j : USize) → j.toNat < len.toNat → β₁ → β₂ → InPlace n (β₁ × β₂)) :
    InPlace n (β₁ × β₂) :=
  ⟨forDown2.loop len body j₀ h init₁ init₂⟩

/-- `forDown` with two accumulators, kept as two loop arguments like those of `forUp2`. -/
@[inline]
public def forDown2 {β₁ β₂ : Type u} (len : USize) (init₁ : β₁) (init₂ : β₂)
    (body : (j : USize) → j.toNat < len.toNat → β₁ → β₂ → InPlace n (β₁ × β₂)) :
    InPlace n (β₁ × β₂) :=
  forDown2From len len (Nat.le_refl _) init₁ init₂ body

/-! ## Specification -/

private theorem run_eq (m : InPlace n α) (a : Float64Array) (h : a.size = n) :
    m.run a h = ((m.fn ⟨a, h⟩).1, (m.fn ⟨a, h⟩).2.array) := rfl

/-- `run` leaves the size unchanged. -/
@[simp] public theorem size_run (m : InPlace n α) (a : Float64Array) (h : a.size = n) :
    (m.run a h).2.size = n := by
  rw [run_eq]; exact (m.fn ⟨a, h⟩).2.size_array

private theorem fn_inj {m m' : InPlace n α} (h : m.fn = m'.fn) : m = m' := by
  obtain ⟨f⟩ := m; obtain ⟨f'⟩ := m'
  cases h; rfl

private theorem State.ext' {s t : State n} (h : s.array = t.array) : s = t := by
  cases s; cases t; cases h; rfl

/-- Two programs are equal when they run the same on every array. -/
@[ext] public theorem ext {m m' : InPlace n α}
    (h : ∀ a (h : a.size = n), m.run a h = m'.run a h) : m = m' := by
  have : m.fn = m'.fn := by
    funext s
    have := h s.array s.size_array
    rw [run_eq, run_eq] at this
    exact Prod.ext (Prod.ext_iff.1 this).1 (State.ext' (Prod.ext_iff.1 this).2)
  obtain ⟨f⟩ := m; obtain ⟨f'⟩ := m'
  cases this; rfl

@[simp] public theorem run_pure (x : α) (a : Float64Array) (h : a.size = n) :
    (pure x : InPlace n α).run a h = (x, a) := by
  rfl

@[simp] public theorem run_bind (m : InPlace n α) (f : α → InPlace n β) (a : Float64Array)
    (h : a.size = n) :
    (m >>= f).run a h = (f (m.run a h).1).run (m.run a h).2 (size_run ..) := by
  rfl

@[simp] public theorem run_read (i : USize) (hi : i.toNat < n) (a : Float64Array)
    (h : a.size = n) : (read i hi).run a h = (a[i.toNat]'(by rw [h]; exact hi), a) := by
  simp only [run_eq, read]; simp

@[simp] public theorem run_write (i : USize) (hi : i.toNat < n) (v : Float) (a : Float64Array)
    (h : a.size = n) :
    (write i hi v).run a h = ((), a.set i.toNat v (by rw [h]; exact hi)) := by
  simp only [run_eq, write]
  congr 1

private theorem run_bind' (m : InPlace n α) (f : α → InPlace n β) (a : Float64Array)
    (h : a.size = n) :
    (m.bind f).run a h = (f (m.run a h).1).run (m.run a h).2 (size_run ..) := by
  rfl

private theorem run_pure' (x : α) (a : Float64Array) (h : a.size = n) :
    (InPlace.pure x : InPlace n α).run a h = (x, a) := by
  rfl

public instance : LawfulMonad (InPlace n) := LawfulMonad.mk'
  (id_map := fun m => InPlace.ext fun a h => by
    show (m.bind fun x => InPlace.pure (id x)).run a h = _
    rw [run_bind', run_pure']; rfl)
  (pure_bind := fun x f => InPlace.ext fun a h => by simp only [run_bind, run_pure])
  (bind_assoc := fun m f g => InPlace.ext fun a h => by simp only [run_bind])

private theorem forUp_loop_eq (len : USize)
    (body : (j : USize) → j.toNat < len.toNat → β → InPlace n β) (j : USize) (b : β)
    (s : State n) :
    forUp.loop len body j b s =
      if hj : j < len then
        (body j hj b >>= fun b => ⟨forUp.loop len body (j + 1) b⟩ : InPlace n β).fn s
      else (b, s) := by
  rw [forUp.loop]; rfl

/-- One step of `forUpFrom`. -/
public theorem forUpFrom_eq (len j : USize) (init : β)
    (body : (j : USize) → j.toNat < len.toNat → β → InPlace n β) :
    forUpFrom len j init body =
      if hj : j < len then body j hj init >>= fun b => forUpFrom len (j + 1) b body
      else pure init := by
  by_cases hc : j < len
  · rw [dite_eq_left_of_eq_true (eq_true hc)]
    apply fn_inj; funext s
    show forUp.loop len body j init s = _
    rw [forUp_loop_eq, dite_eq_left_of_eq_true (eq_true hc)]; rfl
  · rw [dite_eq_right_of_eq_false (eq_false hc)]
    apply fn_inj; funext s
    show forUp.loop len body j init s = _
    rw [forUp_loop_eq, dite_eq_right_of_eq_false (eq_false hc)]; rfl

@[simp] public theorem forUp_eq (len : USize) (init : β)
    (body : (j : USize) → j.toNat < len.toNat → β → InPlace n β) :
    forUp len init body = forUpFrom len 0 init body := by
  rfl

private theorem forUp2_loop_eq {β₁ β₂ : Type u} (len : USize)
    (body : (j : USize) → j.toNat < len.toNat → β₁ → β₂ → InPlace n (β₁ × β₂)) (j : USize)
    (b₁ : β₁) (b₂ : β₂) (s : State n) :
    forUp2.loop len body j b₁ b₂ s =
      if hj : j < len then
        (body j hj b₁ b₂ >>= fun b => ⟨forUp2.loop len body (j + 1) b.1 b.2⟩ :
          InPlace n (β₁ × β₂)).fn s
      else ((b₁, b₂), s) := by
  rw [forUp2.loop]; rfl

/-- One step of `forUp2From`. -/
public theorem forUp2From_eq {β₁ β₂ : Type u} (len j : USize) (init₁ : β₁) (init₂ : β₂)
    (body : (j : USize) → j.toNat < len.toNat → β₁ → β₂ → InPlace n (β₁ × β₂)) :
    forUp2From len j init₁ init₂ body =
      if hj : j < len then
        body j hj init₁ init₂ >>= fun b => forUp2From len (j + 1) b.1 b.2 body
      else pure (init₁, init₂) := by
  by_cases hc : j < len
  · rw [dite_eq_left_of_eq_true (eq_true hc)]
    apply fn_inj; funext s
    show forUp2.loop len body j init₁ init₂ s = _
    rw [forUp2_loop_eq, dite_eq_left_of_eq_true (eq_true hc)]; rfl
  · rw [dite_eq_right_of_eq_false (eq_false hc)]
    apply fn_inj; funext s
    show forUp2.loop len body j init₁ init₂ s = _
    rw [forUp2_loop_eq, dite_eq_right_of_eq_false (eq_false hc)]; rfl

@[simp] public theorem forUp2_eq {β₁ β₂ : Type u} (len : USize) (init₁ : β₁) (init₂ : β₂)
    (body : (j : USize) → j.toNat < len.toNat → β₁ → β₂ → InPlace n (β₁ × β₂)) :
    forUp2 len init₁ init₂ body = forUp2From len 0 init₁ init₂ body := by
  rfl

/-- `forUp2From` is `forUpFrom` on the pair of accumulators. -/
public theorem forUp2From_eq_forUpFrom {β₁ β₂ : Type u} (len j : USize) (init₁ : β₁)
    (init₂ : β₂)
    (body : (j : USize) → j.toNat < len.toNat → β₁ → β₂ → InPlace n (β₁ × β₂)) :
    forUp2From len j init₁ init₂ body =
      forUpFrom len j (init₁, init₂) fun j hj b => body j hj b.1 b.2 := by
  rw [forUp2From_eq, forUpFrom_eq]
  split
  · congr 1; funext b; exact forUp2From_eq_forUpFrom len (j + 1) b.1 b.2 body
  · rfl
termination_by len.toNat - j.toNat
decreasing_by exact lt_succ_of_lt ‹j < len›

private theorem forDown_loop_eq (len : USize)
    (body : (j : USize) → j.toNat < len.toNat → β → InPlace n β) (j : USize)
    (hj : j.toNat ≤ len.toNat) (b : β) (s : State n) :
    forDown.loop len body j hj b s =
      if h0 : j = 0 then (b, s)
      else
        (body (j - 1) (forDown_pred_lt hj h0) b >>= fun b =>
          ⟨forDown.loop len body (j - 1) (Nat.le_of_lt (forDown_pred_lt hj h0)) b⟩ :
          InPlace n β).fn s := by
  rw [forDown.loop]; rfl

/-- One step of `forDownFrom`. -/
public theorem forDownFrom_eq (len j : USize) (h : j.toNat ≤ len.toNat) (init : β)
    (body : (j : USize) → j.toNat < len.toNat → β → InPlace n β) :
    forDownFrom len j h init body =
      if h0 : j = 0 then pure init
      else body (j - 1) (forDown_pred_lt h h0) init >>= fun b =>
        forDownFrom len (j - 1) (Nat.le_of_lt (forDown_pred_lt h h0)) b body := by
  by_cases hc : j = 0
  · rw [dite_eq_left_of_eq_true (eq_true hc)]
    apply fn_inj; funext s
    show forDown.loop len body j h init s = _
    rw [forDown_loop_eq, dite_eq_left_of_eq_true (eq_true hc)]; rfl
  · rw [dite_eq_right_of_eq_false (eq_false hc)]
    apply fn_inj; funext s
    show forDown.loop len body j h init s = _
    rw [forDown_loop_eq, dite_eq_right_of_eq_false (eq_false hc)]; rfl

@[simp] public theorem forDown_eq (len : USize) (init : β)
    (body : (j : USize) → j.toNat < len.toNat → β → InPlace n β) :
    forDown len init body = forDownFrom len len (Nat.le_refl _) init body := by
  rfl

private theorem forDown2_loop_eq {β₁ β₂ : Type u} (len : USize)
    (body : (j : USize) → j.toNat < len.toNat → β₁ → β₂ → InPlace n (β₁ × β₂)) (j : USize)
    (hj : j.toNat ≤ len.toNat) (b₁ : β₁) (b₂ : β₂) (s : State n) :
    forDown2.loop len body j hj b₁ b₂ s =
      if h0 : j = 0 then ((b₁, b₂), s)
      else
        (body (j - 1) (forDown_pred_lt hj h0) b₁ b₂ >>= fun b =>
          ⟨forDown2.loop len body (j - 1) (Nat.le_of_lt (forDown_pred_lt hj h0)) b.1 b.2⟩ :
          InPlace n (β₁ × β₂)).fn s := by
  rw [forDown2.loop]; rfl

/-- One step of `forDown2From`. -/
public theorem forDown2From_eq {β₁ β₂ : Type u} (len j : USize) (h : j.toNat ≤ len.toNat)
    (init₁ : β₁) (init₂ : β₂)
    (body : (j : USize) → j.toNat < len.toNat → β₁ → β₂ → InPlace n (β₁ × β₂)) :
    forDown2From len j h init₁ init₂ body =
      if h0 : j = 0 then pure (init₁, init₂)
      else body (j - 1) (forDown_pred_lt h h0) init₁ init₂ >>= fun b =>
        forDown2From len (j - 1) (Nat.le_of_lt (forDown_pred_lt h h0)) b.1 b.2 body := by
  by_cases hc : j = 0
  · rw [dite_eq_left_of_eq_true (eq_true hc)]
    apply fn_inj; funext s
    show forDown2.loop len body j h init₁ init₂ s = _
    rw [forDown2_loop_eq, dite_eq_left_of_eq_true (eq_true hc)]; rfl
  · rw [dite_eq_right_of_eq_false (eq_false hc)]
    apply fn_inj; funext s
    show forDown2.loop len body j h init₁ init₂ s = _
    rw [forDown2_loop_eq, dite_eq_right_of_eq_false (eq_false hc)]; rfl

@[simp] public theorem forDown2_eq {β₁ β₂ : Type u} (len : USize) (init₁ : β₁) (init₂ : β₂)
    (body : (j : USize) → j.toNat < len.toNat → β₁ → β₂ → InPlace n (β₁ × β₂)) :
    forDown2 len init₁ init₂ body = forDown2From len len (Nat.le_refl _) init₁ init₂ body := by
  rfl

/-- `forDown2From` is `forDownFrom` on the pair of accumulators. -/
public theorem forDown2From_eq_forDownFrom {β₁ β₂ : Type u} (len j : USize)
    (h : j.toNat ≤ len.toNat) (init₁ : β₁) (init₂ : β₂)
    (body : (j : USize) → j.toNat < len.toNat → β₁ → β₂ → InPlace n (β₁ × β₂)) :
    forDown2From len j h init₁ init₂ body =
      forDownFrom len j h (init₁, init₂) fun j hj b => body j hj b.1 b.2 := by
  rw [forDown2From_eq, forDownFrom_eq]
  split
  · rfl
  · congr 1; funext b; exact forDown2From_eq_forDownFrom len (j - 1) _ b.1 b.2 body
termination_by j.toNat
decreasing_by exact forDown_pred_lt_self ‹_›

end InPlace

/--
Runs the program `m` on `a`, and returns its result and the new array: `m.run a rfl`. The array is
made exclusive first, so it is copied once if it is shared, and updated in place otherwise.
-/
@[inline]
public def runInPlace {α : Type u} (a : Float64Array) (m : InPlace a.size α) : α × Float64Array :=
  m.run a rfl

@[simp] public theorem runInPlace_eq {α : Type u} (a : Float64Array) (m : InPlace a.size α) :
    a.runInPlace m = m.run a rfl := by
  rfl

end Float64Array

end ScalarArray
