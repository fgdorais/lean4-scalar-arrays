/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ScalarArray.Int32.Lemmas
import all ScalarArray.Int32.Basic
import all ScalarArray.Int32.Lemmas

/-!
# In-place programs on `Int32Array`

`Int32Array.InPlace n α` is a program that reads and writes an array of size `n` in place and
returns a value of type `α`. Programs are built from `read`, `write`, the monad operations and the
loops `forIn`, `forIn2`, `forInRev` and `forInRev2`, then run on an array with `runInPlace` or
`InPlace.run`, which make the array exclusive once, before the program runs.

The array is never visible to a program: `InPlace` and its state have private constructors, so the
only code that touches the state is the code in this module, which passes it on linearly. That is
what lets `write` store without checking that the array is exclusive. The in-place folds of
`ScalarArray.X.InPlace` are programs of this kind.

The loops must be the loops of this module. A program that calls itself recursively compiles to a
closure for each step, and `for` in `do` notation boxes its mutable variables at each step, so both
are much slower than `forIn`, whose step is inlined into one loop with unboxed accumulators.

Programs are specified by `InPlace.run`, whose behavior the `run_*` lemmas give.
-/

namespace ScalarArray

namespace Int32Array

/--
The state of an in-place program on arrays of size `n`: the array itself. Its constructor is
private, so that no code outside this module can hold a state, or run a program on one.
-/
public structure InPlace.State (n : Nat) where
  private mk ::
  private array : Int32Array
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
public def read (i : USize) (h : i.toNat < n) : InPlace n Int32 :=
  ⟨fun s => (s.array.uget i (by rw [s.size_array]; exact h), s)⟩

/--
`read i h` followed by `k` on the element, for a program `k` in any universe: `read` itself returns
a `Int32`, so in `do` notation it binds only in programs whose results are in `Type`.
-/
@[inline]
public def readThen (i : USize) (h : i.toNat < n) (k : Int32 → InPlace n α) : InPlace n α :=
  ⟨fun s => (k (s.array.uget i (by rw [s.size_array]; exact h))).fn s⟩

/--
The index `off + j` of the window of `len` elements at `off` is in bounds, for `j < len`. This is
the bound that `read` and `write` need in a loop over a window.
-/
public theorem toNat_add_lt_of_window {off len j : USize} (hw : off.toNat + len.toNat ≤ n)
    (hj : j.toNat < len.toNat) : (off + j).toNat < n := by
  rw [USize.toNat_add]
  exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (by lia)

@[inline]
private unsafe def writeImpl (i : USize) (_h : i.toNat < n) (v : Int32) :
    InPlace.{u} n PUnit :=
  ⟨fun s => (⟨⟩, ⟨setUnsafe s.array i v, lcProof⟩)⟩

/--
Stores `v` at index `i`. It compiles to one store, without checking that the array is exclusive:
`run` made it exclusive, and only this module's code holds it since.
-/
@[implemented_by writeImpl]
public def write (i : USize) (h : i.toNat < n) (v : Int32) : InPlace.{u} n PUnit :=
  ⟨fun s => (⟨⟩, ⟨s.array.uset i v (by rw [s.size_array]; exact h),
    by rw [size_uset]; exact s.size_array⟩)⟩

/--
Runs the program `m` on the array `a`, and returns its result and the new array. The array is made
exclusive first, so it is copied once if it is shared, and updated in place otherwise.
-/
@[inline]
public def run (m : InPlace n α) (a : Int32Array) (h : a.size = n) : α × Int32Array :=
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

/-- The index of a step of `forIn`: `lo ≤ j + 1` when `lo ≤ j < hi`. -/
public theorem forIn_le_succ {lo j hi : USize} (h : lo.toNat ≤ j.toNat) (hj : j < hi) :
    lo.toNat ≤ (j + 1).toNat := by
  rw [toNat_succ_of_lt hj]; lia

/-- The loop of `forInFrom`: the next step is at `j + 1`, while `j < hi`. -/
@[specialize]
private def forUp.loop (lo hi : USize)
    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat → β → InPlace n β)
    (j : USize) (hlo : lo.toNat ≤ j.toNat) (b : β) (s : State n) : β × State n :=
  if hj : j < hi then
    match (body j hlo hj b).fn s with
    | (b, s) => forUp.loop lo hi body (j + 1) (forIn_le_succ hlo hj) b s
  else
    (b, s)
termination_by hi.toNat - j.toNat
decreasing_by exact lt_succ_of_lt hj

/--
Runs `body j hlo hj b` for each `j` from `j₀` up to `hi - 1`, threading the accumulator `b` from
`init`. `forIn` is the case `j₀ = lo`. It is specified by `forInFrom_eq`.
-/
@[inline]
public def forInFrom (lo hi j₀ : USize) (h : lo.toNat ≤ j₀.toNat) (init : β)
    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat → β → InPlace n β) :
    InPlace n β :=
  ⟨forUp.loop lo hi body j₀ h init⟩

/--
Runs `body j hlo hj b` for each `j` from `lo` up to `hi - 1`, threading the accumulator `b` from
`init`, and returns the last accumulator. The body gets both bounds of `j`. It runs no step when
`hi ≤ lo`.
-/
@[inline, expose]
public def forIn (lo hi : USize) (init : β)
    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat → β → InPlace n β) :
    InPlace n β :=
  forInFrom lo hi lo (Nat.le_refl _) init body

/-- The loop of `forIn2From`, with the two accumulators as separate arguments. -/
@[specialize]
private def forUp2.loop {β₁ : Type v} {β₂ : Type w} (lo hi : USize)
    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat → β₁ → β₂ →
      InPlace n (β₁ × β₂))
    (j : USize) (hlo : lo.toNat ≤ j.toNat) (b₁ : β₁) (b₂ : β₂) (s : State n) :
    (β₁ × β₂) × State n :=
  if hj : j < hi then
    match (body j hlo hj b₁ b₂).fn s with
    | ((b₁, b₂), s) => forUp2.loop lo hi body (j + 1) (forIn_le_succ hlo hj) b₁ b₂ s
  else
    ((b₁, b₂), s)
termination_by hi.toNat - j.toNat
decreasing_by exact lt_succ_of_lt hj

/-- `forInFrom` with two accumulators. It is specified by `forIn2From_eq`. -/
@[inline]
public def forIn2From {β₁ : Type v} {β₂ : Type w} (lo hi j₀ : USize) (h : lo.toNat ≤ j₀.toNat)
    (init₁ : β₁) (init₂ : β₂)
    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat → β₁ → β₂ →
      InPlace n (β₁ × β₂)) :
    InPlace n (β₁ × β₂) :=
  ⟨forUp2.loop lo hi body j₀ h init₁ init₂⟩

/--
`forIn` with two accumulators, which the loop keeps as two arguments, so that each one stays
unboxed when its type is a scalar, such as a carry and a borrow. A pair accumulator in `forIn`
would be allocated at every step.
-/
@[inline, expose]
public def forIn2 {β₁ : Type v} {β₂ : Type w} (lo hi : USize) (init₁ : β₁) (init₂ : β₂)
    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat → β₁ → β₂ →
      InPlace n (β₁ × β₂)) :
    InPlace n (β₁ × β₂) :=
  forIn2From lo hi lo (Nat.le_refl _) init₁ init₂ body

/-- The index of a step of `forInRev`: `j - 1 < hi` when `lo < j ≤ hi`. -/
public theorem forInRev_pred_lt {lo hi j : USize} (hj : j.toNat ≤ hi.toNat) (h : lo < j) :
    (j - 1).toNat < hi.toNat := by
  have := USize.lt_iff_toNat_lt.1 h
  rw [USize.toNat_sub_of_le _ _ (by rw [USize.le_iff_toNat_le, USize.toNat_one]; lia),
    USize.toNat_one]
  lia

/-- The index of a step of `forInRev`: `lo ≤ j - 1` when `lo < j`. -/
public theorem forInRev_le_pred {lo j : USize} (h : lo < j) : lo.toNat ≤ (j - 1).toNat := by
  have := USize.lt_iff_toNat_lt.1 h
  rw [USize.toNat_sub_of_le _ _ (by rw [USize.le_iff_toNat_le, USize.toNat_one]; lia),
    USize.toNat_one]
  lia

private theorem forInRev_pred_lt_self {lo j : USize} (h : lo < j) : (j - 1).toNat < j.toNat := by
  have := USize.lt_iff_toNat_lt.1 h
  rw [USize.toNat_sub_of_le _ _ (by rw [USize.le_iff_toNat_le, USize.toNat_one]; lia),
    USize.toNat_one]
  lia

/-- The loop of `forInRevFrom`: the next step is at `j - 1`, while `lo < j`. -/
@[specialize]
private def forDown.loop (lo hi : USize)
    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat → β → InPlace n β)
    (j : USize) (hj : j.toNat ≤ hi.toNat) (b : β) (s : State n) : β × State n :=
  if h : lo < j then
    have hj' : (j - 1).toNat < hi.toNat := forInRev_pred_lt hj h
    match (body (j - 1) (forInRev_le_pred h) hj' b).fn s with
    | (b, s) => forDown.loop lo hi body (j - 1) (Nat.le_of_lt hj') b s
  else
    (b, s)
termination_by j.toNat
decreasing_by exact forInRev_pred_lt_self h

/--
Runs `body j hlo hj b` for each `j` from `j₀ - 1` down to `lo`, threading the accumulator `b`
from `init`. `forInRev` is the case `j₀ = hi`. It is specified by `forInRevFrom_eq`.
-/
@[inline]
public def forInRevFrom (lo hi j₀ : USize) (h : j₀.toNat ≤ hi.toNat) (init : β)
    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat → β → InPlace n β) :
    InPlace n β :=
  ⟨forDown.loop lo hi body j₀ h init⟩

/--
Runs `body j hlo hj b` for each `j` from `hi - 1` down to `lo`, threading the accumulator `b` from
`init`, and returns the last accumulator. The body gets both bounds of `j`. It runs no step when
`hi ≤ lo`.
-/
@[inline, expose]
public def forInRev (lo hi : USize) (init : β)
    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat → β → InPlace n β) :
    InPlace n β :=
  forInRevFrom lo hi hi (Nat.le_refl _) init body

/-- The loop of `forInRev2From`, with the two accumulators as separate arguments. -/
@[specialize]
private def forDown2.loop {β₁ : Type v} {β₂ : Type w} (lo hi : USize)
    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat → β₁ → β₂ →
      InPlace n (β₁ × β₂))
    (j : USize) (hj : j.toNat ≤ hi.toNat) (b₁ : β₁) (b₂ : β₂) (s : State n) :
    (β₁ × β₂) × State n :=
  if h : lo < j then
    have hj' : (j - 1).toNat < hi.toNat := forInRev_pred_lt hj h
    match (body (j - 1) (forInRev_le_pred h) hj' b₁ b₂).fn s with
    | ((b₁, b₂), s) => forDown2.loop lo hi body (j - 1) (Nat.le_of_lt hj') b₁ b₂ s
  else
    ((b₁, b₂), s)
termination_by j.toNat
decreasing_by exact forInRev_pred_lt_self h

/-- `forInRevFrom` with two accumulators. It is specified by `forInRev2From_eq`. -/
@[inline]
public def forInRev2From {β₁ : Type v} {β₂ : Type w} (lo hi j₀ : USize)
    (h : j₀.toNat ≤ hi.toNat) (init₁ : β₁) (init₂ : β₂)
    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat → β₁ → β₂ →
      InPlace n (β₁ × β₂)) :
    InPlace n (β₁ × β₂) :=
  ⟨forDown2.loop lo hi body j₀ h init₁ init₂⟩

/-- `forInRev` with two accumulators, kept as two loop arguments like those of `forIn2`. -/
@[inline, expose]
public def forInRev2 {β₁ : Type v} {β₂ : Type w} (lo hi : USize) (init₁ : β₁) (init₂ : β₂)
    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat → β₁ → β₂ →
      InPlace n (β₁ × β₂)) :
    InPlace n (β₁ × β₂) :=
  forInRev2From lo hi hi (Nat.le_refl _) init₁ init₂ body

/-! ## Specification -/

private theorem run_eq (m : InPlace n α) (a : Int32Array) (h : a.size = n) :
    m.run a h = ((m.fn ⟨a, h⟩).1, (m.fn ⟨a, h⟩).2.array) := rfl

/-- `run` leaves the size unchanged. -/
@[simp] public theorem size_run (m : InPlace n α) (a : Int32Array) (h : a.size = n) :
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

@[simp] public theorem run_pure (x : α) (a : Int32Array) (h : a.size = n) :
    (pure x : InPlace n α).run a h = (x, a) := by
  rfl

@[simp] public theorem run_bind (m : InPlace n α) (f : α → InPlace n β) (a : Int32Array)
    (h : a.size = n) :
    (m >>= f).run a h = (f (m.run a h).1).run (m.run a h).2 (size_run ..) := by
  rfl

@[simp] public theorem run_read (i : USize) (hi : i.toNat < n) (a : Int32Array)
    (h : a.size = n) : (read i hi).run a h = (a[i.toNat]'(by rw [h]; exact hi), a) := by
  simp only [run_eq, read]; simp

@[simp] public theorem run_readThen (i : USize) (hi : i.toNat < n) (k : Int32 → InPlace n α)
    (a : Int32Array) (h : a.size = n) :
    (readThen i hi k).run a h = (k (a[i.toNat]'(by rw [h]; exact hi))).run a h := by
  simp only [run_eq, readThen]; simp

@[simp] public theorem run_write (i : USize) (hi : i.toNat < n) (v : Int32) (a : Int32Array)
    (h : a.size = n) :
    (write i hi v : InPlace.{u} n PUnit).run a h = (⟨⟩, a.set i.toNat v (by rw [h]; exact hi)) := by
  simp only [run_eq, write]
  congr 1

private theorem run_bind' (m : InPlace n α) (f : α → InPlace n β) (a : Int32Array)
    (h : a.size = n) :
    (m.bind f).run a h = (f (m.run a h).1).run (m.run a h).2 (size_run ..) := by
  rfl

private theorem run_pure' (x : α) (a : Int32Array) (h : a.size = n) :
    (InPlace.pure x : InPlace n α).run a h = (x, a) := by
  rfl

public instance : LawfulMonad (InPlace n) := LawfulMonad.mk'
  (id_map := fun m => InPlace.ext fun a h => by
    show (m.bind fun x => InPlace.pure (id x)).run a h = _
    rw [run_bind', run_pure']; rfl)
  (pure_bind := fun x f => InPlace.ext fun a h => by simp only [run_bind, run_pure])
  (bind_assoc := fun m f g => InPlace.ext fun a h => by simp only [run_bind])

private theorem forUp_loop_eq (lo hi : USize)
    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat → β → InPlace n β) (j : USize)
    (hlo : lo.toNat ≤ j.toNat) (b : β) (s : State n) :
    forUp.loop lo hi body j hlo b s =
      if hj : j < hi then
        (body j hlo hj b >>= fun b => ⟨forUp.loop lo hi body (j + 1) (forIn_le_succ hlo hj) b⟩ :
          InPlace n β).fn s
      else (b, s) := by
  rw [forUp.loop]; rfl

/-- One step of `forInFrom`. -/
public theorem forInFrom_eq (lo hi j : USize) (hlo : lo.toNat ≤ j.toNat) (init : β)
    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat → β → InPlace n β) :
    forInFrom lo hi j hlo init body =
      if hj : j < hi then
        body j hlo hj init >>= fun b => forInFrom lo hi (j + 1) (forIn_le_succ hlo hj) b body
      else pure init := by
  by_cases hc : j < hi
  · rw [dite_eq_left_of_eq_true (eq_true hc)]
    apply fn_inj; funext s
    show forUp.loop lo hi body j hlo init s = _
    rw [forUp_loop_eq, dite_eq_left_of_eq_true (eq_true hc)]; rfl
  · rw [dite_eq_right_of_eq_false (eq_false hc)]
    apply fn_inj; funext s
    show forUp.loop lo hi body j hlo init s = _
    rw [forUp_loop_eq, dite_eq_right_of_eq_false (eq_false hc)]; rfl

@[simp] public theorem forIn_eq (lo hi : USize) (init : β)
    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat → β → InPlace n β) :
    forIn lo hi init body = forInFrom lo hi lo (Nat.le_refl _) init body := by
  rfl

private theorem forUp2_loop_eq {β₁ : Type v} {β₂ : Type w} (lo hi : USize)
    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat → β₁ → β₂ →
      InPlace n (β₁ × β₂))
    (j : USize) (hlo : lo.toNat ≤ j.toNat) (b₁ : β₁) (b₂ : β₂) (s : State n) :
    forUp2.loop lo hi body j hlo b₁ b₂ s =
      if hj : j < hi then
        (body j hlo hj b₁ b₂ >>= fun b =>
          ⟨forUp2.loop lo hi body (j + 1) (forIn_le_succ hlo hj) b.1 b.2⟩ :
          InPlace n (β₁ × β₂)).fn s
      else ((b₁, b₂), s) := by
  rw [forUp2.loop]; rfl

/-- One step of `forIn2From`. -/
public theorem forIn2From_eq {β₁ : Type v} {β₂ : Type w} (lo hi j : USize)
    (hlo : lo.toNat ≤ j.toNat) (init₁ : β₁) (init₂ : β₂)
    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat → β₁ → β₂ →
      InPlace n (β₁ × β₂)) :
    forIn2From lo hi j hlo init₁ init₂ body =
      if hj : j < hi then
        body j hlo hj init₁ init₂ >>= fun b =>
          forIn2From lo hi (j + 1) (forIn_le_succ hlo hj) b.1 b.2 body
      else pure (init₁, init₂) := by
  by_cases hc : j < hi
  · rw [dite_eq_left_of_eq_true (eq_true hc)]
    apply fn_inj; funext s
    show forUp2.loop lo hi body j hlo init₁ init₂ s = _
    rw [forUp2_loop_eq, dite_eq_left_of_eq_true (eq_true hc)]; rfl
  · rw [dite_eq_right_of_eq_false (eq_false hc)]
    apply fn_inj; funext s
    show forUp2.loop lo hi body j hlo init₁ init₂ s = _
    rw [forUp2_loop_eq, dite_eq_right_of_eq_false (eq_false hc)]; rfl

@[simp] public theorem forIn2_eq {β₁ : Type v} {β₂ : Type w} (lo hi : USize) (init₁ : β₁)
    (init₂ : β₂)
    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat → β₁ → β₂ →
      InPlace n (β₁ × β₂)) :
    forIn2 lo hi init₁ init₂ body = forIn2From lo hi lo (Nat.le_refl _) init₁ init₂ body := by
  rfl

/-- `forIn2From` is `forInFrom` on the pair of accumulators. -/
public theorem forIn2From_eq_forInFrom {β₁ : Type v} {β₂ : Type w} (lo hi j : USize)
    (hlo : lo.toNat ≤ j.toNat) (init₁ : β₁) (init₂ : β₂)
    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat → β₁ → β₂ →
      InPlace n (β₁ × β₂)) :
    forIn2From lo hi j hlo init₁ init₂ body =
      forInFrom lo hi j hlo (init₁, init₂) fun j hlo hj b => body j hlo hj b.1 b.2 := by
  rw [forIn2From_eq, forInFrom_eq]
  split
  · congr 1; funext b; exact forIn2From_eq_forInFrom lo hi (j + 1) _ b.1 b.2 body
  · rfl
termination_by hi.toNat - j.toNat
decreasing_by exact lt_succ_of_lt ‹j < hi›

/-- `forIn2` is `forIn` on the pair of accumulators. -/
public theorem forIn2_eq_forIn {β₁ : Type v} {β₂ : Type w} (lo hi : USize) (init₁ : β₁)
    (init₂ : β₂)
    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat → β₁ → β₂ →
      InPlace n (β₁ × β₂)) :
    forIn2 lo hi init₁ init₂ body =
      forIn lo hi (init₁, init₂) fun j hlo hj b => body j hlo hj b.1 b.2 :=
  forIn2From_eq_forInFrom lo hi lo _ init₁ init₂ body

private theorem forDown_loop_eq (lo hi : USize)
    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat → β → InPlace n β) (j : USize)
    (hj : j.toNat ≤ hi.toNat) (b : β) (s : State n) :
    forDown.loop lo hi body j hj b s =
      if h : lo < j then
        (body (j - 1) (forInRev_le_pred h) (forInRev_pred_lt hj h) b >>= fun b =>
          ⟨forDown.loop lo hi body (j - 1) (Nat.le_of_lt (forInRev_pred_lt hj h)) b⟩ :
          InPlace n β).fn s
      else (b, s) := by
  rw [forDown.loop]; rfl

/-- One step of `forInRevFrom`. -/
public theorem forInRevFrom_eq (lo hi j : USize) (hj : j.toNat ≤ hi.toNat) (init : β)
    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat → β → InPlace n β) :
    forInRevFrom lo hi j hj init body =
      if h : lo < j then
        body (j - 1) (forInRev_le_pred h) (forInRev_pred_lt hj h) init >>= fun b =>
          forInRevFrom lo hi (j - 1) (Nat.le_of_lt (forInRev_pred_lt hj h)) b body
      else pure init := by
  by_cases hc : lo < j
  · rw [dite_eq_left_of_eq_true (eq_true hc)]
    apply fn_inj; funext s
    show forDown.loop lo hi body j hj init s = _
    rw [forDown_loop_eq, dite_eq_left_of_eq_true (eq_true hc)]; rfl
  · rw [dite_eq_right_of_eq_false (eq_false hc)]
    apply fn_inj; funext s
    show forDown.loop lo hi body j hj init s = _
    rw [forDown_loop_eq, dite_eq_right_of_eq_false (eq_false hc)]; rfl

@[simp] public theorem forInRev_eq (lo hi : USize) (init : β)
    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat → β → InPlace n β) :
    forInRev lo hi init body = forInRevFrom lo hi hi (Nat.le_refl _) init body := by
  rfl

private theorem forDown2_loop_eq {β₁ : Type v} {β₂ : Type w} (lo hi : USize)
    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat → β₁ → β₂ →
      InPlace n (β₁ × β₂))
    (j : USize) (hj : j.toNat ≤ hi.toNat) (b₁ : β₁) (b₂ : β₂) (s : State n) :
    forDown2.loop lo hi body j hj b₁ b₂ s =
      if h : lo < j then
        (body (j - 1) (forInRev_le_pred h) (forInRev_pred_lt hj h) b₁ b₂ >>= fun b =>
          ⟨forDown2.loop lo hi body (j - 1) (Nat.le_of_lt (forInRev_pred_lt hj h)) b.1 b.2⟩ :
          InPlace n (β₁ × β₂)).fn s
      else ((b₁, b₂), s) := by
  rw [forDown2.loop]; rfl

/-- One step of `forInRev2From`. -/
public theorem forInRev2From_eq {β₁ : Type v} {β₂ : Type w} (lo hi j : USize)
    (hj : j.toNat ≤ hi.toNat) (init₁ : β₁) (init₂ : β₂)
    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat → β₁ → β₂ →
      InPlace n (β₁ × β₂)) :
    forInRev2From lo hi j hj init₁ init₂ body =
      if h : lo < j then
        body (j - 1) (forInRev_le_pred h) (forInRev_pred_lt hj h) init₁ init₂ >>= fun b =>
          forInRev2From lo hi (j - 1) (Nat.le_of_lt (forInRev_pred_lt hj h)) b.1 b.2 body
      else pure (init₁, init₂) := by
  by_cases hc : lo < j
  · rw [dite_eq_left_of_eq_true (eq_true hc)]
    apply fn_inj; funext s
    show forDown2.loop lo hi body j hj init₁ init₂ s = _
    rw [forDown2_loop_eq, dite_eq_left_of_eq_true (eq_true hc)]; rfl
  · rw [dite_eq_right_of_eq_false (eq_false hc)]
    apply fn_inj; funext s
    show forDown2.loop lo hi body j hj init₁ init₂ s = _
    rw [forDown2_loop_eq, dite_eq_right_of_eq_false (eq_false hc)]; rfl

@[simp] public theorem forInRev2_eq {β₁ : Type v} {β₂ : Type w} (lo hi : USize) (init₁ : β₁)
    (init₂ : β₂)
    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat → β₁ → β₂ →
      InPlace n (β₁ × β₂)) :
    forInRev2 lo hi init₁ init₂ body =
      forInRev2From lo hi hi (Nat.le_refl _) init₁ init₂ body := by
  rfl

/-- `forInRev2From` is `forInRevFrom` on the pair of accumulators. -/
public theorem forInRev2From_eq_forInRevFrom {β₁ : Type v} {β₂ : Type w} (lo hi j : USize)
    (hj : j.toNat ≤ hi.toNat) (init₁ : β₁) (init₂ : β₂)
    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat → β₁ → β₂ →
      InPlace n (β₁ × β₂)) :
    forInRev2From lo hi j hj init₁ init₂ body =
      forInRevFrom lo hi j hj (init₁, init₂) fun j hlo hj b => body j hlo hj b.1 b.2 := by
  rw [forInRev2From_eq, forInRevFrom_eq]
  split
  · congr 1; funext b; exact forInRev2From_eq_forInRevFrom lo hi (j - 1) _ b.1 b.2 body
  · rfl
termination_by j.toNat
decreasing_by exact forInRev_pred_lt_self ‹_›

/-- `forInRev2` is `forInRev` on the pair of accumulators. -/
public theorem forInRev2_eq_forInRev {β₁ : Type v} {β₂ : Type w} (lo hi : USize) (init₁ : β₁)
    (init₂ : β₂)
    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat → β₁ → β₂ →
      InPlace n (β₁ × β₂)) :
    forInRev2 lo hi init₁ init₂ body =
      forInRev lo hi (init₁, init₂) fun j hlo hj b => body j hlo hj b.1 b.2 :=
  forInRev2From_eq_forInRevFrom lo hi hi _ init₁ init₂ body

/-! ## Running a loop straight into a continuation -/

/-- `forUp.loop`, handing the last accumulator and state to `k` instead of returning a pair. -/
@[specialize]
private def forUp.loopThen {γ : Type w} (lo hi : USize)
    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat → β → InPlace n β)
    (j : USize) (hlo : lo.toNat ≤ j.toNat) (b : β) (s : State n) (k : β → State n → γ) : γ :=
  if hj : j < hi then
    match (body j hlo hj b).fn s with
    | (b, s) => forUp.loopThen lo hi body (j + 1) (forIn_le_succ hlo hj) b s k
  else
    k b s
termination_by hi.toNat - j.toNat
decreasing_by exact lt_succ_of_lt hj

private theorem forUp_loopThen_eq {γ : Type w} (lo hi : USize)
    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat → β → InPlace n β)
    (j : USize) (hlo : lo.toNat ≤ j.toNat) (b : β) (s : State n) (k : β → State n → γ) :
    forUp.loopThen lo hi body j hlo b s k =
      k (forUp.loop lo hi body j hlo b s).1 (forUp.loop lo hi body j hlo b s).2 := by
  rw [forUp.loopThen, forUp.loop]
  split
  · exact forUp_loopThen_eq lo hi body (j + 1) _ _ _ k
  · rfl
termination_by hi.toNat - j.toNat
decreasing_by exact lt_succ_of_lt ‹_›

/--
Runs `forIn lo hi init body` on `a`, then `g` on the last accumulator and the new array, which the
loop calls itself: unlike `g` on the result of `run`, it builds no pair.
-/
@[inline]
public def runForInThen {γ : Type w} (a : Int32Array) (h : a.size = n) (lo hi : USize)
    (init : β) (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat → β → InPlace n β)
    (g : β → (a' : Int32Array) → a'.size = n → γ) : γ :=
  forUp.loopThen lo hi body lo (Nat.le_refl _) init
    ⟨a.ensureExclusive, by rw [ensureExclusive_eq]; exact h⟩
    fun b s => g b s.array s.size_array

public theorem runForInThen_eq {γ : Type w} (a : Int32Array) (h : a.size = n) (lo hi : USize)
    (init : β) (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat → β → InPlace n β)
    (g : β → (a' : Int32Array) → a'.size = n → γ) :
    runForInThen a h lo hi init body g =
      g ((forIn lo hi init body).run a h).1 ((forIn lo hi init body).run a h).2
        (size_run ..) := by
  unfold runForInThen
  rw [forUp_loopThen_eq]
  rfl

/-- `forDown.loop`, handing the last accumulator and state to `k` instead of returning a pair. -/
@[specialize]
private def forDown.loopThen {γ : Type w} (lo hi : USize)
    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat → β → InPlace n β)
    (j : USize) (hj : j.toNat ≤ hi.toNat) (b : β) (s : State n) (k : β → State n → γ) : γ :=
  if h : lo < j then
    have hj' := forInRev_pred_lt hj h
    match (body (j - 1) (forInRev_le_pred h) hj' b).fn s with
    | (b, s) => forDown.loopThen lo hi body (j - 1) (Nat.le_of_lt hj') b s k
  else
    k b s
termination_by j.toNat
decreasing_by exact forInRev_pred_lt_self h

private theorem forDown_loopThen_eq {γ : Type w} (lo hi : USize)
    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat → β → InPlace n β)
    (j : USize) (hj : j.toNat ≤ hi.toNat) (b : β) (s : State n) (k : β → State n → γ) :
    forDown.loopThen lo hi body j hj b s k =
      k (forDown.loop lo hi body j hj b s).1 (forDown.loop lo hi body j hj b s).2 := by
  rw [forDown.loopThen, forDown.loop]
  split
  · exact forDown_loopThen_eq lo hi body (j - 1) _ _ _ k
  · rfl
termination_by j.toNat
decreasing_by exact forInRev_pred_lt_self ‹_›

/-- `runForInThen` for `forInRev`. -/
@[inline]
public def runForInRevThen {γ : Type w} (a : Int32Array) (h : a.size = n) (lo hi : USize)
    (init : β) (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat → β → InPlace n β)
    (g : β → (a' : Int32Array) → a'.size = n → γ) : γ :=
  forDown.loopThen lo hi body hi (Nat.le_refl _) init
    ⟨a.ensureExclusive, by rw [ensureExclusive_eq]; exact h⟩
    fun b s => g b s.array s.size_array

public theorem runForInRevThen_eq {γ : Type w} (a : Int32Array) (h : a.size = n)
    (lo hi : USize) (init : β)
    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat → β → InPlace n β)
    (g : β → (a' : Int32Array) → a'.size = n → γ) :
    runForInRevThen a h lo hi init body g =
      g ((forInRev lo hi init body).run a h).1 ((forInRev lo hi init body).run a h).2
        (size_run ..) := by
  unfold runForInRevThen
  rw [forDown_loopThen_eq]
  rfl

/-- `forUp2.loop`, handing the two last accumulators and the state to `k`. -/
@[specialize]
private def forUp2.loopThen {β₁ : Type v} {β₂ : Type w} {γ : Type u} (lo hi : USize)
    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat → β₁ → β₂ →
      InPlace n (β₁ × β₂))
    (j : USize) (hlo : lo.toNat ≤ j.toNat) (b₁ : β₁) (b₂ : β₂) (s : State n)
    (k : β₁ → β₂ → State n → γ) : γ :=
  if hj : j < hi then
    match (body j hlo hj b₁ b₂).fn s with
    | ((b₁, b₂), s) => forUp2.loopThen lo hi body (j + 1) (forIn_le_succ hlo hj) b₁ b₂ s k
  else
    k b₁ b₂ s
termination_by hi.toNat - j.toNat
decreasing_by exact lt_succ_of_lt hj

private theorem forUp2_loopThen_eq {β₁ : Type v} {β₂ : Type w} {γ : Type u} (lo hi : USize)
    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat → β₁ → β₂ →
      InPlace n (β₁ × β₂))
    (j : USize) (hlo : lo.toNat ≤ j.toNat) (b₁ : β₁) (b₂ : β₂) (s : State n)
    (k : β₁ → β₂ → State n → γ) :
    forUp2.loopThen lo hi body j hlo b₁ b₂ s k =
      k (forUp2.loop lo hi body j hlo b₁ b₂ s).1.1 (forUp2.loop lo hi body j hlo b₁ b₂ s).1.2
        (forUp2.loop lo hi body j hlo b₁ b₂ s).2 := by
  rw [forUp2.loopThen, forUp2.loop]
  split
  · exact forUp2_loopThen_eq lo hi body (j + 1) _ _ _ _ k
  · rfl
termination_by hi.toNat - j.toNat
decreasing_by exact lt_succ_of_lt ‹_›

/-- `runForInThen` for `forIn2`, with the two accumulators handed to `g` apart. -/
@[inline]
public def runForIn2Then {β₁ : Type v} {β₂ : Type w} {γ : Type u} (a : Int32Array)
    (h : a.size = n) (lo hi : USize) (init₁ : β₁) (init₂ : β₂)
    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat → β₁ → β₂ →
      InPlace n (β₁ × β₂))
    (g : β₁ → β₂ → (a' : Int32Array) → a'.size = n → γ) : γ :=
  forUp2.loopThen lo hi body lo (Nat.le_refl _) init₁ init₂
    ⟨a.ensureExclusive, by rw [ensureExclusive_eq]; exact h⟩
    fun b₁ b₂ s => g b₁ b₂ s.array s.size_array

public theorem runForIn2Then_eq {β₁ : Type v} {β₂ : Type w} {γ : Type u} (a : Int32Array)
    (h : a.size = n) (lo hi : USize) (init₁ : β₁) (init₂ : β₂)
    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat → β₁ → β₂ →
      InPlace n (β₁ × β₂))
    (g : β₁ → β₂ → (a' : Int32Array) → a'.size = n → γ) :
    runForIn2Then a h lo hi init₁ init₂ body g =
      g ((forIn2 lo hi init₁ init₂ body).run a h).1.1
        ((forIn2 lo hi init₁ init₂ body).run a h).1.2
        ((forIn2 lo hi init₁ init₂ body).run a h).2 (size_run ..) := by
  unfold runForIn2Then
  rw [forUp2_loopThen_eq]
  rfl

end InPlace

/--
Runs the program `m` on `a`, and returns its result and the new array: `m.run a rfl`. The array is
made exclusive first, so it is copied once if it is shared, and updated in place otherwise.
-/
@[inline, expose]
public def runInPlace {α : Type u} (a : Int32Array) (m : InPlace a.size α) : α × Int32Array :=
  m.run a rfl

@[simp] public theorem runInPlace_eq {α : Type u} (a : Int32Array) (m : InPlace a.size α) :
    a.runInPlace m = m.run a rfl := by
  rfl

end Int32Array

end ScalarArray
