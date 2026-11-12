/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ScalarArray.Float32.Lemmas
import all ScalarArray.Internal
import all ScalarArray.Float32.Basic
import all ScalarArray.Float32.Lemmas

/-!
# In-place programs on `Float32Array`

`Float32Array.InPlace n α` is a program that reads and writes an array of size `n` in place and
returns a value of type `α`. It is a monad, and programs are built from:

* `read i h`, `readThen i h k`, `write i h v` and `writeThen i h v k`, at a `USize` index `i`
  with its bound `h` (`toNat_add_lt_of_window` gives the bound of `off + j` in a window);
* `InPlace.ite` and `InPlace.dite`, which branch inside one program;
* the loops `forIn lo hi` and `forInRev lo hi`, which run a body for each `j` from `lo` up to
  `hi - 1`, or from `hi - 1` down to `lo`, threading an accumulator. The body gets both bounds of
  `j`, `lo.toNat ≤ j.toNat` and `j.toNat < hi.toNat`. `forIn2` and `forInRev2` thread two
  accumulators as separate arguments, so that scalars such as carries stay unboxed;
* `forInBind`, `forIn2Bind`, `forInRevBind` and `forInRev2Bind`, a loop followed by the rest of
  the program, which the loop calls itself, so that its last accumulators reach the rest unboxed.

A program runs on an array with `a.runInPlace m` or `m.run a h`, which make the array exclusive
once, before the program runs. `runForInThen`, `runForInRevThen` and `runForIn2Then` run a single
loop and hand its last accumulators and the new array to a continuation, without a result pair.

A tail program `InPlace.Tail n γ` is a program that ends by handing its result and the new array to
a continuation `k`, which returns a `γ`, where `run` would return the pair of them: `Tail.done x k`
ends it, `Tail.bind m t` runs an in-place program `m` before it, and `Tail.readThen`,
`Tail.writeThen`, `Tail.ite`, `Tail.dite` and the loops `Tail.forInBind`, … are those of `InPlace`.
The continuation runs inside the program's last loop, so its last accumulators reach `k` unboxed,
and no result pair is built. A tail program runs with `a.runInPlaceThen t`,
`a.runInPlaceThenOf n h t` or `t.run a h`.

Tail programs also have loops in continuation-passing style, `Tail.forIn lo hi init body k` and
`Tail.forInRev`, with up to four variables in `Tail.forIn2`, `Tail.forIn3`, `Tail.forIn4`, and so
on. Their body is itself a tail program, which ends by calling a continuation `next` on the next
variables, and the loop ends with `k`. Each variable is an argument of the loop, so scalars stay
unboxed, and a nested loop, whose `k` calls the outer `next`, compiles to mutually recursive loops
with no allocation. They are specified by their one-step equations (`Tail.forInFrom_eq`, …).

The array is never visible to a program: `InPlace` and its state have private constructors, so the
only code that touches the state is the code in this module, which passes it on linearly. That is
what lets `write` store without checking that the array is exclusive. The in-place folds of
`ScalarArray.Float32.InPlace` are programs of this kind, and the experimental notation
`inplace a do …` of `ScalarArray.InPlaceSyntax` writes programs of this kind.

The loops must be the loops of this module. A program that calls itself recursively compiles to a
closure for each step, and `for` in `do` notation boxes its mutable variables at each step, so both
are much slower than `forIn`, whose step is inlined into one loop with unboxed accumulators.
Likewise, `if c then t else e` on programs builds both branches as closures, where `InPlace.ite`
branches inside the program.

Programs are specified by `InPlace.run`, whose behavior the `run_*` lemmas give. Each loop has a
one-step equation (`forInFrom_eq`, `forInRevFrom_eq`, …), and each `Bind` loop and `runFor*Then`
an `_eq` lemma in terms of the plain loop. `bind_eq` and `pure_eq` turn `InPlace.bind` and
`InPlace.pure`, which the notation writes, into `>>=` and `pure`.
-/

namespace ScalarArray

namespace Float32Array

/--
The state of an in-place program on arrays of size `n`: the array itself. Its constructor is
private, so that no code outside this module can hold a state, or run a program on one.
-/
public structure InPlace.State (n : Nat) where
  private mk ::
  private array : Float32Array
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
public def read (i : USize) (h : i.toNat < n) : InPlace n Float32 :=
  ⟨fun s => (s.array.uget i (by rw [s.size_array]; exact h), s)⟩

/--
`read i h` followed by `k` on the element, for a program `k` in any universe: `read` itself returns
a `Float32`, so in `do` notation it binds only in programs whose results are in `Type`.
-/
@[inline]
public def readThen (i : USize) (h : i.toNat < n) (k : Float32 → InPlace n α) : InPlace n α :=
  ⟨fun s => (k (s.array.uget i (by rw [s.size_array]; exact h))).fn s⟩

/--
The index `off + j` of the window of `len` elements at `off` is in bounds, for `j < len`. This is
the bound that `read` and `write` need in a loop over a window.
-/
public theorem toNat_add_lt_of_window {off len j : USize} (hw : off.toNat + len.toNat ≤ n)
    (hj : j.toNat < len.toNat) : (off + j).toNat < n := by
  grind

@[inline]
private unsafe def writeImpl (i : USize) (_h : i.toNat < n) (v : Float32) :
    InPlace.{u} n PUnit :=
  ⟨fun s => (⟨⟩, ⟨setUnsafe s.array i v, lcProof⟩)⟩

/--
Stores `v` at index `i`. It compiles to one store, without checking that the array is exclusive:
`run` made it exclusive, and only this module's code holds it since.
-/
@[implemented_by writeImpl]
public def write (i : USize) (h : i.toNat < n) (v : Float32) : InPlace.{u} n PUnit :=
  ⟨fun s => (⟨⟩, ⟨s.array.uset i v (by rw [s.size_array]; exact h),
    by rw [size_uset]; exact s.size_array⟩)⟩

/--
`write i h v` followed by `k`, for a program `k` in any universe: in `write i h v >>= fun _ => k`,
the universe of `write`'s `PUnit` is that of `k`.
-/
@[inline]
public def writeThen (i : USize) (h : i.toNat < n) (v : Float32) (k : InPlace n α) : InPlace n α :=
  (write i h v).bind fun _ => k

/--
Runs `t` if `c` holds and `e` otherwise. Unlike `if c then t else e`, which chooses a program and
then runs it, it compiles to a branch inside one program, without building the programs of the two
branches as closures.
-/
@[inline]
public protected def ite (c : Prop) [Decidable c] (t e : InPlace n α) : InPlace n α :=
  ⟨fun s => if c then t.fn s else e.fn s⟩

/-- `InPlace.ite` where each branch takes the proof of its condition. -/
@[inline]
public protected def dite (c : Prop) [Decidable c] (t : c → InPlace n α) (e : ¬c → InPlace n α) :
    InPlace n α :=
  ⟨fun s => if h : c then (t h).fn s else (e h).fn s⟩

/--
Runs the program `m` on the array `a`, and returns its result and the new array. The array is made
exclusive first, so it is copied once if it is shared, and updated in place otherwise.
-/
@[inline]
public def run (m : InPlace n α) (a : Float32Array) (h : a.size = n) : α × Float32Array :=
  match m.fn ⟨a.ensureExclusive, by rw [ensureExclusive_eq]; exact h⟩ with
  | (x, s) => (x, s.array)

/-! ## Loops -/

/-- The index of a step of `forIn`: `lo ≤ j + 1` when `lo ≤ j < hi`. -/
public theorem forIn_le_succ {lo j hi : USize} (h : lo.toNat ≤ j.toNat) (hj : j < hi) :
    lo.toNat ≤ (j + 1).toNat := by
  grind

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
decreasing_by exact sub_toNat_add_one_lt hj

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
decreasing_by exact sub_toNat_add_one_lt hj

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
  grind

/-- The index of a step of `forInRev`: `lo ≤ j - 1` when `lo < j`. -/
public theorem forInRev_le_pred {lo j : USize} (h : lo < j) : lo.toNat ≤ (j - 1).toNat := by
  grind

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
decreasing_by exact toNat_sub_one_lt_of_lt h

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
decreasing_by exact toNat_sub_one_lt_of_lt h

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

private theorem run_eq (m : InPlace n α) (a : Float32Array) (h : a.size = n) :
    m.run a h = ((m.fn ⟨a, h⟩).1, (m.fn ⟨a, h⟩).2.array) := rfl

/-- `run` leaves the size unchanged. -/
@[simp] public theorem size_run (m : InPlace n α) (a : Float32Array) (h : a.size = n) :
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

@[simp] public theorem run_pure (x : α) (a : Float32Array) (h : a.size = n) :
    (pure x : InPlace n α).run a h = (x, a) := by
  rfl

@[simp] public theorem run_bind (m : InPlace n α) (f : α → InPlace n β) (a : Float32Array)
    (h : a.size = n) :
    (m >>= f).run a h = (f (m.run a h).1).run (m.run a h).2 (size_run ..) := by
  rfl

@[simp] public theorem run_read (i : USize) (hi : i.toNat < n) (a : Float32Array)
    (h : a.size = n) : (read i hi).run a h = (a[i.toNat]'(by rw [h]; exact hi), a) := by
  simp only [run_eq, read]; simp

@[simp] public theorem run_readThen (i : USize) (hi : i.toNat < n) (k : Float32 → InPlace n α)
    (a : Float32Array) (h : a.size = n) :
    (readThen i hi k).run a h = (k (a[i.toNat]'(by rw [h]; exact hi))).run a h := by
  simp only [run_eq, readThen]; simp

@[simp] public theorem run_write (i : USize) (hi : i.toNat < n) (v : Float32) (a : Float32Array)
    (h : a.size = n) :
    (write i hi v : InPlace.{u} n PUnit).run a h = (⟨⟩, a.set i.toNat v (by rw [h]; exact hi)) := by
  simp only [run_eq, write]
  congr 1

@[simp] public theorem run_writeThen (i : USize) (hi : i.toNat < n) (v : Float32) (k : InPlace n α)
    (a : Float32Array) (h : a.size = n) :
    (writeThen i hi v k).run a h =
      k.run (a.set i.toNat v (by rw [h]; exact hi)) (by rw [Float32Array.size_set]; exact h) := by
  show ((write i hi v) >>= fun _ => k).run a h = _
  simp only [run_bind, run_write]

@[simp] public theorem ite_eq (c : Prop) [Decidable c] (t e : InPlace n α) :
    InPlace.ite c t e = if c then t else e := by
  unfold InPlace.ite; split <;> rfl

@[simp] public theorem dite_eq (c : Prop) [Decidable c] (t : c → InPlace n α)
    (e : ¬c → InPlace n α) : InPlace.dite c t e = if h : c then t h else e h := by
  unfold InPlace.dite; split <;> rfl

private theorem run_bind' (m : InPlace n α) (f : α → InPlace n β) (a : Float32Array)
    (h : a.size = n) :
    (m.bind f).run a h = (f (m.run a h).1).run (m.run a h).2 (size_run ..) := by
  rfl

private theorem run_pure' (x : α) (a : Float32Array) (h : a.size = n) :
    (InPlace.pure x : InPlace n α).run a h = (x, a) := by
  rfl

public instance : LawfulMonad (InPlace n) := LawfulMonad.mk'
  (id_map := fun m => InPlace.ext fun a h => by
    show (m.bind fun x => InPlace.pure (id x)).run a h = _
    rw [run_bind', run_pure']; rfl)
  (pure_bind := fun x f => InPlace.ext fun a h => by simp only [run_bind, run_pure])
  (bind_assoc := fun m f g => InPlace.ext fun a h => by simp only [run_bind])

/--
`InPlace.bind` is `>>=`, so that the lemmas about `>>=`, such as `run_bind`, apply to programs
written with it, as the `inplace` notation writes them.
-/
@[simp] public theorem bind_eq (m : InPlace n α) (f : α → InPlace n β) : m.bind f = m >>= f := by
  rfl

/-- `InPlace.pure` is `pure`, so that `run_pure` applies to programs written with it. -/
@[simp] public theorem pure_eq (x : α) : (InPlace.pure x : InPlace n α) = pure x := by
  rfl

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
decreasing_by exact sub_toNat_add_one_lt ‹j < hi›

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
decreasing_by exact toNat_sub_one_lt_of_lt ‹_›

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
decreasing_by exact sub_toNat_add_one_lt hj

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
decreasing_by exact sub_toNat_add_one_lt ‹_›

/--
Runs `forIn lo hi init body` on `a`, then `g` on the last accumulator and the new array, which the
loop calls itself: unlike `g` on the result of `run`, it builds no pair.
-/
@[inline]
public def runForInThen {γ : Type w} (a : Float32Array) (h : a.size = n) (lo hi : USize)
    (init : β) (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat → β → InPlace n β)
    (g : β → (a' : Float32Array) → a'.size = n → γ) : γ :=
  forUp.loopThen lo hi body lo (Nat.le_refl _) init
    ⟨a.ensureExclusive, by rw [ensureExclusive_eq]; exact h⟩
    fun b s => g b s.array s.size_array

public theorem runForInThen_eq {γ : Type w} (a : Float32Array) (h : a.size = n) (lo hi : USize)
    (init : β) (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat → β → InPlace n β)
    (g : β → (a' : Float32Array) → a'.size = n → γ) :
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
decreasing_by exact toNat_sub_one_lt_of_lt h

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
decreasing_by exact toNat_sub_one_lt_of_lt ‹_›

/-- `runForInThen` for `forInRev`. -/
@[inline]
public def runForInRevThen {γ : Type w} (a : Float32Array) (h : a.size = n) (lo hi : USize)
    (init : β) (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat → β → InPlace n β)
    (g : β → (a' : Float32Array) → a'.size = n → γ) : γ :=
  forDown.loopThen lo hi body hi (Nat.le_refl _) init
    ⟨a.ensureExclusive, by rw [ensureExclusive_eq]; exact h⟩
    fun b s => g b s.array s.size_array

public theorem runForInRevThen_eq {γ : Type w} (a : Float32Array) (h : a.size = n)
    (lo hi : USize) (init : β)
    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat → β → InPlace n β)
    (g : β → (a' : Float32Array) → a'.size = n → γ) :
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
decreasing_by exact sub_toNat_add_one_lt hj

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
decreasing_by exact sub_toNat_add_one_lt ‹_›

/-- `runForInThen` for `forIn2`, with the two accumulators handed to `g` apart. -/
@[inline]
public def runForIn2Then {β₁ : Type v} {β₂ : Type w} {γ : Type u} (a : Float32Array)
    (h : a.size = n) (lo hi : USize) (init₁ : β₁) (init₂ : β₂)
    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat → β₁ → β₂ →
      InPlace n (β₁ × β₂))
    (g : β₁ → β₂ → (a' : Float32Array) → a'.size = n → γ) : γ :=
  forUp2.loopThen lo hi body lo (Nat.le_refl _) init₁ init₂
    ⟨a.ensureExclusive, by rw [ensureExclusive_eq]; exact h⟩
    fun b₁ b₂ s => g b₁ b₂ s.array s.size_array

public theorem runForIn2Then_eq {β₁ : Type v} {β₂ : Type w} {γ : Type u} (a : Float32Array)
    (h : a.size = n) (lo hi : USize) (init₁ : β₁) (init₂ : β₂)
    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat → β₁ → β₂ →
      InPlace n (β₁ × β₂))
    (g : β₁ → β₂ → (a' : Float32Array) → a'.size = n → γ) :
    runForIn2Then a h lo hi init₁ init₂ body g =
      g ((forIn2 lo hi init₁ init₂ body).run a h).1.1
        ((forIn2 lo hi init₁ init₂ body).run a h).1.2
        ((forIn2 lo hi init₁ init₂ body).run a h).2 (size_run ..) := by
  unfold runForIn2Then
  rw [forUp2_loopThen_eq]
  rfl

/-! ## Loops that run straight into the rest of a program -/

/--
`forIn lo hi init body >>= k`, with the loop calling `k` itself on its last accumulator: the loop
returns no pair, so a scalar accumulator stays unboxed into `k`. It is specified by `forInBind_eq`.
-/
@[inline]
public def forInBind {γ : Type u} (lo hi : USize) (init : β)
    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat → β → InPlace n β)
    (k : β → InPlace n γ) : InPlace n γ :=
  ⟨fun s => forUp.loopThen lo hi body lo (Nat.le_refl _) init s fun b s => (k b).fn s⟩

public theorem forInBind_eq {γ : Type u} (lo hi : USize) (init : β)
    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat → β → InPlace n β)
    (k : β → InPlace n γ) :
    forInBind lo hi init body k = forIn lo hi init body >>= k := by
  apply fn_inj; funext s
  show forUp.loopThen lo hi body lo _ init s _ = _
  rw [forUp_loopThen_eq]; rfl

/-- `forInBind` for `forIn2`, with the two last accumulators handed to `k` apart. -/
@[inline]
public def forIn2Bind {β₁ : Type v} {β₂ : Type w} {γ : Type u} (lo hi : USize) (init₁ : β₁)
    (init₂ : β₂)
    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat → β₁ → β₂ →
      InPlace n (β₁ × β₂))
    (k : β₁ → β₂ → InPlace n γ) : InPlace n γ :=
  ⟨fun s => forUp2.loopThen lo hi body lo (Nat.le_refl _) init₁ init₂ s fun b₁ b₂ s =>
    (k b₁ b₂).fn s⟩

public theorem forIn2Bind_eq {β₁ : Type v} {β₂ : Type w} {γ : Type (max v w)} (lo hi : USize)
    (init₁ : β₁) (init₂ : β₂)
    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat → β₁ → β₂ →
      InPlace n (β₁ × β₂))
    (k : β₁ → β₂ → InPlace n γ) :
    forIn2Bind lo hi init₁ init₂ body k =
      forIn2 lo hi init₁ init₂ body >>= fun b => k b.1 b.2 := by
  apply fn_inj; funext s
  show forUp2.loopThen lo hi body lo _ init₁ init₂ s _ = _
  rw [forUp2_loopThen_eq]; rfl

/-- `forInBind` for `forInRev`. -/
@[inline]
public def forInRevBind {γ : Type u} (lo hi : USize) (init : β)
    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat → β → InPlace n β)
    (k : β → InPlace n γ) : InPlace n γ :=
  ⟨fun s => forDown.loopThen lo hi body hi (Nat.le_refl _) init s fun b s => (k b).fn s⟩

public theorem forInRevBind_eq {γ : Type u} (lo hi : USize) (init : β)
    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat → β → InPlace n β)
    (k : β → InPlace n γ) :
    forInRevBind lo hi init body k = forInRev lo hi init body >>= k := by
  apply fn_inj; funext s
  show forDown.loopThen lo hi body hi _ init s _ = _
  rw [forDown_loopThen_eq]; rfl

/-- `forDown2.loop`, handing the two last accumulators and the state to `k`. -/
@[specialize]
private def forDown2.loopThen {β₁ : Type v} {β₂ : Type w} {γ : Type u} (lo hi : USize)
    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat → β₁ → β₂ →
      InPlace n (β₁ × β₂))
    (j : USize) (hj : j.toNat ≤ hi.toNat) (b₁ : β₁) (b₂ : β₂) (s : State n)
    (k : β₁ → β₂ → State n → γ) : γ :=
  if h : lo < j then
    have hj' := forInRev_pred_lt hj h
    match (body (j - 1) (forInRev_le_pred h) hj' b₁ b₂).fn s with
    | ((b₁, b₂), s) => forDown2.loopThen lo hi body (j - 1) (Nat.le_of_lt hj') b₁ b₂ s k
  else
    k b₁ b₂ s
termination_by j.toNat
decreasing_by exact toNat_sub_one_lt_of_lt h

private theorem forDown2_loopThen_eq {β₁ : Type v} {β₂ : Type w} {γ : Type u} (lo hi : USize)
    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat → β₁ → β₂ →
      InPlace n (β₁ × β₂))
    (j : USize) (hj : j.toNat ≤ hi.toNat) (b₁ : β₁) (b₂ : β₂) (s : State n)
    (k : β₁ → β₂ → State n → γ) :
    forDown2.loopThen lo hi body j hj b₁ b₂ s k =
      k (forDown2.loop lo hi body j hj b₁ b₂ s).1.1 (forDown2.loop lo hi body j hj b₁ b₂ s).1.2
        (forDown2.loop lo hi body j hj b₁ b₂ s).2 := by
  rw [forDown2.loopThen, forDown2.loop]
  split
  · exact forDown2_loopThen_eq lo hi body (j - 1) _ _ _ _ k
  · rfl
termination_by j.toNat
decreasing_by exact toNat_sub_one_lt_of_lt ‹_›

/-- `forIn2Bind` for `forInRev2`. -/
@[inline]
public def forInRev2Bind {β₁ : Type v} {β₂ : Type w} {γ : Type u} (lo hi : USize) (init₁ : β₁)
    (init₂ : β₂)
    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat → β₁ → β₂ →
      InPlace n (β₁ × β₂))
    (k : β₁ → β₂ → InPlace n γ) : InPlace n γ :=
  ⟨fun s => forDown2.loopThen lo hi body hi (Nat.le_refl _) init₁ init₂ s fun b₁ b₂ s =>
    (k b₁ b₂).fn s⟩

public theorem forInRev2Bind_eq {β₁ : Type v} {β₂ : Type w} {γ : Type (max v w)} (lo hi : USize)
    (init₁ : β₁) (init₂ : β₂)
    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat → β₁ → β₂ →
      InPlace n (β₁ × β₂))
    (k : β₁ → β₂ → InPlace n γ) :
    forInRev2Bind lo hi init₁ init₂ body k =
      forInRev2 lo hi init₁ init₂ body >>= fun b => k b.1 b.2 := by
  apply fn_inj; funext s
  show forDown2.loopThen lo hi body hi _ init₁ init₂ s _ = _
  rw [forDown2_loopThen_eq]; rfl

/-! ## Tail programs -/

/--
A tail program on arrays of size `n`, which returns a `γ`: an in-place program that ends by handing
the new array to a continuation, instead of returning it with a result. The continuation runs where
the program ends, inside its last loop if it ends with one, so the program's last values reach it
unboxed, and no result pair is built. A tail program is built from in-place programs with
`Tail.bind`, `Tail.readThen`, `Tail.ite`, `Tail.dite`, the loops `Tail.forInBind`,
`Tail.forIn2Bind`, `Tail.forInRevBind` and `Tail.forInRev2Bind`, and ends with `Tail.done x k`.
It runs with `Tail.run` or `runInPlaceThen`, and `inplace a do … then k` writes one.
-/
public structure Tail (n : Nat) (γ : Type u) where
  private mk ::
  private fn : State n → γ

namespace Tail

variable {γ : Type w}

/-- Ends the program with the result `x`: hands `x`, the array and its size to `k`. -/
@[inline]
public def done (x : α) (k : α → (a : Float32Array) → a.size = n → γ) : Tail n γ :=
  ⟨fun s => k x s.array s.size_array⟩

/-- Runs the in-place program `m`, then the tail program `k` on its result. -/
@[inline]
public protected def bind (m : InPlace n α) (k : α → Tail n γ) : Tail n γ :=
  ⟨fun s => match m.fn s with | (x, s) => (k x).fn s⟩

/-- `read i h` followed by `k` on the element. -/
@[inline]
public def readThen (i : USize) (h : i.toNat < n) (k : Float32 → Tail n γ) : Tail n γ :=
  ⟨fun s => (k (s.array.uget i (by rw [s.size_array]; exact h))).fn s⟩

/-- `write i h v` followed by `k`. -/
@[inline]
public def writeThen (i : USize) (h : i.toNat < n) (v : Float32) (k : Tail n γ) : Tail n γ :=
  Tail.bind (write.{0} i h v) fun _ => k

/-- Runs `t` if `c` holds and `e` otherwise, as a branch inside one program, like `InPlace.ite`. -/
@[inline]
public protected def ite (c : Prop) [Decidable c] (t e : Tail n γ) : Tail n γ :=
  ⟨fun s => if c then t.fn s else e.fn s⟩

/-- `Tail.ite` where each branch takes the proof of its condition. -/
@[inline]
public protected def dite (c : Prop) [Decidable c] (t : c → Tail n γ) (e : ¬c → Tail n γ) :
    Tail n γ :=
  ⟨fun s => if h : c then (t h).fn s else (e h).fn s⟩

/--
`forIn lo hi init body` followed by the tail program `k` on its last accumulator, which the loop
calls itself. It is specified by `forInBind_eq`.
-/
@[inline]
public def forInBind (lo hi : USize) (init : β)
    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat → β → InPlace n β)
    (k : β → Tail n γ) : Tail n γ :=
  ⟨fun s => forUp.loopThen lo hi body lo (Nat.le_refl _) init s fun b s => (k b).fn s⟩

/-- `Tail.forInBind` for `forIn2`, with the two last accumulators handed to `k` apart. -/
@[inline]
public def forIn2Bind {β₁ : Type v} {β₂ : Type w'} (lo hi : USize) (init₁ : β₁) (init₂ : β₂)
    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat → β₁ → β₂ →
      InPlace n (β₁ × β₂))
    (k : β₁ → β₂ → Tail n γ) : Tail n γ :=
  ⟨fun s => forUp2.loopThen lo hi body lo (Nat.le_refl _) init₁ init₂ s fun b₁ b₂ s =>
    (k b₁ b₂).fn s⟩

/-- `Tail.forInBind` for `forInRev`. -/
@[inline]
public def forInRevBind (lo hi : USize) (init : β)
    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat → β → InPlace n β)
    (k : β → Tail n γ) : Tail n γ :=
  ⟨fun s => forDown.loopThen lo hi body hi (Nat.le_refl _) init s fun b s => (k b).fn s⟩

/-- `Tail.forInBind` for `forInRev2`, with the two last accumulators handed to `k` apart. -/
@[inline]
public def forInRev2Bind {β₁ : Type v} {β₂ : Type w'} (lo hi : USize) (init₁ : β₁)
    (init₂ : β₂)
    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat → β₁ → β₂ →
      InPlace n (β₁ × β₂))
    (k : β₁ → β₂ → Tail n γ) : Tail n γ :=
  ⟨fun s => forDown2.loopThen lo hi body hi (Nat.le_refl _) init₁ init₂ s fun b₁ b₂ s =>
    (k b₁ b₂).fn s⟩

/-! ### Loops in continuation-passing style -/

/-- The loop of `Tail.forInFrom`: `next` runs the step at `j + 1`, and the loop ends with `k`. -/
@[specialize]
private def forUpK.loop {β : Type v}
    (lo hi : USize)
    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat →
      (β → Tail n γ) → β → Tail n γ)
    (k : β → Tail n γ) (j : USize) (hlo : lo.toNat ≤ j.toNat)
    (b : β) (s : State n) : γ :=
  if hj : j < hi then
    (body j hlo hj
      (fun b => ⟨fun s =>
        forUpK.loop lo hi body k (j + 1) (forIn_le_succ hlo hj) b s⟩)
      b).fn s
  else
    (k b).fn s
termination_by hi.toNat - j.toNat
decreasing_by exact sub_toNat_add_one_lt hj

/-- `Tail.forIn` from `j₀` instead of `lo`. It is specified by `Tail.forInFrom_eq`. -/
@[inline]
public def forInFrom {β : Type v}
    (lo hi j₀ : USize) (h : lo.toNat ≤ j₀.toNat) (init : β)
    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat →
      (β → Tail n γ) → β → Tail n γ)
    (k : β → Tail n γ) : Tail n γ :=
  ⟨forUpK.loop lo hi body k j₀ h init⟩

/--
A loop in continuation-passing style, for each `j` from `lo` up to `hi - 1`, followed by the rest
`k` of the program. The body gets `j`, both its bounds, the continuation `next` and the current
variables, and ends by calling `next` on the next variables, which runs the next step, or `k` after
the last one. So the variables are arguments of the loop, and a scalar stays unboxed, and a nested
loop, whose `k` calls the outer `next`, allocates nothing either. A body that doesn't call `next`
leaves the loop early. `Tail.forIn2`, `Tail.forIn3` and `Tail.forIn4` take two, three and four
variables, each its own argument.
-/
@[inline, expose]
public def forIn {β : Type v}
    (lo hi : USize) (init : β)
    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat →
      (β → Tail n γ) → β → Tail n γ)
    (k : β → Tail n γ) : Tail n γ :=
  forInFrom lo hi lo (Nat.le_refl _) init body k

/-- The loop of `Tail.forInRevFrom`: `next` runs the step at `j - 2`, for the index `j - 1`. -/
@[specialize]
private def forDownK.loop {β : Type v}
    (lo hi : USize)
    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat →
      (β → Tail n γ) → β → Tail n γ)
    (k : β → Tail n γ) (j : USize) (hj : j.toNat ≤ hi.toNat)
    (b : β) (s : State n) : γ :=
  if h : lo < j then
    have hj' : (j - 1).toNat < hi.toNat := forInRev_pred_lt hj h
    (body (j - 1) (forInRev_le_pred h) hj'
      (fun b => ⟨fun s =>
        forDownK.loop lo hi body k (j - 1) (Nat.le_of_lt hj') b s⟩)
      b).fn s
  else
    (k b).fn s
termination_by j.toNat
decreasing_by exact toNat_sub_one_lt_of_lt h

/--
`Tail.forInRev` from `j₀ - 1` down to `lo` instead of from `hi - 1`. It is specified by
`Tail.forInRevFrom_eq`.
-/
@[inline]
public def forInRevFrom {β : Type v}
    (lo hi j₀ : USize) (h : j₀.toNat ≤ hi.toNat) (init : β)
    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat →
      (β → Tail n γ) → β → Tail n γ)
    (k : β → Tail n γ) : Tail n γ :=
  ⟨forDownK.loop lo hi body k j₀ h init⟩

/-- `Tail.forIn` from `hi - 1` down to `lo`. -/
@[inline, expose]
public def forInRev {β : Type v}
    (lo hi : USize) (init : β)
    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat →
      (β → Tail n γ) → β → Tail n γ)
    (k : β → Tail n γ) : Tail n γ :=
  forInRevFrom lo hi hi (Nat.le_refl _) init body k

/-- The loop of `Tail.forIn2From`: `next` runs the step at `j + 1`, and the loop ends with `k`. -/
@[specialize]
private def forUpK2.loop {β₁ : Type v₁} {β₂ : Type v₂}
    (lo hi : USize)
    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat →
      (β₁ → β₂ → Tail n γ) → β₁ → β₂ → Tail n γ)
    (k : β₁ → β₂ → Tail n γ) (j : USize) (hlo : lo.toNat ≤ j.toNat)
    (b₁ : β₁) (b₂ : β₂) (s : State n) : γ :=
  if hj : j < hi then
    (body j hlo hj
      (fun b₁ b₂ => ⟨fun s =>
        forUpK2.loop lo hi body k (j + 1) (forIn_le_succ hlo hj) b₁ b₂ s⟩)
      b₁ b₂).fn s
  else
    (k b₁ b₂).fn s
termination_by hi.toNat - j.toNat
decreasing_by exact sub_toNat_add_one_lt hj

/-- `Tail.forIn2` from `j₀` instead of `lo`. It is specified by `Tail.forIn2From_eq`. -/
@[inline]
public def forIn2From {β₁ : Type v₁} {β₂ : Type v₂}
    (lo hi j₀ : USize) (h : lo.toNat ≤ j₀.toNat) (init₁ : β₁) (init₂ : β₂)
    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat →
      (β₁ → β₂ → Tail n γ) → β₁ → β₂ → Tail n γ)
    (k : β₁ → β₂ → Tail n γ) : Tail n γ :=
  ⟨forUpK2.loop lo hi body k j₀ h init₁ init₂⟩

/-- `Tail.forIn` with two variables, which the loop keeps as 2 arguments. -/
@[inline, expose]
public def forIn2 {β₁ : Type v₁} {β₂ : Type v₂}
    (lo hi : USize) (init₁ : β₁) (init₂ : β₂)
    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat →
      (β₁ → β₂ → Tail n γ) → β₁ → β₂ → Tail n γ)
    (k : β₁ → β₂ → Tail n γ) : Tail n γ :=
  forIn2From lo hi lo (Nat.le_refl _) init₁ init₂ body k

/-- The loop of `Tail.forInRev2From`: `next` runs the step at `j - 2`, for the index `j - 1`. -/
@[specialize]
private def forDownK2.loop {β₁ : Type v₁} {β₂ : Type v₂}
    (lo hi : USize)
    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat →
      (β₁ → β₂ → Tail n γ) → β₁ → β₂ → Tail n γ)
    (k : β₁ → β₂ → Tail n γ) (j : USize) (hj : j.toNat ≤ hi.toNat)
    (b₁ : β₁) (b₂ : β₂) (s : State n) : γ :=
  if h : lo < j then
    have hj' : (j - 1).toNat < hi.toNat := forInRev_pred_lt hj h
    (body (j - 1) (forInRev_le_pred h) hj'
      (fun b₁ b₂ => ⟨fun s =>
        forDownK2.loop lo hi body k (j - 1) (Nat.le_of_lt hj') b₁ b₂ s⟩)
      b₁ b₂).fn s
  else
    (k b₁ b₂).fn s
termination_by j.toNat
decreasing_by exact toNat_sub_one_lt_of_lt h

/--
`Tail.forInRev2` from `j₀ - 1` down to `lo` instead of from `hi - 1`. It is specified by
`Tail.forInRev2From_eq`.
-/
@[inline]
public def forInRev2From {β₁ : Type v₁} {β₂ : Type v₂}
    (lo hi j₀ : USize) (h : j₀.toNat ≤ hi.toNat) (init₁ : β₁) (init₂ : β₂)
    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat →
      (β₁ → β₂ → Tail n γ) → β₁ → β₂ → Tail n γ)
    (k : β₁ → β₂ → Tail n γ) : Tail n γ :=
  ⟨forDownK2.loop lo hi body k j₀ h init₁ init₂⟩

/-- `Tail.forIn2` from `hi - 1` down to `lo`. -/
@[inline, expose]
public def forInRev2 {β₁ : Type v₁} {β₂ : Type v₂}
    (lo hi : USize) (init₁ : β₁) (init₂ : β₂)
    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat →
      (β₁ → β₂ → Tail n γ) → β₁ → β₂ → Tail n γ)
    (k : β₁ → β₂ → Tail n γ) : Tail n γ :=
  forInRev2From lo hi hi (Nat.le_refl _) init₁ init₂ body k

/-- The loop of `Tail.forIn3From`: `next` runs the step at `j + 1`, and the loop ends with `k`. -/
@[specialize]
private def forUpK3.loop {β₁ : Type v₁} {β₂ : Type v₂} {β₃ : Type v₃}
    (lo hi : USize)
    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat →
      (β₁ → β₂ → β₃ → Tail n γ) → β₁ → β₂ → β₃ → Tail n γ)
    (k : β₁ → β₂ → β₃ → Tail n γ) (j : USize) (hlo : lo.toNat ≤ j.toNat)
    (b₁ : β₁) (b₂ : β₂) (b₃ : β₃) (s : State n) : γ :=
  if hj : j < hi then
    (body j hlo hj
      (fun b₁ b₂ b₃ => ⟨fun s =>
        forUpK3.loop lo hi body k (j + 1) (forIn_le_succ hlo hj) b₁ b₂ b₃ s⟩)
      b₁ b₂ b₃).fn s
  else
    (k b₁ b₂ b₃).fn s
termination_by hi.toNat - j.toNat
decreasing_by exact sub_toNat_add_one_lt hj

/-- `Tail.forIn3` from `j₀` instead of `lo`. It is specified by `Tail.forIn3From_eq`. -/
@[inline]
public def forIn3From {β₁ : Type v₁} {β₂ : Type v₂} {β₃ : Type v₃}
    (lo hi j₀ : USize) (h : lo.toNat ≤ j₀.toNat) (init₁ : β₁) (init₂ : β₂) (init₃ : β₃)
    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat →
      (β₁ → β₂ → β₃ → Tail n γ) → β₁ → β₂ → β₃ → Tail n γ)
    (k : β₁ → β₂ → β₃ → Tail n γ) : Tail n γ :=
  ⟨forUpK3.loop lo hi body k j₀ h init₁ init₂ init₃⟩

/-- `Tail.forIn` with three variables, which the loop keeps as 3 arguments. -/
@[inline, expose]
public def forIn3 {β₁ : Type v₁} {β₂ : Type v₂} {β₃ : Type v₃}
    (lo hi : USize) (init₁ : β₁) (init₂ : β₂) (init₃ : β₃)
    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat →
      (β₁ → β₂ → β₃ → Tail n γ) → β₁ → β₂ → β₃ → Tail n γ)
    (k : β₁ → β₂ → β₃ → Tail n γ) : Tail n γ :=
  forIn3From lo hi lo (Nat.le_refl _) init₁ init₂ init₃ body k

/-- The loop of `Tail.forInRev3From`: `next` runs the step at `j - 2`, for the index `j - 1`. -/
@[specialize]
private def forDownK3.loop {β₁ : Type v₁} {β₂ : Type v₂} {β₃ : Type v₃}
    (lo hi : USize)
    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat →
      (β₁ → β₂ → β₃ → Tail n γ) → β₁ → β₂ → β₃ → Tail n γ)
    (k : β₁ → β₂ → β₃ → Tail n γ) (j : USize) (hj : j.toNat ≤ hi.toNat)
    (b₁ : β₁) (b₂ : β₂) (b₃ : β₃) (s : State n) : γ :=
  if h : lo < j then
    have hj' : (j - 1).toNat < hi.toNat := forInRev_pred_lt hj h
    (body (j - 1) (forInRev_le_pred h) hj'
      (fun b₁ b₂ b₃ => ⟨fun s =>
        forDownK3.loop lo hi body k (j - 1) (Nat.le_of_lt hj') b₁ b₂ b₃ s⟩)
      b₁ b₂ b₃).fn s
  else
    (k b₁ b₂ b₃).fn s
termination_by j.toNat
decreasing_by exact toNat_sub_one_lt_of_lt h

/--
`Tail.forInRev3` from `j₀ - 1` down to `lo` instead of from `hi - 1`. It is specified by
`Tail.forInRev3From_eq`.
-/
@[inline]
public def forInRev3From {β₁ : Type v₁} {β₂ : Type v₂} {β₃ : Type v₃}
    (lo hi j₀ : USize) (h : j₀.toNat ≤ hi.toNat) (init₁ : β₁) (init₂ : β₂) (init₃ : β₃)
    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat →
      (β₁ → β₂ → β₃ → Tail n γ) → β₁ → β₂ → β₃ → Tail n γ)
    (k : β₁ → β₂ → β₃ → Tail n γ) : Tail n γ :=
  ⟨forDownK3.loop lo hi body k j₀ h init₁ init₂ init₃⟩

/-- `Tail.forIn3` from `hi - 1` down to `lo`. -/
@[inline, expose]
public def forInRev3 {β₁ : Type v₁} {β₂ : Type v₂} {β₃ : Type v₃}
    (lo hi : USize) (init₁ : β₁) (init₂ : β₂) (init₃ : β₃)
    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat →
      (β₁ → β₂ → β₃ → Tail n γ) → β₁ → β₂ → β₃ → Tail n γ)
    (k : β₁ → β₂ → β₃ → Tail n γ) : Tail n γ :=
  forInRev3From lo hi hi (Nat.le_refl _) init₁ init₂ init₃ body k

/-- The loop of `Tail.forIn4From`: `next` runs the step at `j + 1`, and the loop ends with `k`. -/
@[specialize]
private def forUpK4.loop {β₁ : Type v₁} {β₂ : Type v₂} {β₃ : Type v₃} {β₄ : Type v₄}
    (lo hi : USize)
    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat →
      (β₁ → β₂ → β₃ → β₄ → Tail n γ) → β₁ → β₂ → β₃ → β₄ → Tail n γ)
    (k : β₁ → β₂ → β₃ → β₄ → Tail n γ) (j : USize) (hlo : lo.toNat ≤ j.toNat)
    (b₁ : β₁) (b₂ : β₂) (b₃ : β₃) (b₄ : β₄) (s : State n) : γ :=
  if hj : j < hi then
    (body j hlo hj
      (fun b₁ b₂ b₃ b₄ => ⟨fun s =>
        forUpK4.loop lo hi body k (j + 1) (forIn_le_succ hlo hj) b₁ b₂ b₃ b₄ s⟩)
      b₁ b₂ b₃ b₄).fn s
  else
    (k b₁ b₂ b₃ b₄).fn s
termination_by hi.toNat - j.toNat
decreasing_by exact sub_toNat_add_one_lt hj

/-- `Tail.forIn4` from `j₀` instead of `lo`. It is specified by `Tail.forIn4From_eq`. -/
@[inline]
public def forIn4From {β₁ : Type v₁} {β₂ : Type v₂} {β₃ : Type v₃} {β₄ : Type v₄}
    (lo hi j₀ : USize) (h : lo.toNat ≤ j₀.toNat) (init₁ : β₁) (init₂ : β₂) (init₃ : β₃) (init₄ : β₄)
    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat →
      (β₁ → β₂ → β₃ → β₄ → Tail n γ) → β₁ → β₂ → β₃ → β₄ → Tail n γ)
    (k : β₁ → β₂ → β₃ → β₄ → Tail n γ) : Tail n γ :=
  ⟨forUpK4.loop lo hi body k j₀ h init₁ init₂ init₃ init₄⟩

/-- `Tail.forIn` with four variables, which the loop keeps as 4 arguments. -/
@[inline, expose]
public def forIn4 {β₁ : Type v₁} {β₂ : Type v₂} {β₃ : Type v₃} {β₄ : Type v₄}
    (lo hi : USize) (init₁ : β₁) (init₂ : β₂) (init₃ : β₃) (init₄ : β₄)
    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat →
      (β₁ → β₂ → β₃ → β₄ → Tail n γ) → β₁ → β₂ → β₃ → β₄ → Tail n γ)
    (k : β₁ → β₂ → β₃ → β₄ → Tail n γ) : Tail n γ :=
  forIn4From lo hi lo (Nat.le_refl _) init₁ init₂ init₃ init₄ body k

/-- The loop of `Tail.forInRev4From`: `next` runs the step at `j - 2`, for the index `j - 1`. -/
@[specialize]
private def forDownK4.loop {β₁ : Type v₁} {β₂ : Type v₂} {β₃ : Type v₃} {β₄ : Type v₄}
    (lo hi : USize)
    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat →
      (β₁ → β₂ → β₃ → β₄ → Tail n γ) → β₁ → β₂ → β₃ → β₄ → Tail n γ)
    (k : β₁ → β₂ → β₃ → β₄ → Tail n γ) (j : USize) (hj : j.toNat ≤ hi.toNat)
    (b₁ : β₁) (b₂ : β₂) (b₃ : β₃) (b₄ : β₄) (s : State n) : γ :=
  if h : lo < j then
    have hj' : (j - 1).toNat < hi.toNat := forInRev_pred_lt hj h
    (body (j - 1) (forInRev_le_pred h) hj'
      (fun b₁ b₂ b₃ b₄ => ⟨fun s =>
        forDownK4.loop lo hi body k (j - 1) (Nat.le_of_lt hj') b₁ b₂ b₃ b₄ s⟩)
      b₁ b₂ b₃ b₄).fn s
  else
    (k b₁ b₂ b₃ b₄).fn s
termination_by j.toNat
decreasing_by exact toNat_sub_one_lt_of_lt h

/--
`Tail.forInRev4` from `j₀ - 1` down to `lo` instead of from `hi - 1`. It is specified by
`Tail.forInRev4From_eq`.
-/
@[inline]
public def forInRev4From {β₁ : Type v₁} {β₂ : Type v₂} {β₃ : Type v₃} {β₄ : Type v₄}
    (lo hi j₀ : USize) (h : j₀.toNat ≤ hi.toNat) (init₁ : β₁) (init₂ : β₂) (init₃ : β₃) (init₄ : β₄)
    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat →
      (β₁ → β₂ → β₃ → β₄ → Tail n γ) → β₁ → β₂ → β₃ → β₄ → Tail n γ)
    (k : β₁ → β₂ → β₃ → β₄ → Tail n γ) : Tail n γ :=
  ⟨forDownK4.loop lo hi body k j₀ h init₁ init₂ init₃ init₄⟩

/-- `Tail.forIn4` from `hi - 1` down to `lo`. -/
@[inline, expose]
public def forInRev4 {β₁ : Type v₁} {β₂ : Type v₂} {β₃ : Type v₃} {β₄ : Type v₄}
    (lo hi : USize) (init₁ : β₁) (init₂ : β₂) (init₃ : β₃) (init₄ : β₄)
    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat →
      (β₁ → β₂ → β₃ → β₄ → Tail n γ) → β₁ → β₂ → β₃ → β₄ → Tail n γ)
    (k : β₁ → β₂ → β₃ → β₄ → Tail n γ) : Tail n γ :=
  forInRev4From lo hi hi (Nat.le_refl _) init₁ init₂ init₃ init₄ body k

/--
Runs the tail program `t` on the array `a`, and returns what its continuation returns. The array
is made exclusive first, so it is copied once if it is shared, and updated in place otherwise.
-/
@[inline]
public def run (t : Tail n γ) (a : Float32Array) (h : a.size = n) : γ :=
  t.fn ⟨a.ensureExclusive, by rw [ensureExclusive_eq]; exact h⟩

private theorem run_eq (t : Tail n γ) (a : Float32Array) (h : a.size = n) :
    t.run a h = t.fn ⟨a, h⟩ := by
  simp only [run, ensureExclusive_eq]

private theorem fn_inj {t t' : Tail n γ} (h : t.fn = t'.fn) : t = t' := by
  obtain ⟨f⟩ := t; obtain ⟨f'⟩ := t'
  cases h; rfl

/-- Two tail programs are equal when they run the same on every array. -/
@[ext] public theorem ext {t t' : Tail n γ}
    (h : ∀ a (h : a.size = n), t.run a h = t'.run a h) : t = t' := by
  apply fn_inj; funext s
  have := h s.array s.size_array
  rw [run_eq, run_eq] at this
  exact this

@[simp] public theorem run_done (x : α) (k : α → (a : Float32Array) → a.size = n → γ)
    (a : Float32Array) (h : a.size = n) : (done x k).run a h = k x a h := by
  rw [run_eq]; rfl

@[simp] public theorem run_bind (m : InPlace n α) (k : α → Tail n γ) (a : Float32Array)
    (h : a.size = n) :
    (Tail.bind m k).run a h = (k (m.run a h).1).run (m.run a h).2 (size_run ..) := by
  rfl

@[simp] public theorem run_readThen (i : USize) (hi : i.toNat < n) (k : Float32 → Tail n γ)
    (a : Float32Array) (h : a.size = n) :
    (readThen i hi k).run a h = (k (a[i.toNat]'(by rw [h]; exact hi))).run a h := by
  simp only [run_eq, readThen]; simp

@[simp] public theorem run_writeThen (i : USize) (hi : i.toNat < n) (v : Float32) (k : Tail n γ)
    (a : Float32Array) (h : a.size = n) :
    (writeThen i hi v k).run a h =
      k.run (a.set i.toNat v (by rw [h]; exact hi)) (by rw [Float32Array.size_set]; exact h) := by
  show (Tail.bind (write.{0} i hi v) fun _ => k).run a h = _
  simp only [run_bind, InPlace.run_write]

@[simp] public theorem ite_eq (c : Prop) [Decidable c] (t e : Tail n γ) :
    Tail.ite c t e = if c then t else e := by
  unfold Tail.ite; split <;> rfl

@[simp] public theorem dite_eq (c : Prop) [Decidable c] (t : c → Tail n γ)
    (e : ¬c → Tail n γ) : Tail.dite c t e = if h : c then t h else e h := by
  unfold Tail.dite; split <;> rfl

@[simp] public theorem forInBind_eq (lo hi : USize) (init : β)
    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat → β → InPlace n β)
    (k : β → Tail n γ) :
    forInBind lo hi init body k = Tail.bind (InPlace.forIn lo hi init body) k := by
  apply fn_inj; funext s
  show forUp.loopThen lo hi body lo _ init s _ = _
  rw [forUp_loopThen_eq]; rfl

@[simp] public theorem forIn2Bind_eq {β₁ : Type v} {β₂ : Type w'} (lo hi : USize) (init₁ : β₁)
    (init₂ : β₂)
    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat → β₁ → β₂ →
      InPlace n (β₁ × β₂))
    (k : β₁ → β₂ → Tail n γ) :
    forIn2Bind lo hi init₁ init₂ body k =
      Tail.bind (InPlace.forIn2 lo hi init₁ init₂ body) fun b => k b.1 b.2 := by
  apply fn_inj; funext s
  show forUp2.loopThen lo hi body lo _ init₁ init₂ s _ = _
  rw [forUp2_loopThen_eq]; rfl

@[simp] public theorem forInRevBind_eq (lo hi : USize) (init : β)
    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat → β → InPlace n β)
    (k : β → Tail n γ) :
    forInRevBind lo hi init body k = Tail.bind (InPlace.forInRev lo hi init body) k := by
  apply fn_inj; funext s
  show forDown.loopThen lo hi body hi _ init s _ = _
  rw [forDown_loopThen_eq]; rfl

@[simp] public theorem forInRev2Bind_eq {β₁ : Type v} {β₂ : Type w'} (lo hi : USize)
    (init₁ : β₁) (init₂ : β₂)
    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat → β₁ → β₂ →
      InPlace n (β₁ × β₂))
    (k : β₁ → β₂ → Tail n γ) :
    forInRev2Bind lo hi init₁ init₂ body k =
      Tail.bind (InPlace.forInRev2 lo hi init₁ init₂ body) fun b => k b.1 b.2 := by
  apply fn_inj; funext s
  show forDown2.loopThen lo hi body hi _ init₁ init₂ s _ = _
  rw [forDown2_loopThen_eq]; rfl

/-! ### Loops in continuation-passing style -/

/-- One step of `Tail.forInFrom`. -/
public theorem forInFrom_eq {β : Type v}
    (lo hi j : USize) (hlo : lo.toNat ≤ j.toNat) (init : β)
    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat →
      (β → Tail n γ) → β → Tail n γ)
    (k : β → Tail n γ) :
    forInFrom lo hi j hlo init body k =
      if hj : j < hi then
        body j hlo hj
          (fun b =>
            forInFrom lo hi (j + 1) (forIn_le_succ hlo hj) b body k)
          init
      else k init := by
  apply fn_inj; funext s
  show forUpK.loop lo hi body k j hlo init s = _
  rw [forUpK.loop]
  by_cases hj : j < hi
  · simp only [hj, ↓reduceDIte]; rfl
  · simp only [hj, ↓reduceDIte]

@[simp] public theorem forIn_eq {β : Type v}
    (lo hi : USize) (init : β)
    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat →
      (β → Tail n γ) → β → Tail n γ)
    (k : β → Tail n γ) :
    forIn lo hi init body k =
      forInFrom lo hi lo (Nat.le_refl _) init body k := by
  rfl

/-- One step of `Tail.forInRevFrom`. -/
public theorem forInRevFrom_eq {β : Type v}
    (lo hi j : USize) (hj : j.toNat ≤ hi.toNat) (init : β)
    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat →
      (β → Tail n γ) → β → Tail n γ)
    (k : β → Tail n γ) :
    forInRevFrom lo hi j hj init body k =
      if h : lo < j then
        body (j - 1) (forInRev_le_pred h) (forInRev_pred_lt hj h)
          (fun b =>
            forInRevFrom lo hi (j - 1) (Nat.le_of_lt (forInRev_pred_lt hj h)) b body k)
          init
      else k init := by
  apply fn_inj; funext s
  show forDownK.loop lo hi body k j hj init s = _
  rw [forDownK.loop]
  by_cases h : lo < j
  · simp only [h, ↓reduceDIte]; rfl
  · simp only [h, ↓reduceDIte]

@[simp] public theorem forInRev_eq {β : Type v}
    (lo hi : USize) (init : β)
    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat →
      (β → Tail n γ) → β → Tail n γ)
    (k : β → Tail n γ) :
    forInRev lo hi init body k =
      forInRevFrom lo hi hi (Nat.le_refl _) init body k := by
  rfl

/-- One step of `Tail.forIn2From`. -/
public theorem forIn2From_eq {β₁ : Type v₁} {β₂ : Type v₂}
    (lo hi j : USize) (hlo : lo.toNat ≤ j.toNat) (init₁ : β₁) (init₂ : β₂)
    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat →
      (β₁ → β₂ → Tail n γ) → β₁ → β₂ → Tail n γ)
    (k : β₁ → β₂ → Tail n γ) :
    forIn2From lo hi j hlo init₁ init₂ body k =
      if hj : j < hi then
        body j hlo hj
          (fun b₁ b₂ =>
            forIn2From lo hi (j + 1) (forIn_le_succ hlo hj) b₁ b₂ body k)
          init₁ init₂
      else k init₁ init₂ := by
  apply fn_inj; funext s
  show forUpK2.loop lo hi body k j hlo init₁ init₂ s = _
  rw [forUpK2.loop]
  by_cases hj : j < hi
  · simp only [hj, ↓reduceDIte]; rfl
  · simp only [hj, ↓reduceDIte]

@[simp] public theorem forIn2_eq {β₁ : Type v₁} {β₂ : Type v₂}
    (lo hi : USize) (init₁ : β₁) (init₂ : β₂)
    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat →
      (β₁ → β₂ → Tail n γ) → β₁ → β₂ → Tail n γ)
    (k : β₁ → β₂ → Tail n γ) :
    forIn2 lo hi init₁ init₂ body k =
      forIn2From lo hi lo (Nat.le_refl _) init₁ init₂ body k := by
  rfl

/-- One step of `Tail.forInRev2From`. -/
public theorem forInRev2From_eq {β₁ : Type v₁} {β₂ : Type v₂}
    (lo hi j : USize) (hj : j.toNat ≤ hi.toNat) (init₁ : β₁) (init₂ : β₂)
    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat →
      (β₁ → β₂ → Tail n γ) → β₁ → β₂ → Tail n γ)
    (k : β₁ → β₂ → Tail n γ) :
    forInRev2From lo hi j hj init₁ init₂ body k =
      if h : lo < j then
        body (j - 1) (forInRev_le_pred h) (forInRev_pred_lt hj h)
          (fun b₁ b₂ =>
            forInRev2From lo hi (j - 1) (Nat.le_of_lt (forInRev_pred_lt hj h)) b₁ b₂ body k)
          init₁ init₂
      else k init₁ init₂ := by
  apply fn_inj; funext s
  show forDownK2.loop lo hi body k j hj init₁ init₂ s = _
  rw [forDownK2.loop]
  by_cases h : lo < j
  · simp only [h, ↓reduceDIte]; rfl
  · simp only [h, ↓reduceDIte]

@[simp] public theorem forInRev2_eq {β₁ : Type v₁} {β₂ : Type v₂}
    (lo hi : USize) (init₁ : β₁) (init₂ : β₂)
    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat →
      (β₁ → β₂ → Tail n γ) → β₁ → β₂ → Tail n γ)
    (k : β₁ → β₂ → Tail n γ) :
    forInRev2 lo hi init₁ init₂ body k =
      forInRev2From lo hi hi (Nat.le_refl _) init₁ init₂ body k := by
  rfl

/-- One step of `Tail.forIn3From`. -/
public theorem forIn3From_eq {β₁ : Type v₁} {β₂ : Type v₂} {β₃ : Type v₃}
    (lo hi j : USize) (hlo : lo.toNat ≤ j.toNat) (init₁ : β₁) (init₂ : β₂) (init₃ : β₃)
    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat →
      (β₁ → β₂ → β₃ → Tail n γ) → β₁ → β₂ → β₃ → Tail n γ)
    (k : β₁ → β₂ → β₃ → Tail n γ) :
    forIn3From lo hi j hlo init₁ init₂ init₃ body k =
      if hj : j < hi then
        body j hlo hj
          (fun b₁ b₂ b₃ =>
            forIn3From lo hi (j + 1) (forIn_le_succ hlo hj) b₁ b₂ b₃ body k)
          init₁ init₂ init₃
      else k init₁ init₂ init₃ := by
  apply fn_inj; funext s
  show forUpK3.loop lo hi body k j hlo init₁ init₂ init₃ s = _
  rw [forUpK3.loop]
  by_cases hj : j < hi
  · simp only [hj, ↓reduceDIte]; rfl
  · simp only [hj, ↓reduceDIte]

@[simp] public theorem forIn3_eq {β₁ : Type v₁} {β₂ : Type v₂} {β₃ : Type v₃}
    (lo hi : USize) (init₁ : β₁) (init₂ : β₂) (init₃ : β₃)
    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat →
      (β₁ → β₂ → β₃ → Tail n γ) → β₁ → β₂ → β₃ → Tail n γ)
    (k : β₁ → β₂ → β₃ → Tail n γ) :
    forIn3 lo hi init₁ init₂ init₃ body k =
      forIn3From lo hi lo (Nat.le_refl _) init₁ init₂ init₃ body k := by
  rfl

/-- One step of `Tail.forInRev3From`. -/
public theorem forInRev3From_eq {β₁ : Type v₁} {β₂ : Type v₂} {β₃ : Type v₃}
    (lo hi j : USize) (hj : j.toNat ≤ hi.toNat) (init₁ : β₁) (init₂ : β₂) (init₃ : β₃)
    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat →
      (β₁ → β₂ → β₃ → Tail n γ) → β₁ → β₂ → β₃ → Tail n γ)
    (k : β₁ → β₂ → β₃ → Tail n γ) :
    forInRev3From lo hi j hj init₁ init₂ init₃ body k =
      if h : lo < j then
        body (j - 1) (forInRev_le_pred h) (forInRev_pred_lt hj h)
          (fun b₁ b₂ b₃ =>
            forInRev3From lo hi (j - 1) (Nat.le_of_lt (forInRev_pred_lt hj h)) b₁ b₂ b₃ body k)
          init₁ init₂ init₃
      else k init₁ init₂ init₃ := by
  apply fn_inj; funext s
  show forDownK3.loop lo hi body k j hj init₁ init₂ init₃ s = _
  rw [forDownK3.loop]
  by_cases h : lo < j
  · simp only [h, ↓reduceDIte]; rfl
  · simp only [h, ↓reduceDIte]

@[simp] public theorem forInRev3_eq {β₁ : Type v₁} {β₂ : Type v₂} {β₃ : Type v₃}
    (lo hi : USize) (init₁ : β₁) (init₂ : β₂) (init₃ : β₃)
    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat →
      (β₁ → β₂ → β₃ → Tail n γ) → β₁ → β₂ → β₃ → Tail n γ)
    (k : β₁ → β₂ → β₃ → Tail n γ) :
    forInRev3 lo hi init₁ init₂ init₃ body k =
      forInRev3From lo hi hi (Nat.le_refl _) init₁ init₂ init₃ body k := by
  rfl

/-- One step of `Tail.forIn4From`. -/
public theorem forIn4From_eq {β₁ : Type v₁} {β₂ : Type v₂} {β₃ : Type v₃} {β₄ : Type v₄}
    (lo hi j : USize) (hlo : lo.toNat ≤ j.toNat) (init₁ : β₁) (init₂ : β₂) (init₃ : β₃) (init₄ : β₄)
    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat →
      (β₁ → β₂ → β₃ → β₄ → Tail n γ) → β₁ → β₂ → β₃ → β₄ → Tail n γ)
    (k : β₁ → β₂ → β₃ → β₄ → Tail n γ) :
    forIn4From lo hi j hlo init₁ init₂ init₃ init₄ body k =
      if hj : j < hi then
        body j hlo hj
          (fun b₁ b₂ b₃ b₄ =>
            forIn4From lo hi (j + 1) (forIn_le_succ hlo hj) b₁ b₂ b₃ b₄ body k)
          init₁ init₂ init₃ init₄
      else k init₁ init₂ init₃ init₄ := by
  apply fn_inj; funext s
  show forUpK4.loop lo hi body k j hlo init₁ init₂ init₃ init₄ s = _
  rw [forUpK4.loop]
  by_cases hj : j < hi
  · simp only [hj, ↓reduceDIte]; rfl
  · simp only [hj, ↓reduceDIte]

@[simp] public theorem forIn4_eq {β₁ : Type v₁} {β₂ : Type v₂} {β₃ : Type v₃} {β₄ : Type v₄}
    (lo hi : USize) (init₁ : β₁) (init₂ : β₂) (init₃ : β₃) (init₄ : β₄)
    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat →
      (β₁ → β₂ → β₃ → β₄ → Tail n γ) → β₁ → β₂ → β₃ → β₄ → Tail n γ)
    (k : β₁ → β₂ → β₃ → β₄ → Tail n γ) :
    forIn4 lo hi init₁ init₂ init₃ init₄ body k =
      forIn4From lo hi lo (Nat.le_refl _) init₁ init₂ init₃ init₄ body k := by
  rfl

/-- One step of `Tail.forInRev4From`. -/
public theorem forInRev4From_eq {β₁ : Type v₁} {β₂ : Type v₂} {β₃ : Type v₃} {β₄ : Type v₄}
    (lo hi j : USize) (hj : j.toNat ≤ hi.toNat) (init₁ : β₁) (init₂ : β₂) (init₃ : β₃) (init₄ : β₄)
    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat →
      (β₁ → β₂ → β₃ → β₄ → Tail n γ) → β₁ → β₂ → β₃ → β₄ → Tail n γ)
    (k : β₁ → β₂ → β₃ → β₄ → Tail n γ) :
    forInRev4From lo hi j hj init₁ init₂ init₃ init₄ body k =
      if h : lo < j then
        body (j - 1) (forInRev_le_pred h) (forInRev_pred_lt hj h)
          (fun b₁ b₂ b₃ b₄ =>
            forInRev4From lo hi (j - 1) (Nat.le_of_lt (forInRev_pred_lt hj h)) b₁ b₂ b₃ b₄ body k)
          init₁ init₂ init₃ init₄
      else k init₁ init₂ init₃ init₄ := by
  apply fn_inj; funext s
  show forDownK4.loop lo hi body k j hj init₁ init₂ init₃ init₄ s = _
  rw [forDownK4.loop]
  by_cases h : lo < j
  · simp only [h, ↓reduceDIte]; rfl
  · simp only [h, ↓reduceDIte]

@[simp] public theorem forInRev4_eq {β₁ : Type v₁} {β₂ : Type v₂} {β₃ : Type v₃} {β₄ : Type v₄}
    (lo hi : USize) (init₁ : β₁) (init₂ : β₂) (init₃ : β₃) (init₄ : β₄)
    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat →
      (β₁ → β₂ → β₃ → β₄ → Tail n γ) → β₁ → β₂ → β₃ → β₄ → Tail n γ)
    (k : β₁ → β₂ → β₃ → β₄ → Tail n γ) :
    forInRev4 lo hi init₁ init₂ init₃ init₄ body k =
      forInRev4From lo hi hi (Nat.le_refl _) init₁ init₂ init₃ init₄ body k := by
  rfl

end Tail

end InPlace

/--
Runs the program `m` on `a`, and returns its result and the new array: `m.run a rfl`. The array is
made exclusive first, so it is copied once if it is shared, and updated in place otherwise.
-/
@[inline, expose]
public def runInPlace {α : Type u} (a : Float32Array) (m : InPlace a.size α) : α × Float32Array :=
  m.run a rfl

@[simp] public theorem runInPlace_eq {α : Type u} (a : Float32Array) (m : InPlace a.size α) :
    a.runInPlace m = m.run a rfl := by
  rfl

/--
Runs the tail program `t` on `a`, and returns what its continuation returns: `t.run a rfl`. The
array is made exclusive first, so it is copied once if it is shared, and updated in place otherwise.
-/
@[inline, expose]
public def runInPlaceThen {γ : Type u} (a : Float32Array) (t : InPlace.Tail a.size γ) : γ :=
  t.run a rfl

@[simp] public theorem runInPlaceThen_eq {γ : Type u} (a : Float32Array)
    (t : InPlace.Tail a.size γ) :
    a.runInPlaceThen t = t.run a rfl := by
  rfl

/--
Runs the tail program `t` on `a`, for a size `n` of `a`: `t.run a h`. When `n` is a variable bound
to `a.size` before the program, the program's types don't mention `a`, so that the compiler doesn't
keep `a` alive through the program: if it did, the array would no longer be exclusive when the
program makes it so, and it would be copied. `inplace a do …` runs its programs this way.
-/
@[inline, expose]
public def runInPlaceThenOf {γ : Type u} (a : Float32Array) (n : Nat) (h : a.size = n)
    (t : InPlace.Tail n γ) : γ :=
  t.run a h

@[simp] public theorem runInPlaceThenOf_eq {γ : Type u} (a : Float32Array) (n : Nat)
    (h : a.size = n) (t : InPlace.Tail n γ) :
    a.runInPlaceThenOf n h t = t.run a h := by
  rfl

end Float32Array

end ScalarArray
