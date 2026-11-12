/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ScalarArray.Stride
public import ScalarArray.Float32.Program
import all ScalarArray.Internal

/-!
# Updates at index maps, and whole loops, on `Float32Array`

`a.modifyAt idx lo hi g` is `a` with `g i a[idx i]` written at the index `idx i`, for each `i`
from `lo` up to `hi - 1`, in this order. It is the model of a loop that updates the elements at a
map of indices: a stride `a.modifyAt s.idx lo hi g`, for a `ScalarArray.Stride` `s`, the diagonal
of a matrix, a packed triangle or a permutation. When `idx` is injective on the range, which
`Stride.Fits.idx_inj` gives for a stride, the element at `idx i` is `g i a[idx i]`
(`getElem_modifyAt_idx`). The elements at no index of the range are unchanged
(`getElem_modifyAt_of_forall_ne`). `copySlice_eq_modifyAt` gives a copy within bounds as a
`modifyAt` at the indices `destOff + i`, so that a kernel can copy contiguous data with
`copySlice` and strided data with a loop, and specify both the same way.

The whole-loop lemmas of `InPlace.Tail` run a loop in continuation-passing style from any step
`j₀`, where its one-step equation `Tail.forInFrom_eq` runs one step:

* by `Tail.run_forInFrom`, a loop whose step `j` maps its variable and the array by `f j` runs as
  `iterRange f`, and by `Tail.run_forInFrom_unit`, a loop with no variable whose step `j` maps the
  array by `F j` runs as `iterRange F`. A loop of loops is of this kind, with the inner loops
  proved by the same lemmas;
* by `Tail.run_forInFrom_modify`, the loop `for j in lo...hi do a[e j] := g a[e j]` of the
  `inplace` notation, where the value of the index `e j` is `idx j`, runs as `modifyAt idx`, and by
  `Tail.run_forInFrom_write`, so does `for j in lo...hi do a[e j] := g`;
* the `Tail.run_forInRevFrom` lemmas do the same for the loops down, `for j in reverse lo...hi`,
  with `iterRangeRev`, and with `modifyAt` when `idx` is injective on the range.
-/

namespace ScalarArray

namespace Float32Array

/-! ## Updates at index maps -/

/-- The step `i` of `modifyAt`. -/
private def modifyStep (idx : Nat → Nat) (g : Nat → Float32 → Float32) (i : Nat) (a : Float32Array) :
    Float32Array :=
  if h : idx i < a.size then a.set (idx i) (g i a[idx i]) h else a

/--
The array `a` with `g i a[idx i]` written at the index `idx i`, for each `i` from `lo` up to
`hi - 1`, in this order, where `g i` sees the earlier writes. Indices out of bounds are skipped.
It is the model of a loop that updates the elements at the indices `idx i`, such as the steps
`s.idx i` of a stride `s`.
-/
public def modifyAt (a : Float32Array) (idx : Nat → Nat) (lo hi : Nat)
    (g : Nat → Float32 → Float32) : Float32Array :=
  iterRange (modifyStep idx g) lo hi a

private theorem modifyStep_eq (idx : Nat → Nat) (g : Nat → Float32 → Float32) (i : Nat)
    (a : Float32Array) : modifyStep idx g i a = a.set! (idx i) (g i a[idx i]!) := by
  unfold modifyStep
  split
  · rename_i h; simp [set!, h, getElem!_pos]
  · rename_i h; simp [set!, h]

private theorem getElem?_modifyStep (idx : Nat → Nat) (g : Nat → Float32 → Float32) (i : Nat)
    (a : Float32Array) (q : Nat) :
    (modifyStep idx g i a)[q]? = if idx i = q then a[q]?.map (g i) else a[q]? := by
  unfold modifyStep
  split
  · rename_i h
    rw [show a.set (idx i) (g i a[idx i]) h = a.set! (idx i) (g i a[idx i]) by simp [set!, h],
      getElem?_set!]
    split
    · rename_i e; subst e; simp [h]
    · rfl
  · rename_i h
    split
    · rename_i e; subst e; simp [h]
    · rfl

private theorem modifyStep_comm (idx : Nat → Nat) (g : Nat → Float32 → Float32) {i j : Nat}
    (hne : idx i ≠ idx j) (a : Float32Array) :
    modifyStep idx g i (modifyStep idx g j a) = modifyStep idx g j (modifyStep idx g i a) := by
  apply ext_getElem?; intro q
  simp only [getElem?_modifyStep]
  by_cases hi : idx i = q <;> by_cases hj : idx j = q
  · exact absurd (hi.trans hj.symm) hne
  all_goals simp [hi, hj]

@[simp, grind =] public theorem size_modifyAt (a : Float32Array) (idx : Nat → Nat) (lo hi : Nat)
    (g : Nat → Float32 → Float32) : (a.modifyAt idx lo hi g).size = a.size :=
  iterRange_invariant (fun b : Float32Array => b.size = a.size)
    (fun _ _ _ b hb => by rw [← hb]; unfold modifyStep; split <;> simp) rfl

public theorem modifyAt_of_le (a : Float32Array) (idx : Nat → Nat) {lo hi : Nat} (h : hi ≤ lo)
    (g : Nat → Float32 → Float32) : a.modifyAt idx lo hi g = a :=
  iterRange_of_le _ h a

@[simp] public theorem modifyAt_self (a : Float32Array) (idx : Nat → Nat) (lo : Nat)
    (g : Nat → Float32 → Float32) : a.modifyAt idx lo lo g = a :=
  iterRange_self _ lo a

/-- The step `lo` of `modifyAt` comes first. -/
public theorem modifyAt_of_lt (a : Float32Array) (idx : Nat → Nat) {lo hi : Nat} (h : lo < hi)
    (g : Nat → Float32 → Float32) :
    a.modifyAt idx lo hi g = (a.set! (idx lo) (g lo a[idx lo]!)).modifyAt idx (lo + 1) hi g := by
  simp only [modifyAt]; rw [iterRange_of_lt _ h, modifyStep_eq]

/-- The step `hi` of `modifyAt` comes last. -/
public theorem modifyAt_succ (a : Float32Array) (idx : Nat → Nat) {lo hi : Nat} (h : lo ≤ hi)
    (g : Nat → Float32 → Float32) :
    a.modifyAt idx lo (hi + 1) g =
      (a.modifyAt idx lo hi g).set! (idx hi) (g hi (a.modifyAt idx lo hi g)[idx hi]!) := by
  simp only [modifyAt]; rw [iterRange_succ _ h, modifyStep_eq]

/-- `modifyAt` splits at any `mid` between its bounds. -/
public theorem modifyAt_split (a : Float32Array) (idx : Nat → Nat) {lo mid hi : Nat}
    (h₁ : lo ≤ mid) (h₂ : mid ≤ hi) (g : Nat → Float32 → Float32) :
    a.modifyAt idx lo hi g = (a.modifyAt idx lo mid g).modifyAt idx mid hi g :=
  iterRange_split _ h₁ h₂ a

/-- `modifyAt` depends only on the indices and the updates in its range. -/
public theorem modifyAt_congr (a : Float32Array) {idx idx' : Nat → Nat} {lo hi : Nat}
    {g g' : Nat → Float32 → Float32} (hidx : ∀ i, lo ≤ i → i < hi → idx i = idx' i)
    (hg : ∀ i, lo ≤ i → i < hi → g i = g' i) :
    a.modifyAt idx lo hi g = a.modifyAt idx' lo hi g' :=
  iterRange_congr (fun i h₁ h₂ => by
    funext b; simp only [modifyStep, hidx i h₁ h₂, hg i h₁ h₂]) a

private theorem getElem?_modifyAt_of_forall_ne (a : Float32Array) (idx : Nat → Nat)
    {lo hi : Nat} (g : Nat → Float32 → Float32) {p : Nat}
    (hp : ∀ i, lo ≤ i → i < hi → idx i ≠ p) : (a.modifyAt idx lo hi g)[p]? = a[p]? :=
  iterRange_invariant (fun b : Float32Array => b[p]? = a[p]?)
    (fun i h₁ h₂ b hb => by rw [getElem?_modifyStep]; simp [hp i h₁ h₂, hb]) rfl

/-- An element at no index `idx i` of the range is unchanged. -/
public theorem getElem_modifyAt_of_forall_ne (a : Float32Array) (idx : Nat → Nat) {lo hi : Nat}
    (g : Nat → Float32 → Float32) {p : Nat} (hp : ∀ i, lo ≤ i → i < hi → idx i ≠ p)
    (h : p < (a.modifyAt idx lo hi g).size) :
    (a.modifyAt idx lo hi g)[p] = a[p]'(by simpa using h) := by
  have := getElem?_modifyAt_of_forall_ne a idx g hp
  rw [getElem?_pos (a.modifyAt idx lo hi g) p h, getElem?_pos a p (by simpa using h)] at this
  exact Option.some.inj this

private theorem getElem?_modifyAt_idx (a : Float32Array) (idx : Nat → Nat) {lo hi : Nat}
    (g : Nat → Float32 → Float32)
    (hinj : ∀ i, lo ≤ i → i < hi → ∀ j, lo ≤ j → j < hi → idx i = idx j → i = j) {i : Nat}
    (hi₁ : lo ≤ i) (hi₂ : i < hi) :
    (a.modifyAt idx lo hi g)[idx i]? = a[idx i]?.map (g i) := by
  have hsucc := iterRange_succ (modifyStep idx g) hi₁ a
  rw [modifyAt, iterRange_split _ (show lo ≤ i + 1 by lia) (show i + 1 ≤ hi by lia), hsucc]
  rw [← modifyAt, getElem?_modifyAt_of_forall_ne _ idx g
    (fun j h₁ h₂ e => by have := hinj j (by lia) h₂ i hi₁ hi₂ e; lia)]
  rw [getElem?_modifyStep]; simp only [↓reduceIte]
  rw [← modifyAt, getElem?_modifyAt_of_forall_ne _ idx g
    (fun j h₁ h₂ e => by have := hinj j h₁ (by lia) i hi₁ hi₂ e; lia)]

/--
The element at the index `idx i` of a step `i` of the range is `g i` of the element of `a`, when
`idx` is injective on the range.
-/
public theorem getElem_modifyAt_idx (a : Float32Array) (idx : Nat → Nat) {lo hi : Nat}
    (g : Nat → Float32 → Float32)
    (hinj : ∀ i, lo ≤ i → i < hi → ∀ j, lo ≤ j → j < hi → idx i = idx j → i = j) {i : Nat}
    (hi₁ : lo ≤ i) (hi₂ : i < hi) (h : idx i < (a.modifyAt idx lo hi g).size) :
    (a.modifyAt idx lo hi g)[idx i] = g i (a[idx i]'(by simpa using h)) := by
  have := getElem?_modifyAt_idx a idx g hinj hi₁ hi₂
  rw [getElem?_pos (a.modifyAt idx lo hi g) (idx i) h,
    getElem?_pos a (idx i) (by simpa using h)] at this
  exact Option.some.inj this

/--
The step `hi` of `modifyAt` can come first instead of last, when `idx` is injective on the range,
since then no other step reads or writes its element.
-/
public theorem modifyAt_succ_of_injOn (a : Float32Array) (idx : Nat → Nat) {lo hi : Nat}
    (h : lo ≤ hi) (g : Nat → Float32 → Float32)
    (hinj : ∀ i, lo ≤ i → i < hi + 1 → ∀ j, lo ≤ j → j < hi + 1 → idx i = idx j → i = j) :
    a.modifyAt idx lo (hi + 1) g = (a.set! (idx hi) (g hi a[idx hi]!)).modifyAt idx lo hi g := by
  simp only [modifyAt, ← modifyStep_eq]
  obtain ⟨d, hd⟩ : ∃ d, hi - lo = d := ⟨_, rfl⟩
  induction d generalizing lo a with
  | zero =>
    obtain rfl : lo = hi := by lia
    rw [iterRange_of_lt _ (by lia), iterRange_self, iterRange_self]
  | succ d ih =>
    rw [iterRange_of_lt _ (show lo < hi + 1 by lia),
      ih _ (by lia) (fun i h₁ h₂ j h₃ h₄ => hinj i (by lia) h₂ j (by lia) h₄) (by lia),
      iterRange_of_lt _ (show lo < hi by lia),
      modifyStep_comm idx g fun e => by
        have := hinj lo (Nat.le_refl _) (by lia) hi h (by lia) e.symm; lia]

/-- For an index map injective on the range, the order of the steps doesn't matter. -/
private theorem iterRangeRev_modifyStep (a : Float32Array) (idx : Nat → Nat) {lo hi : Nat}
    (g : Nat → Float32 → Float32)
    (hinj : ∀ i, lo ≤ i → i < hi → ∀ j, lo ≤ j → j < hi → idx i = idx j → i = j) :
    iterRangeRev (modifyStep idx g) lo hi a = a.modifyAt idx lo hi g := by
  obtain ⟨d, hd⟩ : ∃ d, hi - lo = d := ⟨_, rfl⟩
  induction d generalizing hi a with
  | zero => rw [iterRangeRev_of_le _ (by lia), modifyAt_of_le _ _ (by lia)]
  | succ d ih =>
    rw [iterRangeRev_of_lt _ (by lia),
      ih _ (fun i h₁ h₂ j h₃ h₄ => hinj i h₁ (by lia) j h₃ (by lia)) (by lia), modifyStep_eq]
    obtain ⟨m, rfl⟩ : ∃ m, hi = m + 1 := ⟨hi - 1, by lia⟩
    rw [Nat.add_sub_cancel, modifyAt_succ_of_injOn _ _ (by lia) _ hinj]

/-! ### Strides -/

/-- The element at the step `i` of a stride that fits in the array. -/
public theorem getElem_modifyAt_stride (a : Float32Array) {s : Stride} {n : Nat}
    (hs : s.Fits n a.size) {lo hi : Nat} (hn : hi ≤ n) (g : Nat → Float32 → Float32) {i : Nat}
    (hi₁ : lo ≤ i) (hi₂ : i < hi) :
    (a.modifyAt s.idx lo hi g)[s.idx i]'(by rw [size_modifyAt]; exact hs.idx_lt (by lia)) =
      g i (a[s.idx i]'(hs.idx_lt (by lia))) :=
  getElem_modifyAt_idx a s.idx g
    (fun i _ h₁ j _ h₂ e => hs.idx_inj (by lia) (by lia) e) hi₁ hi₂ _

/-! ### Copies -/

/-- `copySlice` within bounds writes the elements of `src` at the indices `destOff + i`. -/
public theorem copySlice_eq_modifyAt (src : Float32Array) (srcOff : Nat) (dest : Float32Array)
    (destOff len : Nat) (exact : Bool) (h₁ : srcOff + len ≤ src.size)
    (h₂ : destOff + len ≤ dest.size) :
    src.copySlice srcOff dest destOff len exact =
      dest.modifyAt (destOff + ·) 0 len fun i _ => src[srcOff + i]! := by
  apply ext_getElem (by simp [size_copySlice]; lia)
  intro p hp hp'
  rw [getElem_copySlice]
  by_cases hlo : p < destOff
  · rw [dite_eq_left_of_eq_true (eq_true (by lia)),
      getElem_modifyAt_of_forall_ne _ _ _ (fun i _ _ => by lia)]
  · by_cases hhi : p < destOff + len
    · obtain ⟨i, rfl⟩ : ∃ i, p = destOff + i := ⟨p - destOff, by lia⟩
      rw [dite_eq_right_of_eq_false (eq_false (by lia)),
        dite_eq_left_of_eq_true (eq_true (by lia)),
        getElem_modifyAt_idx _ _ _ (fun _ _ _ _ _ _ e => by lia) (Nat.zero_le _) (by lia),
        getElem!_pos src (srcOff + i) (by lia)]
      congr 1; lia
    · rw [dite_eq_right_of_eq_false (eq_false (by lia)),
        dite_eq_right_of_eq_false (eq_false (by lia)),
        getElem_modifyAt_of_forall_ne _ _ _ (fun i _ _ => by lia)]

namespace InPlace.Tail

variable {n : Nat} {γ : Type w}

private theorem run_congr {t : Tail n γ} {a b : Float32Array} (e : a = b) (ha : a.size = n)
    (hb : b.size = n) : t.run a ha = t.run b hb := by
  subst e; rfl

private theorem run_congr_pair {β : Type v} {k : β → Tail n γ} {x y : β × Float32Array}
    (e : x = y) (hx : x.2.size = n) (hy : y.2.size = n) :
    (k x.1).run x.2 hx = (k y.1).run y.2 hy := by
  subst e; rfl

/-! ## Whole loops -/

/--
Runs the loop `Tail.forInFrom lo hi j₀ hlo init body k` whose step `j` maps its variable `b` and
the array `a` by `f j.toNat (b, a)`, before it runs the next step: it maps them by
`iterRange f j₀.toNat hi.toNat`, and then runs `k`.
-/
public theorem run_forInFrom {β : Type v} (lo hi j₀ : USize) (hlo : lo.toNat ≤ j₀.toNat)
    (init : β)
    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat →
      (β → Tail n γ) → β → Tail n γ)
    (k : β → Tail n γ) (f : Nat → β × Float32Array → β × Float32Array)
    (hf : ∀ j x, (f j x).2.size = x.2.size)
    (hbody : ∀ j hl hj next b a (h : a.size = n),
      (body j hl hj next b).run a h =
        (next (f j.toNat (b, a)).1).run (f j.toNat (b, a)).2 (by rw [hf]; exact h))
    (a : Float32Array) (h : a.size = n) :
    (forInFrom lo hi j₀ hlo init body k).run a h =
      (k (iterRange f j₀.toNat hi.toNat (init, a)).1).run
        (iterRange f j₀.toNat hi.toNat (init, a)).2
        (iterRange_invariant (fun x => x.2.size = n) (fun _ _ _ x hx => (hf _ x).trans hx) h) := by
  obtain ⟨d, hd⟩ : ∃ d, hi.toNat - j₀.toNat = d := ⟨_, rfl⟩
  induction d generalizing j₀ init a with
  | zero =>
    have hj : ¬j₀ < hi := by rw [USize.lt_iff_toNat_lt]; lia
    rw [forInFrom_eq, dite_eq_right_of_eq_false (eq_false hj)]
    exact run_congr_pair (k := k) (x := (init, a)) (iterRange_of_le f (by lia) _).symm h _
  | succ d ih =>
    have hj : j₀ < hi := by rw [USize.lt_iff_toNat_lt]; lia
    have hsucc := toNat_add_one_of_lt hj
    rw [forInFrom_eq, dite_eq_left_of_eq_true (eq_true hj)]
    refine (hbody j₀ hlo hj _ init a h).trans ?_
    rw [ih _ _ _ _ _ (by rw [hsucc]; lia)]
    exact run_congr_pair (by
      rw [hsucc, iterRange_of_lt f (lo := j₀.toNat) (USize.lt_iff_toNat_lt.1 hj)]) _ _

/--
Runs the loop `Tail.forInFrom lo hi j₀ hlo () body k` with no variable whose step `j` maps the
array `a` by `F j.toNat`, before it runs the next step: it maps the array by
`iterRange F j₀.toNat hi.toNat`, and then runs `k`. This is the case of a loop of loops, where `F j`
is the model of the inner loop.
-/
public theorem run_forInFrom_unit (lo hi j₀ : USize) (hlo : lo.toNat ≤ j₀.toNat)
    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat →
      (Unit → Tail n γ) → Unit → Tail n γ)
    (k : Unit → Tail n γ) (F : Nat → Float32Array → Float32Array) (hF : ∀ j a, (F j a).size = a.size)
    (hbody : ∀ j hl hj next a (h : a.size = n),
      (body j hl hj next ()).run a h = (next ()).run (F j.toNat a) (by rw [hF]; exact h))
    (a : Float32Array) (h : a.size = n) :
    (forInFrom lo hi j₀ hlo () body k).run a h =
      (k ()).run (iterRange F j₀.toNat hi.toNat a)
        (iterRange_invariant (fun b => b.size = n) (fun _ _ _ b hb => (hF _ b).trans hb) h) := by
  rw [run_forInFrom lo hi j₀ hlo () body k (fun j x => ((), F j x.2)) (fun j x => hF j x.2)
    (fun j hl hj next _ a h => hbody j hl hj next a h)]
  exact run_congr (apply_iterRange Prod.snd (fun _ _ _ _ => rfl) _) _ _

private theorem run_readThen_writeThen (e : USize) (idx : Nat) (he : e.toNat = idx)
    (p : e.toNat < n) (g : Float32 → Float32) (k : Tail n γ) (a : Float32Array) (h : a.size = n) :
    (readThen e p fun v => writeThen e p (g v) k).run a h =
      k.run (modifyStep (fun _ => idx) (fun _ => g) 0 a) (by
        rw [← h]; unfold modifyStep; split <;> simp) := by
  subst he
  simp only [run_readThen, run_writeThen, modifyStep, show e.toNat < a.size by lia, ↓reduceDIte]

private theorem run_writeThen' (e : USize) (idx : Nat) (he : e.toNat = idx)
    (p : e.toNat < n) (v : Float32) (k : Tail n γ) (a : Float32Array) (h : a.size = n) :
    (writeThen e p v k).run a h =
      k.run (modifyStep (fun _ => idx) (fun _ _ => v) 0 a) (by
        rw [← h]; unfold modifyStep; split <;> simp) := by
  subst he
  simp only [run_writeThen, modifyStep, show e.toNat < a.size by lia, ↓reduceDIte]

/--
Runs the loop `for j in lo...hi do a[e j] := g a[e j]` of the `inplace` notation, from the step
`j₀`, where the value of the index `e j` is `idx j.toNat` and `g` may use the bounds of `j`: it
maps the array by `modifyAt idx j₀.toNat hi.toNat G`, and then runs `k`.
-/
public theorem run_forInFrom_modify (lo hi j₀ : USize) (hlo : lo.toNat ≤ j₀.toNat)
    (e : USize → USize) (idx : Nat → Nat)
    (he : ∀ j : USize, lo.toNat ≤ j.toNat → j.toNat < hi.toNat → (e j).toNat = idx j.toNat)
    (p : ∀ j : USize, lo.toNat ≤ j.toNat → j.toNat < hi.toNat → (e j).toNat < n)
    (g : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat → Float32 → Float32)
    (G : Nat → Float32 → Float32) (hg : ∀ j hl hj v, g j hl hj v = G j.toNat v)
    (k : Unit → Tail n γ) (a : Float32Array) (h : a.size = n) :
    (forInFrom lo hi j₀ hlo ()
        (fun j hl hj next _ => readThen (e j) (p j hl hj) fun v =>
          writeThen (e j) (p j hl hj) (g j hl hj v) (next ())) k).run a h =
      (k ()).run (a.modifyAt idx j₀.toNat hi.toNat G) (by rw [size_modifyAt]; exact h) := by
  rw [run_forInFrom_unit lo hi j₀ hlo _ k (modifyStep idx G)
    (fun _ b => by unfold modifyStep; split <;> simp)]
  · rfl
  · intro j hl hj next a h
    simp only [hg]
    rw [run_readThen_writeThen (e j) _ (he j hl hj)]
    rfl

/--
Runs the loop `for j in lo...hi do a[e j] := g` of the `inplace` notation, from the step `j₀`,
where the value of the index `e j` is `idx j.toNat` and `g` may use the bounds of `j`: it maps the
array by `modifyAt idx j₀.toNat hi.toNat fun i _ => G i`, and then runs `k`.
-/
public theorem run_forInFrom_write (lo hi j₀ : USize) (hlo : lo.toNat ≤ j₀.toNat)
    (e : USize → USize) (idx : Nat → Nat)
    (he : ∀ j : USize, lo.toNat ≤ j.toNat → j.toNat < hi.toNat → (e j).toNat = idx j.toNat)
    (p : ∀ j : USize, lo.toNat ≤ j.toNat → j.toNat < hi.toNat → (e j).toNat < n)
    (g : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat → Float32) (G : Nat → Float32)
    (hg : ∀ j hl hj, g j hl hj = G j.toNat) (k : Unit → Tail n γ) (a : Float32Array)
    (h : a.size = n) :
    (forInFrom lo hi j₀ hlo ()
        (fun j hl hj next _ => writeThen (e j) (p j hl hj) (g j hl hj) (next ())) k).run a h =
      (k ()).run (a.modifyAt idx j₀.toNat hi.toNat fun i _ => G i)
        (by rw [size_modifyAt]; exact h) := by
  rw [run_forInFrom_unit lo hi j₀ hlo _ k (modifyStep idx fun i _ => G i)
    (fun _ b => by unfold modifyStep; split <;> simp)]
  · rfl
  · intro j hl hj next a h
    simp only [hg]
    rw [run_writeThen' (e j) _ (he j hl hj)]
    rfl

/-! ## Whole loops down -/

/--
Runs the loop `Tail.forInRevFrom lo hi j₀ hj₀ init body k`, from `j₀ - 1` down to `lo`, whose step
`j` maps its variable `b` and the array `a` by `f j.toNat (b, a)`, before it runs the next step: it
maps them by `iterRangeRev f lo.toNat j₀.toNat`, and then runs `k`.
-/
public theorem run_forInRevFrom {β : Type v} (lo hi j₀ : USize) (hj₀ : j₀.toNat ≤ hi.toNat)
    (init : β)
    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat →
      (β → Tail n γ) → β → Tail n γ)
    (k : β → Tail n γ) (f : Nat → β × Float32Array → β × Float32Array)
    (hf : ∀ j x, (f j x).2.size = x.2.size)
    (hbody : ∀ j hl hj next b a (h : a.size = n),
      (body j hl hj next b).run a h =
        (next (f j.toNat (b, a)).1).run (f j.toNat (b, a)).2 (by rw [hf]; exact h))
    (a : Float32Array) (h : a.size = n) :
    (forInRevFrom lo hi j₀ hj₀ init body k).run a h =
      (k (iterRangeRev f lo.toNat j₀.toNat (init, a)).1).run
        (iterRangeRev f lo.toNat j₀.toNat (init, a)).2
        (iterRangeRev_invariant (fun x => x.2.size = n) (fun _ _ _ x hx => (hf _ x).trans hx)
          h) := by
  obtain ⟨d, hd⟩ : ∃ d, j₀.toNat - lo.toNat = d := ⟨_, rfl⟩
  induction d generalizing j₀ init a with
  | zero =>
    have hj : ¬lo < j₀ := by rw [USize.lt_iff_toNat_lt]; lia
    rw [forInRevFrom_eq, dite_eq_right_of_eq_false (eq_false hj)]
    exact run_congr_pair (k := k) (x := (init, a)) (iterRangeRev_of_le f (by lia) _).symm h _
  | succ d ih =>
    have hj : lo < j₀ := by rw [USize.lt_iff_toNat_lt]; lia
    have hpred := toNat_sub_one_of_lt hj
    rw [forInRevFrom_eq, dite_eq_left_of_eq_true (eq_true hj)]
    refine (hbody (j₀ - 1) _ _ _ init a h).trans ?_
    rw [ih _ _ _ _ _ (by rw [hpred]; lia)]
    exact run_congr_pair (by
      rw [hpred, iterRangeRev_of_lt f (hi := j₀.toNat) (USize.lt_iff_toNat_lt.1 hj)]) _ _

/--
Runs the loop `Tail.forInRevFrom lo hi j₀ hj₀ () body k` with no variable, from `j₀ - 1` down to
`lo`, whose step `j` maps the array `a` by `F j.toNat`, before it runs the next step: it maps the
array by `iterRangeRev F lo.toNat j₀.toNat`, and then runs `k`.
-/
public theorem run_forInRevFrom_unit (lo hi j₀ : USize) (hj₀ : j₀.toNat ≤ hi.toNat)
    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat →
      (Unit → Tail n γ) → Unit → Tail n γ)
    (k : Unit → Tail n γ) (F : Nat → Float32Array → Float32Array) (hF : ∀ j a, (F j a).size = a.size)
    (hbody : ∀ j hl hj next a (h : a.size = n),
      (body j hl hj next ()).run a h = (next ()).run (F j.toNat a) (by rw [hF]; exact h))
    (a : Float32Array) (h : a.size = n) :
    (forInRevFrom lo hi j₀ hj₀ () body k).run a h =
      (k ()).run (iterRangeRev F lo.toNat j₀.toNat a)
        (iterRangeRev_invariant (fun b => b.size = n) (fun _ _ _ b hb => (hF _ b).trans hb)
          h) := by
  rw [run_forInRevFrom lo hi j₀ hj₀ () body k (fun j x => ((), F j x.2)) (fun j x => hF j x.2)
    (fun j hl hj next _ a h => hbody j hl hj next a h)]
  exact run_congr (apply_iterRangeRev Prod.snd (fun _ _ _ _ => rfl) _) _ _

/--
Runs the loop `for j in reverse lo...hi do a[e j] := g a[e j]` of the `inplace` notation, from
`j₀ - 1` down to `lo`, where the value of the index `e j` is `idx j.toNat`, which is injective on
the range, and `g` may use the bounds of `j`: it maps the array by
`modifyAt idx lo.toNat j₀.toNat G`, and then runs `k`.
-/
public theorem run_forInRevFrom_modify (lo hi j₀ : USize) (hj₀ : j₀.toNat ≤ hi.toNat)
    (e : USize → USize) (idx : Nat → Nat)
    (he : ∀ j : USize, lo.toNat ≤ j.toNat → j.toNat < hi.toNat → (e j).toNat = idx j.toNat)
    (hinj : ∀ i, lo.toNat ≤ i → i < j₀.toNat → ∀ j, lo.toNat ≤ j → j < j₀.toNat →
      idx i = idx j → i = j)
    (p : ∀ j : USize, lo.toNat ≤ j.toNat → j.toNat < hi.toNat → (e j).toNat < n)
    (g : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat → Float32 → Float32)
    (G : Nat → Float32 → Float32) (hg : ∀ j hl hj v, g j hl hj v = G j.toNat v)
    (k : Unit → Tail n γ) (a : Float32Array) (h : a.size = n) :
    (forInRevFrom lo hi j₀ hj₀ ()
        (fun j hl hj next _ => readThen (e j) (p j hl hj) fun v =>
          writeThen (e j) (p j hl hj) (g j hl hj v) (next ())) k).run a h =
      (k ()).run (a.modifyAt idx lo.toNat j₀.toNat G) (by rw [size_modifyAt]; exact h) := by
  rw [run_forInRevFrom_unit lo hi j₀ hj₀ _ k (modifyStep idx G)
    (fun _ b => by unfold modifyStep; split <;> simp)]
  · exact run_congr (iterRangeRev_modifyStep a idx G hinj) _ _
  · intro j hl hj next a h
    simp only [hg]
    rw [run_readThen_writeThen (e j) _ (he j hl hj)]
    rfl

/--
Runs the loop `for j in reverse lo...hi do a[e j] := g` of the `inplace` notation, from `j₀ - 1`
down to `lo`, where the value of the index `e j` is `idx j.toNat`, which is injective on the range,
and `g` may use the bounds of `j`: it maps the array by
`modifyAt idx lo.toNat j₀.toNat fun i _ => G i`, and then runs `k`.
-/
public theorem run_forInRevFrom_write (lo hi j₀ : USize) (hj₀ : j₀.toNat ≤ hi.toNat)
    (e : USize → USize) (idx : Nat → Nat)
    (he : ∀ j : USize, lo.toNat ≤ j.toNat → j.toNat < hi.toNat → (e j).toNat = idx j.toNat)
    (hinj : ∀ i, lo.toNat ≤ i → i < j₀.toNat → ∀ j, lo.toNat ≤ j → j < j₀.toNat →
      idx i = idx j → i = j)
    (p : ∀ j : USize, lo.toNat ≤ j.toNat → j.toNat < hi.toNat → (e j).toNat < n)
    (g : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat → Float32) (G : Nat → Float32)
    (hg : ∀ j hl hj, g j hl hj = G j.toNat) (k : Unit → Tail n γ) (a : Float32Array)
    (h : a.size = n) :
    (forInRevFrom lo hi j₀ hj₀ ()
        (fun j hl hj next _ => writeThen (e j) (p j hl hj) (g j hl hj) (next ())) k).run a h =
      (k ()).run (a.modifyAt idx lo.toNat j₀.toNat fun i _ => G i)
        (by rw [size_modifyAt]; exact h) := by
  rw [run_forInRevFrom_unit lo hi j₀ hj₀ _ k (modifyStep idx fun i _ => G i)
    (fun _ b => by unfold modifyStep; split <;> simp)]
  · exact run_congr (iterRangeRev_modifyStep a idx _ hinj) _ _
  · intro j hl hj next a h
    simp only [hg]
    rw [run_writeThen' (e j) _ (he j hl hj)]
    rfl

end InPlace.Tail

end Float32Array

end ScalarArray
