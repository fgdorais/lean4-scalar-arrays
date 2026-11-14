/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ScalarArray.Stride
public import ScalarArray.Int16.Program
import all ScalarArray.Internal

/-!
# Updates at index maps, and whole loops, on `Int16Array`

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

Two updates at a time have models too. `a.modifyAt2 ia ib lo hi f g` reads the elements at `ia i`
and `ib i` and writes `f i u v` and `g i u v` back, for two index maps of one array, such as two
rows of a matrix, and `zipModifyAt a b ia ib lo hi f g` does the same on two arrays. When the maps
are injective on the range, and for `modifyAt2` never meet, `modifyAt2_eq` and `zipModifyAt_eq`
give them as `modifyAt`s, whose lemmas then apply. `Tail.run_forInFrom_modify2` runs the loop
`for j in lo...hi do let u := a[ea j]; let v := a[eb j]; a[ea j] := …; a[eb j] := …` as
`modifyAt2`.

The strided loops `modifyStride`, `modifyStride2` and `zipModifyStride` run these models on
strides as single loops, which make each array exclusive once and then store without checks. They
are specified by their models with `@[csimp]`.
-/

namespace ScalarArray

namespace Int16Array

/-! ## Updates at index maps -/

/-- The step `i` of `modifyAt`. -/
private def modifyStep (idx : Nat → Nat) (g : Nat → Int16 → Int16) (i : Nat)
    (a : Int16Array) : Int16Array :=
  if h : idx i < a.size then a.set (idx i) (g i a[idx i]) h else a

/--
The array `a` with `g i a[idx i]` written at the index `idx i`, for each `i` from `lo` up to
`hi - 1`, in this order, where `g i` sees the earlier writes. Indices out of bounds are skipped.
It is the model of a loop that updates the elements at the indices `idx i`, such as the steps
`s.idx i` of a stride `s`.
-/
public def modifyAt (a : Int16Array) (idx : Nat → Nat) (lo hi : Nat)
    (g : Nat → Int16 → Int16) : Int16Array :=
  iterRange (modifyStep idx g) lo hi a

private theorem modifyStep_eq (idx : Nat → Nat) (g : Nat → Int16 → Int16) (i : Nat)
    (a : Int16Array) : modifyStep idx g i a = a.set! (idx i) (g i a[idx i]!) := by
  unfold modifyStep
  split
  · rename_i h; simp [set!, h, getElem!_pos]
  · rename_i h; simp [set!, h]

private theorem getElem?_modifyStep (idx : Nat → Nat) (g : Nat → Int16 → Int16) (i : Nat)
    (a : Int16Array) (q : Nat) :
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

private theorem modifyStep_comm (idx : Nat → Nat) (g : Nat → Int16 → Int16) {i j : Nat}
    (hne : idx i ≠ idx j) (a : Int16Array) :
    modifyStep idx g i (modifyStep idx g j a) = modifyStep idx g j (modifyStep idx g i a) := by
  apply ext_getElem?; intro q
  simp only [getElem?_modifyStep]
  by_cases hi : idx i = q <;> by_cases hj : idx j = q
  · exact absurd (hi.trans hj.symm) hne
  all_goals simp [hi, hj]

@[simp, grind =] public theorem size_modifyAt (a : Int16Array) (idx : Nat → Nat) (lo hi : Nat)
    (g : Nat → Int16 → Int16) : (a.modifyAt idx lo hi g).size = a.size :=
  iterRange_invariant (fun b : Int16Array => b.size = a.size)
    (fun _ _ _ b hb => by rw [← hb]; unfold modifyStep; split <;> simp) rfl

public theorem modifyAt_of_le (a : Int16Array) (idx : Nat → Nat) {lo hi : Nat} (h : hi ≤ lo)
    (g : Nat → Int16 → Int16) : a.modifyAt idx lo hi g = a :=
  iterRange_of_le _ h a

@[simp] public theorem modifyAt_self (a : Int16Array) (idx : Nat → Nat) (lo : Nat)
    (g : Nat → Int16 → Int16) : a.modifyAt idx lo lo g = a :=
  iterRange_self _ lo a

/-- The step `lo` of `modifyAt` comes first. -/
public theorem modifyAt_of_lt (a : Int16Array) (idx : Nat → Nat) {lo hi : Nat} (h : lo < hi)
    (g : Nat → Int16 → Int16) :
    a.modifyAt idx lo hi g = (a.set! (idx lo) (g lo a[idx lo]!)).modifyAt idx (lo + 1) hi g := by
  simp only [modifyAt]; rw [iterRange_of_lt _ h, modifyStep_eq]

/-- The step `hi` of `modifyAt` comes last. -/
public theorem modifyAt_succ (a : Int16Array) (idx : Nat → Nat) {lo hi : Nat} (h : lo ≤ hi)
    (g : Nat → Int16 → Int16) :
    a.modifyAt idx lo (hi + 1) g =
      (a.modifyAt idx lo hi g).set! (idx hi) (g hi (a.modifyAt idx lo hi g)[idx hi]!) := by
  simp only [modifyAt]; rw [iterRange_succ _ h, modifyStep_eq]

/-- `modifyAt` splits at any `mid` between its bounds. -/
public theorem modifyAt_split (a : Int16Array) (idx : Nat → Nat) {lo mid hi : Nat}
    (h₁ : lo ≤ mid) (h₂ : mid ≤ hi) (g : Nat → Int16 → Int16) :
    a.modifyAt idx lo hi g = (a.modifyAt idx lo mid g).modifyAt idx mid hi g :=
  iterRange_split _ h₁ h₂ a

/-- `modifyAt` depends only on the indices and the updates in its range. -/
public theorem modifyAt_congr (a : Int16Array) {idx idx' : Nat → Nat} {lo hi : Nat}
    {g g' : Nat → Int16 → Int16} (hidx : ∀ i, lo ≤ i → i < hi → idx i = idx' i)
    (hg : ∀ i, lo ≤ i → i < hi → g i = g' i) :
    a.modifyAt idx lo hi g = a.modifyAt idx' lo hi g' :=
  iterRange_congr (fun i h₁ h₂ => by
    funext b; simp only [modifyStep, hidx i h₁ h₂, hg i h₁ h₂]) a

private theorem getElem?_modifyAt_of_forall_ne (a : Int16Array) (idx : Nat → Nat)
    {lo hi : Nat} (g : Nat → Int16 → Int16) {p : Nat}
    (hp : ∀ i, lo ≤ i → i < hi → idx i ≠ p) : (a.modifyAt idx lo hi g)[p]? = a[p]? :=
  iterRange_invariant (fun b : Int16Array => b[p]? = a[p]?)
    (fun i h₁ h₂ b hb => by rw [getElem?_modifyStep]; simp [hp i h₁ h₂, hb]) rfl

/-- An element at no index `idx i` of the range is unchanged. -/
public theorem getElem_modifyAt_of_forall_ne (a : Int16Array) (idx : Nat → Nat) {lo hi : Nat}
    (g : Nat → Int16 → Int16) {p : Nat} (hp : ∀ i, lo ≤ i → i < hi → idx i ≠ p)
    (h : p < (a.modifyAt idx lo hi g).size) :
    (a.modifyAt idx lo hi g)[p] = a[p]'(by simpa using h) := by
  have := getElem?_modifyAt_of_forall_ne a idx g hp
  rw [getElem?_pos (a.modifyAt idx lo hi g) p h, getElem?_pos a p (by simpa using h)] at this
  exact Option.some.inj this

private theorem getElem?_modifyAt_idx (a : Int16Array) (idx : Nat → Nat) {lo hi : Nat}
    (g : Nat → Int16 → Int16)
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
public theorem getElem_modifyAt_idx (a : Int16Array) (idx : Nat → Nat) {lo hi : Nat}
    (g : Nat → Int16 → Int16)
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
public theorem modifyAt_succ_of_injOn (a : Int16Array) (idx : Nat → Nat) {lo hi : Nat}
    (h : lo ≤ hi) (g : Nat → Int16 → Int16)
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
private theorem iterRangeRev_modifyStep (a : Int16Array) (idx : Nat → Nat) {lo hi : Nat}
    (g : Nat → Int16 → Int16)
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
public theorem getElem_modifyAt_stride (a : Int16Array) {s : Stride} {n : Nat}
    (hs : s.Fits n a.size) {lo hi : Nat} (hn : hi ≤ n) (g : Nat → Int16 → Int16) {i : Nat}
    (hi₁ : lo ≤ i) (hi₂ : i < hi) :
    (a.modifyAt s.idx lo hi g)[s.idx i]'(by rw [size_modifyAt]; exact hs.idx_lt (by lia)) =
      g i (a[s.idx i]'(hs.idx_lt (by lia))) :=
  getElem_modifyAt_idx a s.idx g
    (fun i _ h₁ j _ h₂ e => hs.idx_inj (by lia) (by lia) e) hi₁ hi₂ _

/-! ### Copies -/

/-- `copySlice` within bounds writes the elements of `src` at the indices `destOff + i`. -/
public theorem copySlice_eq_modifyAt (src : Int16Array) (srcOff : Nat) (dest : Int16Array)
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

/-! ## Two updates at a time -/

private theorem getElem!_set!_of_ne (a : Int16Array) {p q : Nat} (v : Int16) (h : p ≠ q) :
    (a.set! p v)[q]! = a[q]! := by
  by_cases hq : q < a.size
  · rw [getElem!_pos _ q (by simpa using hq), getElem!_pos a q hq, getElem_set!]; simp [h]
  · rw [getElem!_neg _ q (by simpa using hq), getElem!_neg a q hq]

private theorem set!_comm (a : Int16Array) {p q : Nat} (v w : Int16) (h : p ≠ q) :
    (a.set! p v).set! q w = (a.set! q w).set! p v := by
  apply ext_getElem?; intro r
  simp only [getElem?_set!, size_set!]
  by_cases hp : p = r <;> by_cases hq : q = r
  · exact absurd (hp.trans hq.symm) h
  all_goals simp [hp, hq]

private theorem uset_eq_set! (a : Int16Array) (i : USize) (v : Int16) (h) :
    a.uset i v h = a.set! i.toNat v := by
  apply ext_getElem (by simp)
  intro j _ _
  simp only [getElem_uset, getElem_set!]

private theorem set_eq_set! (a : Int16Array) (i : Nat) (v : Int16) (h) :
    a.set i v h = a.set! i v := by
  simp [set!, h]

private theorem getElem!_modifyAt_of_forall_ne (a : Int16Array) (idx : Nat → Nat) {lo hi : Nat}
    (g : Nat → Int16 → Int16) {p : Nat} (hp : ∀ i, lo ≤ i → i < hi → idx i ≠ p) :
    (a.modifyAt idx lo hi g)[p]! = a[p]! := by
  by_cases h : p < a.size
  · rw [getElem!_pos _ p (by simpa using h), getElem!_pos a p h,
      getElem_modifyAt_of_forall_ne _ _ _ hp]
  · rw [getElem!_neg _ p (by simpa using h), getElem!_neg a p h]

private theorem modifyStep_set! (idx : Nat → Nat) (g : Nat → Int16 → Int16) (i : Nat)
    (a : Int16Array) {p : Nat} (hp : idx i ≠ p) (v : Int16) :
    (modifyStep idx g i a).set! p v = modifyStep idx g i (a.set! p v) := by
  rw [modifyStep_eq, modifyStep_eq, getElem!_set!_of_ne _ _ hp.symm, set!_comm _ _ _ hp]

/-- A write at an index of no step commutes with `modifyAt`. -/
private theorem modifyAt_set! (a : Int16Array) (idx : Nat → Nat) {lo hi : Nat}
    (g : Nat → Int16 → Int16) {p : Nat} (hp : ∀ i, lo ≤ i → i < hi → idx i ≠ p) (v : Int16) :
    (a.set! p v).modifyAt idx lo hi g = (a.modifyAt idx lo hi g).set! p v :=
  (apply_iterRange (fun b : Int16Array => b.set! p v)
    (fun i h₁ h₂ b => modifyStep_set! idx g i b (hp i h₁ h₂) v) a).symm

/-! ### Two index maps on one array -/

/-- `a[i]!`, without the panic when `i` is out of bounds, so that the models can run. -/
private def get0 (a : Int16Array) (i : Nat) : Int16 :=
  if h : i < a.size then a[i] else default

private theorem get0_eq (a : Int16Array) (i : Nat) : get0 a i = a[i]! := by
  unfold get0; split
  · rename_i h; rw [getElem!_pos a i h]
  · rename_i h; rw [getElem!_neg a i h]


/-- The step `i` of `modifyAt2`. -/
private def modifyStep2 (ia ib : Nat → Nat) (f g : Nat → Int16 → Int16 → Int16) (i : Nat)
    (a : Int16Array) : Int16Array :=
  (a.set! (ia i) (f i (get0 a (ia i)) (get0 a (ib i)))).set! (ib i)
    (g i (get0 a (ia i)) (get0 a (ib i)))

/--
The array `a` where, for each `i` from `lo` up to `hi - 1`, in this order, `u := a[ia i]!` and
`v := a[ib i]!` are read, and then `f i u v` is written at the index `ia i` and `g i u v` at the
index `ib i`, where each step sees the earlier writes. Indices out of bounds read `default` and are
not written. It is the model of a loop that updates two strides of one array together, such as a
plane rotation of two rows of a matrix. When the two index maps are injective on the range and
never meet, `modifyAt2_eq` gives it as two `modifyAt`s.
-/
public def modifyAt2 (a : Int16Array) (ia ib : Nat → Nat) (lo hi : Nat)
    (f g : Nat → Int16 → Int16 → Int16) : Int16Array :=
  iterRange (modifyStep2 ia ib f g) lo hi a

@[simp, grind =] public theorem size_modifyAt2 (a : Int16Array) (ia ib : Nat → Nat) (lo hi : Nat)
    (f g : Nat → Int16 → Int16 → Int16) : (a.modifyAt2 ia ib lo hi f g).size = a.size :=
  iterRange_invariant (fun b : Int16Array => b.size = a.size)
    (fun _ _ _ b hb => by rw [← hb]; simp [modifyStep2]) rfl

public theorem modifyAt2_of_le (a : Int16Array) (ia ib : Nat → Nat) {lo hi : Nat} (h : hi ≤ lo)
    (f g : Nat → Int16 → Int16 → Int16) : a.modifyAt2 ia ib lo hi f g = a :=
  iterRange_of_le _ h a

@[simp] public theorem modifyAt2_self (a : Int16Array) (ia ib : Nat → Nat) (lo : Nat)
    (f g : Nat → Int16 → Int16 → Int16) : a.modifyAt2 ia ib lo lo f g = a :=
  iterRange_self _ lo a

/-- The step `lo` of `modifyAt2` comes first. -/
public theorem modifyAt2_of_lt (a : Int16Array) (ia ib : Nat → Nat) {lo hi : Nat} (h : lo < hi)
    (f g : Nat → Int16 → Int16 → Int16) :
    a.modifyAt2 ia ib lo hi f g =
      ((a.set! (ia lo) (f lo a[ia lo]! a[ib lo]!)).set! (ib lo)
        (g lo a[ia lo]! a[ib lo]!)).modifyAt2 ia ib (lo + 1) hi f g := by
  rw [modifyAt2, iterRange_of_lt _ h]; simp only [modifyStep2, get0_eq]; rfl

/-- `modifyAt2` splits at any `mid` between its bounds. -/
public theorem modifyAt2_split (a : Int16Array) (ia ib : Nat → Nat) {lo mid hi : Nat}
    (h₁ : lo ≤ mid) (h₂ : mid ≤ hi) (f g : Nat → Int16 → Int16 → Int16) :
    a.modifyAt2 ia ib lo hi f g = (a.modifyAt2 ia ib lo mid f g).modifyAt2 ia ib mid hi f g :=
  iterRange_split _ h₁ h₂ a

/-- `modifyAt2` depends only on the indices and the updates in its range. -/
public theorem modifyAt2_congr (a : Int16Array) {ia ia' ib ib' : Nat → Nat} {lo hi : Nat}
    {f f' g g' : Nat → Int16 → Int16 → Int16}
    (hia : ∀ i, lo ≤ i → i < hi → ia i = ia' i) (hib : ∀ i, lo ≤ i → i < hi → ib i = ib' i)
    (hf : ∀ i, lo ≤ i → i < hi → f i = f' i) (hg : ∀ i, lo ≤ i → i < hi → g i = g' i) :
    a.modifyAt2 ia ib lo hi f g = a.modifyAt2 ia' ib' lo hi f' g' :=
  iterRange_congr (fun i h₁ h₂ => by
    funext b; simp only [modifyStep2, hia i h₁ h₂, hib i h₁ h₂, hf i h₁ h₂, hg i h₁ h₂]) a

/--
When `ia` and `ib` are injective on the range and never meet, each step of `modifyAt2` reads only
elements that no other step writes, so it is the `modifyAt` at `ia` followed by the `modifyAt` at
`ib`, both reading the other elements from `a`.
-/
public theorem modifyAt2_eq (a : Int16Array) {ia ib : Nat → Nat} {lo hi : Nat}
    (f g : Nat → Int16 → Int16 → Int16)
    (hia : ∀ i, lo ≤ i → i < hi → ∀ j, lo ≤ j → j < hi → ia i = ia j → i = j)
    (hib : ∀ i, lo ≤ i → i < hi → ∀ j, lo ≤ j → j < hi → ib i = ib j → i = j)
    (hd : ∀ i, lo ≤ i → i < hi → ∀ j, lo ≤ j → j < hi → ia i ≠ ib j) :
    a.modifyAt2 ia ib lo hi f g =
      (a.modifyAt ia lo hi fun i u => f i u a[ib i]!).modifyAt ib lo hi
        fun i v => g i a[ia i]! v := by
  obtain ⟨d, hd'⟩ : ∃ d, hi - lo = d := ⟨_, rfl⟩
  induction d generalizing lo a with
  | zero =>
    rw [modifyAt2_of_le _ _ _ (by lia), modifyAt_of_le _ _ (by lia), modifyAt_of_le _ _ (by lia)]
  | succ d ih =>
    have hlo : lo < hi := by lia
    have nab : ia lo ≠ ib lo := hd lo (Nat.le_refl _) hlo lo (Nat.le_refl _) hlo
    -- the later steps read neither of the elements that step `lo` writes
    have fa : ∀ i, lo + 1 ≤ i → i < hi → ia i ≠ ia lo := fun i h₁ h₂ e => by
      have := hia i (by lia) h₂ lo (Nat.le_refl _) hlo e; lia
    have fb : ∀ i, lo + 1 ≤ i → i < hi → ib i ≠ ib lo := fun i h₁ h₂ e => by
      have := hib i (by lia) h₂ lo (Nat.le_refl _) hlo e; lia
    have fab : ∀ i, lo + 1 ≤ i → i < hi → ia i ≠ ib lo := fun i h₁ h₂ =>
      hd i (by lia) h₂ lo (Nat.le_refl _) hlo
    have fba : ∀ i, lo + 1 ≤ i → i < hi → ib i ≠ ia lo := fun i h₁ h₂ e =>
      hd lo (Nat.le_refl _) hlo i (by lia) h₂ e.symm
    rw [modifyAt2_of_lt _ _ _ hlo, ih _ (fun i h₁ h₂ j h₃ h₄ => hia i (by lia) h₂ j (by lia) h₄)
      (fun i h₁ h₂ j h₃ h₄ => hib i (by lia) h₂ j (by lia) h₄)
      (fun i h₁ h₂ j h₃ h₄ => hd i (by lia) h₂ j (by lia) h₄) (by lia)]
    rw [modifyAt_of_lt _ _ hlo, modifyAt_of_lt _ _ hlo, getElem!_modifyAt_of_forall_ne _ _ _ fab,
      getElem!_set!_of_ne _ _ nab, ← modifyAt_set! _ _ _ fab]
    refine (congrArg (fun X : Int16Array => X.modifyAt ib (lo + 1) hi _)
      (modifyAt_congr _ (fun _ _ _ => rfl) (fun i h₁ h₂ => ?_))).trans
      (modifyAt_congr _ (fun _ _ _ => rfl) (fun i h₁ h₂ => ?_))
    · funext u
      rw [getElem!_set!_of_ne _ _ (fb i h₁ h₂).symm, getElem!_set!_of_ne _ _ (fba i h₁ h₂).symm]
    · funext v
      rw [getElem!_set!_of_ne _ _ (fab i h₁ h₂).symm, getElem!_set!_of_ne _ _ (fa i h₁ h₂).symm]

/-! ### Two arrays -/

/-- The step `i` of `zipModifyAt`. -/
private def zipStep (ia ib : Nat → Nat) (f g : Nat → Int16 → Int16 → Int16) (i : Nat)
    (x : Int16Array × Int16Array) : Int16Array × Int16Array :=
  (x.1.set! (ia i) (f i (get0 x.1 (ia i)) (get0 x.2 (ib i))),
    x.2.set! (ib i) (g i (get0 x.1 (ia i)) (get0 x.2 (ib i))))

/--
The arrays `a` and `b` where, for each `i` from `lo` up to `hi - 1`, in this order,
`u := a[ia i]!` and `v := b[ib i]!` are read, and then `f i u v` is written at the index `ia i` of
`a` and `g i u v` at the index `ib i` of `b`, where each step sees the earlier writes. Indices out
of bounds read `default` and are not written. It is the model of a loop that updates two arrays
together, such as a plane rotation of two vectors. When the two index maps are injective on the
range, `zipModifyAt_eq` gives it as a `modifyAt` of each array.
-/
public def zipModifyAt (a b : Int16Array) (ia ib : Nat → Nat) (lo hi : Nat)
    (f g : Nat → Int16 → Int16 → Int16) : Int16Array × Int16Array :=
  iterRange (zipStep ia ib f g) lo hi (a, b)

private theorem size_zipModifyAt (a b : Int16Array) (ia ib : Nat → Nat) (lo hi : Nat)
    (f g : Nat → Int16 → Int16 → Int16) :
    (zipModifyAt a b ia ib lo hi f g).1.size = a.size ∧
      (zipModifyAt a b ia ib lo hi f g).2.size = b.size :=
  iterRange_invariant (fun x : Int16Array × Int16Array => x.1.size = a.size ∧ x.2.size = b.size)
    (fun _ _ _ x hx => by simp [zipStep, hx]) ⟨rfl, rfl⟩

@[simp, grind =] public theorem size_zipModifyAt_fst (a b : Int16Array) (ia ib : Nat → Nat)
    (lo hi : Nat) (f g : Nat → Int16 → Int16 → Int16) :
    (zipModifyAt a b ia ib lo hi f g).1.size = a.size :=
  (size_zipModifyAt a b ia ib lo hi f g).1

@[simp, grind =] public theorem size_zipModifyAt_snd (a b : Int16Array) (ia ib : Nat → Nat)
    (lo hi : Nat) (f g : Nat → Int16 → Int16 → Int16) :
    (zipModifyAt a b ia ib lo hi f g).2.size = b.size :=
  (size_zipModifyAt a b ia ib lo hi f g).2

public theorem zipModifyAt_of_le (a b : Int16Array) (ia ib : Nat → Nat) {lo hi : Nat}
    (h : hi ≤ lo) (f g : Nat → Int16 → Int16 → Int16) :
    zipModifyAt a b ia ib lo hi f g = (a, b) :=
  iterRange_of_le _ h _

@[simp] public theorem zipModifyAt_self (a b : Int16Array) (ia ib : Nat → Nat) (lo : Nat)
    (f g : Nat → Int16 → Int16 → Int16) : zipModifyAt a b ia ib lo lo f g = (a, b) :=
  iterRange_self _ lo _

/-- The step `lo` of `zipModifyAt` comes first. -/
public theorem zipModifyAt_of_lt (a b : Int16Array) (ia ib : Nat → Nat) {lo hi : Nat}
    (h : lo < hi) (f g : Nat → Int16 → Int16 → Int16) :
    zipModifyAt a b ia ib lo hi f g =
      zipModifyAt (a.set! (ia lo) (f lo a[ia lo]! b[ib lo]!))
        (b.set! (ib lo) (g lo a[ia lo]! b[ib lo]!)) ia ib (lo + 1) hi f g := by
  rw [zipModifyAt, iterRange_of_lt _ h]; simp only [zipStep, get0_eq]; rfl

/-- `zipModifyAt` splits at any `mid` between its bounds. -/
public theorem zipModifyAt_split (a b : Int16Array) (ia ib : Nat → Nat) {lo mid hi : Nat}
    (h₁ : lo ≤ mid) (h₂ : mid ≤ hi) (f g : Nat → Int16 → Int16 → Int16) :
    zipModifyAt a b ia ib lo hi f g =
      zipModifyAt (zipModifyAt a b ia ib lo mid f g).1 (zipModifyAt a b ia ib lo mid f g).2 ia ib
        mid hi f g :=
  iterRange_split _ h₁ h₂ _

/-- `zipModifyAt` depends only on the indices and the updates in its range. -/
public theorem zipModifyAt_congr (a b : Int16Array) {ia ia' ib ib' : Nat → Nat} {lo hi : Nat}
    {f f' g g' : Nat → Int16 → Int16 → Int16}
    (hia : ∀ i, lo ≤ i → i < hi → ia i = ia' i) (hib : ∀ i, lo ≤ i → i < hi → ib i = ib' i)
    (hf : ∀ i, lo ≤ i → i < hi → f i = f' i) (hg : ∀ i, lo ≤ i → i < hi → g i = g' i) :
    zipModifyAt a b ia ib lo hi f g = zipModifyAt a b ia' ib' lo hi f' g' :=
  iterRange_congr (fun i h₁ h₂ => by
    funext x; simp only [zipStep, hia i h₁ h₂, hib i h₁ h₂, hf i h₁ h₂, hg i h₁ h₂]) _

/--
When `ia` and `ib` are injective on the range, each step of `zipModifyAt` reads only elements that
no other step writes, so it is a `modifyAt` of each array, reading the elements of the other array
from the arrays it started with.
-/
public theorem zipModifyAt_eq (a b : Int16Array) {ia ib : Nat → Nat} {lo hi : Nat}
    (f g : Nat → Int16 → Int16 → Int16)
    (hia : ∀ i, lo ≤ i → i < hi → ∀ j, lo ≤ j → j < hi → ia i = ia j → i = j)
    (hib : ∀ i, lo ≤ i → i < hi → ∀ j, lo ≤ j → j < hi → ib i = ib j → i = j) :
    zipModifyAt a b ia ib lo hi f g =
      (a.modifyAt ia lo hi fun i u => f i u b[ib i]!,
        b.modifyAt ib lo hi fun i v => g i a[ia i]! v) := by
  obtain ⟨d, hd'⟩ : ∃ d, hi - lo = d := ⟨_, rfl⟩
  induction d generalizing lo a b with
  | zero =>
    rw [zipModifyAt_of_le _ _ _ _ (by lia), modifyAt_of_le _ _ (by lia),
      modifyAt_of_le _ _ (by lia)]
  | succ d ih =>
    have hlo : lo < hi := by lia
    have fa : ∀ i, lo + 1 ≤ i → i < hi → ia i ≠ ia lo := fun i h₁ h₂ e => by
      have := hia i (by lia) h₂ lo (Nat.le_refl _) hlo e; lia
    have fb : ∀ i, lo + 1 ≤ i → i < hi → ib i ≠ ib lo := fun i h₁ h₂ e => by
      have := hib i (by lia) h₂ lo (Nat.le_refl _) hlo e; lia
    rw [zipModifyAt_of_lt _ _ _ _ hlo,
      ih _ _ (fun i h₁ h₂ j h₃ h₄ => hia i (by lia) h₂ j (by lia) h₄)
      (fun i h₁ h₂ j h₃ h₄ => hib i (by lia) h₂ j (by lia) h₄) (by lia),
      modifyAt_of_lt _ _ hlo, modifyAt_of_lt _ _ hlo]
    congr 1
    · exact modifyAt_congr _ (fun _ _ _ => rfl) (fun i h₁ h₂ => by
        funext u; rw [getElem!_set!_of_ne _ _ (fb i h₁ h₂).symm])
    · exact modifyAt_congr _ (fun _ _ _ => rfl) (fun i h₁ h₂ => by
        funext v; rw [getElem!_set!_of_ne _ _ (fa i h₁ h₂).symm])

/-! ### Strides -/

/-- The element at the step `i` of the first stride of `modifyAt2`, for disjoint strides. -/
public theorem getElem_modifyAt2_stride_left (a : Int16Array) {sa sb : Stride} {n : Nat}
    (ha : sa.Fits n a.size) (hb : sb.Fits n a.size)
    (hd : ∀ i, i < n → ∀ j, j < n → sa.idx i ≠ sb.idx j) {lo hi : Nat} (hn : hi ≤ n)
    (f g : Nat → Int16 → Int16 → Int16) {i : Nat} (hi₁ : lo ≤ i) (hi₂ : i < hi) :
    (a.modifyAt2 sa.idx sb.idx lo hi f g)[sa.idx i]'(by
        rw [size_modifyAt2]; exact ha.idx_lt (by lia)) =
      f i (a[sa.idx i]'(ha.idx_lt (by lia))) (a[sb.idx i]'(hb.idx_lt (by lia))) := by
  simp only [modifyAt2_eq a (lo := lo) (hi := hi) f g
    (fun i _ h₁ j _ h₂ e => ha.idx_inj (by lia) (by lia) e)
    (fun i _ h₁ j _ h₂ e => hb.idx_inj (by lia) (by lia) e)
    (fun i _ h₁ j _ h₂ => hd i (by lia) j (by lia))]
  rw [getElem_modifyAt_of_forall_ne _ _ _ (fun j _ h₂ e => hd i (by lia) j (by lia) e.symm),
    getElem_modifyAt_stride _ ha hn _ hi₁ hi₂, getElem!_pos a (sb.idx i) (hb.idx_lt (by lia))]

/-- The element at the step `i` of the second stride of `modifyAt2`, for disjoint strides. -/
public theorem getElem_modifyAt2_stride_right (a : Int16Array) {sa sb : Stride} {n : Nat}
    (ha : sa.Fits n a.size) (hb : sb.Fits n a.size)
    (hd : ∀ i, i < n → ∀ j, j < n → sa.idx i ≠ sb.idx j) {lo hi : Nat} (hn : hi ≤ n)
    (f g : Nat → Int16 → Int16 → Int16) {i : Nat} (hi₁ : lo ≤ i) (hi₂ : i < hi) :
    (a.modifyAt2 sa.idx sb.idx lo hi f g)[sb.idx i]'(by
        rw [size_modifyAt2]; exact hb.idx_lt (by lia)) =
      g i (a[sa.idx i]'(ha.idx_lt (by lia))) (a[sb.idx i]'(hb.idx_lt (by lia))) := by
  simp only [modifyAt2_eq a (lo := lo) (hi := hi) f g
    (fun i _ h₁ j _ h₂ e => ha.idx_inj (by lia) (by lia) e)
    (fun i _ h₁ j _ h₂ e => hb.idx_inj (by lia) (by lia) e)
    (fun i _ h₁ j _ h₂ => hd i (by lia) j (by lia))]
  rw [getElem_modifyAt_idx _ _ _ (lo := lo) (hi := hi)
      (fun i _ h₁ j _ h₂ e => hb.idx_inj (by lia) (by lia) e) hi₁ hi₂,
    getElem_modifyAt_of_forall_ne _ _ _ (fun j _ h₂ e => hd j (by lia) i (by lia) e),
    getElem!_pos a (sa.idx i) (ha.idx_lt (by lia))]

/-- The element at the step `i` of the stride of the first array of `zipModifyAt`. -/
public theorem getElem_zipModifyAt_stride_fst (a b : Int16Array) {sa sb : Stride} {n : Nat}
    (ha : sa.Fits n a.size) (hb : sb.Fits n b.size) {lo hi : Nat} (hn : hi ≤ n)
    (f g : Nat → Int16 → Int16 → Int16) {i : Nat} (hi₁ : lo ≤ i) (hi₂ : i < hi) :
    (zipModifyAt a b sa.idx sb.idx lo hi f g).1[sa.idx i]'(by
        rw [size_zipModifyAt_fst]; exact ha.idx_lt (by lia)) =
      f i (a[sa.idx i]'(ha.idx_lt (by lia))) (b[sb.idx i]'(hb.idx_lt (by lia))) := by
  simp only [zipModifyAt_eq a b (lo := lo) (hi := hi) f g
    (fun i _ h₁ j _ h₂ e => ha.idx_inj (by lia) (by lia) e)
    (fun i _ h₁ j _ h₂ e => hb.idx_inj (by lia) (by lia) e)]
  rw [getElem_modifyAt_stride _ ha hn _ hi₁ hi₂, getElem!_pos b (sb.idx i) (hb.idx_lt (by lia))]

/-- The element at the step `i` of the stride of the second array of `zipModifyAt`. -/
public theorem getElem_zipModifyAt_stride_snd (a b : Int16Array) {sa sb : Stride} {n : Nat}
    (ha : sa.Fits n a.size) (hb : sb.Fits n b.size) {lo hi : Nat} (hn : hi ≤ n)
    (f g : Nat → Int16 → Int16 → Int16) {i : Nat} (hi₁ : lo ≤ i) (hi₂ : i < hi) :
    (zipModifyAt a b sa.idx sb.idx lo hi f g).2[sb.idx i]'(by
        rw [size_zipModifyAt_snd]; exact hb.idx_lt (by lia)) =
      g i (a[sa.idx i]'(ha.idx_lt (by lia))) (b[sb.idx i]'(hb.idx_lt (by lia))) := by
  simp only [zipModifyAt_eq a b (lo := lo) (hi := hi) f g
    (fun i _ h₁ j _ h₂ e => ha.idx_inj (by lia) (by lia) e)
    (fun i _ h₁ j _ h₂ e => hb.idx_inj (by lia) (by lia) e)]
  rw [getElem_modifyAt_stride _ hb hn _ hi₁ hi₂, getElem!_pos a (sa.idx i) (ha.idx_lt (by lia))]

namespace InPlace.Tail

variable {n : Nat} {γ : Type w}

private theorem run_congr {t : Tail n γ} {a b : Int16Array} (e : a = b) (ha : a.size = n)
    (hb : b.size = n) : t.run a ha = t.run b hb := by
  subst e; rfl

private theorem run_congr_pair {β : Type v} {k : β → Tail n γ} {x y : β × Int16Array}
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
    (k : β → Tail n γ) (f : Nat → β × Int16Array → β × Int16Array)
    (hf : ∀ j x, (f j x).2.size = x.2.size)
    (hbody : ∀ j hl hj next b a (h : a.size = n),
      (body j hl hj next b).run a h =
        (next (f j.toNat (b, a)).1).run (f j.toNat (b, a)).2 (by rw [hf]; exact h))
    (a : Int16Array) (h : a.size = n) :
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
    have hsucc : (j₀ + 1).toNat = j₀.toNat + 1 := by grind
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
    (k : Unit → Tail n γ) (F : Nat → Int16Array → Int16Array)
    (hF : ∀ j a, (F j a).size = a.size)
    (hbody : ∀ j hl hj next a (h : a.size = n),
      (body j hl hj next ()).run a h = (next ()).run (F j.toNat a) (by rw [hF]; exact h))
    (a : Int16Array) (h : a.size = n) :
    (forInFrom lo hi j₀ hlo () body k).run a h =
      (k ()).run (iterRange F j₀.toNat hi.toNat a)
        (iterRange_invariant (fun b => b.size = n) (fun _ _ _ b hb => (hF _ b).trans hb) h) := by
  rw [run_forInFrom lo hi j₀ hlo () body k (fun j x => ((), F j x.2)) (fun j x => hF j x.2)
    (fun j hl hj next _ a h => hbody j hl hj next a h)]
  exact run_congr (apply_iterRange Prod.snd (fun _ _ _ _ => rfl) _) _ _

private theorem run_readThen_writeThen (e : USize) (idx : Nat) (he : e.toNat = idx)
    (p : e.toNat < n) (g : Int16 → Int16) (k : Tail n γ) (a : Int16Array) (h : a.size = n) :
    (readThen e p fun v => writeThen e p (g v) k).run a h =
      k.run (modifyStep (fun _ => idx) (fun _ => g) 0 a) (by
        rw [← h]; unfold modifyStep; split <;> simp) := by
  subst he
  simp only [run_readThen, run_writeThen, modifyStep, show e.toNat < a.size by lia, ↓reduceDIte]

private theorem run_writeThen' (e : USize) (idx : Nat) (he : e.toNat = idx)
    (p : e.toNat < n) (v : Int16) (k : Tail n γ) (a : Int16Array) (h : a.size = n) :
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
    (g : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat → Int16 → Int16)
    (G : Nat → Int16 → Int16) (hg : ∀ j hl hj v, g j hl hj v = G j.toNat v)
    (k : Unit → Tail n γ) (a : Int16Array) (h : a.size = n) :
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
    (g : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat → Int16) (G : Nat → Int16)
    (hg : ∀ j hl hj, g j hl hj = G j.toNat) (k : Unit → Tail n γ) (a : Int16Array)
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

private theorem run_modify2_step (ea eb : USize) (ia ib : Nat) (hea : ea.toNat = ia)
    (heb : eb.toNat = ib) (pa : ea.toNat < n) (pb : eb.toNat < n)
    (f g : Int16 → Int16 → Int16)
    (k : Tail n γ) (a : Int16Array) (h : a.size = n) :
    (readThen ea pa fun u => readThen eb pb fun v =>
        writeThen ea pa (f u v) (writeThen eb pb (g u v) k)).run a h =
      k.run (modifyStep2 (fun _ => ia) (fun _ => ib) (fun _ => f) (fun _ => g) 0 a) (by
        rw [← h]; simp [modifyStep2]) := by
  subst hea heb
  simp only [run_readThen, run_writeThen]
  refine run_congr ?_ _ _
  simp only [modifyStep2, get0_eq, set_eq_set!, getElem!_pos a ea.toNat (by lia),
    getElem!_pos a eb.toNat (by lia)]

/--
Runs the loop `for j in lo...hi do let u := a[ea j]; let v := a[eb j]; a[ea j] := f u v;
a[eb j] := g u v` of the `inplace` notation, from the step `j₀`, where the values of the indices
`ea j` and `eb j` are `ia j.toNat` and `ib j.toNat`, and `f` and `g` may use the bounds of `j`: it
maps the array by `modifyAt2 ia ib j₀.toNat hi.toNat F G`, and then runs `k`.
-/
public theorem run_forInFrom_modify2 (lo hi j₀ : USize) (hlo : lo.toNat ≤ j₀.toNat)
    (ea eb : USize → USize) (ia ib : Nat → Nat)
    (hea : ∀ j : USize, lo.toNat ≤ j.toNat → j.toNat < hi.toNat → (ea j).toNat = ia j.toNat)
    (heb : ∀ j : USize, lo.toNat ≤ j.toNat → j.toNat < hi.toNat → (eb j).toNat = ib j.toNat)
    (pa : ∀ j : USize, lo.toNat ≤ j.toNat → j.toNat < hi.toNat → (ea j).toNat < n)
    (pb : ∀ j : USize, lo.toNat ≤ j.toNat → j.toNat < hi.toNat → (eb j).toNat < n)
    (f g : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat → Int16 → Int16 → Int16)
    (F G : Nat → Int16 → Int16 → Int16) (hf : ∀ j hl hj u v, f j hl hj u v = F j.toNat u v)
    (hg : ∀ j hl hj u v, g j hl hj u v = G j.toNat u v) (k : Unit → Tail n γ) (a : Int16Array)
    (h : a.size = n) :
    (forInFrom lo hi j₀ hlo ()
        (fun j hl hj next _ => readThen (ea j) (pa j hl hj) fun u =>
          readThen (eb j) (pb j hl hj) fun v =>
            writeThen (ea j) (pa j hl hj) (f j hl hj u v)
              (writeThen (eb j) (pb j hl hj) (g j hl hj u v) (next ()))) k).run a h =
      (k ()).run (a.modifyAt2 ia ib j₀.toNat hi.toNat F G) (by rw [size_modifyAt2]; exact h) := by
  rw [run_forInFrom_unit lo hi j₀ hlo _ k (modifyStep2 ia ib F G)
    (fun _ b => by simp [modifyStep2])]
  · rfl
  · intro j hl hj next a h
    simp only [hf, hg]
    rw [run_modify2_step (ea j) (eb j) _ _ (hea j hl hj) (heb j hl hj)]
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
    (k : β → Tail n γ) (f : Nat → β × Int16Array → β × Int16Array)
    (hf : ∀ j x, (f j x).2.size = x.2.size)
    (hbody : ∀ j hl hj next b a (h : a.size = n),
      (body j hl hj next b).run a h =
        (next (f j.toNat (b, a)).1).run (f j.toNat (b, a)).2 (by rw [hf]; exact h))
    (a : Int16Array) (h : a.size = n) :
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
    have hpred : (j₀ - 1).toNat = j₀.toNat - 1 := by grind
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
    (k : Unit → Tail n γ) (F : Nat → Int16Array → Int16Array)
    (hF : ∀ j a, (F j a).size = a.size)
    (hbody : ∀ j hl hj next a (h : a.size = n),
      (body j hl hj next ()).run a h = (next ()).run (F j.toNat a) (by rw [hF]; exact h))
    (a : Int16Array) (h : a.size = n) :
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
    (g : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat → Int16 → Int16)
    (G : Nat → Int16 → Int16) (hg : ∀ j hl hj v, g j hl hj v = G j.toNat v)
    (k : Unit → Tail n γ) (a : Int16Array) (h : a.size = n) :
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
    (g : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat → Int16) (G : Nat → Int16)
    (hg : ∀ j hl hj, g j hl hj = G j.toNat) (k : Unit → Tail n γ) (a : Int16Array)
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

namespace InPlace

/--
`zipForInFrom` runs as `zipModifyAt`, from its step `j₀`, when the values of the indices `ea j`
and `eb j` are `ia j.toNat` and `ib j.toNat`.
-/
public theorem run_zipForInFrom {n m : Nat} (hi j₀ : USize) (ea eb : USize → USize)
    (ia ib : Nat → Nat)
    (hia : ∀ j : USize, j.toNat < hi.toNat → (ea j).toNat = ia j.toNat)
    (hib : ∀ j : USize, j.toNat < hi.toNat → (eb j).toNat = ib j.toNat)
    (hea : ∀ j : USize, j.toNat < hi.toNat → (ea j).toNat < n)
    (heb : ∀ j : USize, j.toNat < hi.toNat → (eb j).toNat < m)
    (f g : Int16 → Int16 → Int16) (a b : Int16Array) (ha : a.size = n) (hb : b.size = m) :
    zipForInFrom hi ea eb hea heb f g j₀ a b ha hb =
      zipModifyAt a b ia ib j₀.toNat hi.toNat (fun _ => f) (fun _ => g) := by
  obtain ⟨d, hd⟩ : ∃ d, hi.toNat - j₀.toNat = d := ⟨_, rfl⟩
  induction d generalizing j₀ a b with
  | zero =>
    have hj : ¬j₀ < hi := by rw [USize.lt_iff_toNat_lt]; lia
    rw [zipForInFrom_eq, dite_eq_right_of_eq_false (eq_false hj),
      zipModifyAt_of_le _ _ _ _ (by lia)]
  | succ d ih =>
    have hj : j₀ < hi := by rw [USize.lt_iff_toNat_lt]; lia
    have hj' : j₀.toNat < hi.toNat := USize.lt_iff_toNat_lt.1 hj
    have hsucc : (j₀ + 1).toNat = j₀.toNat + 1 := by clear ih hia hib hea heb; grind
    have hpa : ia j₀.toNat < a.size := by rw [← hia j₀ hj', ha]; exact hea j₀ hj'
    have hpb : ib j₀.toNat < b.size := by rw [← hib j₀ hj', hb]; exact heb j₀ hj'
    rw [zipForInFrom_eq, dite_eq_left_of_eq_true (eq_true hj), ih _ _ _ _ _ (by rw [hsucc]; lia),
      zipModifyAt_of_lt _ _ _ _ hj', hsucc, getElem!_pos a _ hpa, getElem!_pos b _ hpb]
    simp only [uset_eq_set!, uget_eq_getElem, hia j₀ hj', hib j₀ hj']

end InPlace

/-! ## Strided loops

The loops `modifyStride`, `modifyStride2` and `zipModifyStride` update the elements at the first
`n` steps of strides. Each makes its arrays exclusive once, before it starts, and then updates them
in place without checks. Each is specified by a `modifyAt` model, by `@[csimp]`, and runs as the
model when an array has `USize.size` elements or more, which no array in memory has.
-/

private theorem toNat_toUSize_of_fits {s : Stride} {n size : Nat} (h : s.Fits n size)
    (hs : size < USize.size) : n.toUSize.toNat = n := by
  have := h.le_size
  simp only [Nat.toUSize_eq, USize.toNat_ofNat']
  exact Nat.mod_eq_of_lt (by lia)

/--
`a` with `f` applied to the element at each of the first `n` steps of the stride `s`, which fits
in `a`: the model `a.modifyAt s.idx 0 n fun _ => f`, run as one loop.
-/
public def modifyStride (a : Int16Array) (s : Stride) (n : Nat) (f : Int16 → Int16)
    (_h : s.Fits n a.size) : Int16Array :=
  a.modifyAt s.idx 0 n fun _ => f

public theorem modifyStride_eq (a : Int16Array) (s : Stride) (n : Nat) (f : Int16 → Int16)
    (h : s.Fits n a.size) : a.modifyStride s n f h = a.modifyAt s.idx 0 n fun _ => f := by
  rw [modifyStride]

@[simp, grind =] public theorem size_modifyStride (a : Int16Array) (s : Stride) (n : Nat)
    (f : Int16 → Int16) (h : s.Fits n a.size) : (a.modifyStride s n f h).size = a.size := by
  rw [modifyStride_eq, size_modifyAt]

/--
`modifyStride` as a model, out of line, so that its closure doesn't stop the loop from being
specialized.
-/
@[noinline]
private def modifyStrideModel (a : Int16Array) (s : Stride) (n : Nat) (f : Int16 → Int16) :
    Int16Array :=
  a.modifyAt s.idx 0 n fun _ => f

/-- For internal use only. -/
@[inline]
public def modifyStrideImpl (a : Int16Array) (s : Stride) (n : Nat) (f : Int16 → Int16)
    (h : s.Fits n a.size) : Int16Array :=
  if hs : a.size < USize.size then
    let o := s.off.toUSize
    let c := s.inc.toUSize
    have p : ∀ j : USize, j.toNat < n.toUSize.toNat → (o + c * j).toNat < a.size := fun _ hj =>
      Stride.toNat_idx_toUSize_lt h hs (by rw [toNat_toUSize_of_fits h hs] at hj; exact hj)
    a.runInPlaceThenOf a.size rfl <|
      InPlace.Tail.forIn 0 n.toUSize ()
        (fun j _ hj next _ =>
          InPlace.Tail.readThen (o + c * j) (p j hj) fun v =>
            InPlace.Tail.writeThen (o + c * j) (p j hj) (f v) (next ()))
        fun _ => InPlace.Tail.done () fun _ a _ => a
  else
    modifyStrideModel a s n f

@[csimp] public theorem modifyStride_eq_modifyStrideImpl : @modifyStride = @modifyStrideImpl := by
  funext a s n f h
  unfold modifyStrideImpl modifyStrideModel
  split
  · rename_i hs
    rw [runInPlaceThenOf_eq, InPlace.Tail.forIn,
      InPlace.Tail.run_forInFrom_modify (idx := s.idx) (G := fun _ v => f v)
        (he := fun j _ hj => Stride.toNat_idx_toUSize h hs
          (by rw [toNat_toUSize_of_fits h hs] at hj; exact hj))
        (hg := fun _ _ _ _ => rfl),
      InPlace.Tail.run_done, toNat_toUSize_of_fits h hs]
    rfl
  · rfl

/--
`a` with, at each of the first `n` steps `i` of the strides `sa` and `sb`, which fit in `a`,
`f u v` written at `sa.idx i` and `g u v` at `sb.idx i`, where `u` and `v` are the elements there:
the model `a.modifyAt2 sa.idx sb.idx 0 n (fun _ => f) (fun _ => g)`, run as one loop, such as a
plane rotation of two rows of a matrix. `modifyAt2_eq` gives the elements when the two strides
never meet, which `Stride.idx_ne_idx_of_same_inc` and `Stride.idx_ne_idx_of_lt_off` give.
-/
public def modifyStride2 (a : Int16Array) (sa sb : Stride) (n : Nat)
    (f g : Int16 → Int16 → Int16) (_ha : sa.Fits n a.size) (_hb : sb.Fits n a.size) :
    Int16Array :=
  a.modifyAt2 sa.idx sb.idx 0 n (fun _ => f) (fun _ => g)

public theorem modifyStride2_eq (a : Int16Array) (sa sb : Stride) (n : Nat)
    (f g : Int16 → Int16 → Int16) (ha : sa.Fits n a.size) (hb : sb.Fits n a.size) :
    a.modifyStride2 sa sb n f g ha hb =
      a.modifyAt2 sa.idx sb.idx 0 n (fun _ => f) (fun _ => g) := by
  rw [modifyStride2]

@[simp, grind =] public theorem size_modifyStride2 (a : Int16Array) (sa sb : Stride) (n : Nat)
    (f g : Int16 → Int16 → Int16) (ha : sa.Fits n a.size) (hb : sb.Fits n a.size) :
    (a.modifyStride2 sa sb n f g ha hb).size = a.size := by
  rw [modifyStride2_eq, size_modifyAt2]

/-- `modifyStride2` as a model, out of line, like `modifyStrideModel`. -/
@[noinline]
private def modifyStride2Model (a : Int16Array) (sa sb : Stride) (n : Nat)
    (f g : Int16 → Int16 → Int16) : Int16Array :=
  a.modifyAt2 sa.idx sb.idx 0 n (fun _ => f) (fun _ => g)

/-- For internal use only. -/
@[inline]
public def modifyStride2Impl (a : Int16Array) (sa sb : Stride) (n : Nat)
    (f g : Int16 → Int16 → Int16) (ha : sa.Fits n a.size) (hb : sb.Fits n a.size) :
    Int16Array :=
  if hs : a.size < USize.size then
    let oa := sa.off.toUSize
    let ca := sa.inc.toUSize
    let ob := sb.off.toUSize
    let cb := sb.inc.toUSize
    have pa : ∀ j : USize, j.toNat < n.toUSize.toNat → (oa + ca * j).toNat < a.size := fun _ hj =>
      Stride.toNat_idx_toUSize_lt ha hs (by rw [toNat_toUSize_of_fits ha hs] at hj; exact hj)
    have pb : ∀ j : USize, j.toNat < n.toUSize.toNat → (ob + cb * j).toNat < a.size := fun _ hj =>
      Stride.toNat_idx_toUSize_lt hb hs (by rw [toNat_toUSize_of_fits ha hs] at hj; exact hj)
    a.runInPlaceThenOf a.size rfl <|
      InPlace.Tail.forIn 0 n.toUSize ()
        (fun j _ hj next _ =>
          InPlace.Tail.readThen (oa + ca * j) (pa j hj) fun u =>
            InPlace.Tail.readThen (ob + cb * j) (pb j hj) fun v =>
              InPlace.Tail.writeThen (oa + ca * j) (pa j hj) (f u v)
                (InPlace.Tail.writeThen (ob + cb * j) (pb j hj) (g u v) (next ())))
        fun _ => InPlace.Tail.done () fun _ a _ => a
  else
    modifyStride2Model a sa sb n f g

@[csimp] public theorem modifyStride2_eq_modifyStride2Impl :
    @modifyStride2 = @modifyStride2Impl := by
  funext a sa sb n f g ha hb
  unfold modifyStride2Impl modifyStride2Model
  split
  · rename_i hs
    rw [runInPlaceThenOf_eq, InPlace.Tail.forIn,
      InPlace.Tail.run_forInFrom_modify2 (ia := sa.idx) (ib := sb.idx) (F := fun _ => f)
        (G := fun _ => g)
        (hea := fun j _ hj => Stride.toNat_idx_toUSize ha hs
          (by rw [toNat_toUSize_of_fits ha hs] at hj; exact hj))
        (heb := fun j _ hj => Stride.toNat_idx_toUSize hb hs
          (by rw [toNat_toUSize_of_fits ha hs] at hj; exact hj))
        (hf := fun _ _ _ _ _ => rfl) (hg := fun _ _ _ _ _ => rfl),
      InPlace.Tail.run_done, toNat_toUSize_of_fits ha hs]
    rfl
  · rfl

/--
The arrays `a` and `b` with, at each of the first `n` steps `i` of the strides `sa`, which fits in
`a`, and `sb`, which fits in `b`, `f u v` written at `sa.idx i` in `a` and `g u v` at `sb.idx i`
in `b`, where `u` and `v` are the elements there: the model
`zipModifyAt a b sa.idx sb.idx 0 n (fun _ => f) (fun _ => g)`, run as one loop, such as a plane
rotation of two vectors. `a` and `b` may be the same array: the model treats them as two arrays,
and so does the loop, which then copies one of them.
-/
public def zipModifyStride (a b : Int16Array) (sa sb : Stride) (n : Nat)
    (f g : Int16 → Int16 → Int16) (_ha : sa.Fits n a.size) (_hb : sb.Fits n b.size) :
    Int16Array × Int16Array :=
  zipModifyAt a b sa.idx sb.idx 0 n (fun _ => f) (fun _ => g)

public theorem zipModifyStride_eq (a b : Int16Array) (sa sb : Stride) (n : Nat)
    (f g : Int16 → Int16 → Int16) (ha : sa.Fits n a.size) (hb : sb.Fits n b.size) :
    zipModifyStride a b sa sb n f g ha hb =
      zipModifyAt a b sa.idx sb.idx 0 n (fun _ => f) (fun _ => g) := by
  rw [zipModifyStride]

@[simp, grind =] public theorem size_zipModifyStride_fst (a b : Int16Array) (sa sb : Stride)
    (n : Nat) (f g : Int16 → Int16 → Int16) (ha : sa.Fits n a.size) (hb : sb.Fits n b.size) :
    (zipModifyStride a b sa sb n f g ha hb).1.size = a.size := by
  rw [zipModifyStride_eq, size_zipModifyAt_fst]

@[simp, grind =] public theorem size_zipModifyStride_snd (a b : Int16Array) (sa sb : Stride)
    (n : Nat) (f g : Int16 → Int16 → Int16) (ha : sa.Fits n a.size) (hb : sb.Fits n b.size) :
    (zipModifyStride a b sa sb n f g ha hb).2.size = b.size := by
  rw [zipModifyStride_eq, size_zipModifyAt_snd]

/-- `zipModifyStride` as a model, out of line, like `modifyStrideModel`. -/
@[noinline]
private def zipModifyStrideModel (a b : Int16Array) (sa sb : Stride) (n : Nat)
    (f g : Int16 → Int16 → Int16) : Int16Array × Int16Array :=
  zipModifyAt a b sa.idx sb.idx 0 n (fun _ => f) (fun _ => g)

/-- For internal use only. -/
@[inline]
public def zipModifyStrideImpl (a b : Int16Array) (sa sb : Stride) (n : Nat)
    (f g : Int16 → Int16 → Int16) (ha : sa.Fits n a.size) (hb : sb.Fits n b.size) :
    Int16Array × Int16Array :=
  if hs : a.size < USize.size ∧ b.size < USize.size then
    let oa := sa.off.toUSize
    let ca := sa.inc.toUSize
    let ob := sb.off.toUSize
    let cb := sb.inc.toUSize
    have pa : ∀ j : USize, j.toNat < n.toUSize.toNat → (oa + ca * j).toNat < a.size := fun _ hj =>
      Stride.toNat_idx_toUSize_lt ha hs.1 (by rw [toNat_toUSize_of_fits ha hs.1] at hj; exact hj)
    have pb : ∀ j : USize, j.toNat < n.toUSize.toNat → (ob + cb * j).toNat < b.size := fun _ hj =>
      Stride.toNat_idx_toUSize_lt hb hs.2 (by rw [toNat_toUSize_of_fits ha hs.1] at hj; exact hj)
    InPlace.zipForInFrom n.toUSize (fun j => oa + ca * j) (fun j => ob + cb * j) pa pb f g 0 a b
      rfl rfl
  else
    zipModifyStrideModel a b sa sb n f g

@[csimp] public theorem zipModifyStride_eq_zipModifyStrideImpl :
    @zipModifyStride = @zipModifyStrideImpl := by
  funext a b sa sb n f g ha hb
  unfold zipModifyStrideImpl zipModifyStrideModel
  split
  · rename_i hs
    rw [InPlace.run_zipForInFrom (ia := sa.idx) (ib := sb.idx)
        (hia := fun j hj => Stride.toNat_idx_toUSize ha hs.1
          (by rw [toNat_toUSize_of_fits ha hs.1] at hj; exact hj))
        (hib := fun j hj => Stride.toNat_idx_toUSize hb hs.2
          (by rw [toNat_toUSize_of_fits ha hs.1] at hj; exact hj)),
      toNat_toUSize_of_fits ha hs.1]
    rfl
  · rfl

end Int16Array

end ScalarArray
