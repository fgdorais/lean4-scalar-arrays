/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ScalarArray.ISize.Program
import all ScalarArray.Internal
import all ScalarArray.ISize.Basic
import all ScalarArray.ISize.Array
import all ScalarArray.ISize.Slice
import all ScalarArray.ISize.Lemmas
import Init.Data.Iterators.Lemmas.Basic
import Init.Data.Slice.InternalLemmas

/-!
# In-place writes on `ISizeArray`

Writes through slices, and folds that write each element back in place.
-/

namespace ScalarArray

namespace ISizeArray

/-! ## Writes through slices -/

namespace Slice

/--
Replaces the element at index `i` of the slice, counted from the start of the slice, in the
underlying array. The array is updated in place when neither it nor the slice is shared, so a slice
taken from an array that is no longer used writes into that array. `s.array` gives back the whole
array afterwards.
-/
@[inline, expose]
public def set (s : ISizeArray.Slice) (i : Nat) (v : ISize)
    (h : i < s.size := by get_elem_tactic) : ISizeArray.Slice :=
  ⟨{ s.internalRepresentation with
      array := s.array.set (s.start + i) v
        (by have := s.stop_le_array_size; rw [size_eq] at h; lia)
      stop_le_array_size := by rw [size_set]; exact s.stop_le_array_size }⟩

@[simp] public theorem array_set (s : ISizeArray.Slice) (i : Nat) (v : ISize) (h) :
    (s.set i v h).array =
      s.array.set (s.start + i) v (by have := s.stop_le_array_size; rw [size_eq] at h; lia) :=
  rfl

@[simp] public theorem start_set (s : ISizeArray.Slice) (i : Nat) (v : ISize) (h) :
    (s.set i v h).start = s.start := rfl

@[simp] public theorem stop_set (s : ISizeArray.Slice) (i : Nat) (v : ISize) (h) :
    (s.set i v h).stop = s.stop := rfl

@[simp] public theorem size_set (s : ISizeArray.Slice) (i : Nat) (v : ISize) (h) :
    (s.set i v h).size = s.size := rfl

@[simp] public theorem getElem_set (s : ISizeArray.Slice) (i : Nat) (v : ISize) (h) (j : Nat)
    (hj) :
    (s.set i v h)[j]'hj = if i = j then v else s[j]'(by rw [size_set] at hj; exact hj) := by
  simp only [getElem_eq, array_set, ISizeArray.getElem_set, start_set]
  congr 1
  simp

@[simp] public theorem copy_set (s : ISizeArray.Slice) (i : Nat) (v : ISize) (h) :
    (s.set i v h).copy = s.copy.set i v (by simpa using h) := by
  apply ext_getElem
  · simp
  · intro j _ _
    simp only [getElem_copy, getElem_set, ISizeArray.getElem_set]

/--
Replaces the element at index `i` of the slice in the underlying array, like `set`. If `i` is out of
bounds, the slice is returned unmodified.
-/
@[inline, expose]
public def set! (s : ISizeArray.Slice) (i : Nat) (v : ISize) : ISizeArray.Slice :=
  if h : i < s.size then s.set i v h else s

public theorem set!_eq (s : ISizeArray.Slice) (i : Nat) (v : ISize) :
    s.set! i v = if h : i < s.size then s.set i v h else s := rfl

@[simp] public theorem set!_eq_set (s : ISizeArray.Slice) (i : Nat) (v : ISize)
    (h : i < s.size) : s.set! i v = s.set i v h := by
  simp [set!, h]

/--
Applies `f` to the element at index `i` of the slice, in place like `set`. If `i` is out of bounds,
the slice is returned unmodified.
-/
@[inline, expose]
public def modify (s : ISizeArray.Slice) (i : Nat) (f : ISize → ISize) : ISizeArray.Slice :=
  if h : i < s.size then s.set i (f s[i]) h else s

public theorem modify_eq (s : ISizeArray.Slice) (i : Nat) (f : ISize → ISize) :
    s.modify i f = if h : i < s.size then s.set i (f s[i]) h else s := rfl

@[simp] public theorem start_modify (s : ISizeArray.Slice) (i : Nat) (f : ISize → ISize) :
    (s.modify i f).start = s.start := by
  unfold modify; split <;> rfl

@[simp] public theorem stop_modify (s : ISizeArray.Slice) (i : Nat) (f : ISize → ISize) :
    (s.modify i f).stop = s.stop := by
  unfold modify; split <;> rfl

@[simp] public theorem size_modify (s : ISizeArray.Slice) (i : Nat) (f : ISize → ISize) :
    (s.modify i f).size = s.size := by
  unfold modify; split <;> rfl

@[simp] public theorem getElem_modify (s : ISizeArray.Slice) (i : Nat) (f : ISize → ISize)
    (j : Nat) (hj) :
    (s.modify i f)[j]'hj =
      have hj' : j < s.size := by rw [size_modify] at hj; exact hj
      if i = j then f s[j] else s[j] := by
  have := size_modify s i f
  by_cases h : i < s.size
  · have e : s.modify i f = s.set i (f s[i]) h := by simp [modify_eq, h]
    rw [getElem_congr_coll e, getElem_set]
    split
    · subst_vars; rfl
    · rfl
  · have e : s.modify i f = s := by simp [modify_eq, h]
    rw [getElem_congr_coll e]
    split
    · lia
    · rfl

/-- Swaps the elements at indices `i` and `j` of the slice, in place like `set`. -/
@[inline, expose]
public def swap (s : ISizeArray.Slice) (i j : Nat) (hi : i < s.size := by get_elem_tactic)
    (hj : j < s.size := by get_elem_tactic) : ISizeArray.Slice :=
  -- Both reads come before the first write, so that `s` is no longer used when it is written.
  let x := s[i]
  let y := s[j]
  (s.set i y hi).set j x (by simpa using hj)

public theorem swap_eq (s : ISizeArray.Slice) (i j : Nat) (hi hj) :
    s.swap i j hi hj = (s.set i s[j] hi).set j s[i] (by simpa using hj) := rfl

@[simp] public theorem start_swap (s : ISizeArray.Slice) (i j : Nat) (hi hj) :
    (s.swap i j hi hj).start = s.start := rfl

@[simp] public theorem stop_swap (s : ISizeArray.Slice) (i j : Nat) (hi hj) :
    (s.swap i j hi hj).stop = s.stop := rfl

@[simp] public theorem size_swap (s : ISizeArray.Slice) (i j : Nat) (hi hj) :
    (s.swap i j hi hj).size = s.size := rfl

@[simp] public theorem getElem_swap (s : ISizeArray.Slice) (i j : Nat) (hi hj) (k : Nat) (hk) :
    (s.swap i j hi hj)[k]'hk =
      if j = k then s[i] else if i = k then s[j] else s[k]'(by rw [size_swap] at hk; exact hk) := by
  rw [getElem_congr_coll (swap_eq ..), getElem_set, getElem_set]

/-- The loop of `reverse`: swaps the elements at `i` and `j`, then moves both towards the middle. -/
@[expose]
public def reverse.loop (s : ISizeArray.Slice) (i j : Nat) (hj : j < s.size) :
    ISizeArray.Slice :=
  if h : i < j then reverse.loop (s.swap i j (by lia)) (i + 1) (j - 1) (by simp; lia) else s
termination_by j - i

private unsafe def reverseImpl (s : ISizeArray.Slice) : ISizeArray.Slice :=
  match s with
  | ⟨⟨a, start, stop, h, _⟩⟩ =>
    if start < stop then
      ⟨⟨loop a.ensureExclusive start.toUSize (stop.toUSize - 1), start, stop, h, lcProof⟩⟩
    else
      s
where
  loop (a : ISizeArray) (i j : USize) : ISizeArray :=
    if i < j then
      let x := a.uget i lcProof
      let y := a.uget j lcProof
      loop (setUnsafe (setUnsafe a i y) j x) (i + 1) (j - 1)
    else
      a

/--
Reverses the order of the elements of the slice, in place like `set`. The array is made exclusive
once, before the loop, which then stores without checks.
-/
@[implemented_by reverseImpl, expose]
public def reverse (s : ISizeArray.Slice) : ISizeArray.Slice :=
  if h : 0 < s.size then reverse.loop s 0 (s.size - 1) (by lia) else s

private theorem reverse_loop_props (s : ISizeArray.Slice) (i j : Nat) (hj : j < s.size) :
    (reverse.loop s i j hj).start = s.start ∧ (reverse.loop s i j hj).stop = s.stop := by
  fun_induction reverse.loop s i j hj with
  | case1 s i j hj h ih => simpa using ih
  | case2 => exact ⟨rfl, rfl⟩

@[simp] public theorem start_reverse (s : ISizeArray.Slice) : s.reverse.start = s.start := by
  rw [reverse]; split
  · exact (reverse_loop_props ..).1
  · rfl

@[simp] public theorem stop_reverse (s : ISizeArray.Slice) : s.reverse.stop = s.stop := by
  rw [reverse]; split
  · exact (reverse_loop_props ..).2
  · rfl

@[simp] public theorem size_reverse (s : ISizeArray.Slice) : s.reverse.size = s.size := by
  rw [size_eq, size_eq, start_reverse, stop_reverse]

private theorem size_reverse_loop (s : ISizeArray.Slice) (i j : Nat) (hj : j < s.size) :
    (reverse.loop s i j hj).size = s.size := by
  rw [size_eq, size_eq, (reverse_loop_props ..).1, (reverse_loop_props ..).2]

private theorem getElem_reverse_loop (s : ISizeArray.Slice) (i j : Nat) (hj : j < s.size)
    (hij : i ≤ j + 1) (k : Nat) (hk : k < s.size) :
    (reverse.loop s i j hj)[k]'(by rw [size_reverse_loop]; exact hk) =
      if h : i ≤ k ∧ k ≤ j then s[i + j - k]'(by lia) else s[k] := by
  fun_induction reverse.loop s i j hj with
  | case1 s i j hj h ih =>
    have e : reverse.loop s i j hj =
        reverse.loop (s.swap i j (by lia)) (i + 1) (j - 1) (by simp; lia) := by
      rw [reverse.loop]; simp [h]
    rw [getElem_congr_coll e, ih (by lia) (by simpa using hk)]
    simp only [getElem_swap]
    repeat' split
    all_goals first | lia | rfl | (congr 1; lia)
  | case2 s i j hj h =>
    have e : reverse.loop s i j hj = s := by rw [reverse.loop]; simp [h]
    rw [getElem_congr_coll e]
    split
    · congr 1; lia
    · rfl

@[simp] public theorem getElem_reverse (s : ISizeArray.Slice) (i : Nat) (h) :
    s.reverse[i]'h = s[s.size - 1 - i]'(by simp at h; lia) := by
  have h' : i < s.size := by simpa using h
  have hs : 0 < s.size := by lia
  simp only [reverse, hs, ↓reduceDIte]
  rw [getElem_reverse_loop _ _ _ _ (by lia) _ h']
  simp only [Nat.zero_le, true_and, Nat.zero_add]
  split
  · congr 1
  · lia

@[simp] public theorem toList_copy_reverse (s : ISizeArray.Slice) :
    s.reverse.copy.toList = s.copy.toList.reverse := by
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    simp only [getElem_toList, getElem_copy, getElem_reverse, List.getElem_reverse]
    congr 1
    simp

/-! ## In-place folds over slices -/

/-- The loop of `foldlInPlace`, over `Nat` indices. -/
@[expose]
public def foldlInPlace.loop {β : Type v} (n : Nat)
    (f : (k : USize) → k.toNat < n → ISize → β → ISize × β)
    (s : ISizeArray.Slice) (hs : s.size = n) (k : Nat) (b : β) : ISizeArray.Slice × β :=
  if hk : k < n then
    have hk' : k.toUSize.toNat < n := by
      rw [Nat.toUSize_eq, USize.toNat_ofNat']
      exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) hk
    let p := f k.toUSize hk' (s[k]'(by lia)) b
    foldlInPlace.loop n f (s.set k p.1 (by lia)) (by simpa using hs) (k + 1) p.2
  else
    (s, b)
termination_by n - k

private theorem toNat_add_of_window {off len j : USize} {n : Nat} (hn : n < USize.size)
    (hw : off.toNat + len.toNat ≤ n) (hj : j.toNat < len.toNat) :
    (off + j).toNat = off.toNat + j.toNat := by
  rw [USize.toNat_add]
  exact Nat.mod_eq_of_lt (by have : USize.size = 2 ^ System.Platform.numBits := rfl; lia)

private theorem toNat_succ_of_lt' {j len : USize} (h : j.toNat < len.toNat) :
    (j + 1).toNat = j.toNat + 1 := by
  have h2 := USize.toNat_lt_size len
  rw [USize.toNat_add, USize.toNat_one]
  exact Nat.mod_eq_of_lt (by have : USize.size = 2 ^ System.Platform.numBits := rfl; lia)

private theorem toNat_toUSize_of_lt {m : Nat} (h : m < USize.size) : m.toUSize.toNat = m := by
  rw [Nat.toUSize_eq, USize.toNat_ofNat', Nat.mod_eq_of_lt h]

private theorem slice_ext {s t : ISizeArray.Slice} (ha : s.array = t.array)
    (hs : s.start = t.start) (ht : s.stop = t.stop) : s = t := by
  obtain ⟨⟨a, i, j, h₁, h₂⟩⟩ := s
  obtain ⟨⟨b, i', j', h₁', h₂'⟩⟩ := t
  simp only [Slice.array, Slice.start, Slice.stop] at ha hs ht
  subst ha hs ht; rfl

/-- The step of the in-place folds over the window of `len` elements at `start`. -/
@[inline]
private def foldInPlaceBody {β : Type v} {n : Nat} (start len : USize)
    (hw : start.toNat + len.toNat ≤ n)
    (f : (k : USize) → k.toNat < len.toNat → ISize → β → ISize × β) (k : USize)
    (hk : k.toNat < len.toNat) (b : β) : InPlace n β :=
  InPlace.readThen (start + k) (InPlace.toNat_add_lt_of_window hw hk) fun x =>
  let p := f k hk x b
  InPlace.write (start + k) (InPlace.toNat_add_lt_of_window hw hk) p.1 >>= fun _ => pure p.2

/--
The program of the in-place folds over the window of `len` elements at `start`, from step `j` up.
-/
@[inline]
private def foldlInPlaceProg {β : Type v} {n : Nat} (start len : USize)
    (hw : start.toNat + len.toNat ≤ n)
    (f : (k : USize) → k.toNat < len.toNat → ISize → β → ISize × β) (j : USize) (b : β) :
    InPlace n β :=
  InPlace.forUpFrom len j b (foldInPlaceBody start len hw f)

private theorem run_foldlInPlaceProg {β : Type v} (start len : USize) (N m : Nat)
    (hN : N < USize.size) (hw : start.toNat + len.toNat ≤ N) (hm : len.toNat = m)
    (f : (k : USize) → k.toNat < m → ISize → β → ISize × β)
    (s : ISizeArray.Slice) (hs : s.size = m) (hstart : s.start = start.toNat) (c : ISizeArray)
    (hca : s.array = c) (hc : c.size = N) (j : USize) (hj : j.toNat ≤ len.toNat) (b : β) :
    (foldlInPlaceProg start len hw (fun k hk => f k (hm ▸ hk)) j b).run c hc =
      ((foldlInPlace.loop m f s hs j.toNat b).2, (foldlInPlace.loop m f s hs j.toNat b).1.array) := by
  subst hca
  unfold foldlInPlaceProg
  rw [InPlace.forUpFrom_eq, foldlInPlace.loop]
  unfold foldInPlaceBody
  by_cases hjl : j < len
  · have hjl' : j.toNat < len.toNat := hjl
    have hjm : j.toNat < m := hm ▸ hjl'
    rw [dite_eq_left_of_eq_true (eq_true hjl), dite_eq_left_of_eq_true (eq_true hjm)]
    simp only [InPlace.run_bind, InPlace.run_readThen, InPlace.run_write, InPlace.run_pure]
    have ex := toNat_add_of_window hN hw hjl'
    have ej : j.toNat.toUSize = j := by simp
    have h1 : (j + 1).toNat ≤ len.toNat := by rw [toNat_succ_of_lt' hjl']; lia
    have ih := fun s hs hstart hc b =>
      run_foldlInPlaceProg start len N m hN hw hm f s hs hstart _ rfl hc (j + 1) h1 b
    unfold foldlInPlaceProg foldInPlaceBody at ih
    have hset : ∀ v h, s.array.set (start + j).toNat v h = (s.set j.toNat v (by lia)).array := by
      intro v h; simp only [array_set, ex, hstart]
    simp only [hset]
    rw [ih _ (by simpa using hs) (by simpa using hstart) (by simpa using hc)]
    simp only [toNat_succ_of_lt' hjl']
    congr 3 <;> simp only [Slice.getElem_eq, ex, hstart, ej]
  · have hjm : ¬j.toNat < m := hm ▸ hjl
    rw [dite_eq_right_of_eq_false (eq_false hjl), dite_eq_right_of_eq_false (eq_false hjm)]
    simp only [InPlace.run_pure]
termination_by len.toNat - j.toNat
decreasing_by rw [toNat_succ_of_lt' hjl']; lia


/--
Replaces each element of the slice while threading an accumulator, in place like `set`: for each
`k < s.size`, from `0` up, the element `x` at index `k` of the slice becomes the first component of
`f k hk x b`, whose second component is the next accumulator. Returns the new slice and the last
accumulator.

The array is made exclusive once, before the loop, which then stores without checks, where each
`set` checks at every write. `f` only sees the elements, never the array, which is what makes
skipping the checks safe. The proof `hk : k.toNat < s.size` lets `f` read other arrays with
`uget`.
-/
@[expose]
public def foldlInPlace {β : Type v} (s : ISizeArray.Slice) (init : β)
    (f : (k : USize) → k.toNat < s.size → ISize → β → ISize × β) : ISizeArray.Slice × β :=
  foldlInPlace.loop s.size f s rfl 0 init

private theorem foldlInPlace_loop_props {β : Type v} (n : Nat)
    (f : (k : USize) → k.toNat < n → ISize → β → ISize × β)
    (s : ISizeArray.Slice) (hs : s.size = n) (k : Nat) (b : β) :
    (foldlInPlace.loop n f s hs k b).1.start = s.start ∧
      (foldlInPlace.loop n f s hs k b).1.stop = s.stop := by
  fun_induction foldlInPlace.loop n f s hs k b with
  | case1 s hs k b hk hk' p ih => simpa using ih
  | case2 => exact ⟨rfl, rfl⟩

@[simp] public theorem start_foldlInPlace {β : Type v} (s : ISizeArray.Slice) (init : β)
    (f : (k : USize) → k.toNat < s.size → ISize → β → ISize × β) :
    (s.foldlInPlace init f).1.start = s.start :=
  (foldlInPlace_loop_props ..).1

@[simp] public theorem stop_foldlInPlace {β : Type v} (s : ISizeArray.Slice) (init : β)
    (f : (k : USize) → k.toNat < s.size → ISize → β → ISize × β) :
    (s.foldlInPlace init f).1.stop = s.stop :=
  (foldlInPlace_loop_props ..).2

@[simp] public theorem size_foldlInPlace {β : Type v} (s : ISizeArray.Slice) (init : β)
    (f : (k : USize) → k.toNat < s.size → ISize → β → ISize × β) :
    (s.foldlInPlace init f).1.size = s.size := by
  rw [size_eq, size_eq, start_foldlInPlace, stop_foldlInPlace]

private theorem getElem?_array_set (s : ISizeArray.Slice) (k : Nat) (v : ISize) (h) (i : Nat)
    (hi : i ≠ s.start + k) : (s.set k v h).array[i]? = s.array[i]? := by
  rw [array_set, show ∀ h', s.array.set (s.start + k) v h' = s.array.set! (s.start + k) v from
    fun h' => by simp [ISizeArray.set!, h'], getElem?_set!, ite_eq_right (Ne.symm hi)]

private theorem foldl_congr {α : Type u} {γ : Type v} {f g : γ → α → γ} (l : List α)
    {c c' : γ} (hc : c = c') (h : ∀ c, ∀ a ∈ l, f c a = g c a) :
    l.foldl f c = l.foldl g c' := by
  subst hc
  induction l generalizing c with
  | nil => rfl
  | cons a l ih =>
    rw [List.foldl_cons, List.foldl_cons, h c a (List.mem_cons_self ..)]
    exact ih fun c a ha => h c a (List.mem_cons_of_mem _ ha)

private theorem foldr_congr {α : Type u} {γ : Type v} {f g : α → γ → γ} (l : List α)
    {c c' : γ} (hc : c = c') (h : ∀ a ∈ l, ∀ c, f a c = g a c) :
    l.foldr f c = l.foldr g c' := by
  subst hc
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.foldr_cons, List.foldr_cons, ih fun a ha => h a (List.mem_cons_of_mem _ ha),
      h a (List.mem_cons_self ..)]

private theorem foldlInPlace_loop_array {β : Type v} (n : Nat)
    (f : (k : USize) → k.toNat < n → ISize → β → ISize × β)
    (s : ISizeArray.Slice) (hs : s.size = n) (k : Nat) (b : β) :
    (foldlInPlace.loop n f s hs k b).1.array.size = s.array.size ∧
      ∀ i, i < s.start ∨ s.stop ≤ i →
        (foldlInPlace.loop n f s hs k b).1.array[i]? = s.array[i]? := by
  fun_induction foldlInPlace.loop n f s hs k b with
  | case1 s hs k b hk hk' p ih =>
    obtain ⟨ih₁, ih₂⟩ := ih
    refine ⟨by rw [ih₁, array_set, ISizeArray.size_set], fun i hi => ?_⟩
    rw [ih₂ i (by simpa using hi), getElem?_array_set _ _ _ _ _ (by rw [size_eq] at hs; lia)]
  | case2 => exact ⟨rfl, fun _ _ => rfl⟩

@[simp] public theorem size_array_foldlInPlace {β : Type v} (s : ISizeArray.Slice) (init : β)
    (f : (k : USize) → k.toNat < s.size → ISize → β → ISize × β) :
    (s.foldlInPlace init f).1.array.size = s.array.size :=
  (foldlInPlace_loop_array ..).1

/-- `foldlInPlace` leaves the elements of the array outside the slice unchanged. -/
public theorem getElem?_array_foldlInPlace {β : Type v} (s : ISizeArray.Slice) (init : β)
    (f : (k : USize) → k.toNat < s.size → ISize → β → ISize × β) (i : Nat)
    (hi : i < s.start ∨ s.stop ≤ i) :
    (s.foldlInPlace init f).1.array[i]? = s.array[i]? :=
  (foldlInPlace_loop_array ..).2 i hi

/-- The slice `s` with its array replaced by `a`, of the same size. -/
@[inline]
private def withArray (s : ISizeArray.Slice) (a : ISizeArray) (h : a.size = s.array.size) :
    ISizeArray.Slice :=
  ⟨⟨a, s.start, s.stop, s.start_le_stop, h ▸ s.stop_le_array_size⟩⟩

private theorem toNat_size_toUSize (s : ISizeArray.Slice) (hN : s.array.size < USize.size) :
    s.size.toUSize.toNat = s.size :=
  toNat_toUSize_of_lt (by have := s.stop_le_array_size; rw [size_eq]; lia)

private theorem toNat_start_toUSize (s : ISizeArray.Slice) (hN : s.array.size < USize.size) :
    s.start.toUSize.toNat = s.start :=
  toNat_toUSize_of_lt (by have h₁ := s.start_le_stop; have h₂ := s.stop_le_array_size; lia)

private theorem window_slice (s : ISizeArray.Slice) (hN : s.array.size < USize.size) :
    s.start.toUSize.toNat + s.size.toUSize.toNat ≤ s.array.size := by
  have h₁ := s.stop_le_array_size
  have h₂ := s.start_le_stop
  rw [toNat_size_toUSize s hN, toNat_start_toUSize s hN, size_eq]; lia

/-- For internal use only. -/
@[inline]
public def foldlInPlaceImpl {β : Type v} (s : ISizeArray.Slice) (init : β)
    (f : (k : USize) → k.toNat < s.size → ISize → β → ISize × β) : ISizeArray.Slice × β :=
  if hN : s.array.size < USize.size then
    let r := s.array.runInPlace (foldlInPlaceProg s.start.toUSize s.size.toUSize
      (window_slice s hN) (fun k hk => f k (toNat_size_toUSize s hN ▸ hk)) 0 init)
    (withArray s r.2 (InPlace.size_run ..), r.1)
  else
    s.foldlInPlace init f

@[csimp] public theorem foldlInPlace_eq_foldlInPlaceImpl : @foldlInPlace = @foldlInPlaceImpl := by
  funext β s init f
  unfold foldlInPlaceImpl
  split
  · rename_i hN
    have key := run_foldlInPlaceProg s.start.toUSize s.size.toUSize s.array.size s.size hN
      (window_slice s hN) (toNat_size_toUSize s hN) f s rfl (toNat_start_toUSize s hN).symm _ rfl
      rfl 0 (by simp) init
    apply Prod.ext
    · apply slice_ext
      · exact (congrArg Prod.snd key).symm
      · exact start_foldlInPlace ..
      · exact stop_foldlInPlace ..
    · exact (congrArg Prod.fst key).symm
  · rfl

private theorem toList_copy_set_take (s : ISizeArray.Slice) (k : Nat) (v : ISize)
    (h : k < s.size) : (s.set k v h).copy.toList.take (k + 1) = s.copy.toList.take k ++ [v] := by
  rw [copy_set, toList_set, List.take_add_one, List.take_set_of_le (Nat.le_refl _),
    List.getElem?_set_self (by simpa using h)]
  rfl

private theorem foldlInPlace_loop_eq {β : Type v} (n : Nat)
    (f : (k : USize) → k.toNat < n → ISize → β → ISize × β)
    (s : ISizeArray.Slice) (hs : s.size = n) (k : Nat) (b : β) :
    ((foldlInPlace.loop n f s hs k b).1.copy.toList, (foldlInPlace.loop n f s hs k b).2) =
      ((List.finRange n).drop k).foldl (fun acc i =>
        let p := f i.val.toUSize
          (by
            rw [Nat.toUSize_eq, USize.toNat_ofNat']
            exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) i.2)
          (s[i.val]'(by rw [hs]; exact i.2)) acc.2
        (acc.1 ++ [p.1], p.2)) (s.copy.toList.take k, b) := by
  fun_induction foldlInPlace.loop n f s hs k b with
  | case1 s hs k b hk hk' p ih =>
    have e : (List.finRange n).drop k =
        (List.finRange n)[k]'(by simpa using hk) :: (List.finRange n).drop (k + 1) :=
      List.drop_eq_getElem_cons _
    rw [ih, e, List.foldl_cons, toList_copy_set_take _ _ _ (by lia)]
    apply foldl_congr
    · simp only [List.getElem_finRange, Fin.cast_mk]
      rfl
    intro acc i hi
    have : k + 1 ≤ i.val := by
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hi
      simp only [List.getElem_drop, List.getElem_finRange, Fin.cast_mk]
      lia
    simp only [getElem_set, show k ≠ i.val by lia, ↓reduceIte]
  | case2 s hs k b hk =>
    rw [List.drop_of_length_le (by simp; lia), List.foldl_nil,
      List.take_of_length_le (by simp; lia)]

/--
`foldlInPlace` as a pure left fold over the indices of the slice: the new elements of the slice and
the last accumulator, in one statement. The `Then` form follows by `foldlInPlaceThen_eq`.
-/
public theorem foldlInPlace_eq_foldl_finRange {β : Type v} (s : ISizeArray.Slice) (init : β)
    (f : (k : USize) → k.toNat < s.size → ISize → β → ISize × β) :
    ((s.foldlInPlace init f).1.copy.toList, (s.foldlInPlace init f).2) =
      (List.finRange s.size).foldl (fun acc i =>
        let p := f i.val.toUSize
          (by
            rw [Nat.toUSize_eq, USize.toNat_ofNat']
            exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) i.2)
          s[i] acc.2
        (acc.1 ++ [p.1], p.2)) ([], init) :=
  foldlInPlace_loop_eq ..

/-- The loop of `foldrInPlace`, over `Nat` indices, from `k - 1` down to `0`. -/
@[expose]
public def foldrInPlace.loop {β : Type v} (n : Nat)
    (f : (k : USize) → k.toNat < n → ISize → β → ISize × β)
    (s : ISizeArray.Slice) (hs : s.size = n) : (k : Nat) → k ≤ n → β → ISizeArray.Slice × β
  | 0, _, b => (s, b)
  | k + 1, hk, b =>
    have hk' : k.toUSize.toNat < n := by
      rw [Nat.toUSize_eq, USize.toNat_ofNat']
      exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) hk
    let p := f k.toUSize hk' (s[k]'(by lia)) b
    foldrInPlace.loop n f (s.set k p.1 (by lia)) (by simpa using hs) k (by lia) p.2

/--
Replaces each element of the slice while threading an accumulator, like `foldlInPlace` but from
the last element to the first: for each `k < s.size`, from `s.size - 1` down to `0`, the element
`x` at index `k` of the slice becomes the first component of `f k hk x b`, whose second component
is the next accumulator. Returns the new slice and the last accumulator.

The array is made exclusive once, before the loop, which then stores without checks.
-/
@[expose]
public def foldrInPlace {β : Type v} (s : ISizeArray.Slice) (init : β)
    (f : (k : USize) → k.toNat < s.size → ISize → β → ISize × β) : ISizeArray.Slice × β :=
  foldrInPlace.loop s.size f s rfl s.size (Nat.le_refl _) init

private theorem foldrInPlace_loop_props {β : Type v} (n : Nat)
    (f : (k : USize) → k.toNat < n → ISize → β → ISize × β)
    (s : ISizeArray.Slice) (hs : s.size = n) (k : Nat) (hk : k ≤ n) (b : β) :
    (foldrInPlace.loop n f s hs k hk b).1.start = s.start ∧
      (foldrInPlace.loop n f s hs k hk b).1.stop = s.stop := by
  induction k generalizing s b with
  | zero => exact ⟨rfl, rfl⟩
  | succ k ih =>
    rw [foldrInPlace.loop]
    obtain ⟨h₁, h₂⟩ := ih ..
    exact ⟨h₁, h₂⟩

@[simp] public theorem start_foldrInPlace {β : Type v} (s : ISizeArray.Slice) (init : β)
    (f : (k : USize) → k.toNat < s.size → ISize → β → ISize × β) :
    (s.foldrInPlace init f).1.start = s.start :=
  (foldrInPlace_loop_props ..).1

@[simp] public theorem stop_foldrInPlace {β : Type v} (s : ISizeArray.Slice) (init : β)
    (f : (k : USize) → k.toNat < s.size → ISize → β → ISize × β) :
    (s.foldrInPlace init f).1.stop = s.stop :=
  (foldrInPlace_loop_props ..).2

@[simp] public theorem size_foldrInPlace {β : Type v} (s : ISizeArray.Slice) (init : β)
    (f : (k : USize) → k.toNat < s.size → ISize → β → ISize × β) :
    (s.foldrInPlace init f).1.size = s.size := by
  rw [size_eq, size_eq, start_foldrInPlace, stop_foldrInPlace]

private theorem foldrInPlace_loop_array {β : Type v} (n : Nat)
    (f : (k : USize) → k.toNat < n → ISize → β → ISize × β)
    (s : ISizeArray.Slice) (hs : s.size = n) (k : Nat) (hk : k ≤ n) (b : β) :
    (foldrInPlace.loop n f s hs k hk b).1.array.size = s.array.size ∧
      ∀ i, i < s.start ∨ s.stop ≤ i →
        (foldrInPlace.loop n f s hs k hk b).1.array[i]? = s.array[i]? := by
  induction k generalizing s b with
  | zero => exact ⟨rfl, fun _ _ => rfl⟩
  | succ k ih =>
    rw [foldrInPlace.loop]
    obtain ⟨ih₁, ih₂⟩ := ih ..
    refine ⟨by rw [ih₁, array_set, ISizeArray.size_set], fun i hi => ?_⟩
    rw [ih₂ i (by simpa using hi), getElem?_array_set _ _ _ _ _ (by rw [size_eq] at hs; lia)]

@[simp] public theorem size_array_foldrInPlace {β : Type v} (s : ISizeArray.Slice) (init : β)
    (f : (k : USize) → k.toNat < s.size → ISize → β → ISize × β) :
    (s.foldrInPlace init f).1.array.size = s.array.size :=
  (foldrInPlace_loop_array ..).1

/-- `foldrInPlace` leaves the elements of the array outside the slice unchanged. -/
public theorem getElem?_array_foldrInPlace {β : Type v} (s : ISizeArray.Slice) (init : β)
    (f : (k : USize) → k.toNat < s.size → ISize → β → ISize × β) (i : Nat)
    (hi : i < s.start ∨ s.stop ≤ i) :
    (s.foldrInPlace init f).1.array[i]? = s.array[i]? :=
  (foldrInPlace_loop_array ..).2 i hi

/--
The program of the in-place folds over the window of `len` elements at `start`, from step `j`
down.
-/
@[inline]
private def foldrInPlaceProg {β : Type v} {n : Nat} (start len : USize)
    (hw : start.toNat + len.toNat ≤ n)
    (f : (k : USize) → k.toNat < len.toNat → ISize → β → ISize × β) (j : USize)
    (hj : j.toNat ≤ len.toNat) (b : β) : InPlace n β :=
  InPlace.forDownFrom len j hj b (foldInPlaceBody start len hw f)

private theorem run_foldrInPlaceProg {β : Type v} (start len : USize) (N m : Nat)
    (hN : N < USize.size) (hw : start.toNat + len.toNat ≤ N) (hm : len.toNat = m)
    (f : (k : USize) → k.toNat < m → ISize → β → ISize × β) :
    ∀ (k : Nat) (s : ISizeArray.Slice) (hs : s.size = m) (_ : s.start = start.toNat)
      (c : ISizeArray) (_ : s.array = c) (hc : c.size = N) (j : USize)
      (hj : j.toNat ≤ len.toNat) (hk : j.toNat = k) (b : β),
    (foldrInPlaceProg start len hw (fun k hk => f k (hm ▸ hk)) j hj b).run c hc =
      ((foldrInPlace.loop m f s hs k (by lia) b).2,
        (foldrInPlace.loop m f s hs k (by lia) b).1.array)
  | 0, s, hs, hstart, c, hca, hc, j, hj, hk, b => by
    subst hca
    have h0 : j = 0 := USize.toNat_inj.1 (by simpa using hk)
    unfold foldrInPlaceProg
    rw [InPlace.forDownFrom_eq, dite_eq_left_of_eq_true (eq_true h0), foldrInPlace.loop]
    simp only [InPlace.run_pure]
  | k + 1, s, hs, hstart, c, hca, hc, j, hj, hk, b => by
    subst hca
    have h0 : ¬j = 0 := fun h => by subst h; simp at hk
    have hj1 : (j - 1).toNat = k := by
      rw [USize.toNat_sub_of_le _ _ (by rw [USize.le_iff_toNat_le, USize.toNat_one]; lia),
        USize.toNat_one]
      lia
    have hjl' : (j - 1).toNat < len.toNat := by lia
    unfold foldrInPlaceProg
    rw [InPlace.forDownFrom_eq, dite_eq_right_of_eq_false (eq_false h0), foldrInPlace.loop]
    unfold foldInPlaceBody
    simp only [InPlace.run_bind, InPlace.run_readThen, InPlace.run_write, InPlace.run_pure]
    have ex := toNat_add_of_window hN hw hjl'
    have ej : k.toUSize = j - 1 := by rw [← hj1]; simp
    have ih := fun s hs hstart hc b =>
      run_foldrInPlaceProg start len N m hN hw hm f k s hs hstart _ rfl hc (j - 1) (by lia) hj1 b
    unfold foldrInPlaceProg foldInPlaceBody at ih
    have hset : ∀ v h, s.array.set (start + (j - 1)).toNat v h = (s.set k v (by lia)).array := by
      intro v h; simp only [array_set, ex, hstart, hj1]
    simp only [hset]
    rw [ih _ (by simpa using hs) (by simpa using hstart) (by simpa using hc)]
    congr 3 <;> simp only [Slice.getElem_eq, ex, hstart, ej, hj1]

/-- For internal use only. -/
@[inline]
public def foldrInPlaceImpl {β : Type v} (s : ISizeArray.Slice) (init : β)
    (f : (k : USize) → k.toNat < s.size → ISize → β → ISize × β) : ISizeArray.Slice × β :=
  if hN : s.array.size < USize.size then
    let r := s.array.runInPlace (foldrInPlaceProg s.start.toUSize s.size.toUSize
      (window_slice s hN) (fun k hk => f k (toNat_size_toUSize s hN ▸ hk)) s.size.toUSize
      (Nat.le_refl _) init)
    (withArray s r.2 (InPlace.size_run ..), r.1)
  else
    s.foldrInPlace init f

@[csimp] public theorem foldrInPlace_eq_foldrInPlaceImpl : @foldrInPlace = @foldrInPlaceImpl := by
  funext β s init f
  unfold foldrInPlaceImpl
  split
  · rename_i hN
    have key := run_foldrInPlaceProg s.start.toUSize s.size.toUSize s.array.size s.size hN
      (window_slice s hN) (toNat_size_toUSize s hN) f s.size s rfl (toNat_start_toUSize s hN).symm
      _ rfl rfl _ (Nat.le_refl _) (toNat_size_toUSize s hN) init
    apply Prod.ext
    · apply slice_ext
      · exact (congrArg Prod.snd key).symm
      · exact start_foldrInPlace ..
      · exact stop_foldrInPlace ..
    · exact (congrArg Prod.fst key).symm
  · rfl

private theorem toList_copy_set_drop (s : ISizeArray.Slice) (k : Nat) (v : ISize)
    (h : k < s.size) : (s.set k v h).copy.toList.drop k = v :: s.copy.toList.drop (k + 1) := by
  rw [copy_set, toList_set, List.drop_eq_getElem_cons (by simpa using h), List.getElem_set_self,
    List.drop_set_of_lt (Nat.lt_add_one k)]

private theorem foldrInPlace_loop_eq {β : Type v} (n : Nat)
    (f : (k : USize) → k.toNat < n → ISize → β → ISize × β)
    (s : ISizeArray.Slice) (hs : s.size = n) (k : Nat) (hk : k ≤ n) (b : β) :
    ((foldrInPlace.loop n f s hs k hk b).1.copy.toList, (foldrInPlace.loop n f s hs k hk b).2) =
      ((List.finRange n).take k).foldr (fun i acc =>
        let p := f i.val.toUSize
          (by
            rw [Nat.toUSize_eq, USize.toNat_ofNat']
            exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) i.2)
          (s[i.val]'(by rw [hs]; exact i.2)) acc.2
        (p.1 :: acc.1, p.2)) (s.copy.toList.drop k, b) := by
  induction k generalizing s b with
  | zero => simp [foldrInPlace.loop]
  | succ k ih =>
    rw [foldrInPlace.loop, ih, List.take_add_one, List.getElem?_eq_getElem (by simp; lia),
      Option.toList_some, List.foldr_append, List.foldr_cons, List.foldr_nil,
      toList_copy_set_drop _ _ _ (by lia)]
    apply foldr_congr
    · simp only [List.getElem_finRange, Fin.cast_mk]
    intro i hi acc
    have : i.val < k := by
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hi
      simp only [List.getElem_take, List.getElem_finRange, Fin.cast_mk]
      simp at hj
      lia
    simp only [getElem_set, show k ≠ i.val by lia, ↓reduceIte]

/--
`foldrInPlace` as a pure right fold over the indices of the slice: the new elements of the slice
and the last accumulator, in one statement. The `Then` form follows by `foldrInPlaceThen_eq`.
-/
public theorem foldrInPlace_eq_foldr_finRange {β : Type v} (s : ISizeArray.Slice) (init : β)
    (f : (k : USize) → k.toNat < s.size → ISize → β → ISize × β) :
    ((s.foldrInPlace init f).1.copy.toList, (s.foldrInPlace init f).2) =
      (List.finRange s.size).foldr (fun i acc =>
        let p := f i.val.toUSize
          (by
            rw [Nat.toUSize_eq, USize.toNat_ofNat']
            exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) i.2)
          s[i] acc.2
        (p.1 :: acc.1, p.2)) ([], init) := by
  have := foldrInPlace_loop_eq s.size f s rfl s.size (Nat.le_refl _) init
  rw [List.take_of_length_le (by simp), List.drop_of_length_le (by simp)] at this
  exact this

/--
`foldlInPlace` followed by `g` on the new slice and the last accumulator, which the loop calls
itself where `foldlInPlace` returns them as a pair. The pair is a heap object, allocated once per
call, which shows when the fold runs over short slices many times; when `g` consumes the
accumulator, for example by writing it into the slice, no pair is allocated at all.
`foldlInPlace` is the case `g := Prod.mk`.
-/
@[expose]
public def foldlInPlaceThen {β : Type v} {γ : Type w} (s : ISizeArray.Slice) (init : β)
    (f : (k : USize) → k.toNat < s.size → ISize → β → ISize × β)
    (g : ISizeArray.Slice → β → γ) : γ :=
  g (s.foldlInPlace init f).1 (s.foldlInPlace init f).2

@[simp] public theorem foldlInPlaceThen_eq {β : Type v} {γ : Type w} (s : ISizeArray.Slice)
    (init : β) (f : (k : USize) → k.toNat < s.size → ISize → β → ISize × β)
    (g : ISizeArray.Slice → β → γ) :
    s.foldlInPlaceThen init f g = g (s.foldlInPlace init f).1 (s.foldlInPlace init f).2 :=
  rfl

/-- For internal use only. -/
@[inline]
public def foldlInPlaceThenImpl {β : Type v} {γ : Type w} (s : ISizeArray.Slice) (init : β)
    (f : (k : USize) → k.toNat < s.size → ISize → β → ISize × β)
    (g : ISizeArray.Slice → β → γ) : γ :=
  -- Taking `s` apart up front keeps the continuation from holding `s`, and with it the array.
  match s, f with
  | ⟨⟨a, start, stop, h₁, h₂⟩⟩, f =>
    let s' : ISizeArray.Slice := ⟨⟨a, start, stop, h₁, h₂⟩⟩
    if hN : a.size < USize.size then
      InPlace.runForUpFromThen a rfl s'.size.toUSize 0 init
        (foldInPlaceBody s'.start.toUSize s'.size.toUSize (window_slice s' hN)
          fun k hk => f k (toNat_size_toUSize s' hN ▸ hk))
        fun b a' ha => g ⟨⟨a', start, stop, h₁, ha ▸ h₂⟩⟩ b
    else
      let r := s'.foldlInPlace init f
      g r.1 r.2

@[csimp] public theorem foldlInPlaceThen_eq_foldlInPlaceThenImpl :
    @foldlInPlaceThen = @foldlInPlaceThenImpl := by
  funext β γ s init f g
  obtain ⟨⟨a, start, stop, h₁, h₂⟩⟩ := s
  unfold foldlInPlaceThenImpl
  dsimp only
  split
  · rename_i hN
    rw [InPlace.runForUpFromThen_eq, foldlInPlaceThen_eq, foldlInPlace_eq_foldlInPlaceImpl]
    unfold foldlInPlaceImpl
    split
    · rfl
    · exact absurd hN ‹_›
  · rfl

/--
`foldrInPlace` followed by `g` on the new slice and the last accumulator, which the loop calls
itself where `foldrInPlace` returns them as a pair. When `g` consumes the accumulator, no pair is
allocated. `foldrInPlace` is the case `g := Prod.mk`.
-/
@[expose]
public def foldrInPlaceThen {β : Type v} {γ : Type w} (s : ISizeArray.Slice) (init : β)
    (f : (k : USize) → k.toNat < s.size → ISize → β → ISize × β)
    (g : ISizeArray.Slice → β → γ) : γ :=
  g (s.foldrInPlace init f).1 (s.foldrInPlace init f).2

@[simp] public theorem foldrInPlaceThen_eq {β : Type v} {γ : Type w} (s : ISizeArray.Slice)
    (init : β) (f : (k : USize) → k.toNat < s.size → ISize → β → ISize × β)
    (g : ISizeArray.Slice → β → γ) :
    s.foldrInPlaceThen init f g = g (s.foldrInPlace init f).1 (s.foldrInPlace init f).2 :=
  rfl

/-- For internal use only. -/
@[inline]
public def foldrInPlaceThenImpl {β : Type v} {γ : Type w} (s : ISizeArray.Slice) (init : β)
    (f : (k : USize) → k.toNat < s.size → ISize → β → ISize × β)
    (g : ISizeArray.Slice → β → γ) : γ :=
  -- Taking `s` apart up front keeps the continuation from holding `s`, and with it the array.
  match s, f with
  | ⟨⟨a, start, stop, h₁, h₂⟩⟩, f =>
    let s' : ISizeArray.Slice := ⟨⟨a, start, stop, h₁, h₂⟩⟩
    if hN : a.size < USize.size then
      InPlace.runForDownFromThen a rfl s'.size.toUSize s'.size.toUSize (Nat.le_refl _) init
        (foldInPlaceBody s'.start.toUSize s'.size.toUSize (window_slice s' hN)
          fun k hk => f k (toNat_size_toUSize s' hN ▸ hk))
        fun b a' ha => g ⟨⟨a', start, stop, h₁, ha ▸ h₂⟩⟩ b
    else
      let r := s'.foldrInPlace init f
      g r.1 r.2

@[csimp] public theorem foldrInPlaceThen_eq_foldrInPlaceThenImpl :
    @foldrInPlaceThen = @foldrInPlaceThenImpl := by
  funext β γ s init f g
  obtain ⟨⟨a, start, stop, h₁, h₂⟩⟩ := s
  unfold foldrInPlaceThenImpl
  dsimp only
  split
  · rename_i hN
    rw [InPlace.runForDownFromThen_eq, foldrInPlaceThen_eq, foldrInPlace_eq_foldrInPlaceImpl]
    unfold foldrInPlaceImpl
    split
    · rfl
    · exact absurd hN ‹_›
  · rfl

end Slice

private theorem congr_then {β : Type v} {γ : Type w} {N : Nat}
    (g : (a' : ISizeArray) → a'.size = N → β → γ) {a₁ a₂ : ISizeArray} {b₁ b₂ : β}
    (ha : a₁ = a₂) (hb : b₁ = b₂) (h₁ : a₁.size = N) (h₂ : a₂.size = N) :
    g a₁ h₁ b₁ = g a₂ h₂ b₂ := by
  subst ha hb; rfl

private theorem congr_then2 {β₁ : Type v} {β₂ : Type w} {γ : Type u} {N : Nat}
    (g : (a' : ISizeArray) → a'.size = N → β₁ → β₂ → γ) {a₁ a₂ : ISizeArray} {b₁ c₁ : β₁}
    {b₂ c₂ : β₂} (ha : a₁ = a₂) (hb₁ : b₁ = c₁) (hb₂ : b₂ = c₂) (h₁ : a₁.size = N)
    (h₂ : a₂.size = N) : g a₁ h₁ b₁ b₂ = g a₂ h₂ c₁ c₂ := by
  subst ha hb₁ hb₂; rfl

/-! ## Folding over windows of one array -/

/-- The loop of `foldlInPlace2`, over `Nat` offsets and indices. -/
@[expose]
public def foldlInPlace2.loop {β : Type v} (xs ys rs len : Nat)
    (f : (j : USize) → j.toNat < len → ISize → ISize → β → ISize × β)
    (a : ISizeArray) (hx : xs + len ≤ a.size) (hy : ys + len ≤ a.size)
    (hr : rs + len ≤ a.size) (j : Nat) (b : β) : ISizeArray × β :=
  if hj : j < len then
    have hj' : j.toUSize.toNat < len := by
      rw [Nat.toUSize_eq, USize.toNat_ofNat']
      exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) hj
    let p := f j.toUSize hj' (a[xs + j]'(by lia)) (a[ys + j]'(by lia)) b
    foldlInPlace2.loop xs ys rs len f (a.set (rs + j) p.1) (by simpa using hx) (by simpa using hy)
      (by simpa using hr) (j + 1) p.2
  else
    (a, b)
termination_by len - j

/--
Writes the window of `len` elements at `rs` from the windows at `xs` and `ys` of the same array,
in place, threading an accumulator: for each `j < len`, from `0` up, it reads `x := a[xs + j]` and
`y := a[ys + j]` from the current array, then stores the first component of `f j hj x y b` at
`rs + j`, and the second component is the next accumulator. Returns the new array and the last
accumulator.

Each step reads after the writes of the earlier steps, so overlapping windows are well defined: with
`rs = xs + 1`, for example, step `j` reads what step `j - 1` wrote. Reading the windows through `f`
rather than through another reference to `a` keeps `a` exclusive, which a second reference would
not, and then the first write would copy the whole array.

The array is made exclusive once, before the loop, which then reads and stores without checks.
-/
@[expose]
public def foldlInPlace2 {β : Type v} (a : ISizeArray) (xs ys rs len : USize)
    (hx : xs.toNat + len.toNat ≤ a.size) (hy : ys.toNat + len.toNat ≤ a.size)
    (hr : rs.toNat + len.toNat ≤ a.size) (init : β)
    (f : (j : USize) → j.toNat < len.toNat → ISize → ISize → β → ISize × β) :
    ISizeArray × β :=
  foldlInPlace2.loop xs.toNat ys.toNat rs.toNat len.toNat f a hx hy hr 0 init

private theorem size_foldlInPlace2_loop {β : Type v} (xs ys rs len : Nat)
    (f : (j : USize) → j.toNat < len → ISize → ISize → β → ISize × β)
    (a : ISizeArray) (hx : xs + len ≤ a.size) (hy : ys + len ≤ a.size)
    (hr : rs + len ≤ a.size) (j : Nat) (b : β) : (foldlInPlace2.loop xs ys rs len f a hx hy hr j b).1.size = a.size := by
  fun_induction foldlInPlace2.loop xs ys rs len f a hx hy hr j b with
  | case1 a hx hy hr j b hj hj' p ih => rw [ih, size_set]
  | case2 => rfl

@[simp] public theorem size_foldlInPlace2 {β : Type v} (a : ISizeArray) (xs ys rs len : USize)
    (hx : xs.toNat + len.toNat ≤ a.size) (hy : ys.toNat + len.toNat ≤ a.size)
    (hr : rs.toNat + len.toNat ≤ a.size) (init : β)
    (f : (j : USize) → j.toNat < len.toNat → ISize → ISize → β → ISize × β) :
    (a.foldlInPlace2 xs ys rs len hx hy hr init f).1.size = a.size :=
  size_foldlInPlace2_loop ..


/-- The step of `foldlInPlace2`. -/
@[inline]
private def foldlInPlace2Body {β : Type v} {n : Nat} (xs ys rs len : USize)
    (hx : xs.toNat + len.toNat ≤ n) (hy : ys.toNat + len.toNat ≤ n)
    (hr : rs.toNat + len.toNat ≤ n)
    (f : (j : USize) → j.toNat < len.toNat → ISize → ISize → β → ISize × β) (j : USize)
    (hj : j.toNat < len.toNat) (b : β) : InPlace n β :=
  InPlace.readThen (xs + j) (InPlace.toNat_add_lt_of_window hx hj) fun x =>
  InPlace.readThen (ys + j) (InPlace.toNat_add_lt_of_window hy hj) fun y =>
  let p := f j hj x y b
  InPlace.write (rs + j) (InPlace.toNat_add_lt_of_window hr hj) p.1 >>= fun _ => pure p.2

/-- The program of `foldlInPlace2`, from step `j` on. -/
@[inline]
private def foldlInPlace2Prog {β : Type v} {n : Nat} (xs ys rs len : USize)
    (hx : xs.toNat + len.toNat ≤ n) (hy : ys.toNat + len.toNat ≤ n)
    (hr : rs.toNat + len.toNat ≤ n)
    (f : (j : USize) → j.toNat < len.toNat → ISize → ISize → β → ISize × β) (j : USize)
    (b : β) : InPlace n β :=
  InPlace.forUpFrom len j b (foldlInPlace2Body xs ys rs len hx hy hr f)

private theorem run_foldlInPlace2Prog {β : Type v} (xs ys rs len : USize) (n : Nat)
    (hn : n < USize.size) (hx : xs.toNat + len.toNat ≤ n) (hy : ys.toNat + len.toNat ≤ n)
    (hr : rs.toNat + len.toNat ≤ n)
    (f : (j : USize) → j.toNat < len.toNat → ISize → ISize → β → ISize × β)
    (c : ISizeArray) (hc : c.size = n) (j : USize) (hj : j.toNat ≤ len.toNat) (b : β) :
    (foldlInPlace2Prog xs ys rs len hx hy hr f j b).run c hc =
      ((foldlInPlace2.loop xs.toNat ys.toNat rs.toNat len.toNat f c (hc ▸ hx) (hc ▸ hy)
          (hc ▸ hr) j.toNat b).2,
        (foldlInPlace2.loop xs.toNat ys.toNat rs.toNat len.toNat f c (hc ▸ hx) (hc ▸ hy)
          (hc ▸ hr) j.toNat b).1) := by
  unfold foldlInPlace2Prog
  rw [InPlace.forUpFrom_eq, foldlInPlace2.loop]
  unfold foldlInPlace2Body
  by_cases hjl : j < len
  · have hjl' : j.toNat < len.toNat := hjl
    rw [dite_eq_left_of_eq_true (eq_true hjl), dite_eq_left_of_eq_true (eq_true hjl')]
    simp only [InPlace.run_bind, InPlace.run_readThen, InPlace.run_write, InPlace.run_pure]
    have ex := Slice.toNat_add_of_window hn hx hjl'
    have ey := Slice.toNat_add_of_window hn hy hjl'
    have er := Slice.toNat_add_of_window hn hr hjl'
    have ej : j.toNat.toUSize = j := by simp
    have h1 : (j + 1).toNat ≤ len.toNat := by rw [Slice.toNat_succ_of_lt' hjl']; lia
    have ih := fun c hc b => run_foldlInPlace2Prog xs ys rs len n hn hx hy hr f c hc (j + 1) h1 b
    unfold foldlInPlace2Prog foldlInPlace2Body at ih
    rw [ih]
    simp only [Slice.toNat_succ_of_lt' hjl']
    congr 3 <;> simp only [ex, ey, er, ej]
  · have hjl' : ¬j.toNat < len.toNat := hjl
    rw [dite_eq_right_of_eq_false (eq_false hjl), dite_eq_right_of_eq_false (eq_false hjl')]
    simp only [InPlace.run_pure]
termination_by len.toNat - j.toNat
decreasing_by rw [Slice.toNat_succ_of_lt' hjl']; lia

/-- For internal use only. -/
@[inline]
public def foldlInPlace2Impl {β : Type v} (a : ISizeArray) (xs ys rs len : USize)
    (hx : xs.toNat + len.toNat ≤ a.size) (hy : ys.toNat + len.toNat ≤ a.size)
    (hr : rs.toNat + len.toNat ≤ a.size) (init : β)
    (f : (j : USize) → j.toNat < len.toNat → ISize → ISize → β → ISize × β) :
    ISizeArray × β :=
  if a.size < USize.size then
    let r := a.runInPlace (foldlInPlace2Prog xs ys rs len hx hy hr f 0 init)
    (r.2, r.1)
  else
    a.foldlInPlace2 xs ys rs len hx hy hr init f

@[csimp] public theorem foldlInPlace2_eq_foldlInPlace2Impl :
    @foldlInPlace2 = @foldlInPlace2Impl := by
  funext β a xs ys rs len hx hy hr init f
  unfold foldlInPlace2Impl
  split
  · rename_i hn
    rw [runInPlace_eq, run_foldlInPlace2Prog (hn := hn) (hj := by simp)]
    rfl
  · rfl

/--
`foldlInPlace2` followed by `g` on the new array and the last accumulator, which the loop calls
itself where `foldlInPlace2` returns them as a pair. When `g` consumes the accumulator, no pair is
allocated. `g` also receives a proof that the size is unchanged, so that it can go on with bounded
reads and writes, such as another `foldlInPlace2Then`.
-/
@[expose]
public def foldlInPlace2Then {β : Type v} {γ : Type w} (a : ISizeArray) (xs ys rs len : USize)
    (hx : xs.toNat + len.toNat ≤ a.size) (hy : ys.toNat + len.toNat ≤ a.size)
    (hr : rs.toNat + len.toNat ≤ a.size) (init : β)
    (f : (j : USize) → j.toNat < len.toNat → ISize → ISize → β → ISize × β)
    (g : (a' : ISizeArray) → a'.size = a.size → β → γ) : γ :=
  g (a.foldlInPlace2 xs ys rs len hx hy hr init f).1 (size_foldlInPlace2 ..)
    (a.foldlInPlace2 xs ys rs len hx hy hr init f).2

@[simp] public theorem foldlInPlace2Then_eq {β : Type v} {γ : Type w} (a : ISizeArray)
    (xs ys rs len : USize) (hx : xs.toNat + len.toNat ≤ a.size)
    (hy : ys.toNat + len.toNat ≤ a.size) (hr : rs.toNat + len.toNat ≤ a.size) (init : β)
    (f : (j : USize) → j.toNat < len.toNat → ISize → ISize → β → ISize × β)
    (g : (a' : ISizeArray) → a'.size = a.size → β → γ) :
    a.foldlInPlace2Then xs ys rs len hx hy hr init f g =
      g (a.foldlInPlace2 xs ys rs len hx hy hr init f).1 (size_foldlInPlace2 ..)
        (a.foldlInPlace2 xs ys rs len hx hy hr init f).2 :=
  rfl

/-- For internal use only. -/
@[inline]
public def foldlInPlace2ThenImpl {β : Type v} {γ : Type w} (a : ISizeArray) (xs ys rs len : USize)
    (hx : xs.toNat + len.toNat ≤ a.size) (hy : ys.toNat + len.toNat ≤ a.size)
    (hr : rs.toNat + len.toNat ≤ a.size) (init : β)
    (f : (j : USize) → j.toNat < len.toNat → ISize → ISize → β → ISize × β)
    (g : (a' : ISizeArray) → a'.size = a.size → β → γ) : γ :=
  if _ : a.size < USize.size then
    InPlace.runForUpFromThen a rfl len 0 init (foldlInPlace2Body xs ys rs len hx hy hr f)
      fun b a' ha => g a' ha b
  else
    let r := a.foldlInPlace2 xs ys rs len hx hy hr init f
    g r.1 (size_foldlInPlace2 ..) r.2

@[csimp] public theorem foldlInPlace2Then_eq_foldlInPlace2ThenImpl :
    @foldlInPlace2Then = @foldlInPlace2ThenImpl := by
  funext β γ a xs ys rs len hx hy hr init f g
  unfold foldlInPlace2ThenImpl
  split
  · rename_i hN
    have key := run_foldlInPlace2Prog xs ys rs len a.size hN hx hy hr f a rfl 0 (by simp) init
    rw [InPlace.runForUpFromThen_eq, foldlInPlace2Then_eq]
    exact congr_then g (congrArg Prod.snd key).symm (congrArg Prod.fst key).symm _ _
  · rfl

/-! ## In-place folds over a `USize` range -/

/--
`foldlInPlace` on the slice `a[start.toNat...start.toNat + len.toNat]`, for bounds that are
already `USize`: returns the new array and the last accumulator. It is specified as that slice
fold, so the slice lemmas apply after `foldlInPlaceRange_eq`. The implementation runs the loop of
`foldlInPlace` on the `USize` bounds directly, without building the slice, whose `Nat` bounds
cost a conversion on the way in and out of every call.
-/
@[expose]
public def foldlInPlaceRange {β : Type v} (a : ISizeArray) (start len : USize)
    (h : start.toNat + len.toNat ≤ a.size) (init : β)
    (f : (k : USize) → k.toNat < len.toNat → ISize → β → ISize × β) :
    ISizeArray × β :=
  (((a.toSlice start.toNat (start.toNat + len.toNat)).foldlInPlace init
      fun k hk => f k (by simp only [size_toSlice] at hk; lia)).1.array,
    ((a.toSlice start.toNat (start.toNat + len.toNat)).foldlInPlace init
      fun k hk => f k (by simp only [size_toSlice] at hk; lia)).2)

@[simp] public theorem foldlInPlaceRange_eq {β : Type v} (a : ISizeArray) (start len : USize)
    (h : start.toNat + len.toNat ≤ a.size) (init : β)
    (f : (k : USize) → k.toNat < len.toNat → ISize → β → ISize × β) :
    a.foldlInPlaceRange start len h init f =
      (((a.toSlice start.toNat (start.toNat + len.toNat)).foldlInPlace init
          fun k hk => f k (by simp only [size_toSlice] at hk; lia)).1.array,
        ((a.toSlice start.toNat (start.toNat + len.toNat)).foldlInPlace init
          fun k hk => f k (by simp only [size_toSlice] at hk; lia)).2) :=
  rfl

@[simp] public theorem size_foldlInPlaceRange {β : Type v} (a : ISizeArray) (start len : USize)
    (h : start.toNat + len.toNat ≤ a.size) (init : β)
    (f : (k : USize) → k.toNat < len.toNat → ISize → β → ISize × β) :
    (a.foldlInPlaceRange start len h init f).1.size = a.size := by
  simp

private theorem foldlInPlaceRange_eq_run {β : Type v} (a : ISizeArray) (start len : USize)
    (h : start.toNat + len.toNat ≤ a.size) (init : β)
    (f : (k : USize) → k.toNat < len.toNat → ISize → β → ISize × β) (hN : a.size < USize.size) :
    a.foldlInPlaceRange start len h init f =
      ((a.runInPlace (Slice.foldlInPlaceProg start len h f 0 init)).2,
        (a.runInPlace (Slice.foldlInPlaceProg start len h f 0 init)).1) := by
  have hsz : len.toNat = (a.toSlice start.toNat (start.toNat + len.toNat)).size := by simp; lia
  have hst : (a.toSlice start.toNat (start.toNat + len.toNat)).start = start.toNat := by simp; lia
  have key := Slice.run_foldlInPlaceProg start len a.size _ hN h hsz
    (fun k hk => f k (by simp only [size_toSlice] at hk; lia)) _ rfl hst a (array_toSlice ..) rfl 0
    (by simp) init
  rw [runInPlace_eq]
  exact (Prod.ext (congrArg Prod.snd key) (congrArg Prod.fst key)).symm

/-- For internal use only. -/
@[inline]
public def foldlInPlaceRangeImpl {β : Type v} (a : ISizeArray) (start len : USize)
    (h : start.toNat + len.toNat ≤ a.size) (init : β)
    (f : (k : USize) → k.toNat < len.toNat → ISize → β → ISize × β) :
    ISizeArray × β :=
  if a.size < USize.size then
    let r := a.runInPlace (Slice.foldlInPlaceProg start len h f 0 init)
    (r.2, r.1)
  else
    a.foldlInPlaceRange start len h init f

@[csimp] public theorem foldlInPlaceRange_eq_foldlInPlaceRangeImpl :
    @foldlInPlaceRange = @foldlInPlaceRangeImpl := by
  funext β a start len h init f
  unfold foldlInPlaceRangeImpl
  split
  · exact foldlInPlaceRange_eq_run a start len h init f ‹_›
  · rfl

/--
`foldlInPlaceRange` followed by `g` on the new array and the last accumulator, which the loop
calls itself where `foldlInPlaceRange` returns them as a pair, like `Slice.foldlInPlaceThen`.
`g` also receives a proof that the size is unchanged, like `foldlInPlace2Then`, so that it can go
on with bounded reads and writes.
-/
@[expose]
public def foldlInPlaceRangeThen {β : Type v} {γ : Type w} (a : ISizeArray) (start len : USize)
    (h : start.toNat + len.toNat ≤ a.size) (init : β)
    (f : (k : USize) → k.toNat < len.toNat → ISize → β → ISize × β)
    (g : (a' : ISizeArray) → a'.size = a.size → β → γ) : γ :=
  g (a.foldlInPlaceRange start len h init f).1 (size_foldlInPlaceRange ..)
        (a.foldlInPlaceRange start len h init f).2

@[simp] public theorem foldlInPlaceRangeThen_eq {β : Type v} {γ : Type w} (a : ISizeArray)
    (start len : USize) (h : start.toNat + len.toNat ≤ a.size) (init : β)
    (f : (k : USize) → k.toNat < len.toNat → ISize → β → ISize × β)
    (g : (a' : ISizeArray) → a'.size = a.size → β → γ) :
    a.foldlInPlaceRangeThen start len h init f g =
      g (a.foldlInPlaceRange start len h init f).1 (size_foldlInPlaceRange ..)
        (a.foldlInPlaceRange start len h init f).2 :=
  rfl

/-- For internal use only. -/
@[inline]
public def foldlInPlaceRangeThenImpl {β : Type v} {γ : Type w} (a : ISizeArray) (start len : USize)
    (h : start.toNat + len.toNat ≤ a.size) (init : β)
    (f : (k : USize) → k.toNat < len.toNat → ISize → β → ISize × β)
    (g : (a' : ISizeArray) → a'.size = a.size → β → γ) : γ :=
  if _ : a.size < USize.size then
    InPlace.runForUpFromThen a rfl len 0 init (Slice.foldInPlaceBody start len h f)
      fun b a' ha => g a' ha b
  else
    let r := a.foldlInPlaceRange start len h init f
    g r.1 (size_foldlInPlaceRange ..) r.2

@[csimp] public theorem foldlInPlaceRangeThen_eq_foldlInPlaceRangeThenImpl :
    @foldlInPlaceRangeThen = @foldlInPlaceRangeThenImpl := by
  funext β γ a start len h init f g
  unfold foldlInPlaceRangeThenImpl
  split
  · rename_i hN
    have key := foldlInPlaceRange_eq_run a start len h init f hN
    rw [InPlace.runForUpFromThen_eq, foldlInPlaceRangeThen_eq]
    exact congr_then g (congrArg Prod.fst key) (congrArg Prod.snd key) _ _
  · rfl

/--
`foldlInPlaceRange` with two accumulators: returns the new array and the two last accumulators.
It is specified as `foldlInPlaceRange` on the pair of accumulators, so the lemmas about that fold
apply after `foldlInPlaceRangeWith2Acc_eq`. The implementation passes the two accumulators as
separate arguments of the loop, where a pair would be allocated at every element and would box
scalar accumulators such as `UInt64` carries.
-/
@[expose]
public def foldlInPlaceRangeWith2Acc {β₁ : Type v} {β₂ : Type w} (a : ISizeArray)
    (start len : USize) (h : start.toNat + len.toNat ≤ a.size) (init₁ : β₁) (init₂ : β₂)
    (f : (k : USize) → k.toNat < len.toNat → ISize → β₁ → β₂ → ISize × β₁ × β₂) :
    ISizeArray × β₁ × β₂ :=
  a.foldlInPlaceRange start len h (init₁, init₂) fun k hk x b => f k hk x b.1 b.2

@[simp] public theorem foldlInPlaceRangeWith2Acc_eq {β₁ : Type v} {β₂ : Type w}
    (a : ISizeArray) (start len : USize) (h : start.toNat + len.toNat ≤ a.size) (init₁ : β₁)
    (init₂ : β₂)
    (f : (k : USize) → k.toNat < len.toNat → ISize → β₁ → β₂ → ISize × β₁ × β₂) :
    a.foldlInPlaceRangeWith2Acc start len h init₁ init₂ f =
      a.foldlInPlaceRange start len h (init₁, init₂) fun k hk x b => f k hk x b.1 b.2 :=
  rfl

@[simp] public theorem size_foldlInPlaceRangeWith2Acc {β₁ : Type v} {β₂ : Type w}
    (a : ISizeArray) (start len : USize) (h : start.toNat + len.toNat ≤ a.size) (init₁ : β₁)
    (init₂ : β₂)
    (f : (k : USize) → k.toNat < len.toNat → ISize → β₁ → β₂ → ISize × β₁ × β₂) :
    (a.foldlInPlaceRangeWith2Acc start len h init₁ init₂ f).1.size = a.size := by
  simp

/-- The step of `foldlInPlaceRangeWith2Acc`. -/
@[inline]
private def foldlInPlaceRangeWith2AccBody {β₁ : Type v} {β₂ : Type w} {n : Nat}
    (start len : USize) (hw : start.toNat + len.toNat ≤ n)
    (f : (k : USize) → k.toNat < len.toNat → ISize → β₁ → β₂ → ISize × β₁ × β₂) (k : USize)
    (hk : k.toNat < len.toNat) (b₁ : β₁) (b₂ : β₂) : InPlace n (β₁ × β₂) :=
  InPlace.readThen (start + k) (InPlace.toNat_add_lt_of_window hw hk) fun x =>
  let p := f k hk x b₁ b₂
  InPlace.write (start + k) (InPlace.toNat_add_lt_of_window hw hk) p.1 >>= fun _ =>
    pure (p.2.1, p.2.2)

private theorem forUp2From_with2AccBody {β₁ : Type v} {β₂ : Type w} {n : Nat}
    (start len : USize) (hw : start.toNat + len.toNat ≤ n)
    (f : (k : USize) → k.toNat < len.toNat → ISize → β₁ → β₂ → ISize × β₁ × β₂)
    (init₁ : β₁) (init₂ : β₂) :
    InPlace.forUp2From len 0 init₁ init₂ (foldlInPlaceRangeWith2AccBody start len hw f) =
      InPlace.forUpFrom len 0 (init₁, init₂)
        (Slice.foldInPlaceBody start len hw fun k hk x b => f k hk x b.1 b.2) := by
  rw [InPlace.forUp2From_eq_forUpFrom]
  rfl

/-- The program of `foldlInPlaceRangeWith2Acc`, with the two accumulators kept apart. -/
@[inline]
private def foldlInPlaceRangeWith2AccProg {β₁ : Type v} {β₂ : Type w} {n : Nat}
    (start len : USize) (hw : start.toNat + len.toNat ≤ n)
    (f : (k : USize) → k.toNat < len.toNat → ISize → β₁ → β₂ → ISize × β₁ × β₂)
    (b₁ : β₁) (b₂ : β₂) : InPlace n (β₁ × β₂) :=
  InPlace.forUp2 len b₁ b₂ (foldlInPlaceRangeWith2AccBody start len hw f)

/-- For internal use only. -/
@[inline]
public def foldlInPlaceRangeWith2AccImpl {β₁ : Type v} {β₂ : Type w} (a : ISizeArray)
    (start len : USize) (h : start.toNat + len.toNat ≤ a.size) (init₁ : β₁) (init₂ : β₂)
    (f : (k : USize) → k.toNat < len.toNat → ISize → β₁ → β₂ → ISize × β₁ × β₂) :
    ISizeArray × β₁ × β₂ :=
  if a.size < USize.size then
    let r := a.runInPlace (foldlInPlaceRangeWith2AccProg start len h f init₁ init₂)
    (r.2, r.1.1, r.1.2)
  else
    a.foldlInPlaceRangeWith2Acc start len h init₁ init₂ f

@[csimp] public theorem foldlInPlaceRangeWith2Acc_eq_foldlInPlaceRangeWith2AccImpl :
    @foldlInPlaceRangeWith2Acc = @foldlInPlaceRangeWith2AccImpl := by
  funext β₁ β₂ a start len h init₁ init₂ f
  unfold foldlInPlaceRangeWith2AccImpl
  split
  · rename_i hN
    rw [foldlInPlaceRangeWith2Acc_eq, foldlInPlaceRange_eq_run (hN := hN)]
    unfold foldlInPlaceRangeWith2AccProg
    rw [InPlace.forUp2_eq, forUp2From_with2AccBody]
    rfl
  · rfl

/--
`foldlInPlaceRangeWith2Acc` followed by `g` on the new array, a proof that its size is unchanged
and the two last accumulators, like `foldlInPlaceRangeThen`.
-/
@[expose]
public def foldlInPlaceRangeWith2AccThen {β₁ : Type v} {β₂ : Type w} {γ : Type u}
    (a : ISizeArray) (start len : USize) (h : start.toNat + len.toNat ≤ a.size) (init₁ : β₁)
    (init₂ : β₂)
    (f : (k : USize) → k.toNat < len.toNat → ISize → β₁ → β₂ → ISize × β₁ × β₂)
    (g : (a' : ISizeArray) → a'.size = a.size → β₁ → β₂ → γ) : γ :=
  a.foldlInPlaceRangeThen start len h (init₁, init₂) (fun k hk x b => f k hk x b.1 b.2)
    fun a' ha b => g a' ha b.1 b.2

@[simp] public theorem foldlInPlaceRangeWith2AccThen_eq {β₁ : Type v} {β₂ : Type w} {γ : Type u}
    (a : ISizeArray) (start len : USize) (h : start.toNat + len.toNat ≤ a.size) (init₁ : β₁)
    (init₂ : β₂)
    (f : (k : USize) → k.toNat < len.toNat → ISize → β₁ → β₂ → ISize × β₁ × β₂)
    (g : (a' : ISizeArray) → a'.size = a.size → β₁ → β₂ → γ) :
    a.foldlInPlaceRangeWith2AccThen start len h init₁ init₂ f g =
      a.foldlInPlaceRangeThen start len h (init₁, init₂) (fun k hk x b => f k hk x b.1 b.2)
        fun a' ha b => g a' ha b.1 b.2 :=
  rfl

/-- For internal use only. -/
@[inline]
public def foldlInPlaceRangeWith2AccThenImpl {β₁ : Type v} {β₂ : Type w} {γ : Type u}
    (a : ISizeArray) (start len : USize) (h : start.toNat + len.toNat ≤ a.size) (init₁ : β₁)
    (init₂ : β₂)
    (f : (k : USize) → k.toNat < len.toNat → ISize → β₁ → β₂ → ISize × β₁ × β₂)
    (g : (a' : ISizeArray) → a'.size = a.size → β₁ → β₂ → γ) : γ :=
  if _ : a.size < USize.size then
    InPlace.runForUp2FromThen a rfl len 0 init₁ init₂ (foldlInPlaceRangeWith2AccBody start len h f)
      fun b₁ b₂ a' ha => g a' ha b₁ b₂
  else
    let r := a.foldlInPlaceRangeWith2Acc start len h init₁ init₂ f
    g r.1 (size_foldlInPlaceRangeWith2Acc ..) r.2.1 r.2.2

@[csimp] public theorem foldlInPlaceRangeWith2AccThen_eq_foldlInPlaceRangeWith2AccThenImpl :
    @foldlInPlaceRangeWith2AccThen = @foldlInPlaceRangeWith2AccThenImpl := by
  funext β₁ β₂ γ a start len h init₁ init₂ f g
  unfold foldlInPlaceRangeWith2AccThenImpl
  split
  · rename_i hN
    have key := foldlInPlaceRange_eq_run a start len h (init₁, init₂)
      (fun k hk x b => f k hk x b.1 b.2) hN
    rw [InPlace.runForUp2FromThen_eq, forUp2From_with2AccBody, foldlInPlaceRangeWith2AccThen_eq,
      foldlInPlaceRangeThen_eq]
    exact congr_then2 g (congrArg Prod.fst key) (congrArg (·.2.1) key) (congrArg (·.2.2) key) _ _
  · rfl

/--
`foldrInPlace` on the slice `a[start.toNat...start.toNat + len.toNat]`, for bounds that are
already `USize`, like `foldlInPlaceRange`: returns the new array and the last accumulator.
-/
@[expose]
public def foldrInPlaceRange {β : Type v} (a : ISizeArray) (start len : USize)
    (h : start.toNat + len.toNat ≤ a.size) (init : β)
    (f : (k : USize) → k.toNat < len.toNat → ISize → β → ISize × β) :
    ISizeArray × β :=
  (((a.toSlice start.toNat (start.toNat + len.toNat)).foldrInPlace init
      fun k hk => f k (by simp only [size_toSlice] at hk; lia)).1.array,
    ((a.toSlice start.toNat (start.toNat + len.toNat)).foldrInPlace init
      fun k hk => f k (by simp only [size_toSlice] at hk; lia)).2)

@[simp] public theorem foldrInPlaceRange_eq {β : Type v} (a : ISizeArray) (start len : USize)
    (h : start.toNat + len.toNat ≤ a.size) (init : β)
    (f : (k : USize) → k.toNat < len.toNat → ISize → β → ISize × β) :
    a.foldrInPlaceRange start len h init f =
      (((a.toSlice start.toNat (start.toNat + len.toNat)).foldrInPlace init
          fun k hk => f k (by simp only [size_toSlice] at hk; lia)).1.array,
        ((a.toSlice start.toNat (start.toNat + len.toNat)).foldrInPlace init
          fun k hk => f k (by simp only [size_toSlice] at hk; lia)).2) :=
  rfl

@[simp] public theorem size_foldrInPlaceRange {β : Type v} (a : ISizeArray) (start len : USize)
    (h : start.toNat + len.toNat ≤ a.size) (init : β)
    (f : (k : USize) → k.toNat < len.toNat → ISize → β → ISize × β) :
    (a.foldrInPlaceRange start len h init f).1.size = a.size := by
  simp

private theorem foldrInPlaceRange_eq_run {β : Type v} (a : ISizeArray) (start len : USize)
    (h : start.toNat + len.toNat ≤ a.size) (init : β)
    (f : (k : USize) → k.toNat < len.toNat → ISize → β → ISize × β) (hN : a.size < USize.size) :
    a.foldrInPlaceRange start len h init f =
      ((a.runInPlace (Slice.foldrInPlaceProg start len h f len (Nat.le_refl _) init)).2,
        (a.runInPlace (Slice.foldrInPlaceProg start len h f len (Nat.le_refl _) init)).1) := by
  have hsz : len.toNat = (a.toSlice start.toNat (start.toNat + len.toNat)).size := by simp; lia
  have hst : (a.toSlice start.toNat (start.toNat + len.toNat)).start = start.toNat := by simp; lia
  have key := Slice.run_foldrInPlaceProg start len a.size _ hN h hsz
    (fun k hk => f k (by simp only [size_toSlice] at hk; lia)) _ _ rfl hst a (array_toSlice ..) rfl
    len (Nat.le_refl _) hsz init
  rw [runInPlace_eq]
  exact (Prod.ext (congrArg Prod.snd key) (congrArg Prod.fst key)).symm

/-- For internal use only. -/
@[inline]
public def foldrInPlaceRangeImpl {β : Type v} (a : ISizeArray) (start len : USize)
    (h : start.toNat + len.toNat ≤ a.size) (init : β)
    (f : (k : USize) → k.toNat < len.toNat → ISize → β → ISize × β) :
    ISizeArray × β :=
  if a.size < USize.size then
    let r := a.runInPlace (Slice.foldrInPlaceProg start len h f len (Nat.le_refl _) init)
    (r.2, r.1)
  else
    a.foldrInPlaceRange start len h init f

@[csimp] public theorem foldrInPlaceRange_eq_foldrInPlaceRangeImpl :
    @foldrInPlaceRange = @foldrInPlaceRangeImpl := by
  funext β a start len h init f
  unfold foldrInPlaceRangeImpl
  split
  · exact foldrInPlaceRange_eq_run a start len h init f ‹_›
  · rfl

/--
`foldrInPlaceRange` followed by `g` on the new array, a proof that its size is unchanged and the
last accumulator, like `foldlInPlaceRangeThen`.
-/
@[expose]
public def foldrInPlaceRangeThen {β : Type v} {γ : Type w} (a : ISizeArray) (start len : USize)
    (h : start.toNat + len.toNat ≤ a.size) (init : β)
    (f : (k : USize) → k.toNat < len.toNat → ISize → β → ISize × β)
    (g : (a' : ISizeArray) → a'.size = a.size → β → γ) : γ :=
  g (a.foldrInPlaceRange start len h init f).1 (size_foldrInPlaceRange ..)
        (a.foldrInPlaceRange start len h init f).2

@[simp] public theorem foldrInPlaceRangeThen_eq {β : Type v} {γ : Type w} (a : ISizeArray)
    (start len : USize) (h : start.toNat + len.toNat ≤ a.size) (init : β)
    (f : (k : USize) → k.toNat < len.toNat → ISize → β → ISize × β)
    (g : (a' : ISizeArray) → a'.size = a.size → β → γ) :
    a.foldrInPlaceRangeThen start len h init f g =
      g (a.foldrInPlaceRange start len h init f).1 (size_foldrInPlaceRange ..)
        (a.foldrInPlaceRange start len h init f).2 :=
  rfl

/-- For internal use only. -/
@[inline]
public def foldrInPlaceRangeThenImpl {β : Type v} {γ : Type w} (a : ISizeArray) (start len : USize)
    (h : start.toNat + len.toNat ≤ a.size) (init : β)
    (f : (k : USize) → k.toNat < len.toNat → ISize → β → ISize × β)
    (g : (a' : ISizeArray) → a'.size = a.size → β → γ) : γ :=
  if _ : a.size < USize.size then
    InPlace.runForDownFromThen a rfl len len (Nat.le_refl _) init (Slice.foldInPlaceBody start len h f)
      fun b a' ha => g a' ha b
  else
    let r := a.foldrInPlaceRange start len h init f
    g r.1 (size_foldrInPlaceRange ..) r.2

@[csimp] public theorem foldrInPlaceRangeThen_eq_foldrInPlaceRangeThenImpl :
    @foldrInPlaceRangeThen = @foldrInPlaceRangeThenImpl := by
  funext β γ a start len h init f g
  unfold foldrInPlaceRangeThenImpl
  split
  · rename_i hN
    have key := foldrInPlaceRange_eq_run a start len h init f hN
    rw [InPlace.runForDownFromThen_eq, foldrInPlaceRangeThen_eq]
    exact congr_then g (congrArg Prod.fst key) (congrArg Prod.snd key) _ _
  · rfl

end ISizeArray

end ScalarArray
