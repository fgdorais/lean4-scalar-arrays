/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ScalarArray.ISize.Lemmas
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

/-! ## Writing through slices -/

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
  split <;> (try congr 1) <;> lia

@[simp] public theorem toList_copy_reverse (s : ISizeArray.Slice) :
    s.reverse.copy.toList = s.copy.toList.reverse := by
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    simp only [getElem_toList, getElem_copy, getElem_reverse, List.getElem_reverse]
    congr 1
    simp

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

@[specialize]
private unsafe def foldlInPlaceImpl.loop {β : Type v} {γ : Type w} (base len : USize)
    (f : (k : USize) → k.toNat < len.toNat → ISize → β → ISize × β) (g : ISizeArray → β → γ)
    (a : ISizeArray) (k : USize) (b : β) : γ :=
  if k < len then
    let p := f k lcProof (a.uget (base + k) lcProof) b
    foldlInPlaceImpl.loop base len f g (setUnsafe a (base + k) p.1) (k + 1) p.2
  else
    g a b

@[inline]
private unsafe def foldlInPlaceImpl {β : Type v} (s : ISizeArray.Slice) (init : β)
    (f : (k : USize) → k.toNat < s.size → ISize → β → ISize × β) : ISizeArray.Slice × β :=
  match s with
  | ⟨⟨a, start, stop, h, _⟩⟩ =>
    foldlInPlaceImpl.loop start.toUSize (stop - start).toUSize (fun k _ => f k lcProof)
      (fun a b => (⟨⟨a, start, stop, h, lcProof⟩⟩, b))
      a.ensureExclusive 0 init

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
@[implemented_by foldlInPlaceImpl, expose]
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

@[specialize]
private unsafe def foldrInPlaceImpl.loop {β : Type v} {γ : Type w} (base : USize)
    (f : (k : USize) → ISize → β → ISize × β) (g : ISizeArray → β → γ) (a : ISizeArray)
    (k : USize) (b : β) : γ :=
  if 0 < k then
    let k := k - 1
    let p := f k (a.uget (base + k) lcProof) b
    foldrInPlaceImpl.loop base f g (setUnsafe a (base + k) p.1) k p.2
  else
    g a b

@[inline]
private unsafe def foldrInPlaceImpl {β : Type v} (s : ISizeArray.Slice) (init : β)
    (f : (k : USize) → k.toNat < s.size → ISize → β → ISize × β) : ISizeArray.Slice × β :=
  match s with
  | ⟨⟨a, start, stop, h, _⟩⟩ =>
    foldrInPlaceImpl.loop start.toUSize (fun k => f k lcProof)
      (fun a b => (⟨⟨a, start, stop, h, lcProof⟩⟩, b))
      a.ensureExclusive (stop - start).toUSize init

/--
Replaces each element of the slice while threading an accumulator, like `foldlInPlace` but from
the last element to the first: for each `k < s.size`, from `s.size - 1` down to `0`, the element
`x` at index `k` of the slice becomes the first component of `f k hk x b`, whose second component
is the next accumulator. Returns the new slice and the last accumulator.

The array is made exclusive once, before the loop, which then stores without checks.
-/
@[implemented_by foldrInPlaceImpl, expose]
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

@[inline]
private unsafe def foldlInPlaceThenImpl {β : Type v} {γ : Type w} (s : ISizeArray.Slice)
    (init : β) (f : (k : USize) → k.toNat < s.size → ISize → β → ISize × β)
    (g : ISizeArray.Slice → β → γ) : γ :=
  match s with
  | ⟨⟨a, start, stop, h, _⟩⟩ =>
    foldlInPlaceImpl.loop start.toUSize (stop - start).toUSize (fun k _ => f k lcProof)
      (fun a b => g ⟨⟨a, start, stop, h, lcProof⟩⟩ b)
      a.ensureExclusive 0 init

/--
`foldlInPlace` followed by `g` on the new slice and the last accumulator, which the loop calls
itself where `foldlInPlace` returns them as a pair. The pair is a heap object, allocated once per
call, which shows when the fold runs over short slices many times; when `g` consumes the
accumulator, for example by writing it into the slice, no pair is allocated at all.
`foldlInPlace` is the case `g := Prod.mk`.
-/
@[implemented_by foldlInPlaceThenImpl, expose]
public def foldlInPlaceThen {β : Type v} {γ : Type w} (s : ISizeArray.Slice) (init : β)
    (f : (k : USize) → k.toNat < s.size → ISize → β → ISize × β)
    (g : ISizeArray.Slice → β → γ) : γ :=
  g (s.foldlInPlace init f).1 (s.foldlInPlace init f).2

@[simp] public theorem foldlInPlaceThen_eq {β : Type v} {γ : Type w} (s : ISizeArray.Slice)
    (init : β) (f : (k : USize) → k.toNat < s.size → ISize → β → ISize × β)
    (g : ISizeArray.Slice → β → γ) :
    s.foldlInPlaceThen init f g = g (s.foldlInPlace init f).1 (s.foldlInPlace init f).2 :=
  rfl

@[inline]
private unsafe def foldrInPlaceThenImpl {β : Type v} {γ : Type w} (s : ISizeArray.Slice)
    (init : β) (f : (k : USize) → k.toNat < s.size → ISize → β → ISize × β)
    (g : ISizeArray.Slice → β → γ) : γ :=
  match s with
  | ⟨⟨a, start, stop, h, _⟩⟩ =>
    foldrInPlaceImpl.loop start.toUSize (fun k => f k lcProof)
      (fun a b => g ⟨⟨a, start, stop, h, lcProof⟩⟩ b)
      a.ensureExclusive (stop - start).toUSize init

/--
`foldrInPlace` followed by `g` on the new slice and the last accumulator, which the loop calls
itself where `foldrInPlace` returns them as a pair. When `g` consumes the accumulator, no pair is
allocated. `foldrInPlace` is the case `g := Prod.mk`.
-/
@[implemented_by foldrInPlaceThenImpl, expose]
public def foldrInPlaceThen {β : Type v} {γ : Type w} (s : ISizeArray.Slice) (init : β)
    (f : (k : USize) → k.toNat < s.size → ISize → β → ISize × β)
    (g : ISizeArray.Slice → β → γ) : γ :=
  g (s.foldrInPlace init f).1 (s.foldrInPlace init f).2

@[simp] public theorem foldrInPlaceThen_eq {β : Type v} {γ : Type w} (s : ISizeArray.Slice)
    (init : β) (f : (k : USize) → k.toNat < s.size → ISize → β → ISize × β)
    (g : ISizeArray.Slice → β → γ) :
    s.foldrInPlaceThen init f g = g (s.foldrInPlace init f).1 (s.foldrInPlace init f).2 :=
  rfl

end Slice

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

@[specialize]
private unsafe def foldlInPlace2Impl.loop {β : Type v} {γ : Type w} (xs ys rs len : USize)
    (f : (j : USize) → ISize → ISize → β → ISize × β) (g : ISizeArray → β → γ)
    (a : ISizeArray) (j : USize) (b : β) : γ :=
  if j < len then
    let p := f j (a.uget (xs + j) lcProof) (a.uget (ys + j) lcProof) b
    foldlInPlace2Impl.loop xs ys rs len f g (setUnsafe a (rs + j) p.1) (j + 1) p.2
  else
    g a b

@[inline]
private unsafe def foldlInPlace2Impl {β : Type v} (a : ISizeArray) (xs ys rs len : USize)
    (_ : xs.toNat + len.toNat ≤ a.size) (_ : ys.toNat + len.toNat ≤ a.size)
    (_ : rs.toNat + len.toNat ≤ a.size) (init : β)
    (f : (j : USize) → j.toNat < len.toNat → ISize → ISize → β → ISize × β) :
    ISizeArray × β :=
  foldlInPlace2Impl.loop xs ys rs len (fun j => f j lcProof) Prod.mk a.ensureExclusive 0 init

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
@[implemented_by foldlInPlace2Impl, expose]
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

@[inline]
private unsafe def foldlInPlace2ThenImpl {β : Type v} {γ : Type w} (a : ISizeArray)
    (xs ys rs len : USize) (_ : xs.toNat + len.toNat ≤ a.size)
    (_ : ys.toNat + len.toNat ≤ a.size) (_ : rs.toNat + len.toNat ≤ a.size) (init : β)
    (f : (j : USize) → j.toNat < len.toNat → ISize → ISize → β → ISize × β)
    (g : (a' : ISizeArray) → a'.size = a.size → β → γ) : γ :=
  foldlInPlace2Impl.loop xs ys rs len (fun j => f j lcProof) (fun a' b => g a' lcProof b)
    a.ensureExclusive 0 init

/--
`foldlInPlace2` followed by `g` on the new array and the last accumulator, which the loop calls
itself where `foldlInPlace2` returns them as a pair. When `g` consumes the accumulator, no pair is
allocated. `g` also receives a proof that the size is unchanged, so that it can go on with bounded
reads and writes, such as another `foldlInPlace2Then`.
-/
@[implemented_by foldlInPlace2ThenImpl, expose]
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

/-! ## In-place folds over a `USize` range -/

@[inline]
private unsafe def foldlInPlaceRangeImpl {β : Type v} (a : ISizeArray) (start len : USize)
    (_ : start.toNat + len.toNat ≤ a.size) (init : β)
    (f : (k : USize) → k.toNat < len.toNat → ISize → β → ISize × β) :
    ISizeArray × β :=
  Slice.foldlInPlaceImpl.loop start len f Prod.mk a.ensureExclusive 0 init

/--
`foldlInPlace` on the slice `a[start.toNat...start.toNat + len.toNat]`, for bounds that are
already `USize`: returns the new array and the last accumulator. It is specified as that slice
fold, so the slice lemmas apply after `foldlInPlaceRange_eq`. The implementation runs the loop of
`foldlInPlace` on the `USize` bounds directly, without building the slice, whose `Nat` bounds
cost a conversion on the way in and out of every call.
-/
@[implemented_by foldlInPlaceRangeImpl, expose]
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

@[inline]
private unsafe def foldlInPlaceRangeThenImpl {β : Type v} {γ : Type w} (a : ISizeArray)
    (start len : USize) (_ : start.toNat + len.toNat ≤ a.size) (init : β)
    (f : (k : USize) → k.toNat < len.toNat → ISize → β → ISize × β)
    (g : (a' : ISizeArray) → a'.size = a.size → β → γ) : γ :=
  Slice.foldlInPlaceImpl.loop start len f (fun a' b => g a' lcProof b)
    a.ensureExclusive 0 init

/--
`foldlInPlaceRange` followed by `g` on the new array and the last accumulator, which the loop
calls itself where `foldlInPlaceRange` returns them as a pair, like `Slice.foldlInPlaceThen`.
`g` also receives a proof that the size is unchanged, like `foldlInPlace2Then`, so that it can go
on with bounded reads and writes.
-/
@[implemented_by foldlInPlaceRangeThenImpl, expose]
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

@[inline]
private unsafe def foldrInPlaceRangeImpl {β : Type v} (a : ISizeArray) (start len : USize)
    (_ : start.toNat + len.toNat ≤ a.size) (init : β)
    (f : (k : USize) → k.toNat < len.toNat → ISize → β → ISize × β) :
    ISizeArray × β :=
  Slice.foldrInPlaceImpl.loop start (fun k => f k lcProof) Prod.mk a.ensureExclusive len init

/--
`foldrInPlace` on the slice `a[start.toNat...start.toNat + len.toNat]`, for bounds that are
already `USize`, like `foldlInPlaceRange`: returns the new array and the last accumulator.
-/
@[implemented_by foldrInPlaceRangeImpl, expose]
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

@[inline]
private unsafe def foldrInPlaceRangeThenImpl {β : Type v} {γ : Type w} (a : ISizeArray)
    (start len : USize) (_ : start.toNat + len.toNat ≤ a.size) (init : β)
    (f : (k : USize) → k.toNat < len.toNat → ISize → β → ISize × β)
    (g : (a' : ISizeArray) → a'.size = a.size → β → γ) : γ :=
  Slice.foldrInPlaceImpl.loop start (fun k => f k lcProof) (fun a' b => g a' lcProof b)
    a.ensureExclusive len init

/--
`foldrInPlaceRange` followed by `g` on the new array, a proof that its size is unchanged and the
last accumulator, like `foldlInPlaceRangeThen`.
-/
@[implemented_by foldrInPlaceRangeThenImpl, expose]
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

end ISizeArray

end ScalarArray
