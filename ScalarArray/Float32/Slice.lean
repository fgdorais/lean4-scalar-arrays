/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ScalarArray.Float32.Array
import all ScalarArray.Internal
import all ScalarArray.Float32.Basic
import all ScalarArray.Float32.Array
import Init.Data.Iterators.Lemmas.Basic
import Init.Data.Slice.InternalLemmas

/-!
# Slices of `Float32Array`

Slices of `Float32Array`: the type, reads, slice notation, iterators, folds and searches,
membership and equality, and collecting iterators into arrays.
-/

namespace ScalarArray

namespace Float32Array

/-! ## The slice type -/

/-- Internal representation of `Float32Array.Slice`. -/
public protected structure SliceData where
  /-- The underlying array. -/
  array : Float32Array
  /-- The starting index of the slice (inclusive). -/
  start : Nat
  /-- The ending index of the slice (exclusive). -/
  stop : Nat
  /-- The starting index is no later than the ending index. -/
  start_le_stop : start ≤ stop
  /-- The ending index is no later than the end of the array. -/
  stop_le_array_size : stop ≤ array.size

/--
A region of a `Float32Array`: the elements from index `start` up to, but not including, `stop`.
Taking a slice doesn't copy the array. Slices are written with core's slice notation, such as
`a[i...j]`, `a[i...*]` or `a[*...j]`.
-/
public protected abbrev Slice := Std.Slice Float32Array.SliceData

public instance : Std.Slice.Self (Std.Slice Float32Array.SliceData) Float32Array.Slice where

namespace Slice

@[always_inline, inline, expose, inherit_doc SliceData.array]
public def array (s : Float32Array.Slice) : Float32Array := s.internalRepresentation.array

@[always_inline, inline, expose, inherit_doc SliceData.start]
public def start (s : Float32Array.Slice) : Nat := s.internalRepresentation.start

@[always_inline, inline, expose, inherit_doc SliceData.stop]
public def stop (s : Float32Array.Slice) : Nat := s.internalRepresentation.stop

@[inherit_doc SliceData.start_le_stop]
public theorem start_le_stop (s : Float32Array.Slice) : s.start ≤ s.stop :=
  s.internalRepresentation.start_le_stop

@[inherit_doc SliceData.stop_le_array_size]
public theorem stop_le_array_size (s : Float32Array.Slice) : s.stop ≤ s.array.size :=
  s.internalRepresentation.stop_le_array_size

/-- `s.stop.toUSize` bounds the indices of loops over the slice. -/
private theorem toNat_toUSize_stop_le (s : Float32Array.Slice) :
    s.stop.toUSize.toNat ≤ s.array.size := by
  have := Nat.mod_le s.stop USize.size
  have := s.stop_le_array_size
  simp only [Nat.toUSize_eq, USize.toNat_ofNat']
  lia

public instance : Std.Slice.SliceSize Float32Array.SliceData where
  size s := s.internalRepresentation.stop - s.internalRepresentation.start

public theorem size_eq (s : Float32Array.Slice) : s.size = s.stop - s.start := rfl

/-! ## Reads -/

/-- The element at index `i` of the slice, counted from the start of the slice. -/
@[inline, expose]
public def get (s : Float32Array.Slice) (i : Nat) (h : i < s.size := by get_elem_tactic) :
    Float32 :=
  s.array[s.start + i]'(by have := s.stop_le_array_size; rw [size_eq] at h; lia)

public instance : GetElem Float32Array.Slice Nat Float32 fun s i => i < s.size where
  getElem s i h := s.get i h

/-- The element at index `i` of the slice, or `v₀` if `i` is out of bounds. -/
@[inline]
public def getD (s : Float32Array.Slice) (i : Nat) (v₀ : Float32) : Float32 :=
  if h : i < s.size then s[i] else v₀

/-- The element at index `i` of the slice, or `default` if `i` is out of bounds. -/
public abbrev get! (s : Float32Array.Slice) (i : Nat) : Float32 :=
  getD s i default

/-- Removes the first element of the slice, if any. -/
@[inline, expose]
public def popFront (s : Float32Array.Slice) : Float32Array.Slice :=
  if h : s.start < s.stop then
    ⟨{ s.internalRepresentation with start := s.start + 1, start_le_stop := h }⟩
  else
    s

/-! ## The empty slice, copies and printing -/

/-- The empty slice, backed by an empty array. -/
@[expose]
public protected def empty : Float32Array.Slice :=
  ⟨{ array := Float32Array.empty, start := 0, stop := 0, start_le_stop := Nat.le_refl 0,
     stop_le_array_size := Nat.le_refl 0 }⟩

public instance : EmptyCollection Float32Array.Slice := ⟨Slice.empty⟩

public instance : Inhabited Float32Array.Slice := ⟨Slice.empty⟩

/-- The elements of the slice, copied into a new array with a single `memmove`. -/
@[expose]
public def copy (s : Float32Array.Slice) : Float32Array :=
  s.array.extract s.start s.stop

public theorem getElem_eq (s : Float32Array.Slice) (i : Nat) (h : i < s.size) :
    s[i] = s.array[s.start + i]'(by have := s.stop_le_array_size; rw [size_eq] at h; lia) := rfl

/--
Prints the array and the bounds in slice notation, `(ScalarArray.Float32Array.mk #[...])[i...j]`,
which evaluates to an equal slice: slices are equal when their arrays and bounds are.
-/
public instance : Repr Float32Array.Slice where
  reprPrec s _ := reprArg s.array ++ "[" ++ repr s.start ++ "..." ++ repr s.stop ++ "]"

public instance : ToString Float32Array.Slice where
  toString s := toString s.copy

end Slice

/-! ## Slice notation -/

/--
The slice of `a` from index `start` up to, but not including, `stop`. If `start` or `stop` are not
valid bounds, they are clamped to the size of `a`, and `start` is clamped to `stop`.
-/
@[inline, expose]
public def toSlice (a : Float32Array) (start : Nat := 0) (stop : Nat := a.size) :
    Float32Array.Slice :=
  if h₂ : stop ≤ a.size then
    if h₁ : start ≤ stop then
      ⟨{ array := a, start, stop, start_le_stop := h₁, stop_le_array_size := h₂ }⟩
    else
      ⟨{ array := a, start := stop, stop, start_le_stop := Nat.le_refl _,
         stop_le_array_size := h₂ }⟩
  else
    if h₁ : start ≤ a.size then
      ⟨{ array := a, start, stop := a.size, start_le_stop := h₁,
         stop_le_array_size := Nat.le_refl _ }⟩
    else
      ⟨{ array := a, start := a.size, stop := a.size, start_le_stop := Nat.le_refl _,
         stop_le_array_size := Nat.le_refl _ }⟩

/-- Arrays coerce to slices, which is free. Slices don't coerce back, since that copies. -/
public instance : Coe Float32Array Float32Array.Slice := ⟨(·.toSlice)⟩

public instance : Std.Rcc.Sliceable Float32Array Nat Float32Array.Slice where
  mkSlice a range := a.toSlice range.lower (range.upper + 1)

public instance : Std.Rco.Sliceable Float32Array Nat Float32Array.Slice where
  mkSlice a range := a.toSlice range.lower range.upper

public instance : Std.Rci.Sliceable Float32Array Nat Float32Array.Slice where
  mkSlice a range := a.toSlice range.lower

public instance : Std.Roc.Sliceable Float32Array Nat Float32Array.Slice where
  mkSlice a range := a.toSlice (range.lower + 1) (range.upper + 1)

public instance : Std.Roo.Sliceable Float32Array Nat Float32Array.Slice where
  mkSlice a range := a.toSlice (range.lower + 1) range.upper

public instance : Std.Roi.Sliceable Float32Array Nat Float32Array.Slice where
  mkSlice a range := a.toSlice (range.lower + 1)

public instance : Std.Ric.Sliceable Float32Array Nat Float32Array.Slice where
  mkSlice a range := a.toSlice 0 (range.upper + 1)

public instance : Std.Rio.Sliceable Float32Array Nat Float32Array.Slice where
  mkSlice a range := a.toSlice 0 range.upper

public instance : Std.Rii.Sliceable Float32Array Nat Float32Array.Slice where
  mkSlice a _ := a.toSlice

namespace Slice

/-- The slice of `s` from index `start` up to, but not including, `stop`, clamped like `toSlice`. -/
@[inline, expose]
public def slice (s : Float32Array.Slice) (start : Nat := 0) (stop : Nat := s.size) :
    Float32Array.Slice :=
  s.array.toSlice (s.start + min start s.size) (s.start + min stop s.size)

end Slice

public instance : Std.Rcc.Sliceable Float32Array.Slice Nat Float32Array.Slice where
  mkSlice s range := s.slice range.lower (range.upper + 1)

public instance : Std.Rco.Sliceable Float32Array.Slice Nat Float32Array.Slice where
  mkSlice s range := s.slice range.lower range.upper

public instance : Std.Rci.Sliceable Float32Array.Slice Nat Float32Array.Slice where
  mkSlice s range := s.slice range.lower

public instance : Std.Roc.Sliceable Float32Array.Slice Nat Float32Array.Slice where
  mkSlice s range := s.slice (range.lower + 1) (range.upper + 1)

public instance : Std.Roo.Sliceable Float32Array.Slice Nat Float32Array.Slice where
  mkSlice s range := s.slice (range.lower + 1) range.upper

public instance : Std.Roi.Sliceable Float32Array.Slice Nat Float32Array.Slice where
  mkSlice s range := s.slice (range.lower + 1)

public instance : Std.Ric.Sliceable Float32Array.Slice Nat Float32Array.Slice where
  mkSlice s range := s.slice 0 (range.upper + 1)

public instance : Std.Rio.Sliceable Float32Array.Slice Nat Float32Array.Slice where
  mkSlice s range := s.slice 0 range.upper

public instance : Std.Rii.Sliceable Float32Array.Slice Nat Float32Array.Slice where
  mkSlice s _ := s

/-! ## Iterators -/

/-- The iterator over the elements of a slice, used for `for` loops and the generic slice API. -/
public protected structure SliceIterator where
  /-- The rest of the slice. -/
  xs : Float32Array.Slice

/-- One step of the iterator: the first element of the rest of the slice, if there is one. -/
@[inline, expose]
public def SliceIterator.step :
    Std.IterM (α := Float32Array.SliceIterator) Id Float32 →
      Std.IterStep (Std.IterM (α := Float32Array.SliceIterator) m Float32) Float32
  | ⟨⟨xs⟩⟩ =>
    if h : xs.start < xs.stop then
      have := xs.stop_le_array_size
      .yield ⟨⟨⟨xs.array, xs.start + 1, xs.stop, h, xs.stop_le_array_size⟩⟩⟩ xs.array[xs.start]
    else
      .done

public instance : Std.Iterator Float32Array.SliceIterator Id Float32 where
  IsPlausibleStep it step := step = SliceIterator.step it
  step it := pure <| .deflate ⟨SliceIterator.step it, rfl⟩

private def SliceIterator.finitenessRelation :
    Std.Iterators.FinitenessRelation Float32Array.SliceIterator Id where
  Rel := InvImage WellFoundedRelation.rel
    (fun it => it.internalState.xs.stop - it.internalState.xs.start)
  wf := InvImage.wf _ WellFoundedRelation.wf
  subrelation {it it'} h := by
    rcases it with ⟨⟨⟨⟨array, start, stop, h₁, h₂⟩⟩⟩⟩
    obtain ⟨step, h, h'⟩ := h
    cases h'
    simp only [SliceIterator.step] at h
    split at h
    next hs =>
      simp only [Std.IterStep.successor, Option.some.injEq] at h
      subst h
      simp only [InvImage, WellFoundedRelation.rel, sizeOf_nat, Slice.start, Slice.stop] at hs ⊢
      lia
    next =>
      simp [Std.IterStep.successor] at h

public instance : Std.Iterators.Finite Float32Array.SliceIterator Id :=
  .of_finitenessRelation SliceIterator.finitenessRelation

-- Each element goes through `lift`, like each step of the iterator in the default implementation,
-- so the two agree for every lawful `lift`, which is what core's consumers pass.
@[inline]
private unsafe def SliceIterator.forInImpl {n : Type x → Type x'} [Monad n]
    (lift : (γ : Type) → (δ : Type x) → (γ → n δ) → Id γ → n δ) (γ : Type x)
    (Pl : Float32 → γ → ForInStep γ → Prop)
    (it : Std.IterM (α := Float32Array.SliceIterator) Id Float32) (init : γ)
    (f : (b : Float32) → it.IsPlausibleIndirectOutput b → (c : γ) → n (Subtype (Pl b c))) :
    n γ :=
  let xs := it.internalState.xs
  loop xs.array xs.stop.toUSize xs.start.toUSize init
where
  @[specialize] loop (a : Float32Array) (stop i : USize) (c : γ) : n γ :=
    if i < stop then
      lift _ _ (fun x => do
        match ← f x lcProof c with
        | ⟨.yield c, _⟩ => loop a stop (i + 1) c
        | ⟨.done c, _⟩ => pure c) (pure (a.uget i lcProof))
    else pure c

/--
The loop behind `for` loops and the `Std.Iterators` consumers on slices. Logically it is
`Std.IteratorLoop.defaultImplementation`, which steps the iterator one element at a time; it is
implemented by a loop over the `USize` indices of the underlying array.
-/
@[implemented_by SliceIterator.forInImpl, expose]
public def SliceIterator.forIn {n : Type x → Type x'} [Monad n]
    (lift : (γ : Type) → (δ : Type x) → (γ → n δ) → Id γ → n δ) (γ : Type x)
    (Pl : Float32 → γ → ForInStep γ → Prop)
    (it : Std.IterM (α := Float32Array.SliceIterator) Id Float32) (init : γ)
    (f : (b : Float32) → it.IsPlausibleIndirectOutput b → (c : γ) → n (Subtype (Pl b c))) :
    n γ :=
  Std.IteratorLoop.defaultImplementation.forIn lift γ Pl it init f

public instance [Monad m] : Std.IteratorLoop Float32Array.SliceIterator Id m where
  forIn := SliceIterator.forIn

public instance [Monad m] : Std.LawfulIteratorLoop Float32Array.SliceIterator Id m where
  lawful _ _ _ _ _ _ _ _ := rfl

public instance :
    Std.ToIterator (Std.Slice Float32Array.SliceData) Id Float32Array.SliceIterator Float32 :=
  Std.ToIterator.of Float32Array.SliceIterator (⟨⟨·⟩⟩)

public instance [Monad m] : ForIn m Float32Array.Slice Float32 := inferInstance

public instance [Monad m] : ForM m Float32Array.Slice Float32 where
  forM s f := s.foldlM (fun _ x => f x) ⟨⟩

/-- An iterator over the elements of `a`, for use with the `Std.Iterators` API. -/
@[inline, expose]
public def iter (a : Float32Array) : Std.Iter (α := Float32Array.SliceIterator) Float32 :=
  a.toSlice.iter

/-! ## Folds and searches -/

namespace Slice

/-- Folds a monadic function over the elements of `s`, from last to first. -/
@[expose]
public def foldrM {β : Type v} {m : Type v → Type w} [Monad m] (f : Float32 → β → m β) (init : β)
    (s : Float32Array.Slice) : m β :=
  loop s.size (Nat.le_refl _) init
where
  /-- The loop of `foldrM`: folds `f` over the first `i` elements of `s`, from last to first. -/
  @[specialize] loop : (i : Nat) → i ≤ s.size → β → m β
    | 0, _, b => pure b
    | i + 1, h, b => do loop i (Nat.le_of_succ_le h) (← f s[i] b)

@[noinline, nospecialize]
private def foldrMSlow {β : Type v} {m : Type v → Type w} [Monad m] (f : Float32 → β → m β)
    (init : β) (s : Float32Array.Slice) : m β :=
  s.foldrM f init

/-- For internal use only. -/
@[inline]
public def foldrMImpl {β : Type v} {m : Type v → Type w} [Monad m]
    (f : Float32 → β → m β) (init : β) (s : Float32Array.Slice) : m β :=
  if s.array.size < USize.size then
    loop s.array s.start.toUSize s.stop.toUSize s.toNat_toUSize_stop_le init
  else foldrMSlow f init s
where
  @[specialize] loop (a : Float32Array) (start i : USize) (hi : i.toNat ≤ a.size) (b : β) : m β :=
    if h : start < i then
      have := toNat_sub_one_of_lt h
      have := USize.lt_iff_toNat_lt.1 h
      do loop a start (i - 1) (by lia) (← f (a.uget (i - 1) (by lia)) b)
    else pure b
  termination_by i.toNat
  decreasing_by lia

private theorem foldrMImpl_loop {β : Type v} {m : Type v → Type w} [Monad m]
    (f : Float32 → β → m β) (s : Float32Array.Slice) (start i : USize)
    (hi : i.toNat ≤ s.array.size) (hstart : start.toNat = s.start) (k : Nat) (hk : k ≤ s.size)
    (hik : i.toNat = s.start + k) (b : β) :
    foldrMImpl.loop f s.array start i hi b = foldrM.loop f s k hk b := by
  fun_induction foldrMImpl.loop f s.array start i hi b generalizing k with
  | case1 i hi b hlt _ _ ih =>
    have := USize.lt_iff_toNat_lt.1 hlt
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by lia⟩
    simp only [foldrM.loop, uget, Array.uget, getElem_eq, toNat_sub_one_of_lt hlt]
    congr 1
    · simp only [hik]; rfl
    · funext b; exact ih b k _ (by rw [toNat_sub_one_of_lt hlt]; lia)
  | case2 i hi b hlt =>
    have := USize.le_iff_toNat_le.1 (USize.not_lt.1 hlt)
    obtain rfl : k = 0 := by lia
    rfl

@[csimp] public theorem foldrM_eq_foldrMImpl : @foldrM = @foldrMImpl := by
  funext β m _ f init s
  simp only [foldrMImpl]
  split
  · rename_i hsize
    have := s.start_le_stop
    have := s.stop_le_array_size
    rw [foldrMImpl_loop (k := s.size) (hk := Nat.le_refl _)
      (hstart := toNat_toUSize_of_le hsize (by lia))
      (hik := by rw [toNat_toUSize_of_le hsize (by lia), size_eq]; lia)]
    rfl
  · rfl

/-- Folds a function over the elements of `s`, from last to first. -/
@[inline, expose]
public def foldr {β : Type v} (f : Float32 → β → β) (init : β) (s : Float32Array.Slice) : β :=
  Id.run <| s.foldrM (pure <| f · ·) init

/-- Runs a monadic action on each element of `s`, from last to first. -/
@[inline, expose]
public def forRevM {m : Type v → Type w} [Monad m] (f : Float32 → m PUnit)
    (s : Float32Array.Slice) : m PUnit :=
  s.foldrM (fun x _ => f x) ⟨⟩

/-- The result of the last element of `s` for which `f` returns `some`, searching from the end. -/
@[expose]
public def findSomeRevM? {β : Type v} {m : Type v → Type w} [Monad m] (s : Float32Array.Slice)
    (f : Float32 → m (Option β)) : m (Option β) :=
  loop s.size (Nat.le_refl _)
where
  /-- The loop of `findSomeRevM?`: searches the first `i` elements of `s`, from the end. -/
  @[specialize] loop : (i : Nat) → i ≤ s.size → m (Option β)
    | 0, _ => pure none
    | i + 1, h => do
      match ← f s[i] with
      | some b => pure (some b)
      | none => loop i (Nat.le_of_succ_le h)

@[noinline, nospecialize]
private def findSomeRevMSlow {β : Type v} {m : Type v → Type w} [Monad m]
    (s : Float32Array.Slice) (f : Float32 → m (Option β)) : m (Option β) :=
  s.findSomeRevM? f

/-- For internal use only. -/
@[inline]
public def findSomeRevMImpl {β : Type v} {m : Type v → Type w} [Monad m]
    (s : Float32Array.Slice) (f : Float32 → m (Option β)) : m (Option β) :=
  if s.array.size < USize.size then
    loop s.array s.start.toUSize s.stop.toUSize s.toNat_toUSize_stop_le
  else findSomeRevMSlow s f
where
  @[specialize] loop (a : Float32Array) (start i : USize) (hi : i.toNat ≤ a.size) :
      m (Option β) :=
    if h : start < i then
      have := toNat_sub_one_of_lt h
      have := USize.lt_iff_toNat_lt.1 h
      do
        match ← f (a.uget (i - 1) (by lia)) with
        | some b => pure (some b)
        | none => loop a start (i - 1) (by lia)
    else pure none
  termination_by i.toNat
  decreasing_by lia

private theorem findSomeRevMImpl_loop {β : Type v} {m : Type v → Type w} [Monad m]
    (f : Float32 → m (Option β)) (s : Float32Array.Slice) (start i : USize)
    (hi : i.toNat ≤ s.array.size) (hstart : start.toNat = s.start) (k : Nat) (hk : k ≤ s.size)
    (hik : i.toNat = s.start + k) :
    findSomeRevMImpl.loop f s.array start i hi = findSomeRevM?.loop s f k hk := by
  fun_induction findSomeRevMImpl.loop f s.array start i hi generalizing k with
  | case1 i hi hlt _ _ ih =>
    have := USize.lt_iff_toNat_lt.1 hlt
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by lia⟩
    simp only [findSomeRevM?.loop, uget, Array.uget, getElem_eq, toNat_sub_one_of_lt hlt]
    congr 1
    · simp only [hik]; rfl
    · funext r
      split
      · rfl
      · exact ih k _ (by rw [toNat_sub_one_of_lt hlt]; lia)
  | case2 i hi hlt =>
    have := USize.le_iff_toNat_le.1 (USize.not_lt.1 hlt)
    obtain rfl : k = 0 := by lia
    rfl

@[csimp] public theorem findSomeRevM?_eq_findSomeRevMImpl :
    @findSomeRevM? = @findSomeRevMImpl := by
  funext β m _ s f
  simp only [findSomeRevMImpl]
  split
  · rename_i hsize
    have := s.start_le_stop
    have := s.stop_le_array_size
    rw [findSomeRevMImpl_loop (k := s.size) (hk := Nat.le_refl _)
      (hstart := toNat_toUSize_of_le hsize (by lia))
      (hik := by rw [toNat_toUSize_of_le hsize (by lia), size_eq]; lia)]
    rfl
  · rfl

/-- The last element of `s` that satisfies the monadic predicate `p`. -/
@[inline, expose]
public def findRevM? {m : Type → Type w} [Monad m] (s : Float32Array.Slice) (p : Float32 → m Bool) :
    m (Option Float32) :=
  s.findSomeRevM? fun x => return if (← p x) then some x else none

/-- The last element of `s` that satisfies `p`. -/
@[inline, expose]
public def findRev? (s : Float32Array.Slice) (p : Float32 → Bool) : Option Float32 :=
  Id.run <| s.findRevM? (pure <| p ·)

/-- The first element of `s` that satisfies `p`. -/
@[inline, expose]
public def find? (s : Float32Array.Slice) (p : Float32 → Bool) : Option Float32 :=
  s.iter.find? p

/-- Whether some element of `s` satisfies `p`. -/
@[inline, expose]
public def any (s : Float32Array.Slice) (p : Float32 → Bool) : Bool :=
  s.iter.any p

/-- Whether every element of `s` satisfies `p`. -/
@[inline, expose]
public def all (s : Float32Array.Slice) (p : Float32 → Bool) : Bool :=
  s.iter.all p

/-- Whether some element of `s` is `==` to `v`. -/
@[inline, expose]
public def contains (s : Float32Array.Slice) (v : Float32) : Bool :=
  s.any (v == ·)

/-- The number of elements of `s` that satisfy `p`. -/
@[inline, expose]
public def count (s : Float32Array.Slice) (p : Float32 → Bool) : Nat :=
  s.iter.fold (fun n x => if p x then n + 1 else n) 0

/-! ## Membership and equality -/

/-- `x ∈ s` when `x` is an element of `s`. -/
public instance : Membership Float32 Float32Array.Slice where
  mem s x := x ∈ s.copy

/--
Compares the elements of two slices with `==`: slices of different arrays, or at different offsets,
are equal when their elements are. Logically it compares the copies.
-/
-- There is no `DecidableEq` instance: structural equality of slices compares the underlying arrays
-- and the bounds, so it would disagree with `==`.
public def beq (s t : Float32Array.Slice) : Bool :=
  s.copy == t.copy

@[noinline]
private def beqSlow (s t : Float32Array.Slice) : Bool :=
  s.beq t

/-- For internal use only. -/
-- Compares the sizes as `USize`s, so that the loop knows that the indices into `t` stay in bounds.
public def beqImpl (s t : Float32Array.Slice) : Bool :=
  if s.array.size < USize.size ∧ t.array.size < USize.size then
    let stop := s.stop.toUSize
    let i := s.start.toUSize
    let tstop := t.stop.toUSize
    let j := t.start.toUSize
    if h : j ≤ tstop ∧ stop - i = tstop - j then
      loop s.array t.array stop s.toNat_toUSize_stop_le i j (by
        have : tstop.toNat ≤ t.array.size := t.toNat_toUSize_stop_le
        have := USize.le_iff_toNat_le.1 h.1
        have := congrArg USize.toNat h.2
        rw [USize.toNat_sub_of_le _ _ h.1] at this
        have := toNat_sub_le_toNat_sub stop i
        lia)
    else false
  else beqSlow s t
where
  loop (a b : Float32Array) (stop : USize) (hstop : stop.toNat ≤ a.size) (i j : USize)
      (hj : stop.toNat - i.toNat + j.toNat ≤ b.size) : Bool :=
    if h : i < stop then
      have := USize.lt_iff_toNat_lt.1 h
      have := toNat_add_one_of_lt h
      have := toNat_add_one_le j
      a.uget i (toNat_lt_of_lt h hstop) == b.uget j (by lia) &&
        loop a b stop hstop (i + 1) (j + 1) (by lia)
    else true
  termination_by stop.toNat - i.toNat
  decreasing_by exact sub_toNat_add_one_lt h

private theorem beqImpl_loop (a b : Float32Array) (hb : b.size < USize.size) (stop : USize)
    (hstop : stop.toNat ≤ a.size) (i j : USize) (hj : stop.toNat - i.toNat + j.toNat ≤ b.size) :
    beqImpl.loop a b stop hstop i j hj = true ↔ ∀ (k : Nat) (hk : k < stop.toNat - i.toNat),
      (a.toArray[i.toNat + k]'(by rw [size_toArray']; lia) ==
        b.toArray[j.toNat + k]'(by rw [size_toArray']; lia)) = true := by
  fun_induction beqImpl.loop a b stop hstop i j hj with
  | case1 i j hj hi _ _ _ ih =>
    have := USize.lt_iff_toNat_lt.1 hi
    have hj1 : (j + 1).toNat = j.toNat + 1 := by
      rw [USize.toNat_add, USize.toNat_one, Nat.mod_eq_of_lt (by lia)]
    rw [Bool.and_eq_true, ih]
    simp only [uget, Array.uget, toNat_add_one_of_lt hi, hj1]
    constructor
    · rintro ⟨h0, h⟩ k hk
      cases k with
      | zero => exact h0
      | succ k =>
        have := h k (by lia)
        simp only [Nat.add_assoc, Nat.add_comm 1 k] at this ⊢
        exact this
    · intro h
      refine ⟨h 0 (by lia), fun k hk => ?_⟩
      have := h (k + 1) (by lia)
      simp only [Nat.add_assoc, Nat.add_comm 1 k] at this ⊢
      exact this
  | case2 i j hj hi =>
    have := USize.le_iff_toNat_le.1 (USize.not_lt.1 hi)
    simp only [true_iff]
    intro k hk
    lia

private theorem beq_iff (s t : Float32Array.Slice) :
    beq s t = true ↔ s.size = t.size ∧ ∀ (k : Nat) (hk : k < s.size) (hk' : k < t.size),
      (s.array.toArray[s.start + k]'(by
        have := s.stop_le_array_size; rw [size_toArray']; rw [size_eq] at hk; lia) ==
      t.array.toArray[t.start + k]'(by
        have := t.stop_le_array_size; rw [size_toArray']; rw [size_eq] at hk'; lia)) = true := by
  have hc (u : Float32Array.Slice) : u.copy.toArray = u.array.toArray.extract u.start u.stop := rfl
  have hs (u : Float32Array.Slice) : min u.stop u.array.toArray.size - u.start = u.size := by
    have := u.stop_le_array_size
    rw [size_eq, size_toArray']; lia
  rw [beq, beq_eq_beq_toArray, hc, hc, Array.beq_eq_decide]
  split
  · rename_i h
    simp only [Array.size_extract, hs] at h
    simp only [decide_eq_true_eq, Array.size_extract, Array.getElem_extract, hs, h, true_and]
    exact ⟨fun h' k hk _ => h' k hk, fun h' k hk => h' k hk (h ▸ hk)⟩
  · rename_i h
    simp only [Array.size_extract, hs] at h
    simp [h]

@[csimp] public theorem beq_eq_beqImpl : @beq = @beqImpl := by
  funext s t
  simp only [beqImpl]
  split
  · rename_i hsize
    have := s.start_le_stop
    have := s.stop_le_array_size
    have := t.start_le_stop
    have := t.stop_le_array_size
    have hs1 := toNat_toUSize_of_le hsize.1 (n := s.start) (by lia)
    have hs2 := toNat_toUSize_of_le hsize.1 (n := s.stop) (by lia)
    have ht1 := toNat_toUSize_of_le hsize.2 (n := t.start) (by lia)
    have ht2 := toNat_toUSize_of_le hsize.2 (n := t.stop) (by lia)
    have hle : t.start.toUSize ≤ t.stop.toUSize := USize.le_iff_toNat_le.2 (by lia)
    have hsub : s.stop.toUSize - s.start.toUSize = t.stop.toUSize - t.start.toUSize ↔
        s.size = t.size := by
      rw [← USize.toNat_inj, USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.2 (by lia)),
        USize.toNat_sub_of_le _ _ hle, size_eq, size_eq]
      lia
    rw [Bool.eq_iff_iff, beq_iff]
    by_cases h : s.size = t.size
    · rw [dite_eq_left ⟨hle, hsub.2 h⟩, beqImpl_loop (hb := hsize.2)]
      simp only [hs1, hs2, ht1, h, true_and, ← size_eq]
      exact ⟨fun h' k hk => h' k hk (h ▸ hk), fun h' k hk _ => h' k hk⟩
    · rw [dite_eq_right fun h' => h (hsub.1 h'.2)]
      simp [h]
  · rfl

public instance : BEq Float32Array.Slice := ⟨beq⟩

end Slice

/-! ## Collecting iterators into arrays -/

/--
Collects the values emitted by an iterator into a new array. Together with the `Std.Iterators`
combinators, this gives functions such as `map`, `filter`, `take` and `zipWith`, for example
`(a.iter.map (· + 1)).toFloat32Array`.
-/
@[inline, expose]
public def _root_.Std.Iter.toFloat32Array {α : Type} [Std.Iterator α Id Float32]
    [Std.IteratorLoop α Id Id] (it : Std.Iter (α := α) Float32) : Float32Array :=
  it.fold (·.push ·) empty

/-- Like `Std.Iter.toFloat32Array`, but the new array starts with room for `capacity` elements. -/
@[inline, expose]
public def _root_.Std.Iter.toFloat32ArrayWithCapacity {α : Type} [Std.Iterator α Id Float32]
    [Std.IteratorLoop α Id Id] (it : Std.Iter (α := α) Float32) (capacity : Nat) : Float32Array :=
  it.fold (·.push ·) (emptyWithCapacity capacity)

@[simp] public theorem _root_.Std.Iter.toFloat32ArrayWithCapacity_eq {α : Type}
    [Std.Iterator α Id Float32] [Std.IteratorLoop α Id Id] (it : Std.Iter (α := α) Float32)
    (capacity : Nat) : it.toFloat32ArrayWithCapacity capacity = it.toFloat32Array := rfl

end Float32Array

end ScalarArray
