/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ScalarArray.Float32.Basic
import all ScalarArray.Internal
import all ScalarArray.Float32.Basic
import Init.Data.Iterators.Lemmas.Basic
import Init.Data.Slice.InternalLemmas

/-!
# Arrays of `Float32`: array operations

Removing elements, search, building arrays, iteration, equality, hashing and
printing.
-/

namespace ScalarArray

namespace Float32Array

/-! ## Removing elements -/

/-- Whether `a` has no elements. -/
@[expose] public def isEmpty (a : @& Float32Array) : Bool := a.size == 0

private unsafe def popImpl (a : Float32Array) : Float32Array :=
  if a.size == 0 then
    a
  else
    let s : Raw := Raw.ensureExclusive (unsafeCast a)
    unsafeCast (s.resizeUnsafe (s.size - 1) lcProof lcProof)

/-- Removes the last element of `a`, if any, in place when `a` is not shared. -/
@[implemented_by popImpl, expose]
public def pop (a : Float32Array) : Float32Array :=
  mk a.toArray.pop

/-- The last element of `a`, or `none` if `a` is empty. -/
public def back? (a : @& Float32Array) : Option Float32 := a[a.size - 1]?

/-- The last element of `a`. Panics if `a` is empty, and then returns `default`. -/
public def back! (a : @& Float32Array) : Float32 := a[a.size - 1]!

/-- The last element of `a`, which is not empty. -/
public def back (a : @& Float32Array) (h : 0 < a.size) : Float32 :=
  a[a.size - 1]'(Nat.sub_lt h Nat.one_pos)

private def popWhileImpl (p : Float32 → Bool) (a : Float32Array) : Float32Array :=
  if h : 0 < a.size then
    if p (a.back h) then popWhileImpl p a.pop else a
  else
    a
termination_by a.size
decreasing_by
  have : a.pop.size = a.size - 1 := by cases a; exact Array.size_pop ..
  lia

/--
Removes the longest run of elements at the end of `a` that satisfy `p`, in place when `a` is not
shared.
-/
@[implemented_by popWhileImpl, expose]
public def popWhile (p : Float32 → Bool) (a : Float32Array) : Float32Array :=
  mk (a.toArray.popWhile p)

private unsafe def extractImpl (a : @& Float32Array) (start stop : Nat) : Float32Array :=
  let stop := min stop a.size
  if start < stop then
    let n := (stop - start).toUSize
    copySliceUnsafe (allocUnsafe 0 n) a start.toUSize 0 n
  else
    empty

/--
The elements of `a` from index `start` up to, but not including, `min stop a.size`, copied into a
new array.
-/
@[implemented_by extractImpl, expose]
public def extract (a : @& Float32Array) (start stop : Nat) : Float32Array :=
  mk (a.toArray.extract start stop)

/-! ## Linearity -/

/--
Marks `a` as linear, a debugging aid: if a marked array is ever copied because it is shared when
it needs to be exclusive, as before an in-place write, the runtime panics. The mark goes on an
exclusive array, so if `a` is shared it is copied first and the copy is marked. Logically this is
the identity.
-/
@[never_extract, extern "lean_sarray_mark_linear", expose]
public def markLinear (a : Float32Array) : Float32Array := a

/--
Returns `b`, marked as linear if `a` is marked. Like `markLinear`, marking copies `b` first if it is
shared. Logically this is `b`.
-/
@[never_extract, extern "lean_sarray_propagate_mark", expose]
public def propagateMark (a : @& Float32Array) (b : Float32Array) : Float32Array := b

/-! ## Search -/

/--
The index of the first element at or after `start` that satisfies `p`, with a proof that it is in
bounds.
-/
@[inline]
public def findFinIdx? (a : Float32Array) (p : Float32 → Bool) (start := 0) : Option (Fin a.size) :=
  let rec @[specialize] loop (i : Nat) :=
    if h : i < a.size then
      if p a[i] then some ⟨i, h⟩ else loop (i + 1)
    else
      none
    termination_by a.size - i
  loop start

/-- The index of the first element at or after `start` that satisfies `p`. -/
@[inline]
public def findIdx? (a : Float32Array) (p : Float32 → Bool) (start := 0) : Option Nat :=
  let rec @[specialize] loop (i : Nat) :=
    if h : i < a.size then
      if p a[i] then some i else loop (i + 1)
    else
      none
    termination_by a.size - i
  loop start

/-! ## Building arrays -/

private unsafe def replicateImpl (n : Nat) (v : Float32) : Float32Array :=
  let sz := toUSizeChecked n
  loop sz (allocUnsafe sz sz) 0
where
  loop (sz : USize) (r : Float32Array) (i : USize) : Float32Array :=
    if i < sz then loop sz (setUnsafe r i v) (i + 1) else r

/-- An array of `n` copies of `v`. -/
@[implemented_by replicateImpl, expose]
public def replicate (n : Nat) (v : Float32) : Float32Array :=
  mk (Array.replicate n v)

private unsafe def ofFnImpl {n : Nat} (f : Fin n → Float32) : Float32Array :=
  let sz := toUSizeChecked n
  loop (allocUnsafe sz sz) 0
where
  loop (r : Float32Array) (i : Nat) : Float32Array :=
    if h : i < n then loop (setUnsafe r i.toUSize (f ⟨i, h⟩)) (i + 1) else r

/-- The array `#[f 0, …, f (n - 1)]`. -/
@[implemented_by ofFnImpl, expose]
public def ofFn {n : Nat} (f : Fin n → Float32) : Float32Array :=
  mk (Array.ofFn f)

/-- The array with the elements of `l`. -/
@[expose]
public def ofList (l : List Float32) : Float32Array :=
  mk l.toArray

/-- For internal use only. -/
public def ofListImpl (l : List Float32) : Float32Array :=
  loop l (emptyWithCapacity l.length)
where
  loop : List Float32 → Float32Array → Float32Array
    | [], r => r
    | x :: xs, r => loop xs (r.push x)

private theorem ofListImpl_loop (l : List Float32) (r : Float32Array) :
    ofListImpl.loop l r = mk (r.toArray ++ l.toArray) := by
  induction l generalizing r with
  | nil => simp [ofListImpl.loop]
  | cons x xs ih => simp [ofListImpl.loop, ih, push]

@[csimp] public theorem ofList_eq_ofListImpl : @ofList = @ofListImpl := by
  funext l
  simp [ofList, ofListImpl, ofListImpl_loop, emptyWithCapacity]

/-! ## Iteration -/

/--
Folds a monadic function over the elements of `a` from index `start` up to, but not including,
`stop`, from first to last.
-/
@[expose]
public def foldlM {β : Type v} {m : Type v → Type w} [Monad m] (f : β → Float32 → m β) (init : β)
    (a : @& Float32Array) (start := 0) (stop := a.size) : m β :=
  a.toArray.foldlM f init start stop

@[noinline, nospecialize]
private def foldlMSlow {β : Type v} {m : Type v → Type w} [Monad m] (f : β → Float32 → m β)
    (init : β) (a : @& Float32Array) (start stop : Nat) : m β :=
  a.foldlM f init start stop

/-- For internal use only. -/
@[inline]
public def foldlMImpl {β : Type v} {m : Type v → Type w} [Monad m] (f : β → Float32 → m β)
    (init : β) (a : @& Float32Array) (start := 0) (stop := a.size) : m β :=
  if a.size < USize.size then
    let stop := min stop a.size
    if start < stop then
      loop stop.toUSize (by simp; have := Nat.mod_le stop USize.size; lia) start.toUSize init
    else pure init
  else foldlMSlow f init a start stop
where
  @[specialize] loop (stop : USize) (hstop : stop.toNat ≤ a.size) (i : USize) (b : β) : m β :=
    if h : i < stop then do loop stop hstop (i + 1) (← f b (a.uget i (toNat_lt_of_lt h hstop)))
    else pure b
  termination_by stop.toNat - i.toNat
  decreasing_by exact sub_toNat_add_one_lt h

private theorem foldlMImpl_loop {β : Type v} {m : Type v → Type w} [Monad m]
    (f : β → Float32 → m β) (a : Float32Array) (stop : USize) (hstop : stop.toNat ≤ a.size)
    (h : stop.toNat ≤ a.toArray.size) (i : USize) (b : β) (k : Nat)
    (hk : stop.toNat - i.toNat ≤ k) :
    foldlMImpl.loop f a stop hstop i b =
      Array.foldlM.loop f a.toArray stop.toNat h k i.toNat b := by
  fun_induction foldlMImpl.loop f a stop hstop i b generalizing k with
  | case1 i b hi ih =>
    have := USize.lt_iff_toNat_lt.1 hi
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by lia⟩
    rw [Array.foldlM.loop.eq_1, dite_eq_left this]
    simp only [uget, Array.uget]
    congr 1; funext b
    rw [ih b k (by rw [toNat_add_one_of_lt hi]; lia), toNat_add_one_of_lt hi]
  | case2 i b hi =>
    have := USize.le_iff_toNat_le.1 (USize.not_lt.1 hi)
    rw [Array.foldlM.loop.eq_1, dite_eq_right (by lia)]

private theorem foldlMImpl_eq {β : Type v} {m : Type v → Type w} [Monad m]
    (f : β → Float32 → m β) (init : β) (a : Float32Array) (start stop : Nat)
    (hsize : a.size < USize.size) (h : stop ≤ a.toArray.size)
    (hstop : stop.toUSize.toNat ≤ a.size) :
    (if start < stop then foldlMImpl.loop f a stop.toUSize hstop start.toUSize init
      else pure init) = Array.foldlM.loop f a.toArray stop h (stop - start) start init := by
  have := size_toArray' a
  split <;> rename_i hlt
  · rw [foldlMImpl_loop (h := by rwa [toNat_toUSize_of_le hsize (by lia)]) (k := stop - start)
      (hk := by
        rw [toNat_toUSize_of_le hsize (by lia), toNat_toUSize_of_le hsize (by lia)]
        exact Nat.le_refl _)]
    simp only [toNat_toUSize_of_le hsize (show stop ≤ a.size by lia),
      toNat_toUSize_of_le hsize (show start ≤ a.size by lia)]
  · rw [Array.foldlM.loop.eq_1, dite_eq_right hlt]

@[csimp] public theorem foldlM_eq_foldlMImpl : @foldlM = @foldlMImpl := by
  funext β m _ f init a start stop
  simp only [foldlMImpl]
  split
  · rename_i hsize
    have := size_toArray' a
    simp only [foldlM, Array.foldlM]
    split <;> rename_i h
    · simp only [Nat.min_eq_left (show stop ≤ a.size by lia)]
      exact (foldlMImpl_eq (hsize := hsize) ..).symm
    · simp only [Nat.min_eq_right (show a.size ≤ stop by lia)]
      exact (foldlMImpl_eq (hsize := hsize) ..).symm
  · rfl

/-- Folds a monadic function over the elements of `a`, from last to first. -/
@[expose]
public def foldrM {β : Type v} {m : Type v → Type w} [Monad m] (f : Float32 → β → m β) (init : β)
    (a : @& Float32Array) : m β :=
  a.toArray.foldrM f init

@[noinline, nospecialize]
private def foldrMSlow {β : Type v} {m : Type v → Type w} [Monad m] (f : Float32 → β → m β)
    (init : β) (a : @& Float32Array) : m β :=
  a.foldrM f init

/-- For internal use only. -/
@[inline]
public def foldrMImpl {β : Type v} {m : Type v → Type w} [Monad m] (f : Float32 → β → m β)
    (init : β) (a : @& Float32Array) : m β :=
  if a.size < USize.size then loop a.usize a.toNat_usize_le init else foldrMSlow f init a
where
  @[specialize] loop (i : USize) (hi : i.toNat ≤ a.size) (b : β) : m β :=
    if h : 0 < i then
      have := toNat_sub_one_of_lt h
      have := USize.lt_iff_toNat_lt.1 h
      do loop (i - 1) (by lia) (← f (a.uget (i - 1) (by simp at *; lia)) b)
    else pure b
  termination_by i.toNat
  decreasing_by lia

private theorem foldrMImpl_loop {β : Type v} {m : Type v → Type w} [Monad m]
    (f : Float32 → β → m β) (a : Float32Array) (i : USize) (hi : i.toNat ≤ a.size)
    (h : i.toNat ≤ a.toArray.size) (b : β) :
    foldrMImpl.loop f a i hi b = Array.foldrM.fold f a.toArray 0 i.toNat h b := by
  fun_induction foldrMImpl.loop f a i hi b with
  | case1 i hi b hpos _ _ ih =>
    have := USize.lt_iff_toNat_lt.1 hpos
    obtain ⟨k, hk⟩ : ∃ k, i.toNat = k + 1 := ⟨i.toNat - 1, by simp at this; lia⟩
    simp only [hk, Array.foldrM.fold.eq_2, Nat.succ_eq_add_one, Nat.add_one_ne_zero, beq_iff_eq,
      ite_false, uget, Array.uget, toNat_sub_one_of_lt hpos]
    congr 1; funext b
    rw [ih b (by rw [toNat_sub_one_of_lt hpos]; lia)]
    simp only [toNat_sub_one_of_lt hpos, hk, Nat.add_sub_cancel]
  | case2 i hi b hpos =>
    have : i.toNat = 0 := by simp [USize.lt_iff_toNat_lt] at hpos; lia
    simp only [this, Array.foldrM.fold.eq_1, beq_self_eq_true, ite_self]

@[csimp] public theorem foldrM_eq_foldrMImpl : @foldrM = @foldrMImpl := by
  funext β m _ f init a
  simp only [foldrMImpl]
  split
  · rename_i hsize
    have h := toNat_toUSize_of_le hsize (Nat.le_refl _)
    simp only [usize] at *
    rw [foldrMImpl_loop (h := by rw [h]; exact Nat.le_refl _)]
    simp only [foldrM, Array.foldrM, Nat.le_refl, dite_true, h]
    split
    · rfl
    · have : a.size = 0 := by rw [← size_toArray']; lia
      simp only [this, Array.foldrM.fold.eq_1, beq_self_eq_true, ite_true]
  · rfl

/--
Folds a function over the elements of `a` from index `start` up to, but not including, `stop`, from
first to last.
-/
@[inline, expose]
public def foldl {β : Type v} (f : β → Float32 → β) (init : β) (a : @& Float32Array) (start := 0)
    (stop := a.size) : β :=
  Id.run <| a.foldlM (pure <| f · ·) init start stop

/-- Folds a function over the elements of `a`, from last to first. -/
@[inline, expose]
public def foldr {β : Type v} (f : Float32 → β → β) (init : β) (a : @& Float32Array) : β :=
  Id.run <| a.foldrM (pure <| f · ·) init

/-- Runs a monadic action on each element of `a`, from first to last. -/
@[inline, expose]
public def forM {m : Type v → Type w} [Monad m] (f : Float32 → m PUnit) (a : @& Float32Array) :
    m PUnit :=
  a.foldlM (fun _ x => f x) ⟨⟩

/-- The loop behind `for x in a`. Logically it is the loop over `a.toArray`. -/
@[expose]
public def forIn {β : Type v} {m : Type v → Type w} [Monad m] (a : @& Float32Array) (init : β)
    (f : Float32 → β → m (ForInStep β)) : m β :=
  ForIn.forIn a.toArray init f

@[noinline, nospecialize]
private def forInSlow {β : Type v} {m : Type v → Type w} [Monad m] (a : @& Float32Array)
    (init : β) (f : Float32 → β → m (ForInStep β)) : m β :=
  a.forIn init f

/-- For internal use only. -/
@[inline]
public def forInImpl {β : Type v} {m : Type v → Type w} [Monad m] (a : @& Float32Array)
    (init : β) (f : Float32 → β → m (ForInStep β)) : m β :=
  if a.size < USize.size then loop a.usize a.toNat_usize_le 0 init else forInSlow a init f
where
  @[specialize] loop (stop : USize) (hstop : stop.toNat ≤ a.size) (i : USize) (b : β) : m β :=
    if h : i < stop then do
      match ← f (a.uget i (toNat_lt_of_lt h hstop)) b with
      | .done b => pure b
      | .yield b => loop stop hstop (i + 1) b
    else pure b
  termination_by stop.toNat - i.toNat
  decreasing_by exact sub_toNat_add_one_lt h

private theorem forInImpl_loop {β : Type v} {m : Type v → Type w} [Monad m] (a : Float32Array)
    (f : Float32 → β → m (ForInStep β)) (stop : USize) (hstop : stop.toNat ≤ a.size)
    (hsize : a.size ≤ stop.toNat) (i : USize) (b : β) (hi : i.toNat ≤ a.toArray.size)
    (h : a.toArray.size - i.toNat ≤ a.toArray.size) :
    forInImpl.loop a f stop hstop i b =
      Array.forIn'.loop a.toArray (fun x _ b => f x b) (a.toArray.size - i.toNat) h b := by
  fun_induction forInImpl.loop a f stop hstop i b with
  | case1 i b hi' ih =>
    have := USize.lt_iff_toNat_lt.1 hi'
    have := size_toArray' a
    obtain ⟨k, hk⟩ : ∃ k, a.toArray.size - i.toNat = k + 1 :=
      ⟨a.toArray.size - i.toNat - 1, by lia⟩
    simp only [hk, Array.forIn'.loop.eq_2, uget, Array.uget]
    have : a.toArray.size - 1 - k = i.toNat := by lia
    simp only [this]
    congr 1; funext r
    split
    · rfl
    · rw [ih _ (by rw [toNat_add_one_of_lt hi']; lia) (by lia)]
      simp only [toNat_add_one_of_lt hi']
      congr 1; lia
  | case2 i b hi' =>
    have := USize.le_iff_toNat_le.1 (USize.not_lt.1 hi')
    have : a.toArray.size - i.toNat = 0 := by rw [size_toArray']; lia
    simp only [this, Array.forIn'.loop.eq_1]

@[csimp] public theorem forIn_eq_forInImpl : @forIn = @forInImpl := by
  funext β m _ a init f
  simp only [forInImpl]
  split
  · rename_i hsize
    have h := toNat_toUSize_of_le hsize (Nat.le_refl _)
    rw [forInImpl_loop (hsize := by simp only [usize]; lia) (hi := by simp) (h := by simp)]
    simp only [forIn, ForIn.forIn, ForIn'.forIn', Array.forIn', USize.toNat_zero, Nat.sub_zero]
  · rfl

public instance [Monad m] : ForIn m Float32Array Float32 where
  forIn a b f := Float32Array.forIn a b f

public instance [Monad m] : ForM m Float32Array Float32 where
  forM a f := a.forM f

/-- Whether some element of `a` satisfies `p`. -/
@[expose]
public def any (a : @& Float32Array) (p : Float32 → Bool) : Bool :=
  a.toArray.any p

@[noinline, nospecialize]
private def anySlow (a : @& Float32Array) (p : Float32 → Bool) : Bool :=
  a.any p

/-- For internal use only. -/
@[inline]
public def anyImpl (a : @& Float32Array) (p : Float32 → Bool) : Bool :=
  if a.size < USize.size then loop a.usize a.toNat_usize_le 0 else anySlow a p
where
  @[specialize] loop (stop : USize) (hstop : stop.toNat ≤ a.size) (i : USize) : Bool :=
    if h : i < stop then p (a.uget i (toNat_lt_of_lt h hstop)) || loop stop hstop (i + 1)
    else false
  termination_by stop.toNat - i.toNat
  decreasing_by exact sub_toNat_add_one_lt h

private theorem anyImpl_loop (a : Float32Array) (p : Float32 → Bool) (stop : USize)
    (hstop : stop.toNat ≤ a.size) (h : stop.toNat ≤ a.toArray.size) (i : USize) :
    anyImpl.loop a p stop hstop i =
      Array.anyM.loop (m := Id) (pure <| p ·) a.toArray stop.toNat h i.toNat := by
  fun_induction anyImpl.loop a p stop hstop i with
  | case1 i hi ih =>
    have := USize.lt_iff_toNat_lt.1 hi
    rw [Array.anyM.loop.eq_1, dite_eq_left this, ih, toNat_add_one_of_lt hi]
    simp only [uget, Array.uget]
    cases p a.toArray[i.toNat] <;> rfl
  | case2 i hi =>
    have := USize.le_iff_toNat_le.1 (USize.not_lt.1 hi)
    rw [Array.anyM.loop.eq_1, dite_eq_right (by lia)]
    rfl

@[csimp] public theorem any_eq_anyImpl : @any = @anyImpl := by
  funext a p
  simp only [anyImpl]
  split
  · rename_i hsize
    have h := toNat_toUSize_of_le hsize (Nat.le_refl _)
    rw [anyImpl_loop (h := by simp only [usize]; rw [h]; exact Nat.le_refl _)]
    simp only [any, Array.any, Array.anyM, Nat.le_refl, dite_true, usize, h, USize.toNat_zero]
    rfl
  · rfl

/-- Whether every element of `a` satisfies `p`. -/
@[expose]
public def all (a : @& Float32Array) (p : Float32 → Bool) : Bool :=
  a.toArray.all p

@[noinline, nospecialize]
private def allSlow (a : @& Float32Array) (p : Float32 → Bool) : Bool :=
  a.all p

/-- For internal use only. -/
@[inline]
public def allImpl (a : @& Float32Array) (p : Float32 → Bool) : Bool :=
  if a.size < USize.size then loop a.usize a.toNat_usize_le 0 else allSlow a p
where
  @[specialize] loop (stop : USize) (hstop : stop.toNat ≤ a.size) (i : USize) : Bool :=
    if h : i < stop then p (a.uget i (toNat_lt_of_lt h hstop)) && loop stop hstop (i + 1)
    else true
  termination_by stop.toNat - i.toNat
  decreasing_by exact sub_toNat_add_one_lt h

private theorem allImpl_loop (a : Float32Array) (p : Float32 → Bool) (stop : USize)
    (hstop : stop.toNat ≤ a.size) (i : USize) :
    allImpl.loop a p stop hstop i = !anyImpl.loop a (!p ·) stop hstop i := by
  fun_induction allImpl.loop a p stop hstop i with
  | case1 i hi ih =>
    rw [anyImpl.loop, dite_eq_left hi, ih]
    cases p (a.uget i _) <;> rfl
  | case2 i hi => rw [anyImpl.loop, dite_eq_right hi]; rfl

@[csimp] public theorem all_eq_allImpl : @all = @allImpl := by
  funext a p
  simp only [allImpl]
  split
  · rw [allImpl_loop, all, Array.all_eq_not_any_not, ← any, any_eq_anyImpl, anyImpl,
      ite_eq_left ‹_›]
  · rfl

/-- Whether some element of `a` is `==` to `v`. -/
@[expose]
public def contains (a : @& Float32Array) (v : Float32) : Bool :=
  a.toArray.contains v

/-- For internal use only. -/
public def containsImpl (a : @& Float32Array) (v : Float32) : Bool :=
  a.any (v == ·)

@[csimp] public theorem contains_eq_containsImpl : @contains = @containsImpl := by rfl

/-- `x ∈ a` when `x` is an element of `a`. -/
public instance : Membership Float32 Float32Array where
  mem a x := x ∈ a.toArray

/-! ## Equality -/

private theorem toArray_injective {a b : Float32Array} (h : a.toArray = b.toArray) : a = b := by
  rw [← mk_toArray a, h, mk_toArray]

/--
Compares the elements with `==`, like `Array`. Floating-point equality is not decidable equality:
`NaN` is not equal to itself and `0.0 == -0.0`.
-/
public def beq (a b : @& Float32Array) : Bool :=
  a.toArray == b.toArray

@[noinline]
private def beqSlow (a b : @& Float32Array) : Bool :=
  a.beq b

/-- For internal use only. -/
public def beqImpl (a b : @& Float32Array) : Bool :=
  if a.size < USize.size ∧ b.size < USize.size then
    if h : a.usize = b.usize then loop a.usize a.toNat_usize_le (h ▸ b.toNat_usize_le) 0 else false
  else beqSlow a b
where
  loop (stop : USize) (ha : stop.toNat ≤ a.size) (hb : stop.toNat ≤ b.size) (i : USize) : Bool :=
    if h : i < stop then
      a.uget i (toNat_lt_of_lt h ha) == b.uget i (toNat_lt_of_lt h hb) && loop stop ha hb (i + 1)
    else true
  termination_by stop.toNat - i.toNat
  decreasing_by exact sub_toNat_add_one_lt h

private theorem beqImpl_loop (a b : Float32Array) (stop : USize) (ha : stop.toNat ≤ a.size)
    (hb : stop.toNat ≤ b.size) (i : USize) :
    beqImpl.loop a b stop ha hb i = true ↔ ∀ (k : Nat) (_ : i.toNat ≤ k) (hk : k < stop.toNat),
      (a.toArray[k]'(by rw [size_toArray']; lia) ==
        b.toArray[k]'(by rw [size_toArray']; lia)) = true := by
  fun_induction beqImpl.loop a b stop ha hb i with
  | case1 i hi ih =>
    have := USize.lt_iff_toNat_lt.1 hi
    rw [Bool.and_eq_true, ih]
    simp only [uget, Array.uget, toNat_add_one_of_lt hi]
    constructor
    · rintro ⟨h0, h⟩ k hik hk
      by_cases hk' : k = i.toNat
      · subst hk'; exact h0
      · exact h k (by lia) hk
    · intro h
      exact ⟨h _ (Nat.le_refl _) this, fun k hik hk => h k (by lia) hk⟩
  | case2 i hi =>
    have := USize.le_iff_toNat_le.1 (USize.not_lt.1 hi)
    simp only [true_iff]
    intro k hik hk
    lia

@[csimp] public theorem beq_eq_beqImpl : @beq = @beqImpl := by
  funext a b
  simp only [beqImpl]
  split
  · rename_i hsize
    have ha := toNat_toUSize_of_le hsize.1 (Nat.le_refl _)
    have hb := toNat_toUSize_of_le hsize.2 (Nat.le_refl _)
    have husize : a.usize = b.usize ↔ a.size = b.size := by
      rw [← USize.toNat_inj, usize, usize, ha, hb]
    rw [beq, Array.beq_eq_decide]
    have hdata : a.toArray.size = b.toArray.size ↔ a.size = b.size := .rfl
    by_cases h : a.size = b.size
    · rw [dite_eq_left (husize.2 h), dite_eq_left (hdata.2 h), Bool.eq_iff_iff, decide_eq_true_eq,
        beqImpl_loop]
      simp only [usize, ha, USize.toNat_zero, Nat.zero_le, forall_const]
      exact ⟨fun h' k hk => h' k hk, fun h' k hk => h' k hk⟩
    · rw [dite_eq_right fun h' => h (husize.1 h'), dite_eq_right fun h' => h (hdata.1 h')]
  · rfl

public instance : BEq Float32Array := ⟨beq⟩

private theorem beq_eq_beq_toArray (a b : Float32Array) : (a == b) = (a.toArray == b.toArray) := rfl

/-! ## Conversion and printing -/

/-- The elements of `a` as a list. -/
@[expose] public def toList (a : Float32Array) : List Float32 := a.toArray.toList

/-- Prints `ScalarArray.Float32Array.mk #[...]`, which evaluates to an equal array. -/
public instance : Repr Float32Array where
  reprPrec a prec := Repr.addAppParen ("ScalarArray.Float32Array.mk " ++ reprArg a.toArray) prec

public instance : ToString Float32Array where
  toString a := "Float32Array.mk " ++ toString a.toArray

end Float32Array

end ScalarArray

/-- The array with the elements of `l`. -/
@[inline, expose]
public def List.toFloat32Array (l : List Float32) : ScalarArray.Float32Array :=
  ScalarArray.Float32Array.ofList l
