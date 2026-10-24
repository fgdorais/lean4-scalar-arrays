/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import all ScalarArray.Internal
public import Std.Data.Iterators
import Init.Data.Iterators.Lemmas.Basic
import Init.Data.Slice.InternalLemmas

/-!
# Arrays of `Int32`

`ScalarArray.Int32Array` stores `Int32` values unboxed in a Lean runtime scalar array,
4 bytes per element. Its logical model is `Array Int32`: `Int32Array.mk` and
`Int32Array.data` convert between the two, and every operation is specified by its effect on
the model.

Reads and in-place writes are inline C. `uset`, `set` and `push` update the array in place when it
is not shared and copy it otherwise, like `Array` and `ByteArray`.
-/

namespace ScalarArray

universe u

/--
Arrays of `Int32` values, stored unboxed in a scalar array, 4 bytes per element.

The logical model is an `Array Int32`: `Int32Array.mk` and `Int32Array.data` convert between the
two. `cases` and `induction` split a `Int32Array` as `mk data`.
-/
-- At runtime a `Int32Array` is a `ScalarArray`, so every function that looks inside the quotient
-- must be `extern` or `implemented_by`. A quotient rather than a structure: the compiler represents
-- a one-field structure by its field, so code in any module could match on the constructor and run
-- `Array` code on a scalar array. A quotient has no constructor to match on and the compiler gives it
-- no layout; only `Quot.lift` and `Quot.rec` can see the `Array`.
@[expose] public def Int32Array : Type := Quot fun _ _ : Array Int32 => False

namespace Int32Array

-- `noinline` on `mk` and `data`: the `implemented_by` attribute of `mk` and the `csimp` theorem of
-- `data` come later, and the compiler would otherwise inline their bodies, which treat the scalar
-- array as an `Array`.

/-- The `Int32Array` whose elements are `data`. -/
@[noinline, expose]
public def mk (data : Array Int32) : Int32Array := Quot.mk _ data

/-- The elements of `a` as an `Array Int32`. -/
@[noinline, expose]
public def data (a : @& Int32Array) : Array Int32 :=
  Quot.lift id (fun _ _ h => h.elim) a

@[simp] public theorem data_mk (a : Array Int32) : (mk a).data = a := rfl

@[simp] public theorem mk_data (a : Int32Array) : mk a.data = a :=
  Quot.ind (β := fun a : Int32Array => mk a.data = a) (fun _ => rfl) a

-- `lean_byte_array_size` reads the size of any scalar array, whatever its element size.
@[extern "lean_byte_array_size", tagged_return, expose]
public def size (a : @& Int32Array) : Nat :=
  a.data.size

/--
The size of `a` as a `USize`. Since `USize` can address all memory, no array has more elements than
`USize` can count.
-/
@[extern "lean_sarray_size", simp, expose]
public def usize (a : @& Int32Array) : USize :=
  a.size.toUSize

/-- `a.usize` is at most the size, so it bounds the indices of loops that stop at `a.usize`. -/
public theorem toNat_usize_le (a : Int32Array) : a.usize.toNat ≤ a.size := by
  simp [Nat.mod_le]

@[extern c inline "((uint32_t*)lean_sarray_cptr(#1))[#2]", expose]
public def uget (a : @& Int32Array) (i : USize) (h : i.toNat < a.size := by get_elem_tactic) :
    Int32 :=
  a.data.uget i h

@[expose]
public def get (a : @& Int32Array) (i : @& Nat) (h : i < a.size := by get_elem_tactic) :
    Int32 :=
  a.data[i]

-- Public, like `mkImpl`, `usetImpl`, `setImpl` and `pushImpl` below: a private
-- `implemented_by` target attached with a separate `attribute` command is not visible to other
-- modules, so code there that uses `get`, `mk`, `data`, `uset` or `set` would fail to compile.
@[inline]
public unsafe def getImpl : type_of% @get :=
  fun a i _ => a.uget i.toUSize lcProof

attribute [implemented_by getImpl] get

/--
Stores `v` at index `i` in place. Only valid when `a` is exclusive and `i` is in bounds. Public only
so that `uset` can be inlined into code in other modules.
-/
@[never_extract, extern c inline "#1;\n((uint32_t*)lean_sarray_cptr(#1))[#2] = #3"]
public unsafe def setUnsafe (a : Int32Array) (i : USize) (v : Int32) : Int32Array :=
  mk <| a.data.uset i v lcProof

/--
`a` itself when it is not shared, and a copy otherwise. Public only so that `uset` can be inlined
into code in other modules.
-/
-- The same runtime function as the private `ScalarArray.ensureExclusive`, which code in other
-- modules can't reach. `never_extract`: once `uset` or `push` is inlined, `ensureExclusiveUnsafe c`
-- on a closed array `c` would otherwise be hoisted into a shared constant, which the following
-- in-place write would then modify.
@[never_extract, extern "lean_sarray_ensure_exclusive"]
public unsafe def ensureExclusiveUnsafe (a : Int32Array) : Int32Array := a

private def toUSizeChecked (n : Nat) : USize :=
  if n < USize.size >>> 1 then n.toUSize else panic! "out of memory"

/-- A new array of size `size` with room for `capacity` elements. Requires `size ≤ capacity`. -/
private unsafe def allocUnsafe (size capacity : USize) : Int32Array :=
  unsafeCast <| ScalarArray.allocate 4 size capacity lcProof

private unsafe def mkWithCapacityImpl (a : Array Int32) (capacity : Nat := a.size) :
    Int32Array :=
  let cap := toUSizeChecked capacity
  let sz := toUSizeChecked a.size
  let r := allocUnsafe sz (max sz cap)
  loop sz r 0
where
  loop (sz : USize) (r : Int32Array) (i : USize) : Int32Array :=
    if i < sz then loop sz (setUnsafe r i (a.uget i lcProof)) (i + 1) else r

public unsafe def mkImpl (a : Array Int32) : Int32Array :=
  mkWithCapacityImpl a a.size

attribute [implemented_by mkImpl] Int32Array.mk

private theorem size_data' (a : Int32Array) : a.data.size = a.size := rfl

/-- `n.toUSize` is `n` for every `n` up to the size of an array with fewer than `USize.size`
elements. -/
private theorem toNat_toUSize_of_le {a : Int32Array} (hsize : a.size < USize.size) {n : Nat}
    (h : n ≤ a.size) : n.toUSize.toNat = n := by
  simp only [Nat.toUSize_eq, USize.toNat_ofNat']
  exact Nat.mod_eq_of_lt (by lia)

-- `dataImpl` and the other `Impl` functions below are proved equal to their specifications by
-- `csimp` theorems, which make the compiler call them instead. A `csimp` theorem must be public,
-- and so must the functions it names. The loops index with `USize`, so the proofs need
-- `a.size < USize.size`: the `else` branches are never taken, since no array in memory has
-- `USize.size` elements. Elsewhere they call a `Slow` function that is neither inlined nor
-- specialized, so that the dead branch stays a single call; here the compiled body of `data` would
-- treat the scalar array as an `Array`, so the `else` branch reads the elements with `get` instead.
public def dataImpl (a : @& Int32Array) : Array Int32 :=
  if a.size < USize.size then
    loop a.usize a.toNat_usize_le 0 (Array.replicate a.size default) Array.size_replicate
  else Array.ofFn fun i : Fin a.size => a.get i i.2
where
  loop (sz : USize) (hsz : sz.toNat ≤ a.size) (i : USize) (r : Array Int32)
      (hr : r.size = a.size) : Array Int32 :=
    if h : i < sz then
      have := toNat_lt_of_lt h hsz
      loop sz hsz (i + 1) (r.uset i (a.uget i) (hr ▸ this)) (by simp [hr])
    else r
  termination_by sz.toNat - i.toNat
  decreasing_by exact sub_toNat_add_one_lt h

private theorem dataImpl_loop (a : Int32Array) (sz : USize) (hsz : sz.toNat ≤ a.size)
    (hsz' : a.size ≤ sz.toNat) (i : USize) (r : Array Int32) (hr : r.size = a.size)
    (hi : i.toNat ≤ sz.toNat) (h : ∀ (k : Nat) (hk : k < i.toNat), r[k]'(by lia) = a.data[k]'(by
      rw [size_data']; lia)) :
    dataImpl.loop a sz hsz i r hr = a.data := by
  fun_induction dataImpl.loop a sz hsz i r hr with
  | case1 i r hr hi' _ ih =>
    have := USize.lt_iff_toNat_lt.1 hi'
    apply ih (by rw [toNat_add_one_of_lt hi']; lia)
    intro k hk
    rw [toNat_add_one_of_lt hi'] at hk
    simp only [Array.uset, uget, Array.uget, Array.getElem_set]
    split
    · subst k; rfl
    · exact h k (by lia)
  | case2 i r hr hi' =>
    have := USize.le_iff_toNat_le.1 (USize.not_lt.1 hi')
    exact Array.ext (by rw [hr]; rfl) fun k hk _ => h k (by lia)

@[csimp] public theorem data_eq_dataImpl : @data = @dataImpl := by
  funext a
  simp only [dataImpl]
  split
  · rename_i hsize
    have := toNat_toUSize_of_le hsize (Nat.le_refl _)
    exact (dataImpl_loop a _ _ (by simp only [usize]; lia) 0 _ _ (by simp) (by simp)).symm
  · exact (Array.ofFn_getElem (xs := a.data)).symm

-- After the `implemented_by` attribute of `mk` and the `csimp` theorem of `data`, so that the
-- compiled code uses them.
/-- Case analysis on a `Int32Array` as `mk data`. It is the default for `cases` and `induction`. -/
@[elab_as_elim, cases_eliminator, induction_eliminator]
public def casesMk {motive : Int32Array → Sort u} (mk : (data : Array Int32) → motive (mk data))
    (a : Int32Array) : motive a :=
  mk_data a ▸ mk a.data

private unsafe def emptyWithCapacityImpl (capacity : Nat) : Int32Array :=
  mkWithCapacityImpl #[] capacity

/-- An empty array with room for `capacity` elements before reallocating. -/
@[implemented_by emptyWithCapacityImpl, expose]
public def emptyWithCapacity (capacity : Nat) : Int32Array :=
  mk #[]

@[expose] public def empty : Int32Array := emptyWithCapacity 0

public instance : EmptyCollection Int32Array := ⟨empty⟩

public instance : Inhabited Int32Array := ⟨empty⟩

/--
Replaces the element at index `i`, in place when `a` is not shared. It compiles to inline C: one
check that `a` is exclusive, copying it if not, and one store.
-/
@[expose]
public def uset (a : Int32Array) (i : USize) (v : Int32)
    (h : i.toNat < a.size := by get_elem_tactic) : Int32Array :=
  mk (a.data.uset i v h)

-- Inline, and made of public inline externs, so that it compiles to inline C in other modules.
@[inline]
public unsafe def usetImpl : type_of% @uset :=
  fun a i v _ => setUnsafe (ensureExclusiveUnsafe a) i v

attribute [implemented_by usetImpl] uset

@[expose]
public def set (a : Int32Array) (i : Nat) (v : Int32) (h : i < a.size := by get_elem_tactic) :
    Int32Array :=
  mk (a.data.set i v h)

@[inline]
public unsafe def setImpl : type_of% @set :=
  fun a i v _ => a.uset i.toUSize v lcProof

attribute [implemented_by setImpl] set

@[expose]
public def get! (a : @& Int32Array) (i : @& Nat) : Int32 :=
  if h : i < a.size then a.get i h else panic! "index out of bounds"

@[expose]
public def getD (a : @& Int32Array) (i : @& Nat) (v₀ : Int32) : Int32 :=
  if h : i < a.size then a.get i h else v₀

/-- Replaces the element at index `i`. If `i` is out of bounds, the array is returned unmodified. -/
@[expose]
public def set! (a : Int32Array) (i : Nat) (v : Int32) : Int32Array :=
  if h : i < a.size then a.set i v h else a

public instance : GetElem Int32Array Nat Int32 fun a i => i < a.size where
  getElem a i h := a.get i h

public instance : GetElem Int32Array USize Int32 fun a i => i.toNat < a.size where
  getElem a i h := a.uget i h

/--
The number of elements `a` has room for before it must be reallocated. Public only so that `push`
can be inlined into code in other modules.
-/
@[extern "lean_sarray_capacity"]
public unsafe def capacityUnsafe (a : @& Int32Array) : USize := a.usize

/--
Sets the size of `a` to `_n`. Only valid when `a` is exclusive and `_n` is at most its capacity;
the elements past the old size are uninitialized until stored. Public only so that `push` can be
inlined into code in other modules.
-/
-- The same C as the private `ScalarArray.resizeUnsafe`, which code in other modules can't reach.
@[never_extract, extern c inline "#1;\nlean_sarray_set_size(#1, #2)"]
public unsafe def setSizeUnsafe (a : Int32Array) (_n : USize) : Int32Array := a

/--
`push` when `a` is full: copies `a` with capacity `2 * capacity + 1`, then appends `v`. Out of
line so that inlined `push` call sites stay small. Public only so that `push` can be inlined into
code in other modules.
-/
public unsafe def pushGrowUnsafe (a : Int32Array) (v : Int32) : Int32Array :=
  let s : ScalarArray := unsafeCast a
  let cap := s.capacity
  if cap < cap + cap + 1 then
    let a : Int32Array := unsafeCast (s.copyWithCapacity (cap + cap + 1) lcProof)
    let i := a.usize
    setUnsafe (setSizeUnsafe a (i + 1)) i v
  else
    panic! "out of memory"

-- Inline, and made of public inline externs, so that the common path compiles to inline C in other
-- modules: one capacity check, one exclusivity check, a size bump and one store.
@[inline]
public unsafe def pushImpl (a : Int32Array) (v : Int32) : Int32Array :=
  if a.usize < capacityUnsafe a then
    let a := ensureExclusiveUnsafe a
    let i := a.usize
    setUnsafe (setSizeUnsafe a (i + 1)) i v
  else
    pushGrowUnsafe a v

@[implemented_by pushImpl, expose]
public def push (a : Int32Array) (v : Int32) : Int32Array :=
  mk (a.data.push v)

/--
Copies `n` bytes of the data of `src`, starting at byte `srcOff`, into the data of `dest`, starting
at byte `destOff`. Only valid when `dest` is exclusive and both ranges are within the capacities.
-/
-- TODO: core has no runtime function that copies a slice of a scalar array with any element size;
-- `lean_byte_array_copy_slice` only works for bytes. Replace this once core has one.
@[extern c inline "#1;\n__builtin_memcpy(lean_sarray_cptr(#1) + #4, lean_sarray_cptr(#2) + #3, #5)"]
private unsafe def memcpyUnsafe :
    Int32Array → @& Int32Array → (srcOff destOff n : USize) → Int32Array
  | dest, _, _, _, _ => dest

/--
Copies the `n` elements of `src` starting at index `srcOff` into `dest` starting at index `destOff`,
in place, and grows the size of `dest` to `destOff + n` if it is smaller. Only valid when `dest` is
exclusive, has capacity for `destOff + n` elements, and is not the same object as `src`, and when
`destOff ≤ dest.size` and `srcOff + n ≤ src.size`.
-/
@[inline]
private unsafe def copySliceUnsafe (dest : Int32Array) (src : @& Int32Array)
    (srcOff destOff n : USize) : Int32Array :=
  let esz := (unsafeCast src : ScalarArray).elemSize.toUSize
  let d : ScalarArray := unsafeCast (memcpyUnsafe dest src (srcOff * esz) (destOff * esz) (n * esz))
  unsafeCast (d.resizeUnsafe (max d.size (destOff + n)) lcProof lcProof)

private unsafe def appendImpl (a b : Int32Array) : Int32Array :=
  let s : ScalarArray := unsafeCast a
  let m := (unsafeCast b : ScalarArray).size
  let n := s.size + m
  let cap := s.capacity
  if n < s.size then
    panic! "out of memory"
  else if n ≤ cap then
    let s := s.ensureExclusive
    copySliceUnsafe (unsafeCast s) b 0 s.size m
  else
    let cap := if cap < cap + cap && n ≤ cap + cap then cap + cap else n
    let s := s.copyWithCapacity cap lcProof
    copySliceUnsafe (unsafeCast s) b 0 s.size m

/-- Appends the elements of `b` to `a`, in place when `a` is not shared and has room. -/
@[implemented_by appendImpl, expose]
public def append (a b : Int32Array) : Int32Array :=
  mk (a.data ++ b.data)

public instance : Append Int32Array := ⟨append⟩

private unsafe def copySliceImpl (src : @& Int32Array) (srcOff : Nat) (dest : Int32Array)
    (destOff len : Nat) (exact : Bool := true) : Int32Array :=
  let srcOff := min srcOff src.size
  let n := min len (src.size - srcOff)
  let destOff := min destOff dest.size
  let newSize := max dest.size (destOff + n)
  let s : ScalarArray := unsafeCast dest
  let cap := s.capacity.toNat
  let s :=
    if newSize ≤ cap then
      s.ensureExclusive
    else
      let cap := if exact then newSize else max newSize (cap + cap)
      s.copyWithCapacity (toUSizeChecked cap) lcProof
  copySliceUnsafe (unsafeCast s) src srcOff.toUSize destOff.toUSize n.toUSize

/--
Copies the elements of `src` from index `srcOff` up to, but not including, `srcOff + len` into
`dest` starting at index `destOff`, growing `dest` if necessary. The copy works in place when `dest`
is not shared and has room. If `exact` is `false`, the capacity is doubled when `dest` grows.
-/
@[implemented_by copySliceImpl, expose]
public def copySlice (src : @& Int32Array) (srcOff : Nat) (dest : Int32Array)
    (destOff len : Nat) (exact : Bool := true) : Int32Array :=
  mk (dest.data.extract 0 destOff ++ src.data.extract srcOff (srcOff + len) ++
    dest.data.extract (destOff + min len (src.data.size - srcOff)) dest.data.size)

/-! ## Removing elements -/

@[expose] public def isEmpty (a : @& Int32Array) : Bool := a.size == 0

private unsafe def popImpl (a : Int32Array) : Int32Array :=
  if a.size == 0 then
    a
  else
    let s : ScalarArray := ScalarArray.ensureExclusive (unsafeCast a)
    unsafeCast (s.resizeUnsafe (s.size - 1) lcProof lcProof)

/-- Removes the last element of `a`, if any, in place when `a` is not shared. -/
@[implemented_by popImpl, expose]
public def pop (a : Int32Array) : Int32Array :=
  mk a.data.pop

public def back? (a : @& Int32Array) : Option Int32 := a[a.size - 1]?

public def back! (a : @& Int32Array) : Int32 := a[a.size - 1]!

public def back (a : @& Int32Array) (h : 0 < a.size) : Int32 :=
  a[a.size - 1]'(Nat.sub_lt h Nat.one_pos)

private def popWhileImpl (p : Int32 → Bool) (a : Int32Array) : Int32Array :=
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
public def popWhile (p : Int32 → Bool) (a : Int32Array) : Int32Array :=
  mk (a.data.popWhile p)

private unsafe def extractImpl (a : @& Int32Array) (start stop : Nat) : Int32Array :=
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
public def extract (a : @& Int32Array) (start stop : Nat) : Int32Array :=
  mk (a.data.extract start stop)

/-! ## Linearity -/

/--
Marks `a` as linear, a debugging aid: if a marked array is ever shared and then modified, the
runtime reports it. Logically this is the identity.
-/
@[never_extract, extern "lean_sarray_mark_linear", expose]
public def markLinear (a : Int32Array) : Int32Array := a

/-- Returns `b`, marking it as linear if `a` is marked. Logically this is `b`. -/
@[never_extract, extern "lean_sarray_propagate_mark", expose]
public def propagateMark (a : @& Int32Array) (b : Int32Array) : Int32Array := b

/-! ## Search -/

/--
The index of the first element at or after `start` that satisfies `p`, with a proof that it is in
bounds.
-/
@[inline]
public def findFinIdx? (a : Int32Array) (p : Int32 → Bool) (start := 0) : Option (Fin a.size) :=
  let rec @[specialize] loop (i : Nat) :=
    if h : i < a.size then
      if p a[i] then some ⟨i, h⟩ else loop (i + 1)
    else
      none
    termination_by a.size - i
  loop start

/-- The index of the first element at or after `start` that satisfies `p`. -/
@[inline]
public def findIdx? (a : Int32Array) (p : Int32 → Bool) (start := 0) : Option Nat :=
  let rec @[specialize] loop (i : Nat) :=
    if h : i < a.size then
      if p a[i] then some i else loop (i + 1)
    else
      none
    termination_by a.size - i
  loop start

/-! ## Building arrays -/

private unsafe def replicateImpl (n : Nat) (v : Int32) : Int32Array :=
  let sz := toUSizeChecked n
  loop sz (allocUnsafe sz sz) 0
where
  loop (sz : USize) (r : Int32Array) (i : USize) : Int32Array :=
    if i < sz then loop sz (setUnsafe r i v) (i + 1) else r

/-- An array of `n` copies of `v`. -/
@[implemented_by replicateImpl, expose]
public def replicate (n : Nat) (v : Int32) : Int32Array :=
  mk (Array.replicate n v)

private unsafe def ofFnImpl {n : Nat} (f : Fin n → Int32) : Int32Array :=
  let sz := toUSizeChecked n
  loop (allocUnsafe sz sz) 0
where
  loop (r : Int32Array) (i : Nat) : Int32Array :=
    if h : i < n then loop (setUnsafe r i.toUSize (f ⟨i, h⟩)) (i + 1) else r

/-- The array `#[f 0, …, f (n - 1)]`. -/
@[implemented_by ofFnImpl, expose]
public def ofFn {n : Nat} (f : Fin n → Int32) : Int32Array :=
  mk (Array.ofFn f)

/-- The array with the elements of `l`. -/
@[expose]
public def ofList (l : List Int32) : Int32Array :=
  mk l.toArray

public def ofListImpl (l : List Int32) : Int32Array :=
  loop l (emptyWithCapacity l.length)
where
  loop : List Int32 → Int32Array → Int32Array
    | [], r => r
    | x :: xs, r => loop xs (r.push x)

private theorem ofListImpl_loop (l : List Int32) (r : Int32Array) :
    ofListImpl.loop l r = mk (r.data ++ l.toArray) := by
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
public def foldlM {β : Type v} {m : Type v → Type w} [Monad m] (f : β → Int32 → m β) (init : β)
    (a : @& Int32Array) (start := 0) (stop := a.size) : m β :=
  a.data.foldlM f init start stop

@[noinline, nospecialize]
private def foldlMSlow {β : Type v} {m : Type v → Type w} [Monad m] (f : β → Int32 → m β)
    (init : β) (a : @& Int32Array) (start stop : Nat) : m β :=
  a.foldlM f init start stop

@[inline]
public def foldlMImpl {β : Type v} {m : Type v → Type w} [Monad m] (f : β → Int32 → m β)
    (init : β) (a : @& Int32Array) (start := 0) (stop := a.size) : m β :=
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
    (f : β → Int32 → m β) (a : Int32Array) (stop : USize) (hstop : stop.toNat ≤ a.size)
    (h : stop.toNat ≤ a.data.size) (i : USize) (b : β) (k : Nat)
    (hk : stop.toNat - i.toNat ≤ k) :
    foldlMImpl.loop f a stop hstop i b = Array.foldlM.loop f a.data stop.toNat h k i.toNat b := by
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
    (f : β → Int32 → m β) (init : β) (a : Int32Array) (start stop : Nat)
    (hsize : a.size < USize.size) (h : stop ≤ a.data.size) (hstop : stop.toUSize.toNat ≤ a.size) :
    (if start < stop then foldlMImpl.loop f a stop.toUSize hstop start.toUSize init
      else pure init) = Array.foldlM.loop f a.data stop h (stop - start) start init := by
  have := size_data' a
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
    have := size_data' a
    simp only [foldlM, Array.foldlM]
    split <;> rename_i h
    · simp only [Nat.min_eq_left (show stop ≤ a.size by lia)]
      exact (foldlMImpl_eq (hsize := hsize) ..).symm
    · simp only [Nat.min_eq_right (show a.size ≤ stop by lia)]
      exact (foldlMImpl_eq (hsize := hsize) ..).symm
  · rfl

/-- Folds a monadic function over the elements of `a`, from last to first. -/
@[expose]
public def foldrM {β : Type v} {m : Type v → Type w} [Monad m] (f : Int32 → β → m β) (init : β)
    (a : @& Int32Array) : m β :=
  a.data.foldrM f init

@[noinline, nospecialize]
private def foldrMSlow {β : Type v} {m : Type v → Type w} [Monad m] (f : Int32 → β → m β)
    (init : β) (a : @& Int32Array) : m β :=
  a.foldrM f init

@[inline]
public def foldrMImpl {β : Type v} {m : Type v → Type w} [Monad m] (f : Int32 → β → m β)
    (init : β) (a : @& Int32Array) : m β :=
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
    (f : Int32 → β → m β) (a : Int32Array) (i : USize) (hi : i.toNat ≤ a.size)
    (h : i.toNat ≤ a.data.size) (b : β) :
    foldrMImpl.loop f a i hi b = Array.foldrM.fold f a.data 0 i.toNat h b := by
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
    · have : a.size = 0 := by rw [← size_data']; lia
      simp only [this, Array.foldrM.fold.eq_1, beq_self_eq_true, ite_true]
  · rfl

@[inline, expose]
public def foldl {β : Type v} (f : β → Int32 → β) (init : β) (a : @& Int32Array) (start := 0)
    (stop := a.size) : β :=
  Id.run <| a.foldlM (pure <| f · ·) init start stop

@[inline, expose]
public def foldr {β : Type v} (f : Int32 → β → β) (init : β) (a : @& Int32Array) : β :=
  Id.run <| a.foldrM (pure <| f · ·) init

@[inline, expose]
public def forM {m : Type v → Type w} [Monad m] (f : Int32 → m PUnit) (a : @& Int32Array) :
    m PUnit :=
  a.foldlM (fun _ x => f x) ⟨⟩

@[expose]
public def forIn {β : Type v} {m : Type v → Type w} [Monad m] (a : @& Int32Array) (init : β)
    (f : Int32 → β → m (ForInStep β)) : m β :=
  ForIn.forIn a.data init f

@[noinline, nospecialize]
private def forInSlow {β : Type v} {m : Type v → Type w} [Monad m] (a : @& Int32Array)
    (init : β) (f : Int32 → β → m (ForInStep β)) : m β :=
  a.forIn init f

@[inline]
public def forInImpl {β : Type v} {m : Type v → Type w} [Monad m] (a : @& Int32Array)
    (init : β) (f : Int32 → β → m (ForInStep β)) : m β :=
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

private theorem forInImpl_loop {β : Type v} {m : Type v → Type w} [Monad m] (a : Int32Array)
    (f : Int32 → β → m (ForInStep β)) (stop : USize) (hstop : stop.toNat ≤ a.size)
    (hsize : a.size ≤ stop.toNat) (i : USize) (b : β) (hi : i.toNat ≤ a.data.size)
    (h : a.data.size - i.toNat ≤ a.data.size) :
    forInImpl.loop a f stop hstop i b =
      Array.forIn'.loop a.data (fun x _ b => f x b) (a.data.size - i.toNat) h b := by
  fun_induction forInImpl.loop a f stop hstop i b with
  | case1 i b hi' ih =>
    have := USize.lt_iff_toNat_lt.1 hi'
    have := size_data' a
    obtain ⟨k, hk⟩ : ∃ k, a.data.size - i.toNat = k + 1 := ⟨a.data.size - i.toNat - 1, by lia⟩
    simp only [hk, Array.forIn'.loop.eq_2, uget, Array.uget]
    have : a.data.size - 1 - k = i.toNat := by lia
    simp only [this]
    congr 1; funext r
    split
    · rfl
    · rw [ih _ (by rw [toNat_add_one_of_lt hi']; lia) (by lia)]
      simp only [toNat_add_one_of_lt hi']
      congr 1; lia
  | case2 i b hi' =>
    have := USize.le_iff_toNat_le.1 (USize.not_lt.1 hi')
    have : a.data.size - i.toNat = 0 := by rw [size_data']; lia
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

public instance [Monad m] : ForIn m Int32Array Int32 where
  forIn a b f := Int32Array.forIn a b f

public instance [Monad m] : ForM m Int32Array Int32 where
  forM a f := a.forM f

/-- Whether some element of `a` satisfies `p`. -/
@[expose]
public def any (a : @& Int32Array) (p : Int32 → Bool) : Bool :=
  a.data.any p

@[noinline, nospecialize]
private def anySlow (a : @& Int32Array) (p : Int32 → Bool) : Bool :=
  a.any p

@[inline]
public def anyImpl (a : @& Int32Array) (p : Int32 → Bool) : Bool :=
  if a.size < USize.size then loop a.usize a.toNat_usize_le 0 else anySlow a p
where
  @[specialize] loop (stop : USize) (hstop : stop.toNat ≤ a.size) (i : USize) : Bool :=
    if h : i < stop then p (a.uget i (toNat_lt_of_lt h hstop)) || loop stop hstop (i + 1)
    else false
  termination_by stop.toNat - i.toNat
  decreasing_by exact sub_toNat_add_one_lt h

private theorem anyImpl_loop (a : Int32Array) (p : Int32 → Bool) (stop : USize)
    (hstop : stop.toNat ≤ a.size) (h : stop.toNat ≤ a.data.size) (i : USize) :
    anyImpl.loop a p stop hstop i =
      Array.anyM.loop (m := Id) (pure <| p ·) a.data stop.toNat h i.toNat := by
  fun_induction anyImpl.loop a p stop hstop i with
  | case1 i hi ih =>
    have := USize.lt_iff_toNat_lt.1 hi
    rw [Array.anyM.loop.eq_1, dite_eq_left this, ih, toNat_add_one_of_lt hi]
    simp only [uget, Array.uget]
    cases p a.data[i.toNat] <;> rfl
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
public def all (a : @& Int32Array) (p : Int32 → Bool) : Bool :=
  a.data.all p

@[noinline, nospecialize]
private def allSlow (a : @& Int32Array) (p : Int32 → Bool) : Bool :=
  a.all p

@[inline]
public def allImpl (a : @& Int32Array) (p : Int32 → Bool) : Bool :=
  if a.size < USize.size then loop a.usize a.toNat_usize_le 0 else allSlow a p
where
  @[specialize] loop (stop : USize) (hstop : stop.toNat ≤ a.size) (i : USize) : Bool :=
    if h : i < stop then p (a.uget i (toNat_lt_of_lt h hstop)) && loop stop hstop (i + 1)
    else true
  termination_by stop.toNat - i.toNat
  decreasing_by exact sub_toNat_add_one_lt h

private theorem allImpl_loop (a : Int32Array) (p : Int32 → Bool) (stop : USize)
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
public def contains (a : @& Int32Array) (v : Int32) : Bool :=
  a.data.contains v

public def containsImpl (a : @& Int32Array) (v : Int32) : Bool :=
  a.any (v == ·)

@[csimp] public theorem contains_eq_containsImpl : @contains = @containsImpl := by rfl

/-- `x ∈ a` when `x` is an element of `a`. -/
public instance : Membership Int32 Int32Array where
  mem a x := x ∈ a.data

/-! ## Equality and hashing -/

private theorem data_injective {a b : Int32Array} (h : a.data = b.data) : a = b := by
  rw [← mk_data a, h, mk_data]

/-- Decides equality by comparing the two arrays' memory. -/
@[extern "lean_sarray_dec_eq", expose]
public def decEq (a b : @& Int32Array) : Decidable (a = b) :=
  decidable_of_iff (a.data = b.data) ⟨fun h => by rw [← mk_data a, h, mk_data], fun h => h ▸ rfl⟩

public instance : DecidableEq Int32Array := decEq

private theorem beq_eq_beq_data (a b : Int32Array) : (a == b) = (a.data == b.data) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  exact ⟨congrArg data, data_injective⟩

/-- The same hash as `a.data`. -/
public def hash (a : @& Int32Array) : UInt64 :=
  Hashable.hash a.data

public def hashImpl (a : @& Int32Array) : UInt64 :=
  a.foldl (fun r x => mixHash r (Hashable.hash x)) 7

@[csimp] public theorem hash_eq_hashImpl : @hash = @hashImpl := by rfl

public instance : Hashable Int32Array := ⟨hash⟩

public theorem hash_eq_hash_data (a : Int32Array) : Hashable.hash a = Hashable.hash a.data := by
  rfl

/-! ## Conversion and printing -/

@[expose] public def toList (a : Int32Array) : List Int32 := a.data.toList

public instance : Repr Int32Array where
  reprPrec a _ := "Int32Array.mk " ++ repr a.data

public instance : ToString Int32Array where
  toString a := "Int32Array.mk " ++ toString a.data

/-! ## Slices -/

/-- Internal representation of `Int32Array.Slice`. -/
public protected structure SliceData where
  /-- The underlying array. -/
  array : Int32Array
  /-- The starting index of the slice (inclusive). -/
  start : Nat
  /-- The ending index of the slice (exclusive). -/
  stop : Nat
  /-- The starting index is no later than the ending index. -/
  start_le_stop : start ≤ stop
  /-- The ending index is no later than the end of the array. -/
  stop_le_array_size : stop ≤ array.size

/--
A region of a `Int32Array`: the elements from index `start` up to, but not including, `stop`.
Taking a slice doesn't copy the array. Slices are written with core's slice notation, such as
`a[i...j]`, `a[i...*]` or `a[*...j]`.
-/
public protected abbrev Slice := Std.Slice Int32Array.SliceData

public instance : Std.Slice.Self (Std.Slice Int32Array.SliceData) Int32Array.Slice where

namespace Slice

@[always_inline, inline, expose, inherit_doc SliceData.array]
public def array (s : Int32Array.Slice) : Int32Array := s.internalRepresentation.array

@[always_inline, inline, expose, inherit_doc SliceData.start]
public def start (s : Int32Array.Slice) : Nat := s.internalRepresentation.start

@[always_inline, inline, expose, inherit_doc SliceData.stop]
public def stop (s : Int32Array.Slice) : Nat := s.internalRepresentation.stop

@[inherit_doc SliceData.start_le_stop]
public theorem start_le_stop (s : Int32Array.Slice) : s.start ≤ s.stop :=
  s.internalRepresentation.start_le_stop

@[inherit_doc SliceData.stop_le_array_size]
public theorem stop_le_array_size (s : Int32Array.Slice) : s.stop ≤ s.array.size :=
  s.internalRepresentation.stop_le_array_size

/-- `s.stop.toUSize` bounds the indices of loops over the slice. -/
private theorem toNat_toUSize_stop_le (s : Int32Array.Slice) :
    s.stop.toUSize.toNat ≤ s.array.size := by
  have := Nat.mod_le s.stop USize.size
  have := s.stop_le_array_size
  simp only [Nat.toUSize_eq, USize.toNat_ofNat']
  lia

public instance : Std.Slice.SliceSize Int32Array.SliceData where
  size s := s.internalRepresentation.stop - s.internalRepresentation.start

public theorem size_eq (s : Int32Array.Slice) : s.size = s.stop - s.start := rfl

/-- The element at index `i` of the slice, counted from the start of the slice. -/
@[inline, expose]
public def get (s : Int32Array.Slice) (i : Nat) (h : i < s.size := by get_elem_tactic) :
    Int32 :=
  s.array[s.start + i]'(by have := s.stop_le_array_size; rw [size_eq] at h; lia)

public instance : GetElem Int32Array.Slice Nat Int32 fun s i => i < s.size where
  getElem s i h := s.get i h

/-- The element at index `i` of the slice, or `v₀` if `i` is out of bounds. -/
@[inline]
public def getD (s : Int32Array.Slice) (i : Nat) (v₀ : Int32) : Int32 :=
  if h : i < s.size then s[i] else v₀

/-- The element at index `i` of the slice, or `default` if `i` is out of bounds. -/
public abbrev get! (s : Int32Array.Slice) (i : Nat) : Int32 :=
  getD s i default

/-- Removes the first element of the slice, if any. -/
@[expose]
public def popFront (s : Int32Array.Slice) : Int32Array.Slice :=
  if h : s.start < s.stop then
    ⟨{ s.internalRepresentation with start := s.start + 1, start_le_stop := h }⟩
  else
    s

/-- The empty slice, backed by an empty array. -/
@[expose]
public protected def empty : Int32Array.Slice :=
  ⟨{ array := Int32Array.empty, start := 0, stop := 0, start_le_stop := Nat.le_refl 0,
     stop_le_array_size := Nat.le_refl 0 }⟩

public instance : EmptyCollection Int32Array.Slice := ⟨Slice.empty⟩

public instance : Inhabited Int32Array.Slice := ⟨Slice.empty⟩

/-- The elements of the slice, copied into a new array with a single `memcpy`. -/
@[expose]
public def copy (s : Int32Array.Slice) : Int32Array :=
  s.array.extract s.start s.stop

public theorem getElem_eq (s : Int32Array.Slice) (i : Nat) (h : i < s.size) :
    s[i] = s.array[s.start + i]'(by have := s.stop_le_array_size; rw [size_eq] at h; lia) := rfl

public instance : Repr Int32Array.Slice where
  reprPrec s _ := repr s.copy ++ ".toSlice"

public instance : ToString Int32Array.Slice where
  toString s := toString s.copy

end Slice

/--
The slice of `a` from index `start` up to, but not including, `stop`. If `start` or `stop` are not
valid bounds, they are clamped to the size of `a`, and `start` is clamped to `stop`.
-/
@[expose]
public def toSlice (a : Int32Array) (start : Nat := 0) (stop : Nat := a.size) :
    Int32Array.Slice :=
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
public instance : Coe Int32Array Int32Array.Slice := ⟨(·.toSlice)⟩

public instance : Std.Rcc.Sliceable Int32Array Nat Int32Array.Slice where
  mkSlice a range := a.toSlice range.lower (range.upper + 1)

public instance : Std.Rco.Sliceable Int32Array Nat Int32Array.Slice where
  mkSlice a range := a.toSlice range.lower range.upper

public instance : Std.Rci.Sliceable Int32Array Nat Int32Array.Slice where
  mkSlice a range := a.toSlice range.lower

public instance : Std.Roc.Sliceable Int32Array Nat Int32Array.Slice where
  mkSlice a range := a.toSlice (range.lower + 1) (range.upper + 1)

public instance : Std.Roo.Sliceable Int32Array Nat Int32Array.Slice where
  mkSlice a range := a.toSlice (range.lower + 1) range.upper

public instance : Std.Roi.Sliceable Int32Array Nat Int32Array.Slice where
  mkSlice a range := a.toSlice (range.lower + 1)

public instance : Std.Ric.Sliceable Int32Array Nat Int32Array.Slice where
  mkSlice a range := a.toSlice 0 (range.upper + 1)

public instance : Std.Rio.Sliceable Int32Array Nat Int32Array.Slice where
  mkSlice a range := a.toSlice 0 range.upper

public instance : Std.Rii.Sliceable Int32Array Nat Int32Array.Slice where
  mkSlice a _ := a.toSlice

namespace Slice

/-- The slice of `s` from index `start` up to, but not including, `stop`, clamped like `toSlice`. -/
@[expose]
public def slice (s : Int32Array.Slice) (start : Nat := 0) (stop : Nat := s.size) :
    Int32Array.Slice :=
  s.array.toSlice (s.start + min start s.size) (s.start + min stop s.size)

end Slice

public instance : Std.Rcc.Sliceable Int32Array.Slice Nat Int32Array.Slice where
  mkSlice s range := s.slice range.lower (range.upper + 1)

public instance : Std.Rco.Sliceable Int32Array.Slice Nat Int32Array.Slice where
  mkSlice s range := s.slice range.lower range.upper

public instance : Std.Rci.Sliceable Int32Array.Slice Nat Int32Array.Slice where
  mkSlice s range := s.slice range.lower

public instance : Std.Roc.Sliceable Int32Array.Slice Nat Int32Array.Slice where
  mkSlice s range := s.slice (range.lower + 1) (range.upper + 1)

public instance : Std.Roo.Sliceable Int32Array.Slice Nat Int32Array.Slice where
  mkSlice s range := s.slice (range.lower + 1) range.upper

public instance : Std.Roi.Sliceable Int32Array.Slice Nat Int32Array.Slice where
  mkSlice s range := s.slice (range.lower + 1)

public instance : Std.Ric.Sliceable Int32Array.Slice Nat Int32Array.Slice where
  mkSlice s range := s.slice 0 (range.upper + 1)

public instance : Std.Rio.Sliceable Int32Array.Slice Nat Int32Array.Slice where
  mkSlice s range := s.slice 0 range.upper

public instance : Std.Rii.Sliceable Int32Array.Slice Nat Int32Array.Slice where
  mkSlice s _ := s

/-- The iterator over the elements of a slice, used for `for` loops and the generic slice API. -/
public protected structure SliceIterator where
  /-- The rest of the slice. -/
  xs : Int32Array.Slice

@[inline, expose]
public def SliceIterator.step :
    Std.IterM (α := Int32Array.SliceIterator) Id Int32 →
      Std.IterStep (Std.IterM (α := Int32Array.SliceIterator) m Int32) Int32
  | ⟨⟨xs⟩⟩ =>
    if h : xs.start < xs.stop then
      have := xs.stop_le_array_size
      .yield ⟨⟨⟨xs.array, xs.start + 1, xs.stop, h, xs.stop_le_array_size⟩⟩⟩ xs.array[xs.start]
    else
      .done

public instance : Std.Iterator Int32Array.SliceIterator Id Int32 where
  IsPlausibleStep it step := step = SliceIterator.step it
  step it := pure <| .deflate ⟨SliceIterator.step it, rfl⟩

private def SliceIterator.finitenessRelation :
    Std.Iterators.FinitenessRelation Int32Array.SliceIterator Id where
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

public instance : Std.Iterators.Finite Int32Array.SliceIterator Id :=
  .of_finitenessRelation SliceIterator.finitenessRelation

-- Each element goes through `lift`, like each step of the iterator in the default implementation,
-- so the two agree for every lawful `lift`, which is what core's consumers pass.
@[inline]
private unsafe def SliceIterator.forInImpl {n : Type x → Type x'} [Monad n]
    (lift : (γ : Type) → (δ : Type x) → (γ → n δ) → Id γ → n δ) (γ : Type x)
    (Pl : Int32 → γ → ForInStep γ → Prop)
    (it : Std.IterM (α := Int32Array.SliceIterator) Id Int32) (init : γ)
    (f : (b : Int32) → it.IsPlausibleIndirectOutput b → (c : γ) → n (Subtype (Pl b c))) :
    n γ :=
  let xs := it.internalState.xs
  loop xs.array xs.stop.toUSize xs.start.toUSize init
where
  @[specialize] loop (a : Int32Array) (stop i : USize) (c : γ) : n γ :=
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
    (Pl : Int32 → γ → ForInStep γ → Prop)
    (it : Std.IterM (α := Int32Array.SliceIterator) Id Int32) (init : γ)
    (f : (b : Int32) → it.IsPlausibleIndirectOutput b → (c : γ) → n (Subtype (Pl b c))) :
    n γ :=
  Std.IteratorLoop.defaultImplementation.forIn lift γ Pl it init f

public instance [Monad m] : Std.IteratorLoop Int32Array.SliceIterator Id m where
  forIn := SliceIterator.forIn

public instance [Monad m] : Std.LawfulIteratorLoop Int32Array.SliceIterator Id m where
  lawful _ _ _ _ _ _ _ _ := rfl

public instance :
    Std.ToIterator (Std.Slice Int32Array.SliceData) Id Int32Array.SliceIterator Int32 :=
  Std.ToIterator.of Int32Array.SliceIterator (⟨⟨·⟩⟩)

public instance [Monad m] : ForIn m Int32Array.Slice Int32 := inferInstance

public instance [Monad m] : ForM m Int32Array.Slice Int32 where
  forM s f := s.foldlM (fun _ x => f x) ⟨⟩

/-- An iterator over the elements of `a`, for use with the `Std.Iterators` API. -/
@[inline, expose]
public def iter (a : Int32Array) : Std.Iter (α := Int32Array.SliceIterator) Int32 :=
  a.toSlice.iter

namespace Slice

/-- Folds a monadic function over the elements of `s`, from last to first. -/
@[expose]
public def foldrM {β : Type v} {m : Type v → Type w} [Monad m] (f : Int32 → β → m β) (init : β)
    (s : Int32Array.Slice) : m β :=
  loop s.size (Nat.le_refl _) init
where
  @[specialize] loop : (i : Nat) → i ≤ s.size → β → m β
    | 0, _, b => pure b
    | i + 1, h, b => do loop i (Nat.le_of_succ_le h) (← f s[i] b)

@[noinline, nospecialize]
private def foldrMSlow {β : Type v} {m : Type v → Type w} [Monad m] (f : Int32 → β → m β)
    (init : β) (s : Int32Array.Slice) : m β :=
  s.foldrM f init

@[inline]
public def foldrMImpl {β : Type v} {m : Type v → Type w} [Monad m]
    (f : Int32 → β → m β) (init : β) (s : Int32Array.Slice) : m β :=
  if s.array.size < USize.size then
    loop s.array s.start.toUSize s.stop.toUSize s.toNat_toUSize_stop_le init
  else foldrMSlow f init s
where
  @[specialize] loop (a : Int32Array) (start i : USize) (hi : i.toNat ≤ a.size) (b : β) : m β :=
    if h : start < i then
      have := toNat_sub_one_of_lt h
      have := USize.lt_iff_toNat_lt.1 h
      do loop a start (i - 1) (by lia) (← f (a.uget (i - 1) (by lia)) b)
    else pure b
  termination_by i.toNat
  decreasing_by lia

private theorem foldrMImpl_loop {β : Type v} {m : Type v → Type w} [Monad m]
    (f : Int32 → β → m β) (s : Int32Array.Slice) (start i : USize)
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
public def foldr {β : Type v} (f : Int32 → β → β) (init : β) (s : Int32Array.Slice) : β :=
  Id.run <| s.foldrM (pure <| f · ·) init

/-- Runs a monadic action on each element of `s`, from last to first. -/
@[inline, expose]
public def forRevM {m : Type v → Type w} [Monad m] (f : Int32 → m PUnit)
    (s : Int32Array.Slice) : m PUnit :=
  s.foldrM (fun x _ => f x) ⟨⟩

/-- The result of the last element of `s` for which `f` returns `some`, searching from the end. -/
@[expose]
public def findSomeRevM? {β : Type v} {m : Type v → Type w} [Monad m] (s : Int32Array.Slice)
    (f : Int32 → m (Option β)) : m (Option β) :=
  loop s.size (Nat.le_refl _)
where
  @[specialize] loop : (i : Nat) → i ≤ s.size → m (Option β)
    | 0, _ => pure none
    | i + 1, h => do
      match ← f s[i] with
      | some b => pure (some b)
      | none => loop i (Nat.le_of_succ_le h)

@[noinline, nospecialize]
private def findSomeRevMSlow {β : Type v} {m : Type v → Type w} [Monad m]
    (s : Int32Array.Slice) (f : Int32 → m (Option β)) : m (Option β) :=
  s.findSomeRevM? f

@[inline]
public def findSomeRevMImpl {β : Type v} {m : Type v → Type w} [Monad m]
    (s : Int32Array.Slice) (f : Int32 → m (Option β)) : m (Option β) :=
  if s.array.size < USize.size then
    loop s.array s.start.toUSize s.stop.toUSize s.toNat_toUSize_stop_le
  else findSomeRevMSlow s f
where
  @[specialize] loop (a : Int32Array) (start i : USize) (hi : i.toNat ≤ a.size) :
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
    (f : Int32 → m (Option β)) (s : Int32Array.Slice) (start i : USize)
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
public def findRevM? {m : Type → Type w} [Monad m] (s : Int32Array.Slice) (p : Int32 → m Bool) :
    m (Option Int32) :=
  s.findSomeRevM? fun x => return if (← p x) then some x else none

/-- The last element of `s` that satisfies `p`. -/
@[inline, expose]
public def findRev? (s : Int32Array.Slice) (p : Int32 → Bool) : Option Int32 :=
  Id.run <| s.findRevM? (pure <| p ·)

/-- The first element of `s` that satisfies `p`. -/
@[inline, expose]
public def find? (s : Int32Array.Slice) (p : Int32 → Bool) : Option Int32 :=
  s.iter.find? p

/-- Whether some element of `s` satisfies `p`. -/
@[inline, expose]
public def any (s : Int32Array.Slice) (p : Int32 → Bool) : Bool :=
  s.iter.any p

/-- Whether every element of `s` satisfies `p`. -/
@[inline, expose]
public def all (s : Int32Array.Slice) (p : Int32 → Bool) : Bool :=
  s.iter.all p

/-- Whether some element of `s` is `==` to `v`. -/
@[inline, expose]
public def contains (s : Int32Array.Slice) (v : Int32) : Bool :=
  s.any (v == ·)

/-- The number of elements of `s` that satisfy `p`. -/
@[inline, expose]
public def count (s : Int32Array.Slice) (p : Int32 → Bool) : Nat :=
  s.iter.fold (fun n x => if p x then n + 1 else n) 0

/-- `x ∈ s` when `x` is an element of `s`. -/
public instance : Membership Int32 Int32Array.Slice where
  mem s x := x ∈ s.copy

/--
Compares the elements of two slices with `==`: slices of different arrays, or at different offsets,
are equal when their elements are. Logically it compares the copies.
-/
-- There is no `DecidableEq` instance: structural equality of slices compares the underlying arrays
-- and the bounds, so it would disagree with `==`.
public def beq (s t : Int32Array.Slice) : Bool :=
  s.copy == t.copy

@[noinline]
private def beqSlow (s t : Int32Array.Slice) : Bool :=
  s.beq t

-- Compares the sizes as `USize`s, so that the loop knows that the indices into `t` stay in bounds.
public def beqImpl (s t : Int32Array.Slice) : Bool :=
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
  loop (a b : Int32Array) (stop : USize) (hstop : stop.toNat ≤ a.size) (i j : USize)
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

private theorem beqImpl_loop (a b : Int32Array) (hb : b.size < USize.size) (stop : USize)
    (hstop : stop.toNat ≤ a.size) (i j : USize) (hj : stop.toNat - i.toNat + j.toNat ≤ b.size) :
    beqImpl.loop a b stop hstop i j hj = true ↔ ∀ (k : Nat) (hk : k < stop.toNat - i.toNat),
      (a.data[i.toNat + k]'(by rw [size_data']; lia) ==
        b.data[j.toNat + k]'(by rw [size_data']; lia)) = true := by
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

private theorem beq_iff (s t : Int32Array.Slice) :
    beq s t = true ↔ s.size = t.size ∧ ∀ (k : Nat) (hk : k < s.size) (hk' : k < t.size),
      (s.array.data[s.start + k]'(by
        have := s.stop_le_array_size; rw [size_data']; rw [size_eq] at hk; lia) ==
      t.array.data[t.start + k]'(by
        have := t.stop_le_array_size; rw [size_data']; rw [size_eq] at hk'; lia)) = true := by
  have hc (u : Int32Array.Slice) : u.copy.data = u.array.data.extract u.start u.stop := rfl
  have hs (u : Int32Array.Slice) : min u.stop u.array.data.size - u.start = u.size := by
    have := u.stop_le_array_size
    rw [size_eq, size_data']; lia
  rw [beq, beq_eq_beq_data, hc, hc, Array.beq_eq_decide]
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

public instance : BEq Int32Array.Slice := ⟨beq⟩

end Slice

/--
Collects the values emitted by an iterator into a new array. Together with the `Std.Iterators`
combinators, this gives functions such as `map`, `filter`, `take` and `zipWith`, for example
`(a.iter.map (· + 1)).toInt32Array`.
-/
@[inline, expose]
public def _root_.Std.Iter.toInt32Array {α : Type} [Std.Iterator α Id Int32]
    [Std.IteratorLoop α Id Id] (it : Std.Iter (α := α) Int32) : Int32Array :=
  it.fold (·.push ·) empty

/-- Like `Std.Iter.toInt32Array`, but the new array starts with room for `capacity` elements. -/
@[inline, expose]
public def _root_.Std.Iter.toInt32ArrayWithCapacity {α : Type} [Std.Iterator α Id Int32]
    [Std.IteratorLoop α Id Id] (it : Std.Iter (α := α) Int32) (capacity : Nat) : Int32Array :=
  it.fold (·.push ·) (emptyWithCapacity capacity)

@[simp] public theorem _root_.Std.Iter.toInt32ArrayWithCapacity_eq {α : Type}
    [Std.Iterator α Id Int32] [Std.IteratorLoop α Id Id] (it : Std.Iter (α := α) Int32)
    (capacity : Nat) : it.toInt32ArrayWithCapacity capacity = it.toInt32Array := rfl

@[simp] public theorem size_mk (a : Array Int32) : (mk a).size = a.size := rfl

public theorem size_eq_data_size (a : Int32Array) : a.size = a.data.size := by cases a; rfl

@[simp] public theorem size_data (a : Int32Array) : a.data.size = a.size :=
  (size_eq_data_size a).symm

@[simp] public theorem size_uset (a : Int32Array) (i : USize) (v : Int32) (h) :
    (a.uset i v h).size = a.size :=
  Array.size_set (h := h)

@[simp] public theorem size_set (a : Int32Array) (i : Nat) (v : Int32) (h) :
    (a.set i v h).size = a.size :=
  Array.size_set (h := h)

@[simp] public theorem size_push (a : Int32Array) (v : Int32) :
    (a.push v).size = a.size + 1 := by
  cases a; simp [push, size]

@[simp] public theorem data_append (a b : Int32Array) : (a ++ b).data = a.data ++ b.data := by
  cases a; cases b; rfl

@[simp] public theorem size_append (a b : Int32Array) : (a ++ b).size = a.size + b.size := by
  simp [-size_data, size_eq_data_size]

@[ext] public theorem ext {a b : Int32Array} (h : a.data = b.data) : a = b := data_injective h

@[simp] public theorem getElem_mk (a : Array Int32) (i : Nat) (h : i < (mk a).size) :
    (mk a)[i] = a[i] := rfl

public theorem getElem_eq_getElem_data (a : Int32Array) (i : Nat) (h : i < a.size) :
    a[i] = a.data[i]'(size_eq_data_size a ▸ h) := by
  cases a; rfl

@[simp] public theorem getElem_data (a : Int32Array) (i : Nat) (h : i < a.data.size) :
    a.data[i] = a[i]'(by simpa using h) := by
  cases a; rfl

public theorem ext_getElem {a b : Int32Array} (h₁ : a.size = b.size)
    (h₂ : ∀ (i : Nat) (hi₁ : i < a.size) (hi₂ : i < b.size), a[i] = b[i]) : a = b := by
  ext i hi₁ hi₂
  · simpa using h₁
  · simpa using h₂ i (by simpa using hi₁) (by simpa using hi₂)

@[simp] public theorem getElem_usize (a : Int32Array) (i : USize) (h : i.toNat < a.size) :
    a[i] = a[i.toNat] := by
  cases a; rfl

@[simp] public theorem data_uset (a : Int32Array) (i : USize) (v : Int32) (h) :
    (a.uset i v h).data = a.data.set i.toNat v (size_eq_data_size a ▸ h) := by
  cases a; rfl

@[simp] public theorem data_set (a : Int32Array) (i : Nat) (v : Int32) (h) :
    (a.set i v h).data = a.data.set i v (size_eq_data_size a ▸ h) := by
  cases a; rfl

@[simp] public theorem data_push (a : Int32Array) (v : Int32) :
    (a.push v).data = a.data.push v := by
  cases a; rfl

@[simp] public theorem data_pop (a : Int32Array) : a.pop.data = a.data.pop := by
  cases a; rfl

@[simp] public theorem data_extract (a : Int32Array) (start stop : Nat) :
    (a.extract start stop).data = a.data.extract start stop := by
  cases a; rfl

@[simp] public theorem data_replicate (n : Nat) (v : Int32) :
    (replicate n v).data = Array.replicate n v := rfl

@[simp] public theorem data_ofFn {n : Nat} (f : Fin n → Int32) :
    (ofFn f).data = Array.ofFn f := rfl

@[simp] public theorem data_empty : (empty : Int32Array).data = #[] := rfl

@[simp] public theorem size_pop (a : Int32Array) : a.pop.size = a.size - 1 := by
  simp [-size_data, size_eq_data_size]

@[simp] public theorem size_extract (a : Int32Array) (start stop : Nat) :
    (a.extract start stop).size = min stop a.size - start := by
  simp [-size_data, size_eq_data_size]

@[simp] public theorem size_replicate (n : Nat) (v : Int32) : (replicate n v).size = n := by
  simp [-size_data, size_eq_data_size]

@[simp] public theorem size_ofFn {n : Nat} (f : Fin n → Int32) : (ofFn f).size = n := by
  simp [-size_data, size_eq_data_size]

@[simp] public theorem size_empty : (empty : Int32Array).size = 0 := rfl

@[simp] public theorem getElem_set (a : Int32Array) (i : Nat) (v : Int32) (h) (j : Nat) (hj) :
    (a.set i v h)[j]'hj = if i = j then v else a[j]'(by simpa using hj) := by
  simp [-getElem_data, getElem_eq_getElem_data, Array.getElem_set]

@[simp] public theorem getElem_push (a : Int32Array) (v : Int32) (i : Nat) (h) :
    (a.push v)[i]'h = if h' : i < a.size then a[i] else v := by
  simp [-getElem_data, getElem_eq_getElem_data, Array.getElem_push, -size_data, size_eq_data_size]

@[simp] public theorem getElem_pop (a : Int32Array) (i : Nat) (h) :
    a.pop[i]'h = a[i]'(by simp at h; lia) := by
  simp [-getElem_data, getElem_eq_getElem_data]

@[simp] public theorem data_popWhile (p : Int32 → Bool) (a : Int32Array) :
    (a.popWhile p).data = a.data.popWhile p := by
  cases a; rfl

@[simp] public theorem getElem_append (a b : Int32Array) (i : Nat) (h) :
    (a ++ b)[i]'h = if h' : i < a.size then a[i] else b[i - a.size]'(by simp at h; lia) := by
  simp [-getElem_data, getElem_eq_getElem_data, Array.getElem_append, -size_data, size_eq_data_size]

@[simp] public theorem getElem_extract (a : Int32Array) (start stop i : Nat) (h) :
    (a.extract start stop)[i]'h = a[start + i]'(by simp at h; lia) := by
  simp [-getElem_data, getElem_eq_getElem_data]

@[simp] public theorem getElem_replicate (n : Nat) (v : Int32) (i : Nat) (h) :
    (replicate n v)[i]'h = v := by
  simp [-getElem_data, getElem_eq_getElem_data]

@[simp] public theorem getElem_ofFn {n : Nat} (f : Fin n → Int32) (i : Nat) (h) :
    (ofFn f)[i]'h = f ⟨i, by simpa using h⟩ := by
  simp [-getElem_data, getElem_eq_getElem_data]

public theorem foldl_eq_foldl_data {β : Type v} (f : β → Int32 → β) (init : β)
    (a : Int32Array) :
    a.foldl f init = a.data.foldl f init := by
  rfl

public theorem foldr_eq_foldr_data {β : Type v} (f : Int32 → β → β) (init : β)
    (a : Int32Array) :
    a.foldr f init = a.data.foldr f init := by
  rfl

@[simp] public theorem toList_data (a : Int32Array) : a.data.toList = a.toList := rfl

@[simp] public theorem emptyc_eq_empty : (∅ : Int32Array) = empty := rfl

@[simp] public theorem emptyWithCapacity_eq_empty (c : Nat) : emptyWithCapacity c = empty := rfl

public theorem size_eq_zero_iff {a : Int32Array} : a.size = 0 ↔ a = empty := by
  simp [Int32Array.ext_iff, ← Array.size_eq_zero_iff]

@[simp] public theorem data_set! (a : Int32Array) (i : Nat) (v : Int32) :
    (a.set! i v).data = a.data.set! i v := by
  simp only [set!, Array.set!_eq_setIfInBounds, Array.setIfInBounds, size_eq_data_size]
  split <;> rfl

@[simp] public theorem size_set! (a : Int32Array) (i : Nat) (v : Int32) :
    (a.set! i v).size = a.size := by
  simp [-size_data, size_eq_data_size]

public theorem getElem!_eq_getElem!_data (a : Int32Array) (i : Nat) : a[i]! = a.data[i]! := by
  by_cases h : i < a.size <;> simp [h] <;> rfl

@[simp] public theorem data_ofList (l : List Int32) : (ofList l).data = l.toArray := rfl

@[simp] public theorem size_ofList (l : List Int32) : (ofList l).size = l.length := rfl

@[simp] public theorem getElem_ofList (l : List Int32) (i : Nat) (h) :
    (ofList l)[i]'h = l[i]'(by simpa using h) := rfl

@[simp] public theorem toList_ofList (l : List Int32) : (ofList l).toList = l := rfl

@[simp] public theorem ofList_toList (a : Int32Array) : ofList a.toList = a := by
  simp [Int32Array.ext_iff, ← toList_data]

@[simp] public theorem markLinear_eq (a : Int32Array) : a.markLinear = a := rfl

@[simp] public theorem propagateMark_eq (a b : Int32Array) : a.propagateMark b = b := rfl

@[simp] public theorem append_empty (a : Int32Array) : a ++ empty = a := by
  simp [Int32Array.ext_iff]

@[simp] public theorem empty_append (a : Int32Array) : empty ++ a = a := by
  simp [Int32Array.ext_iff]

public theorem append_assoc (a b c : Int32Array) : a ++ b ++ c = a ++ (b ++ c) := by
  simp [Int32Array.ext_iff]

@[simp] public theorem append_eq_empty_iff {a b : Int32Array} :
    a ++ b = empty ↔ a = empty ∧ b = empty := by
  simp only [Int32Array.ext_iff, data_append, data_empty, Array.append_eq_empty_iff]

@[simp] public theorem append_right_inj (a : Int32Array) {b c : Int32Array} :
    a ++ b = a ++ c ↔ b = c := by
  simp only [Int32Array.ext_iff, data_append, Array.append_right_inj]

@[simp] public theorem append_left_inj {a b : Int32Array} (c : Int32Array) :
    a ++ c = b ++ c ↔ a = b := by
  simp only [Int32Array.ext_iff, data_append, Array.append_left_inj]

public theorem getElem_append_left {a b : Int32Array} {i : Nat} (h : i < a.size) :
    (a ++ b)[i]'(by simp; lia) = a[i] := by
  simp [h]

public theorem getElem_append_right {a b : Int32Array} {i : Nat} (h : a.size ≤ i)
    (h' : i < (a ++ b).size) : (a ++ b)[i] = b[i - a.size]'(by simp at h'; lia) := by
  simp [Nat.not_lt.mpr h]

@[simp] public theorem extract_same (a : Int32Array) (i : Nat) : a.extract i i = empty := by
  simp [Int32Array.ext_iff]; lia

@[simp] public theorem extract_zero_size (a : Int32Array) : a.extract 0 a.size = a := by
  simp [Int32Array.ext_iff]

@[simp] public theorem extract_eq_empty_iff {a : Int32Array} {i j : Nat} :
    a.extract i j = empty ↔ min j a.size ≤ i := by
  simp [Int32Array.ext_iff]

public theorem extract_extract (a : Int32Array) (i j k l : Nat) :
    (a.extract i j).extract k l = a.extract (i + k) (min (i + l) j) := by
  simp [Int32Array.ext_iff]

public theorem extract_append_extract (a : Int32Array) (i j k : Nat) :
    a.extract i j ++ a.extract j k = a.extract (min i j) (max j k) := by
  simp [Int32Array.ext_iff]

@[simp] public theorem extract_append_eq_left (a b : Int32Array) :
    (a ++ b).extract 0 a.size = a := by
  simp [Int32Array.ext_iff]

@[simp] public theorem extract_append_eq_right (a b : Int32Array) :
    (a ++ b).extract a.size (a.size + b.size) = b := by
  simp [Int32Array.ext_iff, -size_data, size_eq_data_size]

@[simp] public theorem data_copySlice (src : Int32Array) (srcOff : Nat) (dest : Int32Array)
    (destOff len : Nat) (exact : Bool) :
    (src.copySlice srcOff dest destOff len exact).data =
      dest.data.extract 0 destOff ++ src.data.extract srcOff (srcOff + len) ++
        dest.data.extract (destOff + min len (src.size - srcOff)) dest.size := by
  simp [copySlice]

public theorem copySlice_eq_append (src : Int32Array) (srcOff : Nat) (dest : Int32Array)
    (destOff len : Nat) (exact : Bool) :
    src.copySlice srcOff dest destOff len exact =
      dest.extract 0 destOff ++ src.extract srcOff (srcOff + len) ++
        dest.extract (destOff + min len (src.size - srcOff)) dest.size := by
  simp [Int32Array.ext_iff]

@[simp] public theorem Slice.size_copy (s : Int32Array.Slice) : s.copy.size = s.size := by
  have := s.stop_le_array_size
  simp only [Slice.copy, size_extract, Slice.size_eq]
  lia

/-! ### Lists -/

@[simp] public theorem toList_mk (a : Array Int32) : (mk a).toList = a.toList := rfl

@[simp] public theorem length_toList (a : Int32Array) : a.toList.length = a.size := by
  simp [← toList_data]

@[simp] public theorem getElem_toList (a : Int32Array) (i : Nat) (h : i < a.toList.length) :
    a.toList[i] = a[i]'(by simpa using h) := by
  simp [← toList_data]

@[simp] public theorem getElem?_toList (a : Int32Array) (i : Nat) : a.toList[i]? = a[i]? := by
  by_cases h : i < a.size <;> simp [h, ← toList_data]

@[simp] public theorem toList_inj {a b : Int32Array} : a.toList = b.toList ↔ a = b :=
  ⟨fun h => by rw [← ofList_toList a, h, ofList_toList], fun h => h ▸ rfl⟩

@[simp] public theorem toList_empty : (empty : Int32Array).toList = [] := rfl

@[simp] public theorem toList_push (a : Int32Array) (v : Int32) :
    (a.push v).toList = a.toList ++ [v] := by
  simp [← toList_data]

@[simp] public theorem toList_pop (a : Int32Array) : a.pop.toList = a.toList.dropLast := by
  simp [← toList_data]

@[simp] public theorem toList_append (a b : Int32Array) :
    (a ++ b).toList = a.toList ++ b.toList := by
  simp [← toList_data]

@[simp] public theorem toList_set (a : Int32Array) (i : Nat) (v : Int32) (h) :
    (a.set i v h).toList = a.toList.set i v := by
  simp [← toList_data]

@[simp] public theorem toList_set! (a : Int32Array) (i : Nat) (v : Int32) :
    (a.set! i v).toList = a.toList.set i v := by
  simp [← toList_data]

@[simp] public theorem toList_extract (a : Int32Array) (start stop : Nat) :
    (a.extract start stop).toList = a.toList.extract start stop := by
  simp [← toList_data]

@[simp] public theorem toList_replicate (n : Nat) (v : Int32) :
    (replicate n v).toList = List.replicate n v := by
  simp [← toList_data]

@[simp] public theorem toList_ofFn {n : Nat} (f : Fin n → Int32) :
    (ofFn f).toList = List.ofFn f := by
  simp [← toList_data]

@[simp] public theorem toList_popWhile (p : Int32 → Bool) (a : Int32Array) :
    (a.popWhile p).toList = (a.toList.reverse.dropWhile p).reverse := by
  rw [← toList_data, data_popWhile, ← Array.toArray_toList (xs := a.data),
    List.popWhile_toArray]
  simp

/-! ### Machine-word indices -/

/--
`usize` is the size when the size fits in a `USize`, which holds for every array in memory. Loops
over `USize` indices take this as a hypothesis, since the model `Array` has no bound on its size.
-/
public theorem toNat_usize_of_lt (a : Int32Array) (h : a.size < USize.size) :
    a.usize.toNat = a.size := by
  simp [Nat.mod_eq_of_lt h]

/-- The guard `i < a.usize` of a loop over `USize` indices bounds the index. -/
public theorem lt_usize_iff (a : Int32Array) (h : a.size < USize.size) {i : USize} :
    i < a.usize ↔ i.toNat < a.size := by
  rw [USize.lt_iff_toNat_lt, toNat_usize_of_lt a h]

/-! ### Last element -/

public theorem back?_eq_getElem? (a : Int32Array) : a.back? = a[a.size - 1]? := by
  simp only [back?]

public theorem back!_eq_getElem! (a : Int32Array) : a.back! = a[a.size - 1]! := by
  simp only [back!]

public theorem back_eq_getElem (a : Int32Array) (h : 0 < a.size) :
    a.back h = a[a.size - 1]'(Nat.sub_lt h Nat.one_pos) := by
  simp only [back]

@[simp] public theorem getLast?_toList (a : Int32Array) : a.toList.getLast? = a.back? := by
  rw [List.getLast?_eq_getElem?, getElem?_toList, length_toList, back?_eq_getElem?]

@[simp] public theorem back?_empty : (empty : Int32Array).back? = none := by
  rw [← getLast?_toList, toList_empty, List.getLast?_nil]

@[simp] public theorem back?_push (a : Int32Array) (v : Int32) :
    (a.push v).back? = some v := by
  rw [← getLast?_toList, toList_push, List.getLast?_concat]

@[simp] public theorem back!_push (a : Int32Array) (v : Int32) : (a.push v).back! = v := by
  simp [back!_eq_getElem!]

@[simp] public theorem back_push (a : Int32Array) (v : Int32) (h) : (a.push v).back h = v := by
  simp [back_eq_getElem]

/-! ### More lists -/

@[simp] public theorem toList_uset (a : Int32Array) (i : USize) (v : Int32) (h) :
    (a.uset i v h).toList = a.toList.set i.toNat v := by
  simp [← toList_data]

@[simp] public theorem toList_copySlice (src : Int32Array) (srcOff : Nat) (dest : Int32Array)
    (destOff len : Nat) (exact : Bool) :
    (src.copySlice srcOff dest destOff len exact).toList =
      dest.toList.extract 0 destOff ++ src.toList.extract srcOff (srcOff + len) ++
        dest.toList.extract (destOff + min len (src.size - srcOff)) dest.size := by
  simp [copySlice_eq_append]

/-! ### Accessors -/

@[simp] public theorem get_eq_getElem (a : Int32Array) (i : Nat) (h) : a.get i h = a[i] := rfl

@[simp] public theorem uget_eq_getElem (a : Int32Array) (i : USize) (h) :
    a.uget i h = a[i.toNat] := by
  cases a; rfl

@[simp] public theorem get!_eq_getElem! (a : Int32Array) (i : Nat) : a.get! i = a[i]! := by
  rw [get!]
  split
  · simp_all [getElem!_pos]
  · simp_all [getElem!_neg]

@[simp] public theorem getD_eq_getD_getElem? (a : Int32Array) (i : Nat) (v₀ : Int32) :
    a.getD i v₀ = a[i]?.getD v₀ := by
  rw [getD]
  split <;> simp_all

@[simp] public theorem isEmpty_iff {a : Int32Array} : a.isEmpty ↔ a = empty := by
  simp [isEmpty, ← size_eq_zero_iff]

/-! ### Queries -/

@[simp] public theorem any_toList (a : Int32Array) (p : Int32 → Bool) :
    a.toList.any p = a.any p := by
  simp [any, ← toList_data]

@[simp] public theorem all_toList (a : Int32Array) (p : Int32 → Bool) :
    a.toList.all p = a.all p := by
  simp [all, ← toList_data]

@[simp] public theorem contains_toList (a : Int32Array) (v : Int32) :
    a.toList.contains v = a.contains v := by
  simp [contains, ← toList_data]

@[simp] public theorem foldl_toList {β : Type v} (f : β → Int32 → β) (init : β)
    (a : Int32Array) : a.toList.foldl f init = a.foldl f init := by
  simp [foldl_eq_foldl_data, ← toList_data]

@[simp] public theorem foldr_toList {β : Type v} (f : Int32 → β → β) (init : β)
    (a : Int32Array) : a.toList.foldr f init = a.foldr f init := by
  simp [foldr_eq_foldr_data, ← toList_data]

@[simp] public theorem forIn_toList {β : Type v} {m : Type v → Type w} [Monad m] [LawfulMonad m]
    (a : Int32Array) (init : β) (f : Int32 → β → m (ForInStep β)) :
    ForIn.forIn a.toList init f = ForIn.forIn a init f := by
  rw [← toList_data, Array.forIn_toList]
  rfl

private theorem findIdx?_loop_eq (a : Int32Array) (p : Int32 → Bool) (i : Nat) :
    findIdx?.loop a p i = ((a.toList.drop i).findIdx? p).map (· + i) := by
  fun_induction findIdx?.loop a p i with
  | case1 i h hp =>
    rw [List.drop_eq_getElem_cons (by simpa using h), List.findIdx?_cons]
    simp [hp]
  | case2 i h hp ih =>
    rw [ih, List.drop_eq_getElem_cons (l := a.toList) (i := i) (by simpa using h),
      List.findIdx?_cons]
    simp [hp, Option.map_map, Function.comp_def, Nat.add_assoc, Nat.add_comm 1]
  | case3 i h =>
    rw [List.drop_of_length_le (by simpa using h)]
    rfl

public theorem findIdx?_eq (a : Int32Array) (p : Int32 → Bool) (start : Nat) :
    a.findIdx? p start = ((a.toList.drop start).findIdx? p).map (· + start) := by
  simp [findIdx?, findIdx?_loop_eq]

@[simp] public theorem findIdx?_toList (a : Int32Array) (p : Int32 → Bool) :
    a.toList.findIdx? p = a.findIdx? p := by
  simp [findIdx?_eq]

private theorem findFinIdx?_loop_eq (a : Int32Array) (p : Int32 → Bool) (i : Nat) :
    (findFinIdx?.loop a p i).map Fin.val = findIdx?.loop a p i := by
  fun_induction findFinIdx?.loop a p i <;> rw [findIdx?.loop] <;> simp_all <;> lia

@[simp] public theorem map_val_findFinIdx? (a : Int32Array) (p : Int32 → Bool) (start : Nat) :
    (a.findFinIdx? p start).map Fin.val = a.findIdx? p start := by
  simp [findFinIdx?, findIdx?, findFinIdx?_loop_eq]

/-! ### Slices -/

@[simp] public theorem Slice.getElem_copy (s : Int32Array.Slice) (i : Nat)
    (h : i < s.copy.size) :
    s.copy[i] = s[i]'(by simpa using h) := by
  simp [Slice.copy, Slice.getElem_eq]

/-- Copying the slice from `start` to `stop` is the same as extracting those elements. -/
@[simp] public theorem copy_toSlice (a : Int32Array) (start stop : Nat) :
    (a.toSlice start stop).copy = a.extract start stop := by
  rw [← toList_inj]
  unfold toSlice
  split <;> split <;>
    simp [Slice.copy, Slice.array, Slice.start, Slice.stop] <;> lia

@[simp] public theorem array_toSlice (a : Int32Array) (start stop : Nat) :
    (a.toSlice start stop).array = a := by
  unfold toSlice
  split <;> split <;> rfl

@[simp] public theorem start_toSlice (a : Int32Array) (start stop : Nat) :
    (a.toSlice start stop).start = min start (min stop a.size) := by
  unfold toSlice
  split <;> split <;> simp only [Slice.start] <;> lia

@[simp] public theorem stop_toSlice (a : Int32Array) (start stop : Nat) :
    (a.toSlice start stop).stop = min stop a.size := by
  unfold toSlice
  split <;> split <;> simp only [Slice.stop] <;> lia

@[simp] public theorem size_toSlice (a : Int32Array) (start stop : Nat) :
    (a.toSlice start stop).size = min stop a.size - start := by
  rw [Slice.size_eq, start_toSlice, stop_toSlice]
  lia

@[simp] public theorem getElem_toSlice (a : Int32Array) (start stop i : Nat) (h) :
    (a.toSlice start stop)[i]'h = a[start + i]'(by simp at h; lia) := by
  simp only [size_toSlice] at h
  simp only [Slice.getElem_eq, array_toSlice, start_toSlice]
  congr 1
  lia

@[simp] public theorem Slice.size_slice (s : Int32Array.Slice) (start stop : Nat) :
    (s.slice start stop).size = min stop s.size - start := by
  have := s.stop_le_array_size
  rw [slice, size_toSlice, size_eq]
  lia

@[simp] public theorem Slice.getElem_slice (s : Int32Array.Slice) (start stop i : Nat) (h) :
    (s.slice start stop)[i]'h = s[start + i]'(by simp at h; lia) := by
  have := s.stop_le_array_size
  have := s.size_eq
  have h' := h
  rw [size_slice, size_eq] at h'
  simp only [Slice.getElem_eq, slice, array_toSlice, start_toSlice]
  congr 1
  lia

@[simp] public theorem Slice.copy_slice (s : Int32Array.Slice) (start stop : Nat) :
    (s.slice start stop).copy = s.copy.extract start stop := by
  apply ext_getElem
  · simp
  · intro i _ _
    simp

@[simp] public theorem Slice.array_popFront (s : Int32Array.Slice) :
    s.popFront.array = s.array := by
  simp only [popFront]
  split <;> rfl

@[simp] public theorem Slice.start_popFront (s : Int32Array.Slice) :
    s.popFront.start = min (s.start + 1) s.stop := by
  rcases s with ⟨⟨_, start, stop, h, _⟩⟩
  simp only [popFront, Slice.start, Slice.stop]
  by_cases hc : start < stop <;> simp [hc] <;> lia

@[simp] public theorem Slice.stop_popFront (s : Int32Array.Slice) :
    s.popFront.stop = s.stop := by
  simp only [popFront]
  split <;> rfl

@[simp] public theorem Slice.size_popFront (s : Int32Array.Slice) :
    s.popFront.size = s.size - 1 := by
  rw [size_eq, size_eq, start_popFront, stop_popFront]
  lia

@[simp] public theorem Slice.getElem_popFront (s : Int32Array.Slice) (i : Nat) (h) :
    s.popFront[i]'h = s[i + 1]'(by simp at h; lia) := by
  have : s.start < s.stop := by rw [size_popFront, size_eq] at h; lia
  simp only [Slice.getElem_eq, array_popFront, start_popFront]
  congr 1
  lia

public theorem Slice.getD_eq (s : Int32Array.Slice) (i : Nat) (v₀ : Int32) :
    s.getD i v₀ = if h : i < s.size then s[i] else v₀ := by
  rw [Slice.getD]

public theorem Slice.get!_eq (s : Int32Array.Slice) (i : Nat) :
    s.get! i = if h : i < s.size then s[i] else default := by
  rw [Slice.get!, Slice.getD]

private theorem Slice.foldrM_loop_eq {β : Type v} (f : Int32 → β → β)
    (s : Int32Array.Slice) (i : Nat) (h : i ≤ s.size) (b : β) :
    Slice.foldrM.loop (m := Id) (pure <| f · ·) s i h b = (s.copy.toList.take i).foldr f b := by
  induction i generalizing b with
  | zero => rfl
  | succ i ih =>
    have hi : i < s.copy.toList.length := by simp; lia
    rw [Slice.foldrM.loop, List.take_add_one, List.getElem?_eq_getElem hi]
    simp [ih]

/-- Folding over a slice is folding over the list of its elements. -/
public theorem Slice.foldr_eq_foldr_toList_copy {β : Type v} (f : Int32 → β → β)
    (init : β) (s : Int32Array.Slice) : s.foldr f init = s.copy.toList.foldr f init := by
  rw [Slice.foldr, Slice.foldrM, Id.run, Slice.foldrM_loop_eq,
    List.take_of_length_le (by simp)]

/-! ### Writes -/

@[simp] public theorem getElem_uset (a : Int32Array) (i : USize) (v : Int32) (h) (j : Nat)
    (hj) : (a.uset i v h)[j]'hj = if i.toNat = j then v else a[j]'(by simpa using hj) := by
  simp [-getElem_data, getElem_eq_getElem_data, Array.getElem_set]

@[simp] public theorem getElem_set! (a : Int32Array) (i : Nat) (v : Int32) (j : Nat) (hj) :
    (a.set! i v)[j]'hj = if i = j then v else a[j]'(by simpa using hj) := by
  simp only [getElem_eq_getElem_data, data_set!, Array.set!_eq_setIfInBounds]
  rw [Array.getElem_setIfInBounds]

@[simp] public theorem getElem?_set! (a : Int32Array) (i : Nat) (v : Int32) (j : Nat) :
    (a.set! i v)[j]? = if i = j then if i < a.size then some v else none else a[j]? := by
  by_cases hj : j < a.size <;> by_cases hij : i = j <;> simp_all

public theorem size_popWhile_le (p : Int32 → Bool) (a : Int32Array) :
    (a.popWhile p).size ≤ a.size := by
  rw [← length_toList, ← length_toList, toList_popWhile, List.length_reverse]
  simpa using (List.dropWhile_sublist (l := a.toList.reverse) p).length_le

@[simp] public theorem size_copySlice (src : Int32Array) (srcOff : Nat) (dest : Int32Array)
    (destOff len : Nat) (exact : Bool) :
    (src.copySlice srcOff dest destOff len exact).size =
      max dest.size (min destOff dest.size + min len (src.size - srcOff)) := by
  simp [-size_data, size_eq_data_size]
  lia

public theorem getElem_copySlice (src : Int32Array) (srcOff : Nat) (dest : Int32Array)
    (destOff len : Nat) (exact : Bool) (i : Nat) (h) :
    (src.copySlice srcOff dest destOff len exact)[i]'h =
      if h₁ : i < min destOff dest.size then dest[i]'(by lia)
      else if h₂ : i - min destOff dest.size < min len (src.size - srcOff) then
        src[srcOff + (i - min destOff dest.size)]'(by lia)
      else dest[i]'(by simp at h; lia) := by
  have hs := size_copySlice src srcOff dest destOff len exact
  simp only [copySlice_eq_append, getElem_append, getElem_extract, size_append, size_extract,
    Nat.sub_zero, Nat.zero_add]
  by_cases h₁ : i < min destOff dest.size
  · have : i < min destOff dest.size + (min (srcOff + len) src.size - srcOff) := by lia
    simp [h₁, this]
  · by_cases h₂ : i - min destOff dest.size < min len (src.size - srcOff)
    · have : i < min destOff dest.size + (min (srcOff + len) src.size - srcOff) := by lia
      simp [h₁, h₂, this]
    · have : ¬i < min destOff dest.size + (min (srcOff + len) src.size - srcOff) := by lia
      simp only [h₁, h₂, this, ↓reduceDIte]
      congr 1
      lia

/-! ### Monadic folds -/

@[simp] public theorem foldlM_toList {β : Type v} {m : Type v → Type w} [Monad m]
    (f : β → Int32 → m β) (init : β) (a : Int32Array) :
    a.toList.foldlM f init = a.foldlM f init := by
  rw [← toList_data, Array.foldlM_toList, foldlM, size_eq_data_size]

@[simp] public theorem foldrM_toList {β : Type v} {m : Type v → Type w} [Monad m]
    (f : Int32 → β → m β) (init : β) (a : Int32Array) :
    a.toList.foldrM f init = a.foldrM f init := by
  rw [← toList_data, Array.foldrM_toList]
  rfl

@[simp] public theorem forM_eq_forM {m : Type v → Type w} [Monad m] (f : Int32 → m PUnit)
    (a : Int32Array) : a.forM f = ForM.forM a f := rfl

@[simp] public theorem forM_toList {m : Type v → Type w} [Monad m] (f : Int32 → m PUnit)
    (a : Int32Array) : ForM.forM a.toList f = ForM.forM a f := by
  cases a with | mk a
  rcases a with ⟨l⟩
  exact (List.forM_toArray l f).symm

/-! ### Membership -/

public theorem mem_def {x : Int32} {a : Int32Array} : x ∈ a ↔ x ∈ a.data := Iff.rfl

@[simp] public theorem mem_data {x : Int32} {a : Int32Array} : x ∈ a.data ↔ x ∈ a := Iff.rfl

@[simp] public theorem mem_mk {x : Int32} {xs : Array Int32} : x ∈ mk xs ↔ x ∈ xs := Iff.rfl

@[simp] public theorem mem_toList {x : Int32} {a : Int32Array} : x ∈ a.toList ↔ x ∈ a := by
  rw [← toList_data, Array.mem_toList_iff, mem_data]

public theorem mem_iff_getElem {x : Int32} {a : Int32Array} :
    x ∈ a ↔ ∃ (i : Nat) (h : i < a.size), a[i] = x := by
  rw [← mem_data, Array.mem_iff_getElem]
  simp

public theorem getElem_mem {a : Int32Array} {i : Nat} (h : i < a.size) : a[i] ∈ a :=
  mem_iff_getElem.mpr ⟨i, h, rfl⟩

@[simp] public theorem not_mem_empty (x : Int32) : ¬x ∈ (empty : Int32Array) := by
  simp [← mem_data]

@[simp] public theorem mem_push {x v : Int32} {a : Int32Array} :
    x ∈ a.push v ↔ x ∈ a ∨ x = v := by
  simp [← mem_data]

@[simp] public theorem mem_append {x : Int32} {a b : Int32Array} :
    x ∈ a ++ b ↔ x ∈ a ∨ x ∈ b := by
  simp [← mem_data]

/-! ### Iterators -/

private theorem toList_foldl_push (a : Int32Array) (l : List Int32) :
    (l.foldl (·.push ·) a).toList = a.toList ++ l := by
  induction l generalizing a <;> simp_all

@[simp] public theorem _root_.Std.Iter.toList_toInt32Array {α : Type} [Std.Iterator α Id Int32]
    [Std.Iterators.Finite α Id] [Std.IteratorLoop α Id Id] [Std.LawfulIteratorLoop α Id Id]
    (it : Std.Iter (α := α) Int32) : it.toInt32Array.toList = it.toList := by
  rw [Std.Iter.toInt32Array, ← Std.Iter.foldl_toList, toList_foldl_push, toList_empty,
    List.nil_append]

private theorem Slice.cons_take_drop (a : Int32Array) (s t : Nat) (h : s < t)
    (h' : s < a.size) :
    a[s] :: (a.toList.drop (s + 1)).take (t - (s + 1)) = (a.toList.drop s).take (t - s) := by
  rw [List.drop_eq_getElem_cons (by simpa using h' : s < a.toList.length),
    show t - s = t - (s + 1) + 1 by lia, List.take_succ_cons, getElem_toList]

private theorem SliceIterator.toList_eq (it : Std.Iter (α := Int32Array.SliceIterator) Int32) :
    it.toList = it.internalState.xs.copy.toList := by
  induction it using Std.Iter.inductSteps with | step it ihy ihs
  rw [Std.Iter.toList_eq_match_step]
  have hs : it.step.val = (SliceIterator.step it.toIterM).mapIterator Std.IterM.toIter := by
    simp [Std.Iter.step, Std.IterM.step, Std.Iterator.step, Std.IterM.Step.toPure]
  rw [hs]
  have h₂ := it.internalState.xs.stop_le_array_size
  by_cases h : it.internalState.xs.start < it.internalState.xs.stop
  · simp only [SliceIterator.step, Std.Iter.toIterM, h, ↓reduceDIte,
      Std.IterStep.mapIterator_yield]
    rw [ihy (out := it.internalState.xs.array[it.internalState.xs.start])]
    · simp only [Slice.copy, Slice.array, Slice.start, Slice.stop, toList_extract,
        List.extract_eq_take_drop, Std.IterM.toIter] at h h₂ ⊢
      exact Slice.cons_take_drop _ _ _ h (by lia)
    · show _ = SliceIterator.step _
      simp only [SliceIterator.step, Std.Iter.toIterM, h, ↓reduceDIte]
      rfl
  · simp only [SliceIterator.step, Std.Iter.toIterM, h, ↓reduceDIte,
      Std.IterStep.mapIterator_done]
    simp [Slice.copy]
    lia

/-! ### Slices as copies -/

@[simp] public theorem Slice.size_empty : (Slice.empty : Int32Array.Slice).size = 0 := rfl

@[simp] public theorem Slice.emptyc_eq_empty : (∅ : Int32Array.Slice) = Slice.empty := rfl

@[simp] public theorem Slice.copy_empty : (Slice.empty : Int32Array.Slice).copy = empty := by
  simp [Slice.copy, Slice.empty, Slice.array, Slice.start, Slice.stop]

@[simp] public theorem Slice.toList_eq_toList_copy (s : Int32Array.Slice) :
    s.toList = s.copy.toList := by
  rw [Std.Slice.Internal.toList_eq_toList_iter, SliceIterator.toList_eq,
    Std.Slice.Internal.iter_eq_toIteratorIter, Std.ToIterator.iter_eq]
  rfl

@[simp] public theorem Slice.toInt32Array_iter (s : Int32Array.Slice) :
    s.iter.toInt32Array = s.copy := by
  rw [← toList_inj, Std.Iter.toList_toInt32Array, Std.Slice.toList_iter, toList_eq_toList_copy]

@[simp] public theorem toInt32Array_iter (a : Int32Array) : a.iter.toInt32Array = a := by
  rw [iter, Slice.toInt32Array_iter, copy_toSlice, extract_zero_size]

@[simp] public theorem Slice.foldl_eq_foldl_copy {β : Type v} (f : β → Int32 → β) (init : β)
    (s : Int32Array.Slice) : s.foldl f init = s.copy.foldl f init := by
  rw [← Std.Slice.foldl_toList, toList_eq_toList_copy, foldl_toList]

@[simp] public theorem Slice.foldlM_eq_foldlM_copy {β : Type v} {m : Type v → Type w} [Monad m]
    [LawfulMonad m] (f : β → Int32 → m β) (init : β) (s : Int32Array.Slice) :
    s.foldlM f init = s.copy.foldlM f init := by
  rw [← Std.Slice.foldlM_toList, toList_eq_toList_copy, foldlM_toList]

@[simp] public theorem Slice.forIn_eq_forIn_copy {β : Type v} {m : Type v → Type w} [Monad m]
    [LawfulMonad m] (s : Int32Array.Slice) (init : β) (f : Int32 → β → m (ForInStep β)) :
    ForIn.forIn s init f = ForIn.forIn s.copy init f := by
  rw [← Std.Slice.forIn_toList, toList_eq_toList_copy, forIn_toList]

@[simp] public theorem Slice.forM_eq_forM_copy {m : Type v → Type w} [Monad m] [LawfulMonad m]
    (s : Int32Array.Slice) (f : Int32 → m PUnit) : ForM.forM s f = ForM.forM s.copy f :=
  foldlM_eq_foldlM_copy ..

@[simp] public theorem Slice.foldr_eq_foldr_copy {β : Type v} (f : Int32 → β → β) (init : β)
    (s : Int32Array.Slice) : s.foldr f init = s.copy.foldr f init := by
  rw [foldr_eq_foldr_toList_copy, foldr_toList]

private theorem Slice.foldrM_loop_eq_foldrM {β : Type v} {m : Type v → Type w} [Monad m]
    [LawfulMonad m] (f : Int32 → β → m β) (s : Int32Array.Slice) (i : Nat) (h : i ≤ s.size)
    (b : β) : Slice.foldrM.loop f s i h b = (s.copy.toList.take i).foldrM f b := by
  induction i generalizing b with
  | zero => simp [Slice.foldrM.loop]
  | succ i ih =>
    have hi : i < s.copy.toList.length := by simp; lia
    rw [Slice.foldrM.loop, List.take_add_one, List.getElem?_eq_getElem hi]
    simp [ih]

@[simp] public theorem Slice.foldrM_eq_foldrM_copy {β : Type v} {m : Type v → Type w} [Monad m]
    [LawfulMonad m] (f : Int32 → β → m β) (init : β) (s : Int32Array.Slice) :
    s.foldrM f init = s.copy.foldrM f init := by
  rw [Slice.foldrM, foldrM_loop_eq_foldrM, List.take_of_length_le (by simp), foldrM_toList]

@[simp] public theorem Slice.any_eq_any_copy (s : Int32Array.Slice) (p : Int32 → Bool) :
    s.any p = s.copy.any p := by
  rw [Slice.any, ← Std.Iter.any_toList, Std.Slice.toList_iter, toList_eq_toList_copy, any_toList]

@[simp] public theorem Slice.all_eq_all_copy (s : Int32Array.Slice) (p : Int32 → Bool) :
    s.all p = s.copy.all p := by
  rw [Slice.all, ← Std.Iter.all_toList, Std.Slice.toList_iter, toList_eq_toList_copy, all_toList]

@[simp] public theorem Slice.contains_eq_contains_copy (s : Int32Array.Slice) (v : Int32) :
    s.contains v = s.copy.contains v := by
  rw [Slice.contains, any_eq_any_copy]
  rfl

@[simp] public theorem Slice.find?_eq_find?_toList_copy (s : Int32Array.Slice)
    (p : Int32 → Bool) : s.find? p = s.copy.toList.find? p := by
  rw [Slice.find?, ← Std.Iter.find?_toList, Std.Slice.toList_iter, toList_eq_toList_copy]

private theorem foldl_count_eq (p : Int32 → Bool) (l : List Int32) (n : Nat) :
    l.foldl (fun n x => if p x then n + 1 else n) n = n + l.countP p := by
  induction l generalizing n with
  | nil => rfl
  | cons x l ih => by_cases hx : p x <;> simp [ih, hx] <;> lia

@[simp] public theorem Slice.count_eq_countP_toList_copy (s : Int32Array.Slice)
    (p : Int32 → Bool) : s.count p = s.copy.toList.countP p := by
  rw [Slice.count, ← Std.Iter.foldl_toList, Std.Slice.toList_iter, toList_eq_toList_copy,
    foldl_count_eq, Nat.zero_add]

private theorem Slice.findSomeRevM?_loop_eq (p : Int32 → Bool) (s : Int32Array.Slice) (i : Nat)
    (h : i ≤ s.size) :
    Slice.findSomeRevM?.loop (m := Id) s (fun x => pure (if p x then some x else none)) i h =
      (s.copy.toList.take i).reverse.find? p := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have hi : i < s.copy.toList.length := by simp; lia
    rw [Slice.findSomeRevM?.loop, List.take_add_one, List.getElem?_eq_getElem hi]
    by_cases hp : p s[i] <;> simp [ih, hp] <;> rfl

@[simp] public theorem Slice.findRev?_eq_find?_reverse_toList_copy (s : Int32Array.Slice)
    (p : Int32 → Bool) : s.findRev? p = s.copy.toList.reverse.find? p := by
  have := Slice.findSomeRevM?_loop_eq p s s.size (Nat.le_refl _)
  rw [List.take_of_length_le (by simp)] at this
  exact this

/-! ### Membership in slices -/

@[simp] public theorem Slice.mem_iff_mem_copy {x : Int32} {s : Int32Array.Slice} :
    x ∈ s ↔ x ∈ s.copy := Iff.rfl

public theorem Slice.mem_iff_getElem {x : Int32} {s : Int32Array.Slice} :
    x ∈ s ↔ ∃ (i : Nat) (h : i < s.size), s[i] = x := by
  rw [mem_iff_mem_copy, Int32Array.mem_iff_getElem]
  simp

public theorem Slice.getElem_mem {s : Int32Array.Slice} {i : Nat} (h : i < s.size) : s[i] ∈ s :=
  mem_iff_getElem.mpr ⟨i, h, rfl⟩

/-! ### Slice equality -/

@[simp] public theorem Slice.beq_eq_beq_copy (s t : Int32Array.Slice) :
    (s == t) = (s.copy == t.copy) := by
  rfl

/-! ## In-place folds -/

@[inline]
private unsafe def foldInPlaceImpl {β : Type v} (a : Int32Array) (start len : USize) (init : β)
    (f : (k : USize) → k.toNat < len.toNat → Int32 → β → Int32 × β)
    (_ : start.toNat + len.toNat ≤ a.size) : Int32Array × β :=
  loop (ensureExclusiveUnsafe a) 0 init
where
  @[specialize] loop (a : Int32Array) (k : USize) (b : β) : Int32Array × β :=
    if k < len then
      let p := f k lcProof (a.uget (start + k) lcProof) b
      loop (setUnsafe a (start + k) p.1) (k + 1) p.2
    else
      (a, b)

/-- The loop of `foldInPlace`, over `Nat` indices. -/
@[expose]
public def foldInPlace.loop {β : Type v} (len' : USize)
    (f : (k : USize) → k.toNat < len'.toNat → Int32 → β → Int32 × β)
    (start len : Nat) (a : Int32Array) (h : start + len ≤ a.size) (hlen : len ≤ len'.toNat)
    (k : Nat) (b : β) : Int32Array × β :=
  if hk : k < len then
    let p := f k.toUSize (by
      have := len'.toNat_lt_size
      rw [USize.toNat_ofNat_of_lt' (by lia)]
      lia) (a[start + k]'(by lia)) b
    foldInPlace.loop len' f start len (a.set (start + k) p.1 (by lia)) (by simpa using h) hlen
      (k + 1) p.2
  else
    (a, b)
termination_by len - k

/--
Replaces each element of `a` from index `start` for `len` elements while threading an
accumulator, in place when `a` is not shared: for each `k < len`, the element `x` at `start + k`
becomes the first component of `f k hk x b`, whose second component is the next accumulator.
Returns the new array and the last accumulator. The proof `hk : k.toNat < len.toNat` lets `f`
read other arrays with `uget`.

The point is the implementation: the result is that of a loop of `set`s, but `a` is made
exclusive once, before the loop, which then stores without checks, where each `uset` checks at
every write. `f` only sees the elements, never the array, which is what makes skipping the
checks safe.
-/
@[implemented_by foldInPlaceImpl, expose]
public def foldInPlace {β : Type v} (a : Int32Array) (start len : USize) (init : β)
    (f : (k : USize) → k.toNat < len.toNat → Int32 → β → Int32 × β)
    (h : start.toNat + len.toNat ≤ a.size) : Int32Array × β :=
  foldInPlace.loop len f start.toNat len.toNat a h (Nat.le_refl _) 0 init

public theorem size_foldInPlace_loop {β : Type v} (len' : USize)
    (f : (k : USize) → k.toNat < len'.toNat → Int32 → β → Int32 × β) (start len : Nat)
    (a : Int32Array) (h : start + len ≤ a.size) (hlen : len ≤ len'.toNat) (k : Nat) (b : β) :
    (foldInPlace.loop len' f start len a h hlen k b).1.size = a.size := by
  induction a, h, k, b using foldInPlace.loop.induct len' f start len hlen with
  | case1 a h k b hk p ih =>
    rw [foldInPlace.loop]
    simp only [hk, ↓reduceDIte]
    rw [ih]
    simp
  | case2 a h k b hk =>
    rw [foldInPlace.loop]
    simp [hk]

@[simp] public theorem size_foldInPlace {β : Type v} (a : Int32Array) (start len : USize)
    (init : β) (f : (k : USize) → k.toNat < len.toNat → Int32 → β → Int32 × β)
    (h : start.toNat + len.toNat ≤ a.size) :
    (a.foldInPlace start len init f h).1.size = a.size :=
  size_foldInPlace_loop len f _ _ a h _ 0 init

@[inline]
private unsafe def foldInPlaceThenImpl {β : Type v} {γ : Type w} (a : Int32Array)
    (start len : USize) (init : β)
    (f : (k : USize) → k.toNat < len.toNat → Int32 → β → Int32 × β)
    (g : Int32Array → β → γ) (_ : start.toNat + len.toNat ≤ a.size) : γ :=
  loop (ensureExclusiveUnsafe a) 0 init
where
  @[specialize] loop (a : Int32Array) (k : USize) (b : β) : γ :=
    if k < len then
      let p := f k lcProof (a.uget (start + k) lcProof) b
      loop (setUnsafe a (start + k) p.1) (k + 1) p.2
    else
      g a b

/--
`foldInPlace` followed by `g` on the new array and the last accumulator, which the loop calls
itself where `foldInPlace` returns them as a pair. The pair is a heap object, allocated once per
call, which shows when the fold runs over short ranges many times; when `g` consumes the
accumulator, for example by writing it into the array, no pair is allocated at all.
`foldInPlace` is the case `g := Prod.mk`.
-/
@[implemented_by foldInPlaceThenImpl, expose]
public def foldInPlaceThen {β : Type v} {γ : Type w} (a : Int32Array) (start len : USize)
    (init : β) (f : (k : USize) → k.toNat < len.toNat → Int32 → β → Int32 × β)
    (g : Int32Array → β → γ) (h : start.toNat + len.toNat ≤ a.size) : γ :=
  g (a.foldInPlace start len init f h).1 (a.foldInPlace start len init f h).2

@[simp] public theorem foldInPlaceThen_eq {β : Type v} {γ : Type w} (a : Int32Array)
    (start len : USize) (init : β)
    (f : (k : USize) → k.toNat < len.toNat → Int32 → β → Int32 × β)
    (g : Int32Array → β → γ) (h : start.toNat + len.toNat ≤ a.size) :
    a.foldInPlaceThen start len init f g h =
      g (a.foldInPlace start len init f h).1 (a.foldInPlace start len init f h).2 :=
  rfl

/-! ## Writing through slices -/

namespace Slice

/--
Replaces the element at index `i` of the slice, counted from the start of the slice, in the
underlying array. The array is updated in place when neither it nor the slice is shared, so a slice
taken from an array that is no longer used writes into that array. `s.array` gives back the whole
array afterwards.
-/
@[inline, expose]
public def set (s : Int32Array.Slice) (i : Nat) (v : Int32)
    (h : i < s.size := by get_elem_tactic) : Int32Array.Slice :=
  ⟨{ s.internalRepresentation with
      array := s.array.set (s.start + i) v
        (by have := s.stop_le_array_size; rw [size_eq] at h; lia)
      stop_le_array_size := by rw [size_set]; exact s.stop_le_array_size }⟩

@[simp] public theorem array_set (s : Int32Array.Slice) (i : Nat) (v : Int32) (h) :
    (s.set i v h).array =
      s.array.set (s.start + i) v (by have := s.stop_le_array_size; rw [size_eq] at h; lia) :=
  rfl

@[simp] public theorem start_set (s : Int32Array.Slice) (i : Nat) (v : Int32) (h) :
    (s.set i v h).start = s.start := rfl

@[simp] public theorem stop_set (s : Int32Array.Slice) (i : Nat) (v : Int32) (h) :
    (s.set i v h).stop = s.stop := rfl

@[simp] public theorem size_set (s : Int32Array.Slice) (i : Nat) (v : Int32) (h) :
    (s.set i v h).size = s.size := rfl

@[simp] public theorem getElem_set (s : Int32Array.Slice) (i : Nat) (v : Int32) (h) (j : Nat)
    (hj) :
    (s.set i v h)[j]'hj = if i = j then v else s[j]'(by rw [size_set] at hj; exact hj) := by
  simp only [getElem_eq, array_set, Int32Array.getElem_set, start_set]
  congr 1
  simp

@[simp] public theorem copy_set (s : Int32Array.Slice) (i : Nat) (v : Int32) (h) :
    (s.set i v h).copy = s.copy.set i v (by simpa using h) := by
  apply ext_getElem
  · simp
  · intro j _ _
    simp only [getElem_copy, getElem_set, Int32Array.getElem_set]

/--
Replaces the element at index `i` of the slice in the underlying array, like `set`. If `i` is out of
bounds, the slice is returned unmodified.
-/
@[inline, expose]
public def set! (s : Int32Array.Slice) (i : Nat) (v : Int32) : Int32Array.Slice :=
  if h : i < s.size then s.set i v h else s

public theorem set!_eq (s : Int32Array.Slice) (i : Nat) (v : Int32) :
    s.set! i v = if h : i < s.size then s.set i v h else s := rfl

@[simp] public theorem set!_eq_set (s : Int32Array.Slice) (i : Nat) (v : Int32)
    (h : i < s.size) : s.set! i v = s.set i v h := by
  simp [set!, h]

/--
Applies `f` to the element at index `i` of the slice, in place like `set`. If `i` is out of bounds,
the slice is returned unmodified.
-/
@[inline, expose]
public def modify (s : Int32Array.Slice) (i : Nat) (f : Int32 → Int32) : Int32Array.Slice :=
  if h : i < s.size then s.set i (f s[i]) h else s

public theorem modify_eq (s : Int32Array.Slice) (i : Nat) (f : Int32 → Int32) :
    s.modify i f = if h : i < s.size then s.set i (f s[i]) h else s := rfl

@[simp] public theorem start_modify (s : Int32Array.Slice) (i : Nat) (f : Int32 → Int32) :
    (s.modify i f).start = s.start := by
  unfold modify; split <;> rfl

@[simp] public theorem stop_modify (s : Int32Array.Slice) (i : Nat) (f : Int32 → Int32) :
    (s.modify i f).stop = s.stop := by
  unfold modify; split <;> rfl

@[simp] public theorem size_modify (s : Int32Array.Slice) (i : Nat) (f : Int32 → Int32) :
    (s.modify i f).size = s.size := by
  unfold modify; split <;> rfl

@[simp] public theorem getElem_modify (s : Int32Array.Slice) (i : Nat) (f : Int32 → Int32)
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
public def swap (s : Int32Array.Slice) (i j : Nat) (hi : i < s.size := by get_elem_tactic)
    (hj : j < s.size := by get_elem_tactic) : Int32Array.Slice :=
  -- Both reads come before the first write, so that `s` is no longer used when it is written.
  let x := s[i]
  let y := s[j]
  (s.set i y hi).set j x (by simpa using hj)

public theorem swap_eq (s : Int32Array.Slice) (i j : Nat) (hi hj) :
    s.swap i j hi hj = (s.set i s[j] hi).set j s[i] (by simpa using hj) := rfl

@[simp] public theorem start_swap (s : Int32Array.Slice) (i j : Nat) (hi hj) :
    (s.swap i j hi hj).start = s.start := rfl

@[simp] public theorem stop_swap (s : Int32Array.Slice) (i j : Nat) (hi hj) :
    (s.swap i j hi hj).stop = s.stop := rfl

@[simp] public theorem size_swap (s : Int32Array.Slice) (i j : Nat) (hi hj) :
    (s.swap i j hi hj).size = s.size := rfl

@[simp] public theorem getElem_swap (s : Int32Array.Slice) (i j : Nat) (hi hj) (k : Nat) (hk) :
    (s.swap i j hi hj)[k]'hk =
      if j = k then s[i] else if i = k then s[j] else s[k]'(by rw [size_swap] at hk; exact hk) := by
  rw [getElem_congr_coll (swap_eq ..), getElem_set, getElem_set]

/-- The loop of `reverse`: swaps the elements at `i` and `j`, then moves both towards the middle. -/
@[expose]
public def reverse.loop (s : Int32Array.Slice) (i j : Nat) (hj : j < s.size) :
    Int32Array.Slice :=
  if h : i < j then reverse.loop (s.swap i j (by lia)) (i + 1) (j - 1) (by simp; lia) else s
termination_by j - i

private unsafe def reverseImpl (s : Int32Array.Slice) : Int32Array.Slice :=
  match s with
  | ⟨⟨a, start, stop, h, _⟩⟩ =>
    if start < stop then
      ⟨⟨loop (ensureExclusiveUnsafe a) start.toUSize (stop.toUSize - 1), start, stop, h, lcProof⟩⟩
    else
      s
where
  loop (a : Int32Array) (i j : USize) : Int32Array :=
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
public def reverse (s : Int32Array.Slice) : Int32Array.Slice :=
  if h : 0 < s.size then reverse.loop s 0 (s.size - 1) (by lia) else s

private theorem reverse_loop_props (s : Int32Array.Slice) (i j : Nat) (hj : j < s.size) :
    (reverse.loop s i j hj).start = s.start ∧ (reverse.loop s i j hj).stop = s.stop := by
  fun_induction reverse.loop s i j hj with
  | case1 s i j hj h ih => simpa using ih
  | case2 => exact ⟨rfl, rfl⟩

@[simp] public theorem start_reverse (s : Int32Array.Slice) : s.reverse.start = s.start := by
  rw [reverse]; split
  · exact (reverse_loop_props ..).1
  · rfl

@[simp] public theorem stop_reverse (s : Int32Array.Slice) : s.reverse.stop = s.stop := by
  rw [reverse]; split
  · exact (reverse_loop_props ..).2
  · rfl

@[simp] public theorem size_reverse (s : Int32Array.Slice) : s.reverse.size = s.size := by
  rw [size_eq, size_eq, start_reverse, stop_reverse]

private theorem size_reverse_loop (s : Int32Array.Slice) (i j : Nat) (hj : j < s.size) :
    (reverse.loop s i j hj).size = s.size := by
  rw [size_eq, size_eq, (reverse_loop_props ..).1, (reverse_loop_props ..).2]

private theorem getElem_reverse_loop (s : Int32Array.Slice) (i j : Nat) (hj : j < s.size)
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

@[simp] public theorem getElem_reverse (s : Int32Array.Slice) (i : Nat) (h) :
    s.reverse[i]'h = s[s.size - 1 - i]'(by simp at h; lia) := by
  have h' : i < s.size := by simpa using h
  have hs : 0 < s.size := by lia
  simp only [reverse, hs, ↓reduceDIte]
  rw [getElem_reverse_loop _ _ _ _ (by lia) _ h']
  simp only [Nat.zero_le, true_and, Nat.zero_add]
  split <;> (try congr 1) <;> lia

@[simp] public theorem toList_copy_reverse (s : Int32Array.Slice) :
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
    (f : (k : USize) → k.toNat < n → Int32 → β → Int32 × β)
    (s : Int32Array.Slice) (hs : s.size = n) (k : Nat) (b : β) : Int32Array.Slice × β :=
  if hk : k < n then
    have hk' : k.toUSize.toNat < n := by
      rw [Nat.toUSize_eq, USize.toNat_ofNat']
      exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) hk
    let p := f k.toUSize hk' (s[k]'(by lia)) b
    foldlInPlace.loop n f (s.set k p.1 (by lia)) (by simpa using hs) (k + 1) p.2
  else
    (s, b)
termination_by n - k

@[inline]
private unsafe def foldlInPlaceImpl {β : Type v} (s : Int32Array.Slice) (init : β)
    (f : (k : USize) → k.toNat < s.size → Int32 → β → Int32 × β) : Int32Array.Slice × β :=
  match s with
  | ⟨⟨a, start, stop, h, _⟩⟩ =>
    Int32Array.foldInPlaceThenImpl a start.toUSize (stop - start).toUSize init
      (fun k _ => f k lcProof)
      (fun a b => (⟨⟨a, start, stop, h, lcProof⟩⟩, b)) lcProof

/--
Replaces each element of the slice while threading an accumulator, in place like `set`: for each
`k < s.size`, from `0` up, the element `x` at index `k` of the slice becomes the first component of
`f k hk x b`, whose second component is the next accumulator. Returns the new slice and the last
accumulator.

This is `Int32Array.foldInPlace` on the slice's range: the array is made exclusive once, before
the loop, which then stores without checks.
-/
@[implemented_by foldlInPlaceImpl, expose]
public def foldlInPlace {β : Type v} (s : Int32Array.Slice) (init : β)
    (f : (k : USize) → k.toNat < s.size → Int32 → β → Int32 × β) : Int32Array.Slice × β :=
  foldlInPlace.loop s.size f s rfl 0 init

private theorem foldlInPlace_loop_props {β : Type v} (n : Nat)
    (f : (k : USize) → k.toNat < n → Int32 → β → Int32 × β)
    (s : Int32Array.Slice) (hs : s.size = n) (k : Nat) (b : β) :
    (foldlInPlace.loop n f s hs k b).1.start = s.start ∧
      (foldlInPlace.loop n f s hs k b).1.stop = s.stop := by
  fun_induction foldlInPlace.loop n f s hs k b with
  | case1 s hs k b hk hk' p ih => simpa using ih
  | case2 => exact ⟨rfl, rfl⟩

@[simp] public theorem start_foldlInPlace {β : Type v} (s : Int32Array.Slice) (init : β)
    (f : (k : USize) → k.toNat < s.size → Int32 → β → Int32 × β) :
    (s.foldlInPlace init f).1.start = s.start :=
  (foldlInPlace_loop_props ..).1

@[simp] public theorem stop_foldlInPlace {β : Type v} (s : Int32Array.Slice) (init : β)
    (f : (k : USize) → k.toNat < s.size → Int32 → β → Int32 × β) :
    (s.foldlInPlace init f).1.stop = s.stop :=
  (foldlInPlace_loop_props ..).2

@[simp] public theorem size_foldlInPlace {β : Type v} (s : Int32Array.Slice) (init : β)
    (f : (k : USize) → k.toNat < s.size → Int32 → β → Int32 × β) :
    (s.foldlInPlace init f).1.size = s.size := by
  rw [size_eq, size_eq, start_foldlInPlace, stop_foldlInPlace]

/-- The loop of `foldrInPlace`, over `Nat` indices, from `k - 1` down to `0`. -/
@[expose]
public def foldrInPlace.loop {β : Type v} (n : Nat)
    (f : (k : USize) → k.toNat < n → Int32 → β → Int32 × β)
    (s : Int32Array.Slice) (hs : s.size = n) : (k : Nat) → k ≤ n → β → Int32Array.Slice × β
  | 0, _, b => (s, b)
  | k + 1, hk, b =>
    have hk' : k.toUSize.toNat < n := by
      rw [Nat.toUSize_eq, USize.toNat_ofNat']
      exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) hk
    let p := f k.toUSize hk' (s[k]'(by lia)) b
    foldrInPlace.loop n f (s.set k p.1 (by lia)) (by simpa using hs) k (by lia) p.2

@[specialize]
private unsafe def foldrInPlaceImpl.loop {β : Type v} {γ : Type w} (base : USize)
    (f : (k : USize) → Int32 → β → Int32 × β) (g : Int32Array → β → γ) (a : Int32Array)
    (k : USize) (b : β) : γ :=
  if 0 < k then
    let k := k - 1
    let p := f k (a.uget (base + k) lcProof) b
    foldrInPlaceImpl.loop base f g (setUnsafe a (base + k) p.1) k p.2
  else
    g a b

@[inline]
private unsafe def foldrInPlaceImpl {β : Type v} (s : Int32Array.Slice) (init : β)
    (f : (k : USize) → k.toNat < s.size → Int32 → β → Int32 × β) : Int32Array.Slice × β :=
  match s with
  | ⟨⟨a, start, stop, h, _⟩⟩ =>
    foldrInPlaceImpl.loop start.toUSize (fun k => f k lcProof)
      (fun a b => (⟨⟨a, start, stop, h, lcProof⟩⟩, b))
      (ensureExclusiveUnsafe a) (stop - start).toUSize init

/--
Replaces each element of the slice while threading an accumulator, like `foldlInPlace` but from
the last element to the first: for each `k < s.size`, from `s.size - 1` down to `0`, the element
`x` at index `k` of the slice becomes the first component of `f k hk x b`, whose second component
is the next accumulator. Returns the new slice and the last accumulator.

The array is made exclusive once, before the loop, which then stores without checks.
-/
@[implemented_by foldrInPlaceImpl, expose]
public def foldrInPlace {β : Type v} (s : Int32Array.Slice) (init : β)
    (f : (k : USize) → k.toNat < s.size → Int32 → β → Int32 × β) : Int32Array.Slice × β :=
  foldrInPlace.loop s.size f s rfl s.size (Nat.le_refl _) init

private theorem foldrInPlace_loop_props {β : Type v} (n : Nat)
    (f : (k : USize) → k.toNat < n → Int32 → β → Int32 × β)
    (s : Int32Array.Slice) (hs : s.size = n) (k : Nat) (hk : k ≤ n) (b : β) :
    (foldrInPlace.loop n f s hs k hk b).1.start = s.start ∧
      (foldrInPlace.loop n f s hs k hk b).1.stop = s.stop := by
  induction k generalizing s b with
  | zero => exact ⟨rfl, rfl⟩
  | succ k ih =>
    rw [foldrInPlace.loop]
    obtain ⟨h₁, h₂⟩ := ih ..
    exact ⟨h₁, h₂⟩

@[simp] public theorem start_foldrInPlace {β : Type v} (s : Int32Array.Slice) (init : β)
    (f : (k : USize) → k.toNat < s.size → Int32 → β → Int32 × β) :
    (s.foldrInPlace init f).1.start = s.start :=
  (foldrInPlace_loop_props ..).1

@[simp] public theorem stop_foldrInPlace {β : Type v} (s : Int32Array.Slice) (init : β)
    (f : (k : USize) → k.toNat < s.size → Int32 → β → Int32 × β) :
    (s.foldrInPlace init f).1.stop = s.stop :=
  (foldrInPlace_loop_props ..).2

@[simp] public theorem size_foldrInPlace {β : Type v} (s : Int32Array.Slice) (init : β)
    (f : (k : USize) → k.toNat < s.size → Int32 → β → Int32 × β) :
    (s.foldrInPlace init f).1.size = s.size := by
  rw [size_eq, size_eq, start_foldrInPlace, stop_foldrInPlace]

@[inline]
private unsafe def foldlInPlaceThenImpl {β : Type v} {γ : Type w} (s : Int32Array.Slice)
    (init : β) (f : (k : USize) → k.toNat < s.size → Int32 → β → Int32 × β)
    (g : Int32Array.Slice → β → γ) : γ :=
  match s with
  | ⟨⟨a, start, stop, h, _⟩⟩ =>
    Int32Array.foldInPlaceThenImpl a start.toUSize (stop - start).toUSize init
      (fun k _ => f k lcProof)
      (fun a b => g ⟨⟨a, start, stop, h, lcProof⟩⟩ b) lcProof

/--
`foldlInPlace` followed by `g` on the new slice and the last accumulator, which the loop calls
itself where `foldlInPlace` returns them as a pair, like `Int32Array.foldInPlaceThen`. When `g`
consumes the accumulator, for example by writing it into the slice, no pair is allocated.
`foldlInPlace` is the case `g := Prod.mk`.
-/
@[implemented_by foldlInPlaceThenImpl, expose]
public def foldlInPlaceThen {β : Type v} {γ : Type w} (s : Int32Array.Slice) (init : β)
    (f : (k : USize) → k.toNat < s.size → Int32 → β → Int32 × β)
    (g : Int32Array.Slice → β → γ) : γ :=
  g (s.foldlInPlace init f).1 (s.foldlInPlace init f).2

@[simp] public theorem foldlInPlaceThen_eq {β : Type v} {γ : Type w} (s : Int32Array.Slice)
    (init : β) (f : (k : USize) → k.toNat < s.size → Int32 → β → Int32 × β)
    (g : Int32Array.Slice → β → γ) :
    s.foldlInPlaceThen init f g = g (s.foldlInPlace init f).1 (s.foldlInPlace init f).2 :=
  rfl

@[inline]
private unsafe def foldrInPlaceThenImpl {β : Type v} {γ : Type w} (s : Int32Array.Slice)
    (init : β) (f : (k : USize) → k.toNat < s.size → Int32 → β → Int32 × β)
    (g : Int32Array.Slice → β → γ) : γ :=
  match s with
  | ⟨⟨a, start, stop, h, _⟩⟩ =>
    foldrInPlaceImpl.loop start.toUSize (fun k => f k lcProof)
      (fun a b => g ⟨⟨a, start, stop, h, lcProof⟩⟩ b)
      (ensureExclusiveUnsafe a) (stop - start).toUSize init

/--
`foldrInPlace` followed by `g` on the new slice and the last accumulator, which the loop calls
itself where `foldrInPlace` returns them as a pair. When `g` consumes the accumulator, no pair is
allocated. `foldrInPlace` is the case `g := Prod.mk`.
-/
@[implemented_by foldrInPlaceThenImpl, expose]
public def foldrInPlaceThen {β : Type v} {γ : Type w} (s : Int32Array.Slice) (init : β)
    (f : (k : USize) → k.toNat < s.size → Int32 → β → Int32 × β)
    (g : Int32Array.Slice → β → γ) : γ :=
  g (s.foldrInPlace init f).1 (s.foldrInPlace init f).2

@[simp] public theorem foldrInPlaceThen_eq {β : Type v} {γ : Type w} (s : Int32Array.Slice)
    (init : β) (f : (k : USize) → k.toNat < s.size → Int32 → β → Int32 × β)
    (g : Int32Array.Slice → β → γ) :
    s.foldrInPlaceThen init f g = g (s.foldrInPlace init f).1 (s.foldrInPlace init f).2 :=
  rfl

end Slice

/-! ### Decidable membership and slice hashing -/

public theorem contains_iff_mem {a : Int32Array} {x : Int32} :
    a.contains x = true ↔ x ∈ a := by
  simp only [contains, Array.contains_iff_mem, mem_data]

private def decMemImpl (x : Int32) (a : Int32Array) : Decidable (x ∈ a) :=
  decidable_of_iff _ contains_iff_mem

/--
Decides membership with `contains`. Logically it decides membership in `a.toList`, so that `decide`
can evaluate it.
-/
@[implemented_by decMemImpl, expose]
public def decMem (x : Int32) (a : Int32Array) : Decidable (x ∈ a) :=
  decidable_of_iff _ mem_toList

public instance (x : Int32) (a : Int32Array) : Decidable (x ∈ a) := decMem x a

@[simp] public theorem contains_eq_mem {a : Int32Array} {x : Int32} :
    a.contains x = decide (x ∈ a) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, contains_iff_mem]

public theorem Slice.contains_iff_mem {s : Int32Array.Slice} {x : Int32} :
    s.contains x = true ↔ x ∈ s := by
  simp

private def Slice.decMemImpl (x : Int32) (s : Int32Array.Slice) : Decidable (x ∈ s) :=
  decidable_of_iff _ Slice.contains_iff_mem

/--
Decides membership with `contains`. Logically it decides membership in `s.copy.toList`, so that
`decide` can evaluate it.
-/
@[implemented_by Slice.decMemImpl, expose]
public def Slice.decMem (x : Int32) (s : Int32Array.Slice) : Decidable (x ∈ s) :=
  decidable_of_iff (x ∈ s.copy.toList) (by simp)

public instance (x : Int32) (s : Int32Array.Slice) : Decidable (x ∈ s) := Slice.decMem x s

private def Slice.hashImpl (s : Int32Array.Slice) : UInt64 :=
  s.foldl (fun r x => mixHash r (Hashable.hash x)) 7

/-- The same hash as `s.copy`, so slices with the same elements have the same hash. -/
@[implemented_by Slice.hashImpl]
public def Slice.hash (s : Int32Array.Slice) : UInt64 :=
  Hashable.hash s.copy

public instance : Hashable Int32Array.Slice := ⟨Slice.hash⟩

public theorem Slice.hash_eq_hash_copy (s : Int32Array.Slice) :
    Hashable.hash s = Hashable.hash s.copy := by
  rfl

public theorem Slice.beq_iff_copy_eq {s t : Int32Array.Slice} :
    (s == t) = true ↔ s.copy = t.copy := by
  simp

public instance : EquivBEq Int32Array.Slice where
  rfl := by simp
  symm h := by simp_all
  trans h₁ h₂ := by simp_all

public instance : LawfulHashable Int32Array.Slice where
  hash_eq s t h := by
    rw [Slice.hash_eq_hash_copy, Slice.hash_eq_hash_copy, Slice.beq_iff_copy_eq.mp h]

/-! ### End of the part left out of the float types -/

end Int32Array

end ScalarArray

/-- The array with the elements of `l`. -/
@[inline, expose]
public def List.toInt32Array (l : List Int32) : ScalarArray.Int32Array :=
  ScalarArray.Int32Array.ofList l
