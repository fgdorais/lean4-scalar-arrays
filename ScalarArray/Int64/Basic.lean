/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ScalarArray.Internal
import all ScalarArray.Internal
public import Std.Data.Iterators
import Init.Data.Iterators.Lemmas.Basic
import Init.Data.Slice.InternalLemmas

/-!
# Arrays of `Int64`: basics

The type, its model, and the operations compiled to the runtime: reads, writes,
`push`, capacity, `append` and `copySlice`.
-/

namespace ScalarArray

universe u

/--
Arrays of `Int64` values, stored unboxed in a scalar array, 8 bytes per element.

The logical model is an `Array Int64`: `Int64Array.mk` and `Int64Array.toArray` convert between
the two. `cases` and `induction` split a `Int64Array` as `mk a`.
-/
-- At runtime a `Int64Array` is a `ScalarArray.Raw`, so every function that looks inside the
-- quotient must be `extern` or `implemented_by`. A quotient rather than a structure: the compiler
-- represents a one-field structure by its field, so code in any module could match on the
-- constructor and run `Array` code on a scalar array. A quotient has no constructor to match on and
-- the compiler gives it no layout; only `Quot.lift` and `Quot.rec` can see the `Array`.
@[expose] public def Int64Array : Type := Quot fun _ _ : Array Int64 => False

namespace Int64Array

-- `noinline` on `mk` and `toArray`: the `implemented_by` attribute of `mk` and the `csimp` theorem
-- of `toArray` come later, and the compiler would otherwise inline their bodies, which treat the
-- scalar array as an `Array`.

/-- The `Int64Array` whose elements are `a`. -/
@[noinline, expose]
public def mk (a : Array Int64) : Int64Array := Quot.mk _ a

/-- The elements of `a` as an `Array Int64`. -/
@[noinline, expose]
public def toArray (a : @& Int64Array) : Array Int64 :=
  Quot.lift id (fun _ _ h => h.elim) a

@[simp] public theorem toArray_mk (a : Array Int64) : (mk a).toArray = a := rfl

@[simp] public theorem mk_toArray (a : Int64Array) : mk a.toArray = a :=
  Quot.ind (β := fun a : Int64Array => mk a.toArray = a) (fun _ => rfl) a

/-- The number of elements of `a`. -/
-- `lean_byte_array_size` reads the size of any scalar array, whatever its element size: in
-- `lean.h` it is `lean_box(lean_sarray_size(a))`. Caution: by its name it is meant for `ByteArray`,
-- so recheck it when the toolchain changes. The tests check `size` for every element size.
@[extern "lean_byte_array_size", tagged_return, expose]
public def size (a : @& Int64Array) : Nat :=
  a.toArray.size

/-- For internal use only. -/
@[inline]
public unsafe def usizeImpl (a : @& Int64Array) : USize := (unsafeCast a : Raw).size

/--
The size of `a` as a `USize`. Since `USize` can address all memory, no array has more elements than
`USize` can count.
-/
@[implemented_by usizeImpl, simp, expose]
public def usize (a : @& Int64Array) : USize :=
  a.size.toUSize

/-- `a.usize` is at most the size, so it bounds the indices of loops that stop at `a.usize`. -/
public theorem toNat_usize_le (a : Int64Array) : a.usize.toNat ≤ a.size := by
  simp [Nat.mod_le]

/-- The element at the `USize` index `i`. It compiles to an inline load. -/
@[extern c inline "((uint64_t*)lean_sarray_cptr(#1))[#2]", expose]
public def uget (a : @& Int64Array) (i : USize) (h : i.toNat < a.size := by get_elem_tactic) :
    Int64 :=
  a.toArray.uget i h

/-- The element at index `i`. -/
@[expose]
public def get (a : @& Int64Array) (i : @& Nat) (h : i < a.size := by get_elem_tactic) :
    Int64 :=
  a.toArray[i]

/-- For internal use only. -/
-- Public, like `mkImpl`, `usetImpl`, `setImpl` and `pushImpl` below: a private
-- `implemented_by` target attached with a separate `attribute` command is not visible to other
-- modules, so code there that uses `get`, `mk`, `toArray`, `uset` or `set` would fail to compile.
@[inline]
public unsafe def getImpl : type_of% @get :=
  fun a i _ => a.uget i.toUSize lcProof

attribute [implemented_by getImpl] get

/--
Stores `v` at index `i` in place. Only valid when `a` is exclusive and `i` is in bounds. Public only
so that `uset` can be inlined into code in other modules.
-/
@[never_extract, extern c inline "#1;\n((uint64_t*)lean_sarray_cptr(#1))[#2] = #3"]
public unsafe def setUnsafe (a : Int64Array) (i : USize) (v : Int64) : Int64Array :=
  mk <| a.toArray.uset i v lcProof

/-- For internal use only. -/
@[inline, never_extract]
public unsafe def ensureExclusiveImpl (a : Int64Array) : Int64Array :=
  unsafeCast (unsafeCast a : Raw).ensureExclusive

/--
Returns `a` itself when it is not shared, and a copy otherwise. Logically this is the identity.
It is useful before a run of in-place writes, so that only the first one can copy.
-/
-- `never_extract`: once `uset` or `push` is inlined, `c.ensureExclusive` on a closed array `c`
-- would otherwise be hoisted into a shared constant, which the following in-place write would then
-- modify.
@[never_extract, implemented_by ensureExclusiveImpl, expose]
public def ensureExclusive (a : Int64Array) : Int64Array := a

private def toUSizeChecked (n : Nat) : USize :=
  if n < USize.size >>> 1 then n.toUSize else panic! "out of memory"

/--
`ensureCapacity` and `ensureExclusiveWithCapacity` when `a` lacks room for `n` elements: copies `a`
with room for exactly `max n a.size` elements. Out of line so that inlined call sites stay small.
Public only so that those functions can be inlined into code in other modules.
-/
-- `never_extract`: on a closed array, a hoisted copy would be a shared constant, so the writes that
-- follow would copy it again.
@[never_extract]
public unsafe def ensureCapacityGrowUnsafe (a : Int64Array) (n : Nat) : Int64Array :=
  let s : Raw := unsafeCast a
  unsafeCast (s.copyWithCapacity (toUSizeChecked (max n s.size.toNat)) lcProof)

/-- For internal use only. -/
-- Inline, and made of public inline externs, so that the common path compiles to an inline capacity
-- check in other modules.
@[inline]
public unsafe def ensureCapacityImpl (a : Int64Array) (n : Nat) : Int64Array :=
  if n ≤ (unsafeCast a : Raw).capacity.toNat then a else ensureCapacityGrowUnsafe a n

/--
Returns `a` itself when it has room for `n` elements, and otherwise a copy with room for exactly
`max n a.size` elements. Logically this is the identity. Unlike `ensureExclusiveWithCapacity`, it
does not copy `a` just because it is shared.
-/
@[never_extract, implemented_by ensureCapacityImpl, expose]
public def ensureCapacity (a : Int64Array) (n : Nat) : Int64Array := a

/-- For internal use only. -/
-- Inline, like `ensureCapacityImpl`: one capacity check, then one exclusivity check. The copy made
-- when `a` lacks room is exclusive, so `a` is copied at most once.
@[inline]
public unsafe def ensureExclusiveWithCapacityImpl (a : Int64Array) (n : Nat) : Int64Array :=
  if n ≤ (unsafeCast a : Raw).capacity.toNat then a.ensureExclusive
  else ensureCapacityGrowUnsafe a n

/--
Returns `a` itself when it is not shared and has room for `n` elements, and otherwise a single copy
with room for exactly `max n a.size` elements. Logically this is the identity. It is useful before a
run of in-place writes and pushes, so that none of them copies.
-/
@[never_extract, implemented_by ensureExclusiveWithCapacityImpl, expose]
public def ensureExclusiveWithCapacity (a : Int64Array) (n : Nat) : Int64Array := a

/-- A new array of size `size` with room for `capacity` elements. Requires `size ≤ capacity`. -/
private unsafe def allocUnsafe (size capacity : USize) : Int64Array :=
  unsafeCast <| Raw.allocate 8 size capacity lcProof

private unsafe def mkWithCapacityImpl (a : Array Int64) (capacity : Nat := a.size) :
    Int64Array :=
  let cap := toUSizeChecked capacity
  let sz := toUSizeChecked a.size
  let r := allocUnsafe sz (max sz cap)
  loop sz r 0
where
  loop (sz : USize) (r : Int64Array) (i : USize) : Int64Array :=
    if i < sz then loop sz (setUnsafe r i (a.uget i lcProof)) (i + 1) else r

/-- For internal use only. -/
public unsafe def mkImpl (a : Array Int64) : Int64Array :=
  mkWithCapacityImpl a a.size

attribute [implemented_by mkImpl] Int64Array.mk

private theorem size_toArray' (a : Int64Array) : a.toArray.size = a.size := rfl

/-- `n.toUSize` is `n` for every `n` up to the size of an array with fewer than `USize.size`
elements. -/
private theorem toNat_toUSize_of_le {a : Int64Array} (hsize : a.size < USize.size) {n : Nat}
    (h : n ≤ a.size) : n.toUSize.toNat = n := by
  simp only [Nat.toUSize_eq, USize.toNat_ofNat']
  exact Nat.mod_eq_of_lt (by lia)

/-- For internal use only. -/
-- `toArrayImpl` and the other `Impl` functions below are proved equal to their specifications by
-- `csimp` theorems, which make the compiler call them instead. A `csimp` theorem must be public,
-- and so must the functions it names. The loops index with `USize`, so the proofs need
-- `a.size < USize.size`: the `else` branches are never taken, since no array in memory has
-- `USize.size` elements. Elsewhere they call a `Slow` function that is neither inlined nor
-- specialized, so that the dead branch stays a single call; here the compiled body of `toArray`
-- would treat the scalar array as an `Array`, so the `else` branch reads the elements with `get`
-- instead.
public def toArrayImpl (a : @& Int64Array) : Array Int64 :=
  if a.size < USize.size then
    loop a.usize a.toNat_usize_le 0 (Array.replicate a.size default) Array.size_replicate
  else Array.ofFn fun i : Fin a.size => a.get i i.2
where
  loop (sz : USize) (hsz : sz.toNat ≤ a.size) (i : USize) (r : Array Int64)
      (hr : r.size = a.size) : Array Int64 :=
    if h : i < sz then
      have := toNat_lt_of_lt h hsz
      loop sz hsz (i + 1) (r.uset i (a.uget i) (hr ▸ this)) (by simp [hr])
    else r
  termination_by sz.toNat - i.toNat
  decreasing_by exact sub_toNat_add_one_lt h

private theorem toArrayImpl_loop (a : Int64Array) (sz : USize) (hsz : sz.toNat ≤ a.size)
    (hsz' : a.size ≤ sz.toNat) (i : USize) (r : Array Int64) (hr : r.size = a.size)
    (hi : i.toNat ≤ sz.toNat)
    (h : ∀ (k : Nat) (hk : k < i.toNat), r[k]'(by lia) = a.toArray[k]'(by rw [size_toArray']; lia)) :
    toArrayImpl.loop a sz hsz i r hr = a.toArray := by
  fun_induction toArrayImpl.loop a sz hsz i r hr with
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

@[csimp] public theorem toArray_eq_toArrayImpl : @toArray = @toArrayImpl := by
  funext a
  simp only [toArrayImpl]
  split
  · rename_i hsize
    have := toNat_toUSize_of_le hsize (Nat.le_refl _)
    exact (toArrayImpl_loop a _ _ (by simp only [usize]; lia) 0 _ _ (by simp) (by simp)).symm
  · exact (Array.ofFn_getElem (xs := a.toArray)).symm

-- After the `implemented_by` attribute of `mk` and the `csimp` theorem of `toArray`, so that the
-- compiled code uses them.
/-- Case analysis on a `Int64Array` as `mk a`. It is the default for `cases` and `induction`. -/
@[elab_as_elim, cases_eliminator, induction_eliminator]
public def casesMk {motive : Int64Array → Sort u} (mk : (a : Array Int64) → motive (mk a))
    (a : Int64Array) : motive a :=
  mk_toArray a ▸ mk a.toArray

private unsafe def emptyWithCapacityImpl (capacity : Nat) : Int64Array :=
  mkWithCapacityImpl #[] capacity

/-- An empty array with room for `capacity` elements before reallocating. -/
@[implemented_by emptyWithCapacityImpl, expose]
public def emptyWithCapacity (capacity : Nat) : Int64Array :=
  mk #[]

/-- The empty array. -/
@[expose] public def empty : Int64Array := emptyWithCapacity 0

public instance : EmptyCollection Int64Array := ⟨empty⟩

public instance : Inhabited Int64Array := ⟨empty⟩

/--
Replaces the element at index `i`, in place when `a` is not shared. It compiles to inline C: one
check that `a` is exclusive, copying it if not, and one store.
-/
@[expose]
public def uset (a : Int64Array) (i : USize) (v : Int64)
    (h : i.toNat < a.size := by get_elem_tactic) : Int64Array :=
  mk (a.toArray.uset i v h)

/-- For internal use only. -/
-- Inline, and made of public inline externs, so that it compiles to inline C in other modules.
@[inline]
public unsafe def usetImpl : type_of% @uset :=
  fun a i v _ => setUnsafe a.ensureExclusive i v

attribute [implemented_by usetImpl] uset

/-- Replaces the element at index `i`, in place when `a` is not shared, like `uset`. -/
@[expose]
public def set (a : Int64Array) (i : Nat) (v : Int64) (h : i < a.size := by get_elem_tactic) :
    Int64Array :=
  mk (a.toArray.set i v h)

/-- For internal use only. -/
@[inline]
public unsafe def setImpl : type_of% @set :=
  fun a i v _ => a.uset i.toUSize v lcProof

attribute [implemented_by setImpl] set

/-- The element at index `i`. Panics if `i` is out of bounds, and then returns `default`. -/
@[expose]
public def get! (a : @& Int64Array) (i : @& Nat) : Int64 :=
  if h : i < a.size then a.get i h else panic! "index out of bounds"

/-- The element at index `i`, or `v₀` if `i` is out of bounds. -/
@[expose]
public def getD (a : @& Int64Array) (i : @& Nat) (v₀ : Int64) : Int64 :=
  if h : i < a.size then a.get i h else v₀

/-- Replaces the element at index `i`. If `i` is out of bounds, the array is returned unmodified. -/
@[expose]
public def set! (a : Int64Array) (i : Nat) (v : Int64) : Int64Array :=
  if h : i < a.size then a.set i v h else a

public instance : GetElem Int64Array Nat Int64 fun a i => i < a.size where
  getElem a i h := a.get i h

public instance : GetElem Int64Array USize Int64 fun a i => i.toNat < a.size where
  getElem a i h := a.uget i h

/--
`push` when `a` is full: copies `a` with capacity `2 * capacity + 1`, then appends `v`. Out of
line so that inlined `push` call sites stay small. Public only so that `push` can be inlined into
code in other modules.
-/
public unsafe def pushGrowUnsafe (a : Int64Array) (v : Int64) : Int64Array :=
  let s : Raw := unsafeCast a
  let cap := s.capacity
  if cap < cap + cap + 1 then
    let s := s.copyWithCapacity (cap + cap + 1) lcProof
    let i := s.size
    setUnsafe (unsafeCast (s.resizeUnsafe (i + 1) lcProof lcProof)) i v
  else
    panic! "out of memory"

/-- For internal use only. -/
-- Inline, and made of public inline externs, so that the common path compiles to inline C in other
-- modules: one capacity check, one exclusivity check, a size bump and one store.
@[inline]
public unsafe def pushImpl (a : Int64Array) (v : Int64) : Int64Array :=
  if a.usize < (unsafeCast a : Raw).capacity then
    let a := a.ensureExclusive
    let i := a.usize
    let s : Raw := unsafeCast a
    setUnsafe (unsafeCast (s.resizeUnsafe (i + 1) lcProof lcProof)) i v
  else
    pushGrowUnsafe a v

/--
Appends `v` to `a`, in place when `a` is not shared and has room. A full array grows to capacity
`2 * capacity + 1`, so repeated pushes take amortized constant time.
-/
@[implemented_by pushImpl, expose]
public def push (a : Int64Array) (v : Int64) : Int64Array :=
  mk (a.toArray.push v)

/--
Copies the `n` elements of `src` starting at index `srcOff` into `dest` starting at index `destOff`,
in place, and grows the size of `dest` to `destOff + n` if it is smaller. Only valid when `dest` is
exclusive and has capacity for `destOff + n` elements, and when `destOff ≤ dest.size` and
`srcOff + n ≤ src.size`. The ranges may overlap.
-/
@[inline]
private unsafe def copySliceUnsafe (dest : Int64Array) (src : @& Int64Array)
    (srcOff destOff n : USize) : Int64Array :=
  let src : Raw := unsafeCast src
  let esz := src.elemSize.toUSize
  let d := (unsafeCast dest : Raw).memmoveUnsafe src (srcOff * esz) (destOff * esz) (n * esz)
  unsafeCast (d.resizeUnsafe (max d.size (destOff + n)) lcProof lcProof)

private unsafe def appendImpl (a b : Int64Array) : Int64Array :=
  let s : Raw := unsafeCast a
  let m := (unsafeCast b : Raw).size
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
public def append (a b : Int64Array) : Int64Array :=
  mk (a.toArray ++ b.toArray)

public instance : Append Int64Array := ⟨append⟩

private unsafe def copySliceImpl (src : @& Int64Array) (srcOff : Nat) (dest : Int64Array)
    (destOff len : Nat) (exact : Bool := true) : Int64Array :=
  let srcOff := min srcOff src.size
  let n := min len (src.size - srcOff)
  let destOff := min destOff dest.size
  let newSize := max dest.size (destOff + n)
  let s : Raw := unsafeCast dest
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
public def copySlice (src : @& Int64Array) (srcOff : Nat) (dest : Int64Array)
    (destOff len : Nat) (exact : Bool := true) : Int64Array :=
  mk (dest.toArray.extract 0 destOff ++ src.toArray.extract srcOff (srcOff + len) ++
    dest.toArray.extract (destOff + min len (src.toArray.size - srcOff)) dest.toArray.size)

end Int64Array

end ScalarArray
