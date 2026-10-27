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
# Arrays of `UInt16`: basics

The type, its model, and the operations compiled to the runtime: reads, writes,
`push`, capacity, `append` and `copySlice`.
-/

namespace ScalarArray

universe u

/--
Arrays of `UInt16` values, stored unboxed in a scalar array, 2 bytes per element.

The logical model is an `Array UInt16`: `UInt16Array.mk` and `UInt16Array.toArray` convert between
the two. `cases` and `induction` split a `UInt16Array` as `mk a`.
-/
-- At runtime a `UInt16Array` is a `ScalarArray.Raw`, so every function that looks inside the
-- quotient must be `extern` or `implemented_by`. A quotient rather than a structure: the compiler
-- represents a one-field structure by its field, so code in any module could match on the
-- constructor and run `Array` code on a scalar array. A quotient has no constructor to match on and
-- the compiler gives it no layout; only `Quot.lift` and `Quot.rec` can see the `Array`.
@[expose] public def UInt16Array : Type := Quot fun _ _ : Array UInt16 => False

namespace UInt16Array

-- `noinline` on `mk` and `toArray`: the `implemented_by` attribute of `mk` and the `csimp` theorem
-- of `toArray` come later, and the compiler would otherwise inline their bodies, which treat the
-- scalar array as an `Array`.

/-- The `UInt16Array` whose elements are `a`. -/
@[noinline, expose]
public def mk (a : Array UInt16) : UInt16Array := Quot.mk _ a

/-- The elements of `a` as an `Array UInt16`. -/
@[noinline, expose]
public def toArray (a : @& UInt16Array) : Array UInt16 :=
  Quot.lift id (fun _ _ h => h.elim) a

@[simp] public theorem toArray_mk (a : Array UInt16) : (mk a).toArray = a := rfl

@[simp] public theorem mk_toArray (a : UInt16Array) : mk a.toArray = a :=
  Quot.ind (β := fun a : UInt16Array => mk a.toArray = a) (fun _ => rfl) a

-- `lean_byte_array_size` reads the size of any scalar array, whatever its element size: in
-- `lean.h` it is `lean_box(lean_sarray_size(a))`. Caution: by its name it is meant for `ByteArray`,
-- so recheck it when the toolchain changes. The tests check `size` for every element size.
@[extern "lean_byte_array_size", tagged_return, expose]
public def size (a : @& UInt16Array) : Nat :=
  a.toArray.size

/--
The size of `a` as a `USize`. Since `USize` can address all memory, no array has more elements than
`USize` can count.
-/
@[inline]
public unsafe def usizeImpl (a : @& UInt16Array) : USize := (unsafeCast a : Raw).size

@[implemented_by usizeImpl, simp, expose]
public def usize (a : @& UInt16Array) : USize :=
  a.size.toUSize

/-- `a.usize` is at most the size, so it bounds the indices of loops that stop at `a.usize`. -/
public theorem toNat_usize_le (a : UInt16Array) : a.usize.toNat ≤ a.size := by
  simp [Nat.mod_le]

@[extern c inline "((uint16_t*)lean_sarray_cptr(#1))[#2]", expose]
public def uget (a : @& UInt16Array) (i : USize) (h : i.toNat < a.size := by get_elem_tactic) :
    UInt16 :=
  a.toArray.uget i h

@[expose]
public def get (a : @& UInt16Array) (i : @& Nat) (h : i < a.size := by get_elem_tactic) :
    UInt16 :=
  a.toArray[i]

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
@[never_extract, extern c inline "#1;\n((uint16_t*)lean_sarray_cptr(#1))[#2] = #3"]
public unsafe def setUnsafe (a : UInt16Array) (i : USize) (v : UInt16) : UInt16Array :=
  mk <| a.toArray.uset i v lcProof

@[inline, never_extract]
public unsafe def ensureExclusiveImpl (a : UInt16Array) : UInt16Array :=
  unsafeCast (unsafeCast a : Raw).ensureExclusive

/--
Returns `a` itself when it is not shared, and a copy otherwise. Logically this is the identity.
It is useful before a run of in-place writes, so that only the first one can copy.
-/
-- `never_extract`: once `uset` or `push` is inlined, `c.ensureExclusive` on a closed array `c`
-- would otherwise be hoisted into a shared constant, which the following in-place write would then
-- modify.
@[never_extract, implemented_by ensureExclusiveImpl, expose]
public def ensureExclusive (a : UInt16Array) : UInt16Array := a

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
public unsafe def ensureCapacityGrowUnsafe (a : UInt16Array) (n : Nat) : UInt16Array :=
  let s : Raw := unsafeCast a
  unsafeCast (s.copyWithCapacity (toUSizeChecked (max n s.size.toNat)) lcProof)

-- Inline, and made of public inline externs, so that the common path compiles to an inline capacity
-- check in other modules.
@[inline]
public unsafe def ensureCapacityImpl (a : UInt16Array) (n : Nat) : UInt16Array :=
  if n ≤ (unsafeCast a : Raw).capacity.toNat then a else ensureCapacityGrowUnsafe a n

/--
Returns `a` itself when it has room for `n` elements, and otherwise a copy with room for exactly
`max n a.size` elements. Logically this is the identity. Unlike `ensureExclusiveWithCapacity`, it
does not copy `a` just because it is shared.
-/
@[never_extract, implemented_by ensureCapacityImpl, expose]
public def ensureCapacity (a : UInt16Array) (n : Nat) : UInt16Array := a

-- Inline, like `ensureCapacityImpl`: one capacity check, then one exclusivity check. The copy made
-- when `a` lacks room is exclusive, so `a` is copied at most once.
@[inline]
public unsafe def ensureExclusiveWithCapacityImpl (a : UInt16Array) (n : Nat) : UInt16Array :=
  if n ≤ (unsafeCast a : Raw).capacity.toNat then a.ensureExclusive
  else ensureCapacityGrowUnsafe a n

/--
Returns `a` itself when it is not shared and has room for `n` elements, and otherwise a single copy
with room for exactly `max n a.size` elements. Logically this is the identity. It is useful before a
run of in-place writes and pushes, so that none of them copies.
-/
@[never_extract, implemented_by ensureExclusiveWithCapacityImpl, expose]
public def ensureExclusiveWithCapacity (a : UInt16Array) (n : Nat) : UInt16Array := a

/-- A new array of size `size` with room for `capacity` elements. Requires `size ≤ capacity`. -/
private unsafe def allocUnsafe (size capacity : USize) : UInt16Array :=
  unsafeCast <| Raw.allocate 2 size capacity lcProof

private unsafe def mkWithCapacityImpl (a : Array UInt16) (capacity : Nat := a.size) :
    UInt16Array :=
  let cap := toUSizeChecked capacity
  let sz := toUSizeChecked a.size
  let r := allocUnsafe sz (max sz cap)
  loop sz r 0
where
  loop (sz : USize) (r : UInt16Array) (i : USize) : UInt16Array :=
    if i < sz then loop sz (setUnsafe r i (a.uget i lcProof)) (i + 1) else r

public unsafe def mkImpl (a : Array UInt16) : UInt16Array :=
  mkWithCapacityImpl a a.size

attribute [implemented_by mkImpl] UInt16Array.mk

private theorem size_toArray' (a : UInt16Array) : a.toArray.size = a.size := rfl

/-- `n.toUSize` is `n` for every `n` up to the size of an array with fewer than `USize.size`
elements. -/
private theorem toNat_toUSize_of_le {a : UInt16Array} (hsize : a.size < USize.size) {n : Nat}
    (h : n ≤ a.size) : n.toUSize.toNat = n := by
  simp only [Nat.toUSize_eq, USize.toNat_ofNat']
  exact Nat.mod_eq_of_lt (by lia)

-- `toArrayImpl` and the other `Impl` functions below are proved equal to their specifications by
-- `csimp` theorems, which make the compiler call them instead. A `csimp` theorem must be public,
-- and so must the functions it names. The loops index with `USize`, so the proofs need
-- `a.size < USize.size`: the `else` branches are never taken, since no array in memory has
-- `USize.size` elements. Elsewhere they call a `Slow` function that is neither inlined nor
-- specialized, so that the dead branch stays a single call; here the compiled body of `toArray`
-- would treat the scalar array as an `Array`, so the `else` branch reads the elements with `get`
-- instead.
public def toArrayImpl (a : @& UInt16Array) : Array UInt16 :=
  if a.size < USize.size then
    loop a.usize a.toNat_usize_le 0 (Array.replicate a.size default) Array.size_replicate
  else Array.ofFn fun i : Fin a.size => a.get i i.2
where
  loop (sz : USize) (hsz : sz.toNat ≤ a.size) (i : USize) (r : Array UInt16)
      (hr : r.size = a.size) : Array UInt16 :=
    if h : i < sz then
      have := toNat_lt_of_lt h hsz
      loop sz hsz (i + 1) (r.uset i (a.uget i) (hr ▸ this)) (by simp [hr])
    else r
  termination_by sz.toNat - i.toNat
  decreasing_by exact sub_toNat_add_one_lt h

private theorem toArrayImpl_loop (a : UInt16Array) (sz : USize) (hsz : sz.toNat ≤ a.size)
    (hsz' : a.size ≤ sz.toNat) (i : USize) (r : Array UInt16) (hr : r.size = a.size)
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
/-- Case analysis on a `UInt16Array` as `mk a`. It is the default for `cases` and `induction`. -/
@[elab_as_elim, cases_eliminator, induction_eliminator]
public def casesMk {motive : UInt16Array → Sort u} (mk : (a : Array UInt16) → motive (mk a))
    (a : UInt16Array) : motive a :=
  mk_toArray a ▸ mk a.toArray

private unsafe def emptyWithCapacityImpl (capacity : Nat) : UInt16Array :=
  mkWithCapacityImpl #[] capacity

/-- An empty array with room for `capacity` elements before reallocating. -/
@[implemented_by emptyWithCapacityImpl, expose]
public def emptyWithCapacity (capacity : Nat) : UInt16Array :=
  mk #[]

@[expose] public def empty : UInt16Array := emptyWithCapacity 0

public instance : EmptyCollection UInt16Array := ⟨empty⟩

public instance : Inhabited UInt16Array := ⟨empty⟩

/--
Replaces the element at index `i`, in place when `a` is not shared. It compiles to inline C: one
check that `a` is exclusive, copying it if not, and one store.
-/
@[expose]
public def uset (a : UInt16Array) (i : USize) (v : UInt16)
    (h : i.toNat < a.size := by get_elem_tactic) : UInt16Array :=
  mk (a.toArray.uset i v h)

-- Inline, and made of public inline externs, so that it compiles to inline C in other modules.
@[inline]
public unsafe def usetImpl : type_of% @uset :=
  fun a i v _ => setUnsafe a.ensureExclusive i v

attribute [implemented_by usetImpl] uset

@[expose]
public def set (a : UInt16Array) (i : Nat) (v : UInt16) (h : i < a.size := by get_elem_tactic) :
    UInt16Array :=
  mk (a.toArray.set i v h)

@[inline]
public unsafe def setImpl : type_of% @set :=
  fun a i v _ => a.uset i.toUSize v lcProof

attribute [implemented_by setImpl] set

@[expose]
public def get! (a : @& UInt16Array) (i : @& Nat) : UInt16 :=
  if h : i < a.size then a.get i h else panic! "index out of bounds"

@[expose]
public def getD (a : @& UInt16Array) (i : @& Nat) (v₀ : UInt16) : UInt16 :=
  if h : i < a.size then a.get i h else v₀

/-- Replaces the element at index `i`. If `i` is out of bounds, the array is returned unmodified. -/
@[expose]
public def set! (a : UInt16Array) (i : Nat) (v : UInt16) : UInt16Array :=
  if h : i < a.size then a.set i v h else a

public instance : GetElem UInt16Array Nat UInt16 fun a i => i < a.size where
  getElem a i h := a.get i h

public instance : GetElem UInt16Array USize UInt16 fun a i => i.toNat < a.size where
  getElem a i h := a.uget i h

/--
`push` when `a` is full: copies `a` with capacity `2 * capacity + 1`, then appends `v`. Out of
line so that inlined `push` call sites stay small. Public only so that `push` can be inlined into
code in other modules.
-/
public unsafe def pushGrowUnsafe (a : UInt16Array) (v : UInt16) : UInt16Array :=
  let s : Raw := unsafeCast a
  let cap := s.capacity
  if cap < cap + cap + 1 then
    let s := s.copyWithCapacity (cap + cap + 1) lcProof
    let i := s.size
    setUnsafe (unsafeCast (s.resizeUnsafe (i + 1) lcProof lcProof)) i v
  else
    panic! "out of memory"

-- Inline, and made of public inline externs, so that the common path compiles to inline C in other
-- modules: one capacity check, one exclusivity check, a size bump and one store.
@[inline]
public unsafe def pushImpl (a : UInt16Array) (v : UInt16) : UInt16Array :=
  if a.usize < (unsafeCast a : Raw).capacity then
    let a := a.ensureExclusive
    let i := a.usize
    let s : Raw := unsafeCast a
    setUnsafe (unsafeCast (s.resizeUnsafe (i + 1) lcProof lcProof)) i v
  else
    pushGrowUnsafe a v

@[implemented_by pushImpl, expose]
public def push (a : UInt16Array) (v : UInt16) : UInt16Array :=
  mk (a.toArray.push v)

/--
Copies the `n` elements of `src` starting at index `srcOff` into `dest` starting at index `destOff`,
in place, and grows the size of `dest` to `destOff + n` if it is smaller. Only valid when `dest` is
exclusive, has capacity for `destOff + n` elements, and is not the same object as `src`, and when
`destOff ≤ dest.size` and `srcOff + n ≤ src.size`.
-/
@[inline]
private unsafe def copySliceUnsafe (dest : UInt16Array) (src : @& UInt16Array)
    (srcOff destOff n : USize) : UInt16Array :=
  let src : Raw := unsafeCast src
  let esz := src.elemSize.toUSize
  let d := (unsafeCast dest : Raw).memmoveUnsafe src (srcOff * esz) (destOff * esz) (n * esz)
  unsafeCast (d.resizeUnsafe (max d.size (destOff + n)) lcProof lcProof)

private unsafe def appendImpl (a b : UInt16Array) : UInt16Array :=
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
public def append (a b : UInt16Array) : UInt16Array :=
  mk (a.toArray ++ b.toArray)

public instance : Append UInt16Array := ⟨append⟩

private unsafe def copySliceImpl (src : @& UInt16Array) (srcOff : Nat) (dest : UInt16Array)
    (destOff len : Nat) (exact : Bool := true) : UInt16Array :=
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
public def copySlice (src : @& UInt16Array) (srcOff : Nat) (dest : UInt16Array)
    (destOff len : Nat) (exact : Bool := true) : UInt16Array :=
  mk (dest.toArray.extract 0 destOff ++ src.toArray.extract srcOff (srcOff + len) ++
    dest.toArray.extract (destOff + min len (src.toArray.size - srcOff)) dest.toArray.size)

end UInt16Array

end ScalarArray
