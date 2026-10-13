/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import all ScalarArray.Internal
public import Std.Data.Iterators

/-!
# Arrays of `Int64`

`ScalarArray.Int64Array` stores `Int64` values unboxed in a Lean runtime scalar array,
8 bytes per element. Its logical model is `Array Int64`: `Int64Array.mk` and
`Int64Array.data` convert between the two, and every operation is specified by its effect on
the model.

Reads and in-place writes are inline C. `uset`, `set` and `push` update the array in place when it
is not shared and copy it otherwise, like `Array` and `ByteArray`.
-/

namespace ScalarArray

/--
Arrays of `Int64` values, stored unboxed in a scalar array, 8 bytes per element.

The logical model is an `Array Int64`. At runtime a `Int64Array` is a `ScalarArray`, so every
function that looks inside the constructor must be `extern` or `implemented_by`.
-/
public inductive Int64Array : Type
  | public mk (data : Array Int64)

namespace Int64Array

-- `lean_byte_array_size` reads the size of any scalar array, whatever its element size.
@[extern "lean_byte_array_size", tagged_return, expose]
public def size : (a : @& Int64Array) → Nat
  | mk a => a.size

/--
The size of `a` as a `USize`. Since `USize` can address all memory, no array has more elements than
`USize` can count.
-/
@[extern "lean_sarray_size", simp, expose]
public def usize (a : @& Int64Array) : USize :=
  a.size.toUSize

@[extern c inline "((uint64_t*)lean_sarray_cptr(#1))[#2]", expose]
public def uget :
    (a : @& Int64Array) → (i : USize) → (h : i.toNat < a.size := by get_elem_tactic) → Int64
  | mk a, i, h => a.uget i h

@[expose]
public def get :
    (a : @& Int64Array) → (i : @& Nat) → (h : i < a.size := by get_elem_tactic) → Int64
  | mk a, i, h => a[i]

@[inline]
private unsafe def getImpl : type_of% @get :=
  fun a i _ => a.uget i.toUSize lcProof

attribute [implemented_by getImpl] get

/-- Stores `v` at index `i` in place. Only valid when `a` is exclusive and `i` is in bounds. -/
@[extern c inline "#1;\n((uint64_t*)lean_sarray_cptr(#1))[#2] = #3"]
private unsafe def setInt64Unsafe : Int64Array → USize → Int64 → Int64Array
  | .mk a, i, v => .mk <| a.uset i v lcProof

private unsafe def toUSizeChecked (n : Nat) : USize :=
  if n < USize.size >>> 1 then n.toUSize else panic! "out of memory"

/-- A new array of size `size` with room for `capacity` elements. Requires `size ≤ capacity`. -/
private unsafe def allocUnsafe (size capacity : USize) : Int64Array :=
  unsafeCast <| ScalarArray.allocate 8 size capacity lcProof

private unsafe def mkWithCapacityImpl (a : Array Int64) (capacity : Nat := a.size) :
    Int64Array :=
  let cap := toUSizeChecked capacity
  let sz := toUSizeChecked a.size
  let r := allocUnsafe sz (max sz cap)
  loop sz r 0
where
  loop (sz : USize) (r : Int64Array) (i : USize) : Int64Array :=
    if i < sz then loop sz (setInt64Unsafe r i (a.uget i lcProof)) (i + 1) else r

private unsafe def mkImpl (a : Array Int64) : Int64Array :=
  mkWithCapacityImpl a a.size

attribute [implemented_by mkImpl] Int64Array.mk

private unsafe def dataImpl (a : @& Int64Array) : Array Int64 :=
  loop a.usize 0 (Array.replicate a.size default)
where
  loop (sz i : USize) (r : Array Int64) : Array Int64 :=
    if i < sz then loop sz (i + 1) (r.uset i (a.uget i lcProof) lcProof) else r

/-- The elements of `a` as an `Array Int64`. -/
@[implemented_by dataImpl, expose]
public def data : (a : @& Int64Array) → Array Int64
  | mk a => a

private unsafe def emptyWithCapacityImpl (capacity : Nat) : Int64Array :=
  mkWithCapacityImpl #[] capacity

/-- An empty array with room for `capacity` elements before reallocating. -/
@[implemented_by emptyWithCapacityImpl, expose]
public def emptyWithCapacity (capacity : Nat) : Int64Array :=
  mk #[]

@[expose] public def empty : Int64Array := emptyWithCapacity 0

public instance : EmptyCollection Int64Array := ⟨empty⟩

public instance : Inhabited Int64Array := ⟨empty⟩

@[expose]
public def uset :
    (a : Int64Array) → (i : USize) → (v : Int64) →
    (h : i.toNat < a.size := by get_elem_tactic) → Int64Array
  | mk a, i, v, h => mk (a.uset i v h)

private unsafe def usetImpl : type_of% @uset :=
  fun a i v _ => setInt64Unsafe (unsafeCast <| ScalarArray.ensureExclusive (unsafeCast a)) i v

attribute [implemented_by usetImpl] uset

@[expose]
public def set :
    (a : Int64Array) → (i : Nat) → (v : Int64) → (h : i < a.size := by get_elem_tactic) →
    Int64Array
  | mk a, i, v, h => mk (a.set i v h)

private unsafe def setImpl : type_of% @set :=
  fun a i v _ => usetImpl a i.toUSize v lcProof

attribute [implemented_by setImpl] set

public def get! (a : @& Int64Array) (i : @& Nat) : Int64 :=
  if h : i < a.size then a.get i h else panic! "index out of bounds"

public def getD (a : @& Int64Array) (i : @& Nat) (v₀ : Int64) : Int64 :=
  if h : i < a.size then a.get i h else v₀

private unsafe def setBangImpl (a : Int64Array) (i : Nat) (v : Int64) : Int64Array :=
  if h : i < a.size then setImpl a i v h else a

/-- Replaces the element at index `i`. If `i` is out of bounds, the array is returned unmodified. -/
@[implemented_by setBangImpl, expose]
public def set! : Int64Array → Nat → Int64 → Int64Array
  | mk a, i, v => mk (a.set! i v)

public instance : GetElem Int64Array Nat Int64 fun a i => i < a.size where
  getElem a i h := a.get i h

public instance : GetElem Int64Array USize Int64 fun a i => i.toNat < a.size where
  getElem a i h := a.uget i h

private unsafe def pushImpl (a : Int64Array) (v : Int64) : Int64Array :=
  let s : ScalarArray := unsafeCast a
  let cap := s.capacity
  if s.size < cap then
    loop s.ensureExclusive
  else if cap < cap + cap + 1 then
    loop (s.copyWithCapacity (cap + cap + 1) lcProof)
  else
    panic! "out of memory"
where
  loop (s : ScalarArray) : Int64Array :=
    let i := s.size
    setInt64Unsafe (unsafeCast (s.resizeUnsafe (i + 1) lcProof lcProof)) i v

@[implemented_by pushImpl, expose]
public def push : Int64Array → Int64 → Int64Array
  | mk a, v => mk (a.push v)

/--
Copies `n` bytes of the data of `src`, starting at byte `srcOff`, into the data of `dest`, starting
at byte `destOff`. Only valid when `dest` is exclusive and both ranges are within the capacities.
-/
-- TODO: core has no runtime function that copies a slice of a scalar array with any element size;
-- `lean_byte_array_copy_slice` only works for bytes. Replace this once core has one.
@[extern c inline "#1;\n__builtin_memcpy(lean_sarray_cptr(#1) + #4, lean_sarray_cptr(#2) + #3, #5)"]
private unsafe def memcpyUnsafe :
    Int64Array → @& Int64Array → (srcOff destOff n : USize) → Int64Array
  | dest, _, _, _, _ => dest

/--
Copies the `n` elements of `src` starting at index `srcOff` into `dest` starting at index `destOff`,
in place, and grows the size of `dest` to `destOff + n` if it is smaller. Only valid when `dest` is
exclusive, has capacity for `destOff + n` elements, and is not the same object as `src`, and when
`destOff ≤ dest.size` and `srcOff + n ≤ src.size`.
-/
@[inline]
private unsafe def copySliceUnsafe (dest : Int64Array) (src : @& Int64Array)
    (srcOff destOff n : USize) : Int64Array :=
  let esz := (unsafeCast src : ScalarArray).elemSize.toUSize
  let d : ScalarArray := unsafeCast (memcpyUnsafe dest src (srcOff * esz) (destOff * esz) (n * esz))
  unsafeCast (d.resizeUnsafe (max d.size (destOff + n)) lcProof lcProof)

private unsafe def appendImpl (a b : Int64Array) : Int64Array :=
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
public def append : Int64Array → Int64Array → Int64Array
  | mk a, mk b => mk (a ++ b)

public instance : Append Int64Array := ⟨append⟩

private unsafe def copySliceImpl (src : @& Int64Array) (srcOff : Nat) (dest : Int64Array)
    (destOff len : Nat) (exact : Bool := true) : Int64Array :=
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
public def copySlice (src : @& Int64Array) (srcOff : Nat) (dest : Int64Array)
    (destOff len : Nat) (exact : Bool := true) : Int64Array :=
  mk (dest.data.extract 0 destOff ++ src.data.extract srcOff (srcOff + len) ++
    dest.data.extract (destOff + min len (src.data.size - srcOff)) dest.data.size)

/-! ## Removing elements -/

public def isEmpty (a : @& Int64Array) : Bool := a.size == 0

private unsafe def popImpl (a : Int64Array) : Int64Array :=
  if a.size == 0 then
    a
  else
    let s : ScalarArray := ScalarArray.ensureExclusive (unsafeCast a)
    unsafeCast (s.resizeUnsafe (s.size - 1) lcProof lcProof)

/-- Removes the last element of `a`, if any, in place when `a` is not shared. -/
@[implemented_by popImpl, expose]
public def pop : Int64Array → Int64Array
  | mk a => mk a.pop

public def back? (a : @& Int64Array) : Option Int64 := a[a.size - 1]?

public def back! (a : @& Int64Array) : Int64 := a[a.size - 1]!

public def back (a : @& Int64Array) (h : 0 < a.size) : Int64 :=
  a[a.size - 1]'(Nat.sub_lt h Nat.one_pos)

private def popWhileImpl (p : Int64 → Bool) (a : Int64Array) : Int64Array :=
  if h : 0 < a.size then
    if p (a.back h) then popWhileImpl p a.pop else a
  else
    a
termination_by a.size
decreasing_by
  have : a.pop.size = a.size - 1 := by cases a; exact Array.size_pop ..
  omega

/--
Removes the longest run of elements at the end of `a` that satisfy `p`, in place when `a` is not
shared.
-/
@[implemented_by popWhileImpl, expose]
public def popWhile (p : Int64 → Bool) : Int64Array → Int64Array
  | mk a => mk (a.popWhile p)

private unsafe def extractImpl (a : @& Int64Array) (start stop : Nat) : Int64Array :=
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
public def extract : (a : @& Int64Array) → (start stop : Nat) → Int64Array
  | mk a, start, stop => mk (a.extract start stop)

/-! ## Linearity -/

/--
Marks `a` as linear, a debugging aid: if a marked array is ever shared and then modified, the
runtime reports it. Logically this is the identity.
-/
@[never_extract, extern "lean_sarray_mark_linear", expose]
public def markLinear (a : Int64Array) : Int64Array := a

/-- Returns `b`, marking it as linear if `a` is marked. Logically this is `b`. -/
@[never_extract, extern "lean_sarray_propagate_mark", expose]
public def propagateMark (a : @& Int64Array) (b : Int64Array) : Int64Array := b

/-! ## Search -/

/--
The index of the first element at or after `start` that satisfies `p`, with a proof that it is in
bounds.
-/
@[inline]
public def findFinIdx? (a : Int64Array) (p : Int64 → Bool) (start := 0) : Option (Fin a.size) :=
  let rec @[specialize] loop (i : Nat) :=
    if h : i < a.size then
      if p a[i] then some ⟨i, h⟩ else loop (i + 1)
    else
      none
    termination_by a.size - i
  loop start

/-- The index of the first element at or after `start` that satisfies `p`. -/
@[inline]
public def findIdx? (a : Int64Array) (p : Int64 → Bool) (start := 0) : Option Nat :=
  let rec @[specialize] loop (i : Nat) :=
    if h : i < a.size then
      if p a[i] then some i else loop (i + 1)
    else
      none
    termination_by a.size - i
  loop start

/-! ## Building arrays -/

private unsafe def replicateImpl (n : Nat) (v : Int64) : Int64Array :=
  let sz := toUSizeChecked n
  loop sz (allocUnsafe sz sz) 0
where
  loop (sz : USize) (r : Int64Array) (i : USize) : Int64Array :=
    if i < sz then loop sz (setInt64Unsafe r i v) (i + 1) else r

/-- An array of `n` copies of `v`. -/
@[implemented_by replicateImpl, expose]
public def replicate (n : Nat) (v : Int64) : Int64Array :=
  mk (Array.replicate n v)

private unsafe def ofFnImpl {n : Nat} (f : Fin n → Int64) : Int64Array :=
  let sz := toUSizeChecked n
  loop (allocUnsafe sz sz) 0
where
  loop (r : Int64Array) (i : Nat) : Int64Array :=
    if h : i < n then loop (setInt64Unsafe r i.toUSize (f ⟨i, h⟩)) (i + 1) else r

/-- The array `#[f 0, …, f (n - 1)]`. -/
@[implemented_by ofFnImpl, expose]
public def ofFn {n : Nat} (f : Fin n → Int64) : Int64Array :=
  mk (Array.ofFn f)

private unsafe def ofListImpl (l : List Int64) : Int64Array :=
  loop l (emptyWithCapacity l.length)
where
  loop : List Int64 → Int64Array → Int64Array
    | [], r => r
    | x :: xs, r => loop xs (r.push x)

/-- The array with the elements of `l`. -/
@[implemented_by ofListImpl, expose]
public def ofList (l : List Int64) : Int64Array :=
  mk l.toArray

/-! ## Iteration -/

@[specialize]
private unsafe def foldlMImpl {β : Type v} {m : Type v → Type w} [Monad m] (f : β → Int64 → m β)
    (init : β) (a : @& Int64Array) (start := 0) (stop := a.size) : m β :=
  let stop := min stop a.size
  if start < stop then loop stop.toUSize start.toUSize init else pure init
where
  loop (stop i : USize) (b : β) : m β :=
    if i < stop then do loop stop (i + 1) (← f b (a.uget i lcProof)) else pure b

/--
Folds a monadic function over the elements of `a` from index `start` up to, but not including,
`stop`, from first to last.
-/
@[implemented_by foldlMImpl, expose]
public def foldlM {β : Type v} {m : Type v → Type w} [Monad m] (f : β → Int64 → m β) (init : β)
    (a : @& Int64Array) (start := 0) (stop := a.size) : m β :=
  a.data.foldlM f init start stop

@[specialize]
private unsafe def foldrMImpl {β : Type v} {m : Type v → Type w} [Monad m] (f : Int64 → β → m β)
    (init : β) (a : @& Int64Array) : m β :=
  loop a.usize init
where
  loop (i : USize) (b : β) : m β :=
    if h : 0 < i ∧ (i - 1).toNat < a.size then do loop (i - 1) (← f (a.uget (i - 1) h.2) b)
    else pure b

/-- Folds a monadic function over the elements of `a`, from last to first. -/
@[implemented_by foldrMImpl, expose]
public def foldrM {β : Type v} {m : Type v → Type w} [Monad m] (f : Int64 → β → m β) (init : β)
    (a : @& Int64Array) : m β :=
  a.data.foldrM f init

@[inline, expose]
public def foldl {β : Type v} (f : β → Int64 → β) (init : β) (a : @& Int64Array) (start := 0)
    (stop := a.size) : β :=
  Id.run <| a.foldlM (pure <| f · ·) init start stop

@[inline, expose]
public def foldr {β : Type v} (f : Int64 → β → β) (init : β) (a : @& Int64Array) : β :=
  Id.run <| a.foldrM (pure <| f · ·) init

@[inline]
public def forM {m : Type v → Type w} [Monad m] (f : Int64 → m PUnit) (a : @& Int64Array) :
    m PUnit :=
  a.foldlM (fun _ x => f x) ⟨⟩

@[specialize]
private unsafe def forInImpl {β : Type v} {m : Type v → Type w} [Monad m] (a : @& Int64Array)
    (init : β) (f : Int64 → β → m (ForInStep β)) : m β :=
  loop 0 init
where
  loop (i : USize) (b : β) : m β :=
    if h : i.toNat < a.size then do
      match ← f (a.uget i h) b with
      | .done b => pure b
      | .yield b => loop (i + 1) b
    else pure b

@[implemented_by forInImpl]
public def forIn {β : Type v} {m : Type v → Type w} [Monad m] (a : @& Int64Array) (init : β)
    (f : Int64 → β → m (ForInStep β)) : m β :=
  ForIn.forIn a.data init f

public instance [Monad m] : ForIn m Int64Array Int64 where
  forIn a b f := Int64Array.forIn a b f

@[specialize]
private unsafe def anyImpl (a : @& Int64Array) (p : Int64 → Bool) : Bool :=
  loop 0
where
  loop (i : USize) : Bool :=
    if h : i.toNat < a.size then p (a.uget i h) || loop (i + 1) else false

/-- Whether some element of `a` satisfies `p`. -/
@[implemented_by anyImpl]
public def any (a : @& Int64Array) (p : Int64 → Bool) : Bool :=
  a.data.any p

@[specialize]
private unsafe def allImpl (a : @& Int64Array) (p : Int64 → Bool) : Bool :=
  loop 0
where
  loop (i : USize) : Bool :=
    if h : i.toNat < a.size then p (a.uget i h) && loop (i + 1) else true

/-- Whether every element of `a` satisfies `p`. -/
@[implemented_by allImpl]
public def all (a : @& Int64Array) (p : Int64 → Bool) : Bool :=
  a.data.all p

private unsafe def containsImpl (a : @& Int64Array) (v : Int64) : Bool :=
  anyImpl a (v == ·)

/-- Whether `v` is an element of `a`. -/
@[implemented_by containsImpl]
public def contains (a : @& Int64Array) (v : Int64) : Bool :=
  a.data.contains v

/-! ## Equality and hashing -/

private theorem data_injective : {a b : Int64Array} → a.data = b.data → a = b
  | mk _, mk _, rfl => rfl

/-- Decides equality by comparing the two arrays' memory. -/
@[extern "lean_sarray_dec_eq"]
public def decEq (a b : @& Int64Array) : Decidable (a = b) :=
  decidable_of_iff (a.data = b.data) ⟨data_injective, fun h => h ▸ rfl⟩

public instance : DecidableEq Int64Array := decEq

private unsafe def hashImpl (a : @& Int64Array) : UInt64 :=
  foldlMImpl (m := Id) (fun r x => mixHash r (Hashable.hash x)) 7 a

/-- The same hash as `a.data`. -/
@[implemented_by hashImpl]
public def hash (a : @& Int64Array) : UInt64 :=
  Hashable.hash a.data

public instance : Hashable Int64Array := ⟨hash⟩

/-! ## Conversion and printing -/

@[expose] public def toList (a : Int64Array) : List Int64 := a.data.toList

public instance : Repr Int64Array where
  reprPrec a _ := "Int64Array.mk " ++ repr a.data

public instance : ToString Int64Array where
  toString a := "Int64Array.mk " ++ toString a.data

/-! ## Slices -/

/-- Internal representation of `Int64Array.Slice`. -/
public protected structure SliceData where
  /-- The underlying array. -/
  array : Int64Array
  /-- The starting index of the slice (inclusive). -/
  start : Nat
  /-- The ending index of the slice (exclusive). -/
  stop : Nat
  /-- The starting index is no later than the ending index. -/
  start_le_stop : start ≤ stop
  /-- The ending index is no later than the end of the array. -/
  stop_le_array_size : stop ≤ array.size

/--
A region of a `Int64Array`: the elements from index `start` up to, but not including, `stop`.
Taking a slice doesn't copy the array. Slices are written with core's slice notation, such as
`a[i...j]`, `a[i...*]` or `a[*...j]`.
-/
public protected abbrev Slice := Std.Slice Int64Array.SliceData

public instance : Std.Slice.Self (Std.Slice Int64Array.SliceData) Int64Array.Slice where

namespace Slice

@[always_inline, inline, expose, inherit_doc SliceData.array]
public def array (s : Int64Array.Slice) : Int64Array := s.internalRepresentation.array

@[always_inline, inline, expose, inherit_doc SliceData.start]
public def start (s : Int64Array.Slice) : Nat := s.internalRepresentation.start

@[always_inline, inline, expose, inherit_doc SliceData.stop]
public def stop (s : Int64Array.Slice) : Nat := s.internalRepresentation.stop

@[inherit_doc SliceData.start_le_stop]
public theorem start_le_stop (s : Int64Array.Slice) : s.start ≤ s.stop :=
  s.internalRepresentation.start_le_stop

@[inherit_doc SliceData.stop_le_array_size]
public theorem stop_le_array_size (s : Int64Array.Slice) : s.stop ≤ s.array.size :=
  s.internalRepresentation.stop_le_array_size

public instance : Std.Slice.SliceSize Int64Array.SliceData where
  size s := s.internalRepresentation.stop - s.internalRepresentation.start

public theorem size_eq (s : Int64Array.Slice) : s.size = s.stop - s.start := rfl

/-- The element at index `i` of the slice, counted from the start of the slice. -/
@[inline, expose]
public def get (s : Int64Array.Slice) (i : Nat) (h : i < s.size := by get_elem_tactic) :
    Int64 :=
  s.array[s.start + i]'(by have := s.stop_le_array_size; rw [size_eq] at h; omega)

public instance : GetElem Int64Array.Slice Nat Int64 fun s i => i < s.size where
  getElem s i h := s.get i h

/-- The element at index `i` of the slice, or `v₀` if `i` is out of bounds. -/
@[inline]
public def getD (s : Int64Array.Slice) (i : Nat) (v₀ : Int64) : Int64 :=
  if h : i < s.size then s[i] else v₀

/-- The element at index `i` of the slice, or `default` if `i` is out of bounds. -/
public abbrev get! (s : Int64Array.Slice) (i : Nat) : Int64 :=
  getD s i default

/-- Removes the first element of the slice, if any. -/
@[expose]
public def popFront (s : Int64Array.Slice) : Int64Array.Slice :=
  if h : s.start < s.stop then
    ⟨{ s.internalRepresentation with start := s.start + 1, start_le_stop := h }⟩
  else
    s

/-- The empty slice, backed by an empty array. -/
@[expose]
public protected def empty : Int64Array.Slice :=
  ⟨{ array := Int64Array.empty, start := 0, stop := 0, start_le_stop := Nat.le_refl 0,
     stop_le_array_size := Nat.le_refl 0 }⟩

public instance : EmptyCollection Int64Array.Slice := ⟨Slice.empty⟩

public instance : Inhabited Int64Array.Slice := ⟨Slice.empty⟩

/-- The elements of the slice, copied into a new array with a single `memcpy`. -/
@[expose]
public def copy (s : Int64Array.Slice) : Int64Array :=
  s.array.extract s.start s.stop

public theorem getElem_eq (s : Int64Array.Slice) (i : Nat) (h : i < s.size) :
    s[i] = s.array[s.start + i]'(by have := s.stop_le_array_size; rw [size_eq] at h; omega) := rfl

public instance : Repr Int64Array.Slice where
  reprPrec s _ := repr s.copy ++ ".toSlice"

public instance : ToString Int64Array.Slice where
  toString s := toString s.copy

end Slice

/--
The slice of `a` from index `start` up to, but not including, `stop`. If `start` or `stop` are not
valid bounds, they are clamped to the size of `a`, and `start` is clamped to `stop`.
-/
@[expose]
public def toSlice (a : Int64Array) (start : Nat := 0) (stop : Nat := a.size) :
    Int64Array.Slice :=
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
public instance : Coe Int64Array Int64Array.Slice := ⟨(·.toSlice)⟩

public instance : Std.Rcc.Sliceable Int64Array Nat Int64Array.Slice where
  mkSlice a range := a.toSlice range.lower (range.upper + 1)

public instance : Std.Rco.Sliceable Int64Array Nat Int64Array.Slice where
  mkSlice a range := a.toSlice range.lower range.upper

public instance : Std.Rci.Sliceable Int64Array Nat Int64Array.Slice where
  mkSlice a range := a.toSlice range.lower

public instance : Std.Roc.Sliceable Int64Array Nat Int64Array.Slice where
  mkSlice a range := a.toSlice (range.lower + 1) (range.upper + 1)

public instance : Std.Roo.Sliceable Int64Array Nat Int64Array.Slice where
  mkSlice a range := a.toSlice (range.lower + 1) range.upper

public instance : Std.Roi.Sliceable Int64Array Nat Int64Array.Slice where
  mkSlice a range := a.toSlice (range.lower + 1)

public instance : Std.Ric.Sliceable Int64Array Nat Int64Array.Slice where
  mkSlice a range := a.toSlice 0 (range.upper + 1)

public instance : Std.Rio.Sliceable Int64Array Nat Int64Array.Slice where
  mkSlice a range := a.toSlice 0 range.upper

public instance : Std.Rii.Sliceable Int64Array Nat Int64Array.Slice where
  mkSlice a _ := a.toSlice

namespace Slice

/-- The slice of `s` from index `start` up to, but not including, `stop`, clamped like `toSlice`. -/
@[expose]
public def slice (s : Int64Array.Slice) (start : Nat := 0) (stop : Nat := s.size) :
    Int64Array.Slice :=
  s.array.toSlice (s.start + min start s.size) (s.start + min stop s.size)

end Slice

public instance : Std.Rcc.Sliceable Int64Array.Slice Nat Int64Array.Slice where
  mkSlice s range := s.slice range.lower (range.upper + 1)

public instance : Std.Rco.Sliceable Int64Array.Slice Nat Int64Array.Slice where
  mkSlice s range := s.slice range.lower range.upper

public instance : Std.Rci.Sliceable Int64Array.Slice Nat Int64Array.Slice where
  mkSlice s range := s.slice range.lower

public instance : Std.Roc.Sliceable Int64Array.Slice Nat Int64Array.Slice where
  mkSlice s range := s.slice (range.lower + 1) (range.upper + 1)

public instance : Std.Roo.Sliceable Int64Array.Slice Nat Int64Array.Slice where
  mkSlice s range := s.slice (range.lower + 1) range.upper

public instance : Std.Roi.Sliceable Int64Array.Slice Nat Int64Array.Slice where
  mkSlice s range := s.slice (range.lower + 1)

public instance : Std.Ric.Sliceable Int64Array.Slice Nat Int64Array.Slice where
  mkSlice s range := s.slice 0 (range.upper + 1)

public instance : Std.Rio.Sliceable Int64Array.Slice Nat Int64Array.Slice where
  mkSlice s range := s.slice 0 range.upper

public instance : Std.Rii.Sliceable Int64Array.Slice Nat Int64Array.Slice where
  mkSlice s _ := s

/-- The iterator over the elements of a slice, used for `for` loops and the generic slice API. -/
public protected structure SliceIterator where
  /-- The rest of the slice. -/
  xs : Int64Array.Slice

@[inline, expose]
public def SliceIterator.step :
    Std.IterM (α := Int64Array.SliceIterator) Id Int64 →
      Std.IterStep (Std.IterM (α := Int64Array.SliceIterator) m Int64) Int64
  | ⟨⟨xs⟩⟩ =>
    if h : xs.start < xs.stop then
      have := xs.stop_le_array_size
      .yield ⟨⟨⟨xs.array, xs.start + 1, xs.stop, h, xs.stop_le_array_size⟩⟩⟩ xs.array[xs.start]
    else
      .done

public instance : Std.Iterator Int64Array.SliceIterator Id Int64 where
  IsPlausibleStep it step := step = SliceIterator.step it
  step it := pure <| .deflate ⟨SliceIterator.step it, rfl⟩

private def SliceIterator.finitenessRelation :
    Std.Iterators.FinitenessRelation Int64Array.SliceIterator Id where
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
      omega
    next =>
      simp [Std.IterStep.successor] at h

public instance : Std.Iterators.Finite Int64Array.SliceIterator Id :=
  .of_finitenessRelation SliceIterator.finitenessRelation

public instance [Monad m] : Std.IteratorLoop Int64Array.SliceIterator Id m :=
  .defaultImplementation

public instance :
    Std.ToIterator (Std.Slice Int64Array.SliceData) Id Int64Array.SliceIterator Int64 :=
  Std.ToIterator.of Int64Array.SliceIterator (⟨⟨·⟩⟩)

public instance [Monad m] : ForIn m Int64Array.Slice Int64 := inferInstance

/-- An iterator over the elements of `a`, for use with the `Std.Iterators` API. -/
@[inline, expose]
public def iter (a : Int64Array) : Std.Iter (α := Int64Array.SliceIterator) Int64 :=
  a.toSlice.iter

namespace Slice

/-- Folds a monadic function over the elements of `s`, from last to first. -/
@[inline, expose]
public def foldrM {β : Type v} {m : Type v → Type w} [Monad m] (f : Int64 → β → m β) (init : β)
    (s : Int64Array.Slice) : m β :=
  loop s.size (Nat.le_refl _) init
where
  @[specialize] loop : (i : Nat) → i ≤ s.size → β → m β
    | 0, _, b => pure b
    | i + 1, h, b => do loop i (Nat.le_of_succ_le h) (← f s[i] b)

/-- Folds a function over the elements of `s`, from last to first. -/
@[inline, expose]
public def foldr {β : Type v} (f : Int64 → β → β) (init : β) (s : Int64Array.Slice) : β :=
  Id.run <| s.foldrM (pure <| f · ·) init

/-- Runs a monadic action on each element of `s`, from last to first. -/
@[inline, expose]
public def forRevM {m : Type v → Type w} [Monad m] (f : Int64 → m PUnit)
    (s : Int64Array.Slice) : m PUnit :=
  s.foldrM (fun x _ => f x) ⟨⟩

/-- The result of the last element of `s` for which `f` returns `some`, searching from the end. -/
@[inline, expose]
public def findSomeRevM? {β : Type v} {m : Type v → Type w} [Monad m] (s : Int64Array.Slice)
    (f : Int64 → m (Option β)) : m (Option β) :=
  loop s.size (Nat.le_refl _)
where
  @[specialize] loop : (i : Nat) → i ≤ s.size → m (Option β)
    | 0, _ => pure none
    | i + 1, h => do
      match ← f s[i] with
      | some b => pure (some b)
      | none => loop i (Nat.le_of_succ_le h)

/-- The last element of `s` that satisfies the monadic predicate `p`. -/
@[inline, expose]
public def findRevM? {m : Type → Type w} [Monad m] (s : Int64Array.Slice) (p : Int64 → m Bool) :
    m (Option Int64) :=
  s.findSomeRevM? fun x => return if (← p x) then some x else none

/-- The last element of `s` that satisfies `p`. -/
@[inline, expose]
public def findRev? (s : Int64Array.Slice) (p : Int64 → Bool) : Option Int64 :=
  Id.run <| s.findRevM? (pure <| p ·)

/-- The first element of `s` that satisfies `p`. -/
@[inline, expose]
public def find? (s : Int64Array.Slice) (p : Int64 → Bool) : Option Int64 :=
  s.iter.find? p

/-- Whether some element of `s` satisfies `p`. -/
@[inline, expose]
public def any (s : Int64Array.Slice) (p : Int64 → Bool) : Bool :=
  s.iter.any p

/-- Whether every element of `s` satisfies `p`. -/
@[inline, expose]
public def all (s : Int64Array.Slice) (p : Int64 → Bool) : Bool :=
  s.iter.all p

/-- Whether `v` is an element of `s`. -/
@[inline, expose]
public def contains (s : Int64Array.Slice) (v : Int64) : Bool :=
  s.any (v == ·)

/-- The number of elements of `s` that satisfy `p`. -/
@[inline, expose]
public def count (s : Int64Array.Slice) (p : Int64 → Bool) : Nat :=
  s.iter.fold (fun n x => if p x then n + 1 else n) 0

end Slice

/--
Collects the values emitted by an iterator into a new array. Together with the `Std.Iterators`
combinators, this gives functions such as `map`, `filter`, `take` and `zipWith`, for example
`(a.iter.map (· + 1)).toInt64Array`.
-/
@[inline, expose]
public def _root_.Std.Iter.toInt64Array {α : Type} [Std.Iterator α Id Int64]
    [Std.IteratorLoop α Id Id] (it : Std.Iter (α := α) Int64) : Int64Array :=
  it.fold (·.push ·) empty

/-- Like `Std.Iter.toInt64Array`, but the new array starts with room for `capacity` elements. -/
@[inline, expose]
public def _root_.Std.Iter.toInt64ArrayWithCapacity {α : Type} [Std.Iterator α Id Int64]
    [Std.IteratorLoop α Id Id] (it : Std.Iter (α := α) Int64) (capacity : Nat) : Int64Array :=
  it.fold (·.push ·) (emptyWithCapacity capacity)

@[simp] public theorem _root_.Std.Iter.toInt64ArrayWithCapacity_eq {α : Type}
    [Std.Iterator α Id Int64] [Std.IteratorLoop α Id Id] (it : Std.Iter (α := α) Int64)
    (capacity : Nat) : it.toInt64ArrayWithCapacity capacity = it.toInt64Array := rfl

@[simp] public theorem size_mk (a : Array Int64) : (mk a).size = a.size := rfl

@[simp] public theorem data_mk (a : Array Int64) : (mk a).data = a := rfl

@[simp] public theorem mk_data (a : Int64Array) : mk a.data = a := by cases a; rfl

public theorem size_eq_data_size (a : Int64Array) : a.size = a.data.size := by cases a; rfl

@[simp] public theorem size_data (a : Int64Array) : a.data.size = a.size :=
  (size_eq_data_size a).symm

@[simp] public theorem size_uset (a : Int64Array) (i : USize) (v : Int64) (h) :
    (a.uset i v h).size = a.size := by
  cases a; exact Array.size_set ..

@[simp] public theorem size_set (a : Int64Array) (i : Nat) (v : Int64) (h) :
    (a.set i v h).size = a.size := by
  cases a; exact Array.size_set ..

@[simp] public theorem size_push (a : Int64Array) (v : Int64) :
    (a.push v).size = a.size + 1 := by
  cases a; simp [push, size]

@[simp] public theorem data_append (a b : Int64Array) : (a ++ b).data = a.data ++ b.data := by
  cases a; cases b; rfl

@[simp] public theorem size_append (a b : Int64Array) : (a ++ b).size = a.size + b.size := by
  simp [-size_data, size_eq_data_size]

@[ext] public theorem ext {a b : Int64Array} (h : a.data = b.data) : a = b := data_injective h

@[simp] public theorem getElem_mk (a : Array Int64) (i : Nat) (h : i < (mk a).size) :
    (mk a)[i] = a[i] := rfl

public theorem getElem_eq_getElem_data (a : Int64Array) (i : Nat) (h : i < a.size) :
    a[i] = a.data[i]'(size_eq_data_size a ▸ h) := by
  cases a; rfl

@[simp] public theorem getElem_data (a : Int64Array) (i : Nat) (h : i < a.data.size) :
    a.data[i] = a[i]'(by simpa using h) := by
  cases a; rfl

public theorem ext_getElem {a b : Int64Array} (h₁ : a.size = b.size)
    (h₂ : ∀ (i : Nat) (hi₁ : i < a.size) (hi₂ : i < b.size), a[i] = b[i]) : a = b := by
  ext i hi₁ hi₂
  · simpa using h₁
  · simpa using h₂ i (by simpa using hi₁) (by simpa using hi₂)

@[simp] public theorem getElem_usize (a : Int64Array) (i : USize) (h : i.toNat < a.size) :
    a[i] = a[i.toNat] := by
  cases a; rfl

@[simp] public theorem data_uset (a : Int64Array) (i : USize) (v : Int64) (h) :
    (a.uset i v h).data = a.data.set i.toNat v (size_eq_data_size a ▸ h) := by
  cases a; rfl

@[simp] public theorem data_set (a : Int64Array) (i : Nat) (v : Int64) (h) :
    (a.set i v h).data = a.data.set i v (size_eq_data_size a ▸ h) := by
  cases a; rfl

@[simp] public theorem data_push (a : Int64Array) (v : Int64) :
    (a.push v).data = a.data.push v := by
  cases a; rfl

@[simp] public theorem data_pop (a : Int64Array) : a.pop.data = a.data.pop := by
  cases a; rfl

@[simp] public theorem data_extract (a : Int64Array) (start stop : Nat) :
    (a.extract start stop).data = a.data.extract start stop := by
  cases a; rfl

@[simp] public theorem data_replicate (n : Nat) (v : Int64) :
    (replicate n v).data = Array.replicate n v := rfl

@[simp] public theorem data_ofFn {n : Nat} (f : Fin n → Int64) :
    (ofFn f).data = Array.ofFn f := rfl

@[simp] public theorem data_empty : (empty : Int64Array).data = #[] := rfl

@[simp] public theorem size_pop (a : Int64Array) : a.pop.size = a.size - 1 := by
  simp [-size_data, size_eq_data_size]

@[simp] public theorem size_extract (a : Int64Array) (start stop : Nat) :
    (a.extract start stop).size = min stop a.size - start := by
  simp [-size_data, size_eq_data_size]

@[simp] public theorem size_replicate (n : Nat) (v : Int64) : (replicate n v).size = n := by
  simp [-size_data, size_eq_data_size]

@[simp] public theorem size_ofFn {n : Nat} (f : Fin n → Int64) : (ofFn f).size = n := by
  simp [-size_data, size_eq_data_size]

@[simp] public theorem size_empty : (empty : Int64Array).size = 0 := rfl

@[simp] public theorem getElem_set (a : Int64Array) (i : Nat) (v : Int64) (h) (j : Nat) (hj) :
    (a.set i v h)[j]'hj = if i = j then v else a[j]'(by simpa using hj) := by
  simp [-getElem_data, getElem_eq_getElem_data, Array.getElem_set]

@[simp] public theorem getElem_push (a : Int64Array) (v : Int64) (i : Nat) (h) :
    (a.push v)[i]'h = if h' : i < a.size then a[i] else v := by
  simp [-getElem_data, getElem_eq_getElem_data, Array.getElem_push, -size_data, size_eq_data_size]

@[simp] public theorem getElem_pop (a : Int64Array) (i : Nat) (h) :
    a.pop[i]'h = a[i]'(by simp at h; omega) := by
  simp [-getElem_data, getElem_eq_getElem_data]

@[simp] public theorem data_popWhile (p : Int64 → Bool) (a : Int64Array) :
    (a.popWhile p).data = a.data.popWhile p := by
  cases a; rfl

@[simp] public theorem getElem_append (a b : Int64Array) (i : Nat) (h) :
    (a ++ b)[i]'h = if h' : i < a.size then a[i] else b[i - a.size]'(by simp at h; omega) := by
  simp [-getElem_data, getElem_eq_getElem_data, Array.getElem_append, -size_data, size_eq_data_size]

@[simp] public theorem getElem_extract (a : Int64Array) (start stop i : Nat) (h) :
    (a.extract start stop)[i]'h = a[start + i]'(by simp at h; omega) := by
  simp [-getElem_data, getElem_eq_getElem_data]

@[simp] public theorem getElem_replicate (n : Nat) (v : Int64) (i : Nat) (h) :
    (replicate n v)[i]'h = v := by
  simp [-getElem_data, getElem_eq_getElem_data]

@[simp] public theorem getElem_ofFn {n : Nat} (f : Fin n → Int64) (i : Nat) (h) :
    (ofFn f)[i]'h = f ⟨i, by simpa using h⟩ := by
  simp [-getElem_data, getElem_eq_getElem_data]

public theorem foldl_eq_foldl_data {β : Type v} (f : β → Int64 → β) (init : β)
    (a : Int64Array) :
    a.foldl f init = a.data.foldl f init := by
  rfl

public theorem foldr_eq_foldr_data {β : Type v} (f : Int64 → β → β) (init : β)
    (a : Int64Array) :
    a.foldr f init = a.data.foldr f init := by
  rfl

@[simp] public theorem toList_data (a : Int64Array) : a.data.toList = a.toList := rfl

@[simp] public theorem emptyc_eq_empty : (∅ : Int64Array) = empty := rfl

@[simp] public theorem emptyWithCapacity_eq_empty (c : Nat) : emptyWithCapacity c = empty := rfl

public theorem size_eq_zero_iff {a : Int64Array} : a.size = 0 ↔ a = empty := by
  simp [Int64Array.ext_iff, ← Array.size_eq_zero_iff]

@[simp] public theorem data_set! (a : Int64Array) (i : Nat) (v : Int64) :
    (a.set! i v).data = a.data.set! i v := by
  cases a; rfl

@[simp] public theorem size_set! (a : Int64Array) (i : Nat) (v : Int64) :
    (a.set! i v).size = a.size := by
  simp [-size_data, size_eq_data_size]

public theorem getElem!_eq_getElem!_data (a : Int64Array) (i : Nat) : a[i]! = a.data[i]! := by
  rcases a with ⟨a⟩
  by_cases h : i < a.size <;> simp [getElem!_def, getElem?_def, h] <;> rfl

@[simp] public theorem data_ofList (l : List Int64) : (ofList l).data = l.toArray := rfl

@[simp] public theorem size_ofList (l : List Int64) : (ofList l).size = l.length := rfl

@[simp] public theorem getElem_ofList (l : List Int64) (i : Nat) (h) :
    (ofList l)[i]'h = l[i]'(by simpa using h) := rfl

@[simp] public theorem toList_ofList (l : List Int64) : (ofList l).toList = l := rfl

@[simp] public theorem ofList_toList (a : Int64Array) : ofList a.toList = a := by
  simp [Int64Array.ext_iff, ← toList_data]

@[simp] public theorem markLinear_eq (a : Int64Array) : a.markLinear = a := rfl

@[simp] public theorem propagateMark_eq (a b : Int64Array) : a.propagateMark b = b := rfl

@[simp] public theorem append_empty (a : Int64Array) : a ++ empty = a := by
  simp [Int64Array.ext_iff]

@[simp] public theorem empty_append (a : Int64Array) : empty ++ a = a := by
  simp [Int64Array.ext_iff]

public theorem append_assoc (a b c : Int64Array) : a ++ b ++ c = a ++ (b ++ c) := by
  simp [Int64Array.ext_iff]

@[simp] public theorem append_eq_empty_iff {a b : Int64Array} :
    a ++ b = empty ↔ a = empty ∧ b = empty := by
  simp only [Int64Array.ext_iff, data_append, data_empty, Array.append_eq_empty_iff]

@[simp] public theorem append_right_inj (a : Int64Array) {b c : Int64Array} :
    a ++ b = a ++ c ↔ b = c := by
  simp only [Int64Array.ext_iff, data_append, Array.append_right_inj]

@[simp] public theorem append_left_inj {a b : Int64Array} (c : Int64Array) :
    a ++ c = b ++ c ↔ a = b := by
  simp only [Int64Array.ext_iff, data_append, Array.append_left_inj]

public theorem getElem_append_left {a b : Int64Array} {i : Nat} (h : i < a.size) :
    (a ++ b)[i]'(by simp; omega) = a[i] := by
  simp [h]

public theorem getElem_append_right {a b : Int64Array} {i : Nat} (h : a.size ≤ i)
    (h' : i < (a ++ b).size) : (a ++ b)[i] = b[i - a.size]'(by simp at h'; omega) := by
  simp [Nat.not_lt.mpr h]

@[simp] public theorem extract_same (a : Int64Array) (i : Nat) : a.extract i i = empty := by
  simp [Int64Array.ext_iff]; omega

@[simp] public theorem extract_zero_size (a : Int64Array) : a.extract 0 a.size = a := by
  simp [Int64Array.ext_iff]

@[simp] public theorem extract_eq_empty_iff {a : Int64Array} {i j : Nat} :
    a.extract i j = empty ↔ min j a.size ≤ i := by
  simp [Int64Array.ext_iff]

public theorem extract_extract (a : Int64Array) (i j k l : Nat) :
    (a.extract i j).extract k l = a.extract (i + k) (min (i + l) j) := by
  simp [Int64Array.ext_iff]

public theorem extract_append_extract (a : Int64Array) (i j k : Nat) :
    a.extract i j ++ a.extract j k = a.extract (min i j) (max j k) := by
  simp [Int64Array.ext_iff]

@[simp] public theorem extract_append_eq_left (a b : Int64Array) :
    (a ++ b).extract 0 a.size = a := by
  simp [Int64Array.ext_iff]

@[simp] public theorem extract_append_eq_right (a b : Int64Array) :
    (a ++ b).extract a.size (a.size + b.size) = b := by
  simp [Int64Array.ext_iff, -size_data, size_eq_data_size]

@[simp] public theorem data_copySlice (src : Int64Array) (srcOff : Nat) (dest : Int64Array)
    (destOff len : Nat) (exact : Bool) :
    (src.copySlice srcOff dest destOff len exact).data =
      dest.data.extract 0 destOff ++ src.data.extract srcOff (srcOff + len) ++
        dest.data.extract (destOff + min len (src.size - srcOff)) dest.size := by
  simp [copySlice]

public theorem copySlice_eq_append (src : Int64Array) (srcOff : Nat) (dest : Int64Array)
    (destOff len : Nat) (exact : Bool) :
    src.copySlice srcOff dest destOff len exact =
      dest.extract 0 destOff ++ src.extract srcOff (srcOff + len) ++
        dest.extract (destOff + min len (src.size - srcOff)) dest.size := by
  simp [Int64Array.ext_iff]

@[simp] public theorem Slice.size_copy (s : Int64Array.Slice) : s.copy.size = s.size := by
  have := s.stop_le_array_size
  simp only [Slice.copy, size_extract, Slice.size_eq]
  omega


end Int64Array

end ScalarArray

/-- The array with the elements of `l`. -/
@[inline, expose]
public def List.toInt64Array (l : List Int64) : ScalarArray.Int64Array :=
  ScalarArray.Int64Array.ofList l
