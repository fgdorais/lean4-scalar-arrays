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
# Arrays of `ISize`

`ScalarArray.ISizeArray` stores `ISize` values unboxed in a Lean runtime scalar array,
one machine word per element. Its logical model is `Array ISize`: `ISizeArray.mk` and
`ISizeArray.data` convert between the two, and every operation is specified by its effect on
the model.

Reads and in-place writes are inline C. `uset`, `set` and `push` update the array in place when it
is not shared and copy it otherwise, like `Array` and `ByteArray`.
-/

namespace ScalarArray

/--
Arrays of `ISize` values, stored unboxed in a scalar array, one machine word per element.

The logical model is an `Array ISize`. At runtime a `ISizeArray` is a `ScalarArray`, so every
function that looks inside the constructor must be `extern` or `implemented_by`.
-/
public inductive ISizeArray : Type
  | public mk (data : Array ISize)

namespace ISizeArray

-- `lean_byte_array_size` reads the size of any scalar array, whatever its element size.
@[extern "lean_byte_array_size", tagged_return, expose]
public def size : (a : @& ISizeArray) → Nat
  | mk a => a.size

/--
The size of `a` as a `USize`. Since `USize` can address all memory, no array has more elements than
`USize` can count.
-/
@[extern "lean_sarray_size", simp, expose]
public def usize (a : @& ISizeArray) : USize :=
  a.size.toUSize

@[extern c inline "((size_t*)lean_sarray_cptr(#1))[#2]", expose]
public def uget :
    (a : @& ISizeArray) → (i : USize) → (h : i.toNat < a.size := by get_elem_tactic) → ISize
  | mk a, i, h => a.uget i h

@[expose]
public def get :
    (a : @& ISizeArray) → (i : @& Nat) → (h : i < a.size := by get_elem_tactic) → ISize
  | mk a, i, h => a[i]

-- Public, like `mkImpl`, `usetImpl` and `setImpl` below: a private `implemented_by` target
-- attached with a separate `attribute` command is not visible to other modules, so code there
-- that uses `get`, `mk`, `uset` or `set` would fail to compile.
@[inline]
public unsafe def getImpl : type_of% @get :=
  fun a i _ => a.uget i.toUSize lcProof

attribute [implemented_by getImpl] get

/--
Stores `v` at index `i` in place. Only valid when `a` is exclusive and `i` is in bounds. Public only
so that `uset` can be inlined into code in other modules.
-/
@[extern c inline "#1;\n((size_t*)lean_sarray_cptr(#1))[#2] = #3"]
public unsafe def setUnsafe : ISizeArray → USize → ISize → ISizeArray
  | .mk a, i, v => .mk <| a.uset i v lcProof

/--
`a` itself when it is not shared, and a copy otherwise. Public only so that `uset` can be inlined
into code in other modules.
-/
-- The same runtime function as the private `ScalarArray.ensureExclusive`, which code in other
-- modules can't reach.
@[extern "lean_sarray_ensure_exclusive"]
public unsafe def ensureExclusiveUnsafe (a : ISizeArray) : ISizeArray := a

private unsafe def toUSizeChecked (n : Nat) : USize :=
  if n < USize.size >>> 1 then n.toUSize else panic! "out of memory"

/-- A new array of size `size` with room for `capacity` elements. Requires `size ≤ capacity`. -/
private unsafe def allocUnsafe (size capacity : USize) : ISizeArray :=
  unsafeCast <| ScalarArray.allocate (System.Platform.numBits / 8).toUInt32 size capacity lcProof

private unsafe def mkWithCapacityImpl (a : Array ISize) (capacity : Nat := a.size) :
    ISizeArray :=
  let cap := toUSizeChecked capacity
  let sz := toUSizeChecked a.size
  let r := allocUnsafe sz (max sz cap)
  loop sz r 0
where
  loop (sz : USize) (r : ISizeArray) (i : USize) : ISizeArray :=
    if i < sz then loop sz (setUnsafe r i (a.uget i lcProof)) (i + 1) else r

public unsafe def mkImpl (a : Array ISize) : ISizeArray :=
  mkWithCapacityImpl a a.size

attribute [implemented_by mkImpl] ISizeArray.mk

private unsafe def dataImpl (a : @& ISizeArray) : Array ISize :=
  loop a.usize 0 (Array.replicate a.size default)
where
  loop (sz i : USize) (r : Array ISize) : Array ISize :=
    if i < sz then loop sz (i + 1) (r.uset i (a.uget i lcProof) lcProof) else r

/-- The elements of `a` as an `Array ISize`. -/
@[implemented_by dataImpl, expose]
public def data : (a : @& ISizeArray) → Array ISize
  | mk a => a

private unsafe def emptyWithCapacityImpl (capacity : Nat) : ISizeArray :=
  mkWithCapacityImpl #[] capacity

/-- An empty array with room for `capacity` elements before reallocating. -/
@[implemented_by emptyWithCapacityImpl, expose]
public def emptyWithCapacity (capacity : Nat) : ISizeArray :=
  mk #[]

@[expose] public def empty : ISizeArray := emptyWithCapacity 0

public instance : EmptyCollection ISizeArray := ⟨empty⟩

public instance : Inhabited ISizeArray := ⟨empty⟩

/--
Replaces the element at index `i`, in place when `a` is not shared. It compiles to inline C: one
check that `a` is exclusive, copying it if not, and one store.
-/
@[expose]
public def uset :
    (a : ISizeArray) → (i : USize) → (v : ISize) →
    (h : i.toNat < a.size := by get_elem_tactic) → ISizeArray
  | mk a, i, v, h => mk (a.uset i v h)

-- Inline, and made of public inline externs, so that it compiles to inline C in other modules.
@[inline]
public unsafe def usetImpl : type_of% @uset :=
  fun a i v _ => setUnsafe (ensureExclusiveUnsafe a) i v

attribute [implemented_by usetImpl] uset

@[expose]
public def set :
    (a : ISizeArray) → (i : Nat) → (v : ISize) → (h : i < a.size := by get_elem_tactic) →
    ISizeArray
  | mk a, i, v, h => mk (a.set i v h)

@[inline]
public unsafe def setImpl : type_of% @set :=
  fun a i v _ => a.uset i.toUSize v lcProof

attribute [implemented_by setImpl] set

@[expose]
public def get! (a : @& ISizeArray) (i : @& Nat) : ISize :=
  if h : i < a.size then a.get i h else panic! "index out of bounds"

@[expose]
public def getD (a : @& ISizeArray) (i : @& Nat) (v₀ : ISize) : ISize :=
  if h : i < a.size then a.get i h else v₀

private unsafe def setBangImpl (a : ISizeArray) (i : Nat) (v : ISize) : ISizeArray :=
  if h : i < a.size then setImpl a i v h else a

/-- Replaces the element at index `i`. If `i` is out of bounds, the array is returned unmodified. -/
@[implemented_by setBangImpl, expose]
public def set! : ISizeArray → Nat → ISize → ISizeArray
  | mk a, i, v => mk (a.set! i v)

public instance : GetElem ISizeArray Nat ISize fun a i => i < a.size where
  getElem a i h := a.get i h

public instance : GetElem ISizeArray USize ISize fun a i => i.toNat < a.size where
  getElem a i h := a.uget i h

private unsafe def pushImpl (a : ISizeArray) (v : ISize) : ISizeArray :=
  let s : ScalarArray := unsafeCast a
  let cap := s.capacity
  if s.size < cap then
    loop s.ensureExclusive
  else if cap < cap + cap + 1 then
    loop (s.copyWithCapacity (cap + cap + 1) lcProof)
  else
    panic! "out of memory"
where
  loop (s : ScalarArray) : ISizeArray :=
    let i := s.size
    setUnsafe (unsafeCast (s.resizeUnsafe (i + 1) lcProof lcProof)) i v

@[implemented_by pushImpl, expose]
public def push : ISizeArray → ISize → ISizeArray
  | mk a, v => mk (a.push v)

/--
Copies `n` bytes of the data of `src`, starting at byte `srcOff`, into the data of `dest`, starting
at byte `destOff`. Only valid when `dest` is exclusive and both ranges are within the capacities.
-/
-- TODO: core has no runtime function that copies a slice of a scalar array with any element size;
-- `lean_byte_array_copy_slice` only works for bytes. Replace this once core has one.
@[extern c inline "#1;\n__builtin_memcpy(lean_sarray_cptr(#1) + #4, lean_sarray_cptr(#2) + #3, #5)"]
private unsafe def memcpyUnsafe :
    ISizeArray → @& ISizeArray → (srcOff destOff n : USize) → ISizeArray
  | dest, _, _, _, _ => dest

/--
Copies the `n` elements of `src` starting at index `srcOff` into `dest` starting at index `destOff`,
in place, and grows the size of `dest` to `destOff + n` if it is smaller. Only valid when `dest` is
exclusive, has capacity for `destOff + n` elements, and is not the same object as `src`, and when
`destOff ≤ dest.size` and `srcOff + n ≤ src.size`.
-/
@[inline]
private unsafe def copySliceUnsafe (dest : ISizeArray) (src : @& ISizeArray)
    (srcOff destOff n : USize) : ISizeArray :=
  let esz := (unsafeCast src : ScalarArray).elemSize.toUSize
  let d : ScalarArray := unsafeCast (memcpyUnsafe dest src (srcOff * esz) (destOff * esz) (n * esz))
  unsafeCast (d.resizeUnsafe (max d.size (destOff + n)) lcProof lcProof)

private unsafe def appendImpl (a b : ISizeArray) : ISizeArray :=
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
public def append : ISizeArray → ISizeArray → ISizeArray
  | mk a, mk b => mk (a ++ b)

public instance : Append ISizeArray := ⟨append⟩

private unsafe def copySliceImpl (src : @& ISizeArray) (srcOff : Nat) (dest : ISizeArray)
    (destOff len : Nat) (exact : Bool := true) : ISizeArray :=
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
public def copySlice (src : @& ISizeArray) (srcOff : Nat) (dest : ISizeArray)
    (destOff len : Nat) (exact : Bool := true) : ISizeArray :=
  mk (dest.data.extract 0 destOff ++ src.data.extract srcOff (srcOff + len) ++
    dest.data.extract (destOff + min len (src.data.size - srcOff)) dest.data.size)

/-! ## Removing elements -/

@[expose] public def isEmpty (a : @& ISizeArray) : Bool := a.size == 0

private unsafe def popImpl (a : ISizeArray) : ISizeArray :=
  if a.size == 0 then
    a
  else
    let s : ScalarArray := ScalarArray.ensureExclusive (unsafeCast a)
    unsafeCast (s.resizeUnsafe (s.size - 1) lcProof lcProof)

/-- Removes the last element of `a`, if any, in place when `a` is not shared. -/
@[implemented_by popImpl, expose]
public def pop : ISizeArray → ISizeArray
  | mk a => mk a.pop

public def back? (a : @& ISizeArray) : Option ISize := a[a.size - 1]?

public def back! (a : @& ISizeArray) : ISize := a[a.size - 1]!

public def back (a : @& ISizeArray) (h : 0 < a.size) : ISize :=
  a[a.size - 1]'(Nat.sub_lt h Nat.one_pos)

private def popWhileImpl (p : ISize → Bool) (a : ISizeArray) : ISizeArray :=
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
public def popWhile (p : ISize → Bool) : ISizeArray → ISizeArray
  | mk a => mk (a.popWhile p)

private unsafe def extractImpl (a : @& ISizeArray) (start stop : Nat) : ISizeArray :=
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
public def extract : (a : @& ISizeArray) → (start stop : Nat) → ISizeArray
  | mk a, start, stop => mk (a.extract start stop)

/-! ## Linearity -/

/--
Marks `a` as linear, a debugging aid: if a marked array is ever shared and then modified, the
runtime reports it. Logically this is the identity.
-/
@[never_extract, extern "lean_sarray_mark_linear", expose]
public def markLinear (a : ISizeArray) : ISizeArray := a

/-- Returns `b`, marking it as linear if `a` is marked. Logically this is `b`. -/
@[never_extract, extern "lean_sarray_propagate_mark", expose]
public def propagateMark (a : @& ISizeArray) (b : ISizeArray) : ISizeArray := b

/-! ## Search -/

/--
The index of the first element at or after `start` that satisfies `p`, with a proof that it is in
bounds.
-/
@[inline]
public def findFinIdx? (a : ISizeArray) (p : ISize → Bool) (start := 0) : Option (Fin a.size) :=
  let rec @[specialize] loop (i : Nat) :=
    if h : i < a.size then
      if p a[i] then some ⟨i, h⟩ else loop (i + 1)
    else
      none
    termination_by a.size - i
  loop start

/-- The index of the first element at or after `start` that satisfies `p`. -/
@[inline]
public def findIdx? (a : ISizeArray) (p : ISize → Bool) (start := 0) : Option Nat :=
  let rec @[specialize] loop (i : Nat) :=
    if h : i < a.size then
      if p a[i] then some i else loop (i + 1)
    else
      none
    termination_by a.size - i
  loop start

/-! ## Building arrays -/

private unsafe def replicateImpl (n : Nat) (v : ISize) : ISizeArray :=
  let sz := toUSizeChecked n
  loop sz (allocUnsafe sz sz) 0
where
  loop (sz : USize) (r : ISizeArray) (i : USize) : ISizeArray :=
    if i < sz then loop sz (setUnsafe r i v) (i + 1) else r

/-- An array of `n` copies of `v`. -/
@[implemented_by replicateImpl, expose]
public def replicate (n : Nat) (v : ISize) : ISizeArray :=
  mk (Array.replicate n v)

private unsafe def ofFnImpl {n : Nat} (f : Fin n → ISize) : ISizeArray :=
  let sz := toUSizeChecked n
  loop (allocUnsafe sz sz) 0
where
  loop (r : ISizeArray) (i : Nat) : ISizeArray :=
    if h : i < n then loop (setUnsafe r i.toUSize (f ⟨i, h⟩)) (i + 1) else r

/-- The array `#[f 0, …, f (n - 1)]`. -/
@[implemented_by ofFnImpl, expose]
public def ofFn {n : Nat} (f : Fin n → ISize) : ISizeArray :=
  mk (Array.ofFn f)

private unsafe def ofListImpl (l : List ISize) : ISizeArray :=
  loop l (emptyWithCapacity l.length)
where
  loop : List ISize → ISizeArray → ISizeArray
    | [], r => r
    | x :: xs, r => loop xs (r.push x)

/-- The array with the elements of `l`. -/
@[implemented_by ofListImpl, expose]
public def ofList (l : List ISize) : ISizeArray :=
  mk l.toArray

/-! ## Iteration -/

@[specialize]
private unsafe def foldlMImpl {β : Type v} {m : Type v → Type w} [Monad m] (f : β → ISize → m β)
    (init : β) (a : @& ISizeArray) (start := 0) (stop := a.size) : m β :=
  let stop := min stop a.size
  if start < stop then loop stop.toUSize start.toUSize init else pure init
where
  @[specialize] loop (stop i : USize) (b : β) : m β :=
    if i < stop then do loop stop (i + 1) (← f b (a.uget i lcProof)) else pure b

/--
Folds a monadic function over the elements of `a` from index `start` up to, but not including,
`stop`, from first to last.
-/
@[implemented_by foldlMImpl, expose]
public def foldlM {β : Type v} {m : Type v → Type w} [Monad m] (f : β → ISize → m β) (init : β)
    (a : @& ISizeArray) (start := 0) (stop := a.size) : m β :=
  a.data.foldlM f init start stop

@[specialize]
private unsafe def foldrMImpl {β : Type v} {m : Type v → Type w} [Monad m] (f : ISize → β → m β)
    (init : β) (a : @& ISizeArray) : m β :=
  loop a.usize init
where
  @[specialize] loop (i : USize) (b : β) : m β :=
    if 0 < i then do loop (i - 1) (← f (a.uget (i - 1) lcProof) b) else pure b

/-- Folds a monadic function over the elements of `a`, from last to first. -/
@[implemented_by foldrMImpl, expose]
public def foldrM {β : Type v} {m : Type v → Type w} [Monad m] (f : ISize → β → m β) (init : β)
    (a : @& ISizeArray) : m β :=
  a.data.foldrM f init

@[inline, expose]
public def foldl {β : Type v} (f : β → ISize → β) (init : β) (a : @& ISizeArray) (start := 0)
    (stop := a.size) : β :=
  Id.run <| a.foldlM (pure <| f · ·) init start stop

@[inline, expose]
public def foldr {β : Type v} (f : ISize → β → β) (init : β) (a : @& ISizeArray) : β :=
  Id.run <| a.foldrM (pure <| f · ·) init

@[inline, expose]
public def forM {m : Type v → Type w} [Monad m] (f : ISize → m PUnit) (a : @& ISizeArray) :
    m PUnit :=
  a.foldlM (fun _ x => f x) ⟨⟩

@[specialize]
private unsafe def forInImpl {β : Type v} {m : Type v → Type w} [Monad m] (a : @& ISizeArray)
    (init : β) (f : ISize → β → m (ForInStep β)) : m β :=
  loop a.usize 0 init
where
  @[specialize] loop (stop i : USize) (b : β) : m β :=
    if i < stop then do
      match ← f (a.uget i lcProof) b with
      | .done b => pure b
      | .yield b => loop stop (i + 1) b
    else pure b

@[implemented_by forInImpl, expose]
public def forIn {β : Type v} {m : Type v → Type w} [Monad m] (a : @& ISizeArray) (init : β)
    (f : ISize → β → m (ForInStep β)) : m β :=
  ForIn.forIn a.data init f

public instance [Monad m] : ForIn m ISizeArray ISize where
  forIn a b f := ISizeArray.forIn a b f

public instance [Monad m] : ForM m ISizeArray ISize where
  forM a f := a.forM f

@[specialize]
private unsafe def anyImpl (a : @& ISizeArray) (p : ISize → Bool) : Bool :=
  loop a.usize 0
where
  @[specialize] loop (stop i : USize) : Bool :=
    if i < stop then p (a.uget i lcProof) || loop stop (i + 1) else false

/-- Whether some element of `a` satisfies `p`. -/
@[implemented_by anyImpl, expose]
public def any (a : @& ISizeArray) (p : ISize → Bool) : Bool :=
  a.data.any p

@[specialize]
private unsafe def allImpl (a : @& ISizeArray) (p : ISize → Bool) : Bool :=
  loop a.usize 0
where
  @[specialize] loop (stop i : USize) : Bool :=
    if i < stop then p (a.uget i lcProof) && loop stop (i + 1) else true

/-- Whether every element of `a` satisfies `p`. -/
@[implemented_by allImpl, expose]
public def all (a : @& ISizeArray) (p : ISize → Bool) : Bool :=
  a.data.all p

private unsafe def containsImpl (a : @& ISizeArray) (v : ISize) : Bool :=
  anyImpl a (v == ·)

/-- Whether `v` is an element of `a`. -/
@[implemented_by containsImpl, expose]
public def contains (a : @& ISizeArray) (v : ISize) : Bool :=
  a.data.contains v

/-- `x ∈ a` when `x` is an element of `a`. -/
public instance : Membership ISize ISizeArray where
  mem a x := x ∈ a.data

/-! ## Equality and hashing -/

private theorem data_injective : {a b : ISizeArray} → a.data = b.data → a = b
  | mk _, mk _, rfl => rfl

/-- Decides equality by comparing the two arrays' memory. -/
@[extern "lean_sarray_dec_eq", expose]
public def decEq (a b : @& ISizeArray) : Decidable (a = b) :=
  decidable_of_iff (a.data = b.data) ⟨fun h => by cases a; cases b; cases h; rfl, fun h => h ▸ rfl⟩

public instance : DecidableEq ISizeArray := decEq

private unsafe def hashImpl (a : @& ISizeArray) : UInt64 :=
  foldlMImpl (m := Id) (fun r x => mixHash r (Hashable.hash x)) 7 a

/-- The same hash as `a.data`. -/
@[implemented_by hashImpl]
public def hash (a : @& ISizeArray) : UInt64 :=
  Hashable.hash a.data

public instance : Hashable ISizeArray := ⟨hash⟩

public theorem hash_eq_hash_data (a : ISizeArray) : Hashable.hash a = Hashable.hash a.data := by
  rfl

/-! ## Conversion and printing -/

@[expose] public def toList (a : ISizeArray) : List ISize := a.data.toList

public instance : Repr ISizeArray where
  reprPrec a _ := "ISizeArray.mk " ++ repr a.data

public instance : ToString ISizeArray where
  toString a := "ISizeArray.mk " ++ toString a.data

/-! ## Slices -/

/-- Internal representation of `ISizeArray.Slice`. -/
public protected structure SliceData where
  /-- The underlying array. -/
  array : ISizeArray
  /-- The starting index of the slice (inclusive). -/
  start : Nat
  /-- The ending index of the slice (exclusive). -/
  stop : Nat
  /-- The starting index is no later than the ending index. -/
  start_le_stop : start ≤ stop
  /-- The ending index is no later than the end of the array. -/
  stop_le_array_size : stop ≤ array.size

/--
A region of a `ISizeArray`: the elements from index `start` up to, but not including, `stop`.
Taking a slice doesn't copy the array. Slices are written with core's slice notation, such as
`a[i...j]`, `a[i...*]` or `a[*...j]`.
-/
public protected abbrev Slice := Std.Slice ISizeArray.SliceData

public instance : Std.Slice.Self (Std.Slice ISizeArray.SliceData) ISizeArray.Slice where

namespace Slice

@[always_inline, inline, expose, inherit_doc SliceData.array]
public def array (s : ISizeArray.Slice) : ISizeArray := s.internalRepresentation.array

@[always_inline, inline, expose, inherit_doc SliceData.start]
public def start (s : ISizeArray.Slice) : Nat := s.internalRepresentation.start

@[always_inline, inline, expose, inherit_doc SliceData.stop]
public def stop (s : ISizeArray.Slice) : Nat := s.internalRepresentation.stop

@[inherit_doc SliceData.start_le_stop]
public theorem start_le_stop (s : ISizeArray.Slice) : s.start ≤ s.stop :=
  s.internalRepresentation.start_le_stop

@[inherit_doc SliceData.stop_le_array_size]
public theorem stop_le_array_size (s : ISizeArray.Slice) : s.stop ≤ s.array.size :=
  s.internalRepresentation.stop_le_array_size

public instance : Std.Slice.SliceSize ISizeArray.SliceData where
  size s := s.internalRepresentation.stop - s.internalRepresentation.start

public theorem size_eq (s : ISizeArray.Slice) : s.size = s.stop - s.start := rfl

/-- The element at index `i` of the slice, counted from the start of the slice. -/
@[inline, expose]
public def get (s : ISizeArray.Slice) (i : Nat) (h : i < s.size := by get_elem_tactic) :
    ISize :=
  s.array[s.start + i]'(by have := s.stop_le_array_size; rw [size_eq] at h; omega)

public instance : GetElem ISizeArray.Slice Nat ISize fun s i => i < s.size where
  getElem s i h := s.get i h

/-- The element at index `i` of the slice, or `v₀` if `i` is out of bounds. -/
@[inline]
public def getD (s : ISizeArray.Slice) (i : Nat) (v₀ : ISize) : ISize :=
  if h : i < s.size then s[i] else v₀

/-- The element at index `i` of the slice, or `default` if `i` is out of bounds. -/
public abbrev get! (s : ISizeArray.Slice) (i : Nat) : ISize :=
  getD s i default

/-- Removes the first element of the slice, if any. -/
@[expose]
public def popFront (s : ISizeArray.Slice) : ISizeArray.Slice :=
  if h : s.start < s.stop then
    ⟨{ s.internalRepresentation with start := s.start + 1, start_le_stop := h }⟩
  else
    s

/-- The empty slice, backed by an empty array. -/
@[expose]
public protected def empty : ISizeArray.Slice :=
  ⟨{ array := ISizeArray.empty, start := 0, stop := 0, start_le_stop := Nat.le_refl 0,
     stop_le_array_size := Nat.le_refl 0 }⟩

public instance : EmptyCollection ISizeArray.Slice := ⟨Slice.empty⟩

public instance : Inhabited ISizeArray.Slice := ⟨Slice.empty⟩

/-- The elements of the slice, copied into a new array with a single `memcpy`. -/
@[expose]
public def copy (s : ISizeArray.Slice) : ISizeArray :=
  s.array.extract s.start s.stop

public theorem getElem_eq (s : ISizeArray.Slice) (i : Nat) (h : i < s.size) :
    s[i] = s.array[s.start + i]'(by have := s.stop_le_array_size; rw [size_eq] at h; omega) := rfl

public instance : Repr ISizeArray.Slice where
  reprPrec s _ := repr s.copy ++ ".toSlice"

public instance : ToString ISizeArray.Slice where
  toString s := toString s.copy

end Slice

/--
The slice of `a` from index `start` up to, but not including, `stop`. If `start` or `stop` are not
valid bounds, they are clamped to the size of `a`, and `start` is clamped to `stop`.
-/
@[expose]
public def toSlice (a : ISizeArray) (start : Nat := 0) (stop : Nat := a.size) :
    ISizeArray.Slice :=
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
public instance : Coe ISizeArray ISizeArray.Slice := ⟨(·.toSlice)⟩

public instance : Std.Rcc.Sliceable ISizeArray Nat ISizeArray.Slice where
  mkSlice a range := a.toSlice range.lower (range.upper + 1)

public instance : Std.Rco.Sliceable ISizeArray Nat ISizeArray.Slice where
  mkSlice a range := a.toSlice range.lower range.upper

public instance : Std.Rci.Sliceable ISizeArray Nat ISizeArray.Slice where
  mkSlice a range := a.toSlice range.lower

public instance : Std.Roc.Sliceable ISizeArray Nat ISizeArray.Slice where
  mkSlice a range := a.toSlice (range.lower + 1) (range.upper + 1)

public instance : Std.Roo.Sliceable ISizeArray Nat ISizeArray.Slice where
  mkSlice a range := a.toSlice (range.lower + 1) range.upper

public instance : Std.Roi.Sliceable ISizeArray Nat ISizeArray.Slice where
  mkSlice a range := a.toSlice (range.lower + 1)

public instance : Std.Ric.Sliceable ISizeArray Nat ISizeArray.Slice where
  mkSlice a range := a.toSlice 0 (range.upper + 1)

public instance : Std.Rio.Sliceable ISizeArray Nat ISizeArray.Slice where
  mkSlice a range := a.toSlice 0 range.upper

public instance : Std.Rii.Sliceable ISizeArray Nat ISizeArray.Slice where
  mkSlice a _ := a.toSlice

namespace Slice

/-- The slice of `s` from index `start` up to, but not including, `stop`, clamped like `toSlice`. -/
@[expose]
public def slice (s : ISizeArray.Slice) (start : Nat := 0) (stop : Nat := s.size) :
    ISizeArray.Slice :=
  s.array.toSlice (s.start + min start s.size) (s.start + min stop s.size)

end Slice

public instance : Std.Rcc.Sliceable ISizeArray.Slice Nat ISizeArray.Slice where
  mkSlice s range := s.slice range.lower (range.upper + 1)

public instance : Std.Rco.Sliceable ISizeArray.Slice Nat ISizeArray.Slice where
  mkSlice s range := s.slice range.lower range.upper

public instance : Std.Rci.Sliceable ISizeArray.Slice Nat ISizeArray.Slice where
  mkSlice s range := s.slice range.lower

public instance : Std.Roc.Sliceable ISizeArray.Slice Nat ISizeArray.Slice where
  mkSlice s range := s.slice (range.lower + 1) (range.upper + 1)

public instance : Std.Roo.Sliceable ISizeArray.Slice Nat ISizeArray.Slice where
  mkSlice s range := s.slice (range.lower + 1) range.upper

public instance : Std.Roi.Sliceable ISizeArray.Slice Nat ISizeArray.Slice where
  mkSlice s range := s.slice (range.lower + 1)

public instance : Std.Ric.Sliceable ISizeArray.Slice Nat ISizeArray.Slice where
  mkSlice s range := s.slice 0 (range.upper + 1)

public instance : Std.Rio.Sliceable ISizeArray.Slice Nat ISizeArray.Slice where
  mkSlice s range := s.slice 0 range.upper

public instance : Std.Rii.Sliceable ISizeArray.Slice Nat ISizeArray.Slice where
  mkSlice s _ := s

/-- The iterator over the elements of a slice, used for `for` loops and the generic slice API. -/
public protected structure SliceIterator where
  /-- The rest of the slice. -/
  xs : ISizeArray.Slice

@[inline, expose]
public def SliceIterator.step :
    Std.IterM (α := ISizeArray.SliceIterator) Id ISize →
      Std.IterStep (Std.IterM (α := ISizeArray.SliceIterator) m ISize) ISize
  | ⟨⟨xs⟩⟩ =>
    if h : xs.start < xs.stop then
      have := xs.stop_le_array_size
      .yield ⟨⟨⟨xs.array, xs.start + 1, xs.stop, h, xs.stop_le_array_size⟩⟩⟩ xs.array[xs.start]
    else
      .done

public instance : Std.Iterator ISizeArray.SliceIterator Id ISize where
  IsPlausibleStep it step := step = SliceIterator.step it
  step it := pure <| .deflate ⟨SliceIterator.step it, rfl⟩

private def SliceIterator.finitenessRelation :
    Std.Iterators.FinitenessRelation ISizeArray.SliceIterator Id where
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

public instance : Std.Iterators.Finite ISizeArray.SliceIterator Id :=
  .of_finitenessRelation SliceIterator.finitenessRelation

-- Each element goes through `lift`, like each step of the iterator in the default implementation,
-- so the two agree for every lawful `lift`, which is what core's consumers pass.
@[specialize]
private unsafe def SliceIterator.forInImpl {n : Type x → Type x'} [Monad n]
    (lift : (γ : Type) → (δ : Type x) → (γ → n δ) → Id γ → n δ) (γ : Type x)
    (Pl : ISize → γ → ForInStep γ → Prop)
    (it : Std.IterM (α := ISizeArray.SliceIterator) Id ISize) (init : γ)
    (f : (b : ISize) → it.IsPlausibleIndirectOutput b → (c : γ) → n (Subtype (Pl b c))) :
    n γ :=
  let xs := it.internalState.xs
  loop xs.array xs.stop.toUSize xs.start.toUSize init
where
  @[specialize] loop (a : ISizeArray) (stop i : USize) (c : γ) : n γ :=
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
    (Pl : ISize → γ → ForInStep γ → Prop)
    (it : Std.IterM (α := ISizeArray.SliceIterator) Id ISize) (init : γ)
    (f : (b : ISize) → it.IsPlausibleIndirectOutput b → (c : γ) → n (Subtype (Pl b c))) :
    n γ :=
  Std.IteratorLoop.defaultImplementation.forIn lift γ Pl it init f

public instance [Monad m] : Std.IteratorLoop ISizeArray.SliceIterator Id m where
  forIn := SliceIterator.forIn

public instance [Monad m] : Std.LawfulIteratorLoop ISizeArray.SliceIterator Id m where
  lawful _ _ _ _ _ _ _ _ := rfl

public instance :
    Std.ToIterator (Std.Slice ISizeArray.SliceData) Id ISizeArray.SliceIterator ISize :=
  Std.ToIterator.of ISizeArray.SliceIterator (⟨⟨·⟩⟩)

public instance [Monad m] : ForIn m ISizeArray.Slice ISize := inferInstance

public instance [Monad m] : ForM m ISizeArray.Slice ISize where
  forM s f := s.foldlM (fun _ x => f x) ⟨⟩

/-- An iterator over the elements of `a`, for use with the `Std.Iterators` API. -/
@[inline, expose]
public def iter (a : ISizeArray) : Std.Iter (α := ISizeArray.SliceIterator) ISize :=
  a.toSlice.iter

namespace Slice

@[specialize]
private unsafe def foldrMImpl {β : Type v} {m : Type v → Type w} [Monad m]
    (f : ISize → β → m β) (init : β) (s : ISizeArray.Slice) : m β :=
  loop s.array s.start.toUSize s.stop.toUSize init
where
  @[specialize] loop (a : ISizeArray) (start i : USize) (b : β) : m β :=
    if start < i then do loop a start (i - 1) (← f (a.uget (i - 1) lcProof) b) else pure b

/-- Folds a monadic function over the elements of `s`, from last to first. -/
@[implemented_by foldrMImpl, expose]
public def foldrM {β : Type v} {m : Type v → Type w} [Monad m] (f : ISize → β → m β) (init : β)
    (s : ISizeArray.Slice) : m β :=
  loop s.size (Nat.le_refl _) init
where
  @[specialize] loop : (i : Nat) → i ≤ s.size → β → m β
    | 0, _, b => pure b
    | i + 1, h, b => do loop i (Nat.le_of_succ_le h) (← f s[i] b)

/-- Folds a function over the elements of `s`, from last to first. -/
@[inline, expose]
public def foldr {β : Type v} (f : ISize → β → β) (init : β) (s : ISizeArray.Slice) : β :=
  Id.run <| s.foldrM (pure <| f · ·) init

/-- Runs a monadic action on each element of `s`, from last to first. -/
@[inline, expose]
public def forRevM {m : Type v → Type w} [Monad m] (f : ISize → m PUnit)
    (s : ISizeArray.Slice) : m PUnit :=
  s.foldrM (fun x _ => f x) ⟨⟩

@[specialize]
private unsafe def findSomeRevMImpl {β : Type v} {m : Type v → Type w} [Monad m]
    (s : ISizeArray.Slice) (f : ISize → m (Option β)) : m (Option β) :=
  loop s.array s.start.toUSize s.stop.toUSize
where
  @[specialize] loop (a : ISizeArray) (start i : USize) : m (Option β) :=
    if start < i then do
      match ← f (a.uget (i - 1) lcProof) with
      | some b => pure (some b)
      | none => loop a start (i - 1)
    else pure none

/-- The result of the last element of `s` for which `f` returns `some`, searching from the end. -/
@[implemented_by findSomeRevMImpl, expose]
public def findSomeRevM? {β : Type v} {m : Type v → Type w} [Monad m] (s : ISizeArray.Slice)
    (f : ISize → m (Option β)) : m (Option β) :=
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
public def findRevM? {m : Type → Type w} [Monad m] (s : ISizeArray.Slice) (p : ISize → m Bool) :
    m (Option ISize) :=
  s.findSomeRevM? fun x => return if (← p x) then some x else none

/-- The last element of `s` that satisfies `p`. -/
@[inline, expose]
public def findRev? (s : ISizeArray.Slice) (p : ISize → Bool) : Option ISize :=
  Id.run <| s.findRevM? (pure <| p ·)

/-- The first element of `s` that satisfies `p`. -/
@[inline, expose]
public def find? (s : ISizeArray.Slice) (p : ISize → Bool) : Option ISize :=
  s.iter.find? p

/-- Whether some element of `s` satisfies `p`. -/
@[inline, expose]
public def any (s : ISizeArray.Slice) (p : ISize → Bool) : Bool :=
  s.iter.any p

/-- Whether every element of `s` satisfies `p`. -/
@[inline, expose]
public def all (s : ISizeArray.Slice) (p : ISize → Bool) : Bool :=
  s.iter.all p

/-- Whether `v` is an element of `s`. -/
@[inline, expose]
public def contains (s : ISizeArray.Slice) (v : ISize) : Bool :=
  s.any (v == ·)

/-- The number of elements of `s` that satisfy `p`. -/
@[inline, expose]
public def count (s : ISizeArray.Slice) (p : ISize → Bool) : Nat :=
  s.iter.fold (fun n x => if p x then n + 1 else n) 0

/-- `x ∈ s` when `x` is an element of `s`. -/
public instance : Membership ISize ISizeArray.Slice where
  mem s x := x ∈ s.copy

private unsafe def beqImpl (s t : ISizeArray.Slice) : Bool :=
  s.size == t.size && loop s.array t.array s.stop.toUSize s.start.toUSize t.start.toUSize
where
  loop (a b : ISizeArray) (stop i j : USize) : Bool :=
    if i < stop then a.uget i lcProof == b.uget j lcProof && loop a b stop (i + 1) (j + 1)
    else true

/--
Compares the elements of two slices with `==`: slices of different arrays, or at different offsets,
are equal when their elements are. Logically it compares the copies.
-/
-- There is no `DecidableEq` instance: structural equality of slices compares the underlying arrays
-- and the bounds, so it would disagree with `==`.
@[implemented_by beqImpl]
public def beq (s t : ISizeArray.Slice) : Bool :=
  s.copy == t.copy

public instance : BEq ISizeArray.Slice := ⟨beq⟩

end Slice

/--
Collects the values emitted by an iterator into a new array. Together with the `Std.Iterators`
combinators, this gives functions such as `map`, `filter`, `take` and `zipWith`, for example
`(a.iter.map (· + 1)).toISizeArray`.
-/
@[inline, expose]
public def _root_.Std.Iter.toISizeArray {α : Type} [Std.Iterator α Id ISize]
    [Std.IteratorLoop α Id Id] (it : Std.Iter (α := α) ISize) : ISizeArray :=
  it.fold (·.push ·) empty

/-- Like `Std.Iter.toISizeArray`, but the new array starts with room for `capacity` elements. -/
@[inline, expose]
public def _root_.Std.Iter.toISizeArrayWithCapacity {α : Type} [Std.Iterator α Id ISize]
    [Std.IteratorLoop α Id Id] (it : Std.Iter (α := α) ISize) (capacity : Nat) : ISizeArray :=
  it.fold (·.push ·) (emptyWithCapacity capacity)

@[simp] public theorem _root_.Std.Iter.toISizeArrayWithCapacity_eq {α : Type}
    [Std.Iterator α Id ISize] [Std.IteratorLoop α Id Id] (it : Std.Iter (α := α) ISize)
    (capacity : Nat) : it.toISizeArrayWithCapacity capacity = it.toISizeArray := rfl

@[simp] public theorem size_mk (a : Array ISize) : (mk a).size = a.size := rfl

@[simp] public theorem data_mk (a : Array ISize) : (mk a).data = a := rfl

@[simp] public theorem mk_data (a : ISizeArray) : mk a.data = a := by cases a; rfl

public theorem size_eq_data_size (a : ISizeArray) : a.size = a.data.size := by cases a; rfl

@[simp] public theorem size_data (a : ISizeArray) : a.data.size = a.size :=
  (size_eq_data_size a).symm

@[simp] public theorem size_uset (a : ISizeArray) (i : USize) (v : ISize) (h) :
    (a.uset i v h).size = a.size := by
  cases a; exact Array.size_set ..

@[simp] public theorem size_set (a : ISizeArray) (i : Nat) (v : ISize) (h) :
    (a.set i v h).size = a.size := by
  cases a; exact Array.size_set ..

@[simp] public theorem size_push (a : ISizeArray) (v : ISize) :
    (a.push v).size = a.size + 1 := by
  cases a; simp [push, size]

@[simp] public theorem data_append (a b : ISizeArray) : (a ++ b).data = a.data ++ b.data := by
  cases a; cases b; rfl

@[simp] public theorem size_append (a b : ISizeArray) : (a ++ b).size = a.size + b.size := by
  simp [-size_data, size_eq_data_size]

@[ext] public theorem ext {a b : ISizeArray} (h : a.data = b.data) : a = b := data_injective h

@[simp] public theorem getElem_mk (a : Array ISize) (i : Nat) (h : i < (mk a).size) :
    (mk a)[i] = a[i] := rfl

public theorem getElem_eq_getElem_data (a : ISizeArray) (i : Nat) (h : i < a.size) :
    a[i] = a.data[i]'(size_eq_data_size a ▸ h) := by
  cases a; rfl

@[simp] public theorem getElem_data (a : ISizeArray) (i : Nat) (h : i < a.data.size) :
    a.data[i] = a[i]'(by simpa using h) := by
  cases a; rfl

public theorem ext_getElem {a b : ISizeArray} (h₁ : a.size = b.size)
    (h₂ : ∀ (i : Nat) (hi₁ : i < a.size) (hi₂ : i < b.size), a[i] = b[i]) : a = b := by
  ext i hi₁ hi₂
  · simpa using h₁
  · simpa using h₂ i (by simpa using hi₁) (by simpa using hi₂)

@[simp] public theorem getElem_usize (a : ISizeArray) (i : USize) (h : i.toNat < a.size) :
    a[i] = a[i.toNat] := by
  cases a; rfl

@[simp] public theorem data_uset (a : ISizeArray) (i : USize) (v : ISize) (h) :
    (a.uset i v h).data = a.data.set i.toNat v (size_eq_data_size a ▸ h) := by
  cases a; rfl

@[simp] public theorem data_set (a : ISizeArray) (i : Nat) (v : ISize) (h) :
    (a.set i v h).data = a.data.set i v (size_eq_data_size a ▸ h) := by
  cases a; rfl

@[simp] public theorem data_push (a : ISizeArray) (v : ISize) :
    (a.push v).data = a.data.push v := by
  cases a; rfl

@[simp] public theorem data_pop (a : ISizeArray) : a.pop.data = a.data.pop := by
  cases a; rfl

@[simp] public theorem data_extract (a : ISizeArray) (start stop : Nat) :
    (a.extract start stop).data = a.data.extract start stop := by
  cases a; rfl

@[simp] public theorem data_replicate (n : Nat) (v : ISize) :
    (replicate n v).data = Array.replicate n v := rfl

@[simp] public theorem data_ofFn {n : Nat} (f : Fin n → ISize) :
    (ofFn f).data = Array.ofFn f := rfl

@[simp] public theorem data_empty : (empty : ISizeArray).data = #[] := rfl

@[simp] public theorem size_pop (a : ISizeArray) : a.pop.size = a.size - 1 := by
  simp [-size_data, size_eq_data_size]

@[simp] public theorem size_extract (a : ISizeArray) (start stop : Nat) :
    (a.extract start stop).size = min stop a.size - start := by
  simp [-size_data, size_eq_data_size]

@[simp] public theorem size_replicate (n : Nat) (v : ISize) : (replicate n v).size = n := by
  simp [-size_data, size_eq_data_size]

@[simp] public theorem size_ofFn {n : Nat} (f : Fin n → ISize) : (ofFn f).size = n := by
  simp [-size_data, size_eq_data_size]

@[simp] public theorem size_empty : (empty : ISizeArray).size = 0 := rfl

@[simp] public theorem getElem_set (a : ISizeArray) (i : Nat) (v : ISize) (h) (j : Nat) (hj) :
    (a.set i v h)[j]'hj = if i = j then v else a[j]'(by simpa using hj) := by
  simp [-getElem_data, getElem_eq_getElem_data, Array.getElem_set]

@[simp] public theorem getElem_push (a : ISizeArray) (v : ISize) (i : Nat) (h) :
    (a.push v)[i]'h = if h' : i < a.size then a[i] else v := by
  simp [-getElem_data, getElem_eq_getElem_data, Array.getElem_push, -size_data, size_eq_data_size]

@[simp] public theorem getElem_pop (a : ISizeArray) (i : Nat) (h) :
    a.pop[i]'h = a[i]'(by simp at h; omega) := by
  simp [-getElem_data, getElem_eq_getElem_data]

@[simp] public theorem data_popWhile (p : ISize → Bool) (a : ISizeArray) :
    (a.popWhile p).data = a.data.popWhile p := by
  cases a; rfl

@[simp] public theorem getElem_append (a b : ISizeArray) (i : Nat) (h) :
    (a ++ b)[i]'h = if h' : i < a.size then a[i] else b[i - a.size]'(by simp at h; omega) := by
  simp [-getElem_data, getElem_eq_getElem_data, Array.getElem_append, -size_data, size_eq_data_size]

@[simp] public theorem getElem_extract (a : ISizeArray) (start stop i : Nat) (h) :
    (a.extract start stop)[i]'h = a[start + i]'(by simp at h; omega) := by
  simp [-getElem_data, getElem_eq_getElem_data]

@[simp] public theorem getElem_replicate (n : Nat) (v : ISize) (i : Nat) (h) :
    (replicate n v)[i]'h = v := by
  simp [-getElem_data, getElem_eq_getElem_data]

@[simp] public theorem getElem_ofFn {n : Nat} (f : Fin n → ISize) (i : Nat) (h) :
    (ofFn f)[i]'h = f ⟨i, by simpa using h⟩ := by
  simp [-getElem_data, getElem_eq_getElem_data]

public theorem foldl_eq_foldl_data {β : Type v} (f : β → ISize → β) (init : β)
    (a : ISizeArray) :
    a.foldl f init = a.data.foldl f init := by
  rfl

public theorem foldr_eq_foldr_data {β : Type v} (f : ISize → β → β) (init : β)
    (a : ISizeArray) :
    a.foldr f init = a.data.foldr f init := by
  rfl

@[simp] public theorem toList_data (a : ISizeArray) : a.data.toList = a.toList := rfl

@[simp] public theorem emptyc_eq_empty : (∅ : ISizeArray) = empty := rfl

@[simp] public theorem emptyWithCapacity_eq_empty (c : Nat) : emptyWithCapacity c = empty := rfl

public theorem size_eq_zero_iff {a : ISizeArray} : a.size = 0 ↔ a = empty := by
  simp [ISizeArray.ext_iff, ← Array.size_eq_zero_iff]

@[simp] public theorem data_set! (a : ISizeArray) (i : Nat) (v : ISize) :
    (a.set! i v).data = a.data.set! i v := by
  cases a; rfl

@[simp] public theorem size_set! (a : ISizeArray) (i : Nat) (v : ISize) :
    (a.set! i v).size = a.size := by
  simp [-size_data, size_eq_data_size]

public theorem getElem!_eq_getElem!_data (a : ISizeArray) (i : Nat) : a[i]! = a.data[i]! := by
  rcases a with ⟨a⟩
  by_cases h : i < a.size <;> simp [getElem!_def, getElem?_def, h] <;> rfl

@[simp] public theorem data_ofList (l : List ISize) : (ofList l).data = l.toArray := rfl

@[simp] public theorem size_ofList (l : List ISize) : (ofList l).size = l.length := rfl

@[simp] public theorem getElem_ofList (l : List ISize) (i : Nat) (h) :
    (ofList l)[i]'h = l[i]'(by simpa using h) := rfl

@[simp] public theorem toList_ofList (l : List ISize) : (ofList l).toList = l := rfl

@[simp] public theorem ofList_toList (a : ISizeArray) : ofList a.toList = a := by
  simp [ISizeArray.ext_iff, ← toList_data]

@[simp] public theorem markLinear_eq (a : ISizeArray) : a.markLinear = a := rfl

@[simp] public theorem propagateMark_eq (a b : ISizeArray) : a.propagateMark b = b := rfl

@[simp] public theorem append_empty (a : ISizeArray) : a ++ empty = a := by
  simp [ISizeArray.ext_iff]

@[simp] public theorem empty_append (a : ISizeArray) : empty ++ a = a := by
  simp [ISizeArray.ext_iff]

public theorem append_assoc (a b c : ISizeArray) : a ++ b ++ c = a ++ (b ++ c) := by
  simp [ISizeArray.ext_iff]

@[simp] public theorem append_eq_empty_iff {a b : ISizeArray} :
    a ++ b = empty ↔ a = empty ∧ b = empty := by
  simp only [ISizeArray.ext_iff, data_append, data_empty, Array.append_eq_empty_iff]

@[simp] public theorem append_right_inj (a : ISizeArray) {b c : ISizeArray} :
    a ++ b = a ++ c ↔ b = c := by
  simp only [ISizeArray.ext_iff, data_append, Array.append_right_inj]

@[simp] public theorem append_left_inj {a b : ISizeArray} (c : ISizeArray) :
    a ++ c = b ++ c ↔ a = b := by
  simp only [ISizeArray.ext_iff, data_append, Array.append_left_inj]

public theorem getElem_append_left {a b : ISizeArray} {i : Nat} (h : i < a.size) :
    (a ++ b)[i]'(by simp; omega) = a[i] := by
  simp [h]

public theorem getElem_append_right {a b : ISizeArray} {i : Nat} (h : a.size ≤ i)
    (h' : i < (a ++ b).size) : (a ++ b)[i] = b[i - a.size]'(by simp at h'; omega) := by
  simp [Nat.not_lt.mpr h]

@[simp] public theorem extract_same (a : ISizeArray) (i : Nat) : a.extract i i = empty := by
  simp [ISizeArray.ext_iff]; omega

@[simp] public theorem extract_zero_size (a : ISizeArray) : a.extract 0 a.size = a := by
  simp [ISizeArray.ext_iff]

@[simp] public theorem extract_eq_empty_iff {a : ISizeArray} {i j : Nat} :
    a.extract i j = empty ↔ min j a.size ≤ i := by
  simp [ISizeArray.ext_iff]

public theorem extract_extract (a : ISizeArray) (i j k l : Nat) :
    (a.extract i j).extract k l = a.extract (i + k) (min (i + l) j) := by
  simp [ISizeArray.ext_iff]

public theorem extract_append_extract (a : ISizeArray) (i j k : Nat) :
    a.extract i j ++ a.extract j k = a.extract (min i j) (max j k) := by
  simp [ISizeArray.ext_iff]

@[simp] public theorem extract_append_eq_left (a b : ISizeArray) :
    (a ++ b).extract 0 a.size = a := by
  simp [ISizeArray.ext_iff]

@[simp] public theorem extract_append_eq_right (a b : ISizeArray) :
    (a ++ b).extract a.size (a.size + b.size) = b := by
  simp [ISizeArray.ext_iff, -size_data, size_eq_data_size]

@[simp] public theorem data_copySlice (src : ISizeArray) (srcOff : Nat) (dest : ISizeArray)
    (destOff len : Nat) (exact : Bool) :
    (src.copySlice srcOff dest destOff len exact).data =
      dest.data.extract 0 destOff ++ src.data.extract srcOff (srcOff + len) ++
        dest.data.extract (destOff + min len (src.size - srcOff)) dest.size := by
  simp [copySlice]

public theorem copySlice_eq_append (src : ISizeArray) (srcOff : Nat) (dest : ISizeArray)
    (destOff len : Nat) (exact : Bool) :
    src.copySlice srcOff dest destOff len exact =
      dest.extract 0 destOff ++ src.extract srcOff (srcOff + len) ++
        dest.extract (destOff + min len (src.size - srcOff)) dest.size := by
  simp [ISizeArray.ext_iff]

@[simp] public theorem Slice.size_copy (s : ISizeArray.Slice) : s.copy.size = s.size := by
  have := s.stop_le_array_size
  simp only [Slice.copy, size_extract, Slice.size_eq]
  omega

/-! ### Lists -/

@[simp] public theorem toList_mk (a : Array ISize) : (mk a).toList = a.toList := rfl

@[simp] public theorem length_toList (a : ISizeArray) : a.toList.length = a.size := by
  simp [← toList_data]

@[simp] public theorem getElem_toList (a : ISizeArray) (i : Nat) (h : i < a.toList.length) :
    a.toList[i] = a[i]'(by simpa using h) := by
  simp [← toList_data]

@[simp] public theorem getElem?_toList (a : ISizeArray) (i : Nat) : a.toList[i]? = a[i]? := by
  by_cases h : i < a.size <;> simp [h, ← toList_data]

@[simp] public theorem toList_inj {a b : ISizeArray} : a.toList = b.toList ↔ a = b :=
  ⟨fun h => by rw [← ofList_toList a, h, ofList_toList], fun h => h ▸ rfl⟩

@[simp] public theorem toList_empty : (empty : ISizeArray).toList = [] := rfl

@[simp] public theorem toList_push (a : ISizeArray) (v : ISize) :
    (a.push v).toList = a.toList ++ [v] := by
  simp [← toList_data]

@[simp] public theorem toList_pop (a : ISizeArray) : a.pop.toList = a.toList.dropLast := by
  simp [← toList_data]

@[simp] public theorem toList_append (a b : ISizeArray) :
    (a ++ b).toList = a.toList ++ b.toList := by
  simp [← toList_data]

@[simp] public theorem toList_set (a : ISizeArray) (i : Nat) (v : ISize) (h) :
    (a.set i v h).toList = a.toList.set i v := by
  simp [← toList_data]

@[simp] public theorem toList_set! (a : ISizeArray) (i : Nat) (v : ISize) :
    (a.set! i v).toList = a.toList.set i v := by
  simp [← toList_data]

@[simp] public theorem toList_extract (a : ISizeArray) (start stop : Nat) :
    (a.extract start stop).toList = a.toList.extract start stop := by
  simp [← toList_data]

@[simp] public theorem toList_replicate (n : Nat) (v : ISize) :
    (replicate n v).toList = List.replicate n v := by
  simp [← toList_data]

@[simp] public theorem toList_ofFn {n : Nat} (f : Fin n → ISize) :
    (ofFn f).toList = List.ofFn f := by
  simp [← toList_data]

@[simp] public theorem toList_popWhile (p : ISize → Bool) (a : ISizeArray) :
    (a.popWhile p).toList = (a.toList.reverse.dropWhile p).reverse := by
  rw [← toList_data, data_popWhile, ← Array.toArray_toList (xs := a.data),
    List.popWhile_toArray]
  simp

/-! ### Machine-word indices -/

/--
`usize` is the size when the size fits in a `USize`, which holds for every array in memory. Loops
over `USize` indices take this as a hypothesis, since the model `Array` has no bound on its size.
-/
public theorem toNat_usize_of_lt (a : ISizeArray) (h : a.size < USize.size) :
    a.usize.toNat = a.size := by
  simp [Nat.mod_eq_of_lt h]

/-- The guard `i < a.usize` of a loop over `USize` indices bounds the index. -/
public theorem lt_usize_iff (a : ISizeArray) (h : a.size < USize.size) {i : USize} :
    i < a.usize ↔ i.toNat < a.size := by
  rw [USize.lt_iff_toNat_lt, toNat_usize_of_lt a h]

/-! ### Last element -/

public theorem back?_eq_getElem? (a : ISizeArray) : a.back? = a[a.size - 1]? := by
  simp only [back?]

public theorem back!_eq_getElem! (a : ISizeArray) : a.back! = a[a.size - 1]! := by
  simp only [back!]

public theorem back_eq_getElem (a : ISizeArray) (h : 0 < a.size) :
    a.back h = a[a.size - 1]'(Nat.sub_lt h Nat.one_pos) := by
  simp only [back]

@[simp] public theorem getLast?_toList (a : ISizeArray) : a.toList.getLast? = a.back? := by
  rw [List.getLast?_eq_getElem?, getElem?_toList, length_toList, back?_eq_getElem?]

@[simp] public theorem back?_empty : (empty : ISizeArray).back? = none := by
  rw [← getLast?_toList, toList_empty, List.getLast?_nil]

@[simp] public theorem back?_push (a : ISizeArray) (v : ISize) :
    (a.push v).back? = some v := by
  rw [← getLast?_toList, toList_push, List.getLast?_concat]

@[simp] public theorem back!_push (a : ISizeArray) (v : ISize) : (a.push v).back! = v := by
  simp [back!_eq_getElem!]

@[simp] public theorem back_push (a : ISizeArray) (v : ISize) (h) : (a.push v).back h = v := by
  simp [back_eq_getElem]

/-! ### More lists -/

@[simp] public theorem toList_uset (a : ISizeArray) (i : USize) (v : ISize) (h) :
    (a.uset i v h).toList = a.toList.set i.toNat v := by
  simp [← toList_data]

@[simp] public theorem toList_copySlice (src : ISizeArray) (srcOff : Nat) (dest : ISizeArray)
    (destOff len : Nat) (exact : Bool) :
    (src.copySlice srcOff dest destOff len exact).toList =
      dest.toList.extract 0 destOff ++ src.toList.extract srcOff (srcOff + len) ++
        dest.toList.extract (destOff + min len (src.size - srcOff)) dest.size := by
  simp [copySlice_eq_append]

/-! ### Accessors -/

@[simp] public theorem get_eq_getElem (a : ISizeArray) (i : Nat) (h) : a.get i h = a[i] := rfl

@[simp] public theorem uget_eq_getElem (a : ISizeArray) (i : USize) (h) :
    a.uget i h = a[i.toNat] := by
  cases a; rfl

@[simp] public theorem get!_eq_getElem! (a : ISizeArray) (i : Nat) : a.get! i = a[i]! := by
  rw [get!]
  split
  · simp_all [getElem!_pos]
  · simp_all [getElem!_neg]

@[simp] public theorem getD_eq_getD_getElem? (a : ISizeArray) (i : Nat) (v₀ : ISize) :
    a.getD i v₀ = a[i]?.getD v₀ := by
  rw [getD]
  split <;> simp_all

@[simp] public theorem isEmpty_iff {a : ISizeArray} : a.isEmpty ↔ a = empty := by
  simp [isEmpty, ← size_eq_zero_iff]

/-! ### Queries -/

@[simp] public theorem any_toList (a : ISizeArray) (p : ISize → Bool) :
    a.toList.any p = a.any p := by
  simp [any, ← toList_data]

@[simp] public theorem all_toList (a : ISizeArray) (p : ISize → Bool) :
    a.toList.all p = a.all p := by
  simp [all, ← toList_data]

@[simp] public theorem contains_toList (a : ISizeArray) (v : ISize) :
    a.toList.contains v = a.contains v := by
  simp [contains, ← toList_data]

@[simp] public theorem foldl_toList {β : Type v} (f : β → ISize → β) (init : β)
    (a : ISizeArray) : a.toList.foldl f init = a.foldl f init := by
  simp [foldl_eq_foldl_data, ← toList_data]

@[simp] public theorem foldr_toList {β : Type v} (f : ISize → β → β) (init : β)
    (a : ISizeArray) : a.toList.foldr f init = a.foldr f init := by
  simp [foldr_eq_foldr_data, ← toList_data]

@[simp] public theorem forIn_toList {β : Type v} {m : Type v → Type w} [Monad m] [LawfulMonad m]
    (a : ISizeArray) (init : β) (f : ISize → β → m (ForInStep β)) :
    ForIn.forIn a.toList init f = ForIn.forIn a init f := by
  rw [← toList_data, Array.forIn_toList]
  rfl

private theorem findIdx?_loop_eq (a : ISizeArray) (p : ISize → Bool) (i : Nat) :
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

public theorem findIdx?_eq (a : ISizeArray) (p : ISize → Bool) (start : Nat) :
    a.findIdx? p start = ((a.toList.drop start).findIdx? p).map (· + start) := by
  simp [findIdx?, findIdx?_loop_eq]

@[simp] public theorem findIdx?_toList (a : ISizeArray) (p : ISize → Bool) :
    a.toList.findIdx? p = a.findIdx? p := by
  simp [findIdx?_eq]

private theorem findFinIdx?_loop_eq (a : ISizeArray) (p : ISize → Bool) (i : Nat) :
    (findFinIdx?.loop a p i).map Fin.val = findIdx?.loop a p i := by
  fun_induction findFinIdx?.loop a p i <;> rw [findIdx?.loop] <;> simp_all <;> omega

@[simp] public theorem map_val_findFinIdx? (a : ISizeArray) (p : ISize → Bool) (start : Nat) :
    (a.findFinIdx? p start).map Fin.val = a.findIdx? p start := by
  simp [findFinIdx?, findIdx?, findFinIdx?_loop_eq]

/-! ### Slices -/

@[simp] public theorem Slice.getElem_copy (s : ISizeArray.Slice) (i : Nat)
    (h : i < s.copy.size) :
    s.copy[i] = s[i]'(by simpa using h) := by
  simp [Slice.copy, Slice.getElem_eq]

/-- Copying the slice from `start` to `stop` is the same as extracting those elements. -/
@[simp] public theorem copy_toSlice (a : ISizeArray) (start stop : Nat) :
    (a.toSlice start stop).copy = a.extract start stop := by
  rw [← toList_inj]
  unfold toSlice
  split <;> split <;>
    simp [Slice.copy, Slice.array, Slice.start, Slice.stop] <;> omega

@[simp] public theorem array_toSlice (a : ISizeArray) (start stop : Nat) :
    (a.toSlice start stop).array = a := by
  unfold toSlice
  split <;> split <;> rfl

@[simp] public theorem start_toSlice (a : ISizeArray) (start stop : Nat) :
    (a.toSlice start stop).start = min start (min stop a.size) := by
  unfold toSlice
  split <;> split <;> simp only [Slice.start] <;> omega

@[simp] public theorem stop_toSlice (a : ISizeArray) (start stop : Nat) :
    (a.toSlice start stop).stop = min stop a.size := by
  unfold toSlice
  split <;> split <;> simp only [Slice.stop] <;> omega

@[simp] public theorem size_toSlice (a : ISizeArray) (start stop : Nat) :
    (a.toSlice start stop).size = min stop a.size - start := by
  rw [Slice.size_eq, start_toSlice, stop_toSlice]
  omega

@[simp] public theorem getElem_toSlice (a : ISizeArray) (start stop i : Nat) (h) :
    (a.toSlice start stop)[i]'h = a[start + i]'(by simp at h; omega) := by
  simp only [size_toSlice] at h
  simp only [Slice.getElem_eq, array_toSlice, start_toSlice]
  congr 1
  omega

@[simp] public theorem Slice.size_slice (s : ISizeArray.Slice) (start stop : Nat) :
    (s.slice start stop).size = min stop s.size - start := by
  have := s.stop_le_array_size
  rw [slice, size_toSlice, size_eq]
  omega

@[simp] public theorem Slice.getElem_slice (s : ISizeArray.Slice) (start stop i : Nat) (h) :
    (s.slice start stop)[i]'h = s[start + i]'(by simp at h; omega) := by
  have := s.stop_le_array_size
  have := s.size_eq
  have h' := h
  rw [size_slice, size_eq] at h'
  simp only [Slice.getElem_eq, slice, array_toSlice, start_toSlice]
  congr 1
  omega

@[simp] public theorem Slice.copy_slice (s : ISizeArray.Slice) (start stop : Nat) :
    (s.slice start stop).copy = s.copy.extract start stop := by
  apply ext_getElem
  · simp
  · intro i _ _
    simp

@[simp] public theorem Slice.array_popFront (s : ISizeArray.Slice) :
    s.popFront.array = s.array := by
  simp only [popFront]
  split <;> rfl

@[simp] public theorem Slice.start_popFront (s : ISizeArray.Slice) :
    s.popFront.start = min (s.start + 1) s.stop := by
  rcases s with ⟨⟨_, start, stop, h, _⟩⟩
  simp only [popFront, Slice.start, Slice.stop]
  by_cases hc : start < stop <;> simp [hc] <;> omega

@[simp] public theorem Slice.stop_popFront (s : ISizeArray.Slice) :
    s.popFront.stop = s.stop := by
  simp only [popFront]
  split <;> rfl

@[simp] public theorem Slice.size_popFront (s : ISizeArray.Slice) :
    s.popFront.size = s.size - 1 := by
  rw [size_eq, size_eq, start_popFront, stop_popFront]
  omega

@[simp] public theorem Slice.getElem_popFront (s : ISizeArray.Slice) (i : Nat) (h) :
    s.popFront[i]'h = s[i + 1]'(by simp at h; omega) := by
  have : s.start < s.stop := by rw [size_popFront, size_eq] at h; omega
  simp only [Slice.getElem_eq, array_popFront, start_popFront]
  congr 1
  omega

public theorem Slice.getD_eq (s : ISizeArray.Slice) (i : Nat) (v₀ : ISize) :
    s.getD i v₀ = if h : i < s.size then s[i] else v₀ := by
  rw [Slice.getD]

public theorem Slice.get!_eq (s : ISizeArray.Slice) (i : Nat) :
    s.get! i = if h : i < s.size then s[i] else default := by
  rw [Slice.get!, Slice.getD]

private theorem Slice.foldrM_loop_eq {β : Type v} (f : ISize → β → β)
    (s : ISizeArray.Slice) (i : Nat) (h : i ≤ s.size) (b : β) :
    Slice.foldrM.loop (m := Id) (pure <| f · ·) s i h b = (s.copy.toList.take i).foldr f b := by
  induction i generalizing b with
  | zero => rfl
  | succ i ih =>
    have hi : i < s.copy.toList.length := by simp; omega
    rw [Slice.foldrM.loop, List.take_add_one, List.getElem?_eq_getElem hi]
    simp [ih]

/-- Folding over a slice is folding over the list of its elements. -/
public theorem Slice.foldr_eq_foldr_toList_copy {β : Type v} (f : ISize → β → β)
    (init : β) (s : ISizeArray.Slice) : s.foldr f init = s.copy.toList.foldr f init := by
  rw [Slice.foldr, Slice.foldrM, Id.run, Slice.foldrM_loop_eq,
    List.take_of_length_le (by simp)]

/-! ### Writes -/

@[simp] public theorem getElem_uset (a : ISizeArray) (i : USize) (v : ISize) (h) (j : Nat)
    (hj) : (a.uset i v h)[j]'hj = if i.toNat = j then v else a[j]'(by simpa using hj) := by
  simp [-getElem_data, getElem_eq_getElem_data, Array.getElem_set]

@[simp] public theorem getElem_set! (a : ISizeArray) (i : Nat) (v : ISize) (j : Nat) (hj) :
    (a.set! i v)[j]'hj = if i = j then v else a[j]'(by simpa using hj) := by
  simp only [getElem_eq_getElem_data, data_set!, Array.set!_eq_setIfInBounds]
  rw [Array.getElem_setIfInBounds]

@[simp] public theorem getElem?_set! (a : ISizeArray) (i : Nat) (v : ISize) (j : Nat) :
    (a.set! i v)[j]? = if i = j then if i < a.size then some v else none else a[j]? := by
  by_cases hj : j < a.size <;> by_cases hij : i = j <;> simp_all

public theorem size_popWhile_le (p : ISize → Bool) (a : ISizeArray) :
    (a.popWhile p).size ≤ a.size := by
  rw [← length_toList, ← length_toList, toList_popWhile, List.length_reverse]
  simpa using (List.dropWhile_sublist (l := a.toList.reverse) p).length_le

@[simp] public theorem size_copySlice (src : ISizeArray) (srcOff : Nat) (dest : ISizeArray)
    (destOff len : Nat) (exact : Bool) :
    (src.copySlice srcOff dest destOff len exact).size =
      max dest.size (min destOff dest.size + min len (src.size - srcOff)) := by
  simp [-size_data, size_eq_data_size]
  omega

public theorem getElem_copySlice (src : ISizeArray) (srcOff : Nat) (dest : ISizeArray)
    (destOff len : Nat) (exact : Bool) (i : Nat) (h) :
    (src.copySlice srcOff dest destOff len exact)[i]'h =
      if h₁ : i < min destOff dest.size then dest[i]'(by omega)
      else if h₂ : i - min destOff dest.size < min len (src.size - srcOff) then
        src[srcOff + (i - min destOff dest.size)]'(by omega)
      else dest[i]'(by simp at h; omega) := by
  have hs := size_copySlice src srcOff dest destOff len exact
  simp only [copySlice_eq_append, getElem_append, getElem_extract, size_append, size_extract,
    Nat.sub_zero, Nat.zero_add]
  by_cases h₁ : i < min destOff dest.size
  · have : i < min destOff dest.size + (min (srcOff + len) src.size - srcOff) := by omega
    simp [h₁, this]
  · by_cases h₂ : i - min destOff dest.size < min len (src.size - srcOff)
    · have : i < min destOff dest.size + (min (srcOff + len) src.size - srcOff) := by omega
      simp [h₁, h₂, this]
    · have : ¬i < min destOff dest.size + (min (srcOff + len) src.size - srcOff) := by omega
      simp only [h₁, h₂, this, ↓reduceDIte]
      congr 1
      omega

/-! ### Monadic folds -/

@[simp] public theorem foldlM_toList {β : Type v} {m : Type v → Type w} [Monad m]
    (f : β → ISize → m β) (init : β) (a : ISizeArray) :
    a.toList.foldlM f init = a.foldlM f init := by
  rw [← toList_data, Array.foldlM_toList, foldlM, size_eq_data_size]

@[simp] public theorem foldrM_toList {β : Type v} {m : Type v → Type w} [Monad m]
    (f : ISize → β → m β) (init : β) (a : ISizeArray) :
    a.toList.foldrM f init = a.foldrM f init := by
  rw [← toList_data, Array.foldrM_toList]
  rfl

@[simp] public theorem forM_eq_forM {m : Type v → Type w} [Monad m] (f : ISize → m PUnit)
    (a : ISizeArray) : a.forM f = ForM.forM a f := rfl

@[simp] public theorem forM_toList {m : Type v → Type w} [Monad m] (f : ISize → m PUnit)
    (a : ISizeArray) : ForM.forM a.toList f = ForM.forM a f := by
  rcases a with ⟨⟨l⟩⟩
  exact (List.forM_toArray l f).symm

/-! ### Membership -/

public theorem mem_def {x : ISize} {a : ISizeArray} : x ∈ a ↔ x ∈ a.data := Iff.rfl

@[simp] public theorem mem_data {x : ISize} {a : ISizeArray} : x ∈ a.data ↔ x ∈ a := Iff.rfl

@[simp] public theorem mem_mk {x : ISize} {xs : Array ISize} : x ∈ mk xs ↔ x ∈ xs := Iff.rfl

@[simp] public theorem mem_toList {x : ISize} {a : ISizeArray} : x ∈ a.toList ↔ x ∈ a := by
  rw [← toList_data, Array.mem_toList_iff, mem_data]

public theorem mem_iff_getElem {x : ISize} {a : ISizeArray} :
    x ∈ a ↔ ∃ (i : Nat) (h : i < a.size), a[i] = x := by
  rw [← mem_data, Array.mem_iff_getElem]
  simp

public theorem getElem_mem {a : ISizeArray} {i : Nat} (h : i < a.size) : a[i] ∈ a :=
  mem_iff_getElem.mpr ⟨i, h, rfl⟩

@[simp] public theorem not_mem_empty (x : ISize) : ¬x ∈ (empty : ISizeArray) := by
  simp [← mem_data]

@[simp] public theorem mem_push {x v : ISize} {a : ISizeArray} :
    x ∈ a.push v ↔ x ∈ a ∨ x = v := by
  simp [← mem_data]

@[simp] public theorem mem_append {x : ISize} {a b : ISizeArray} :
    x ∈ a ++ b ↔ x ∈ a ∨ x ∈ b := by
  simp [← mem_data]

/-! ### Iterators -/

private theorem toList_foldl_push (a : ISizeArray) (l : List ISize) :
    (l.foldl (·.push ·) a).toList = a.toList ++ l := by
  induction l generalizing a <;> simp_all

@[simp] public theorem _root_.Std.Iter.toList_toISizeArray {α : Type} [Std.Iterator α Id ISize]
    [Std.Iterators.Finite α Id] [Std.IteratorLoop α Id Id] [Std.LawfulIteratorLoop α Id Id]
    (it : Std.Iter (α := α) ISize) : it.toISizeArray.toList = it.toList := by
  rw [Std.Iter.toISizeArray, ← Std.Iter.foldl_toList, toList_foldl_push, toList_empty,
    List.nil_append]

private theorem Slice.cons_take_drop (a : ISizeArray) (s t : Nat) (h : s < t)
    (h' : s < a.size) :
    a[s] :: (a.toList.drop (s + 1)).take (t - (s + 1)) = (a.toList.drop s).take (t - s) := by
  rw [List.drop_eq_getElem_cons (by simpa using h' : s < a.toList.length),
    show t - s = t - (s + 1) + 1 by omega, List.take_succ_cons, getElem_toList]

private theorem SliceIterator.toList_eq (it : Std.Iter (α := ISizeArray.SliceIterator) ISize) :
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
      exact Slice.cons_take_drop _ _ _ h (by omega)
    · show _ = SliceIterator.step _
      simp only [SliceIterator.step, Std.Iter.toIterM, h, ↓reduceDIte]
      rfl
  · simp only [SliceIterator.step, Std.Iter.toIterM, h, ↓reduceDIte,
      Std.IterStep.mapIterator_done]
    simp [Slice.copy]
    omega

/-! ### Slices as copies -/

@[simp] public theorem Slice.size_empty : (Slice.empty : ISizeArray.Slice).size = 0 := rfl

@[simp] public theorem Slice.emptyc_eq_empty : (∅ : ISizeArray.Slice) = Slice.empty := rfl

@[simp] public theorem Slice.copy_empty : (Slice.empty : ISizeArray.Slice).copy = empty := by
  simp [Slice.copy, Slice.empty, Slice.array, Slice.start, Slice.stop]

@[simp] public theorem Slice.toList_eq_toList_copy (s : ISizeArray.Slice) :
    s.toList = s.copy.toList := by
  rw [Std.Slice.Internal.toList_eq_toList_iter, SliceIterator.toList_eq,
    Std.Slice.Internal.iter_eq_toIteratorIter, Std.ToIterator.iter_eq]
  rfl

@[simp] public theorem Slice.toISizeArray_iter (s : ISizeArray.Slice) :
    s.iter.toISizeArray = s.copy := by
  rw [← toList_inj, Std.Iter.toList_toISizeArray, Std.Slice.toList_iter, toList_eq_toList_copy]

@[simp] public theorem toISizeArray_iter (a : ISizeArray) : a.iter.toISizeArray = a := by
  rw [iter, Slice.toISizeArray_iter, copy_toSlice, extract_zero_size]

@[simp] public theorem Slice.foldl_eq_foldl_copy {β : Type v} (f : β → ISize → β) (init : β)
    (s : ISizeArray.Slice) : s.foldl f init = s.copy.foldl f init := by
  rw [← Std.Slice.foldl_toList, toList_eq_toList_copy, foldl_toList]

@[simp] public theorem Slice.foldlM_eq_foldlM_copy {β : Type v} {m : Type v → Type w} [Monad m]
    [LawfulMonad m] (f : β → ISize → m β) (init : β) (s : ISizeArray.Slice) :
    s.foldlM f init = s.copy.foldlM f init := by
  rw [← Std.Slice.foldlM_toList, toList_eq_toList_copy, foldlM_toList]

@[simp] public theorem Slice.forIn_eq_forIn_copy {β : Type v} {m : Type v → Type w} [Monad m]
    [LawfulMonad m] (s : ISizeArray.Slice) (init : β) (f : ISize → β → m (ForInStep β)) :
    ForIn.forIn s init f = ForIn.forIn s.copy init f := by
  rw [← Std.Slice.forIn_toList, toList_eq_toList_copy, forIn_toList]

@[simp] public theorem Slice.forM_eq_forM_copy {m : Type v → Type w} [Monad m] [LawfulMonad m]
    (s : ISizeArray.Slice) (f : ISize → m PUnit) : ForM.forM s f = ForM.forM s.copy f :=
  foldlM_eq_foldlM_copy ..

@[simp] public theorem Slice.foldr_eq_foldr_copy {β : Type v} (f : ISize → β → β) (init : β)
    (s : ISizeArray.Slice) : s.foldr f init = s.copy.foldr f init := by
  rw [foldr_eq_foldr_toList_copy, foldr_toList]

private theorem Slice.foldrM_loop_eq_foldrM {β : Type v} {m : Type v → Type w} [Monad m]
    [LawfulMonad m] (f : ISize → β → m β) (s : ISizeArray.Slice) (i : Nat) (h : i ≤ s.size)
    (b : β) : Slice.foldrM.loop f s i h b = (s.copy.toList.take i).foldrM f b := by
  induction i generalizing b with
  | zero => simp [Slice.foldrM.loop]
  | succ i ih =>
    have hi : i < s.copy.toList.length := by simp; omega
    rw [Slice.foldrM.loop, List.take_add_one, List.getElem?_eq_getElem hi]
    simp [ih]

@[simp] public theorem Slice.foldrM_eq_foldrM_copy {β : Type v} {m : Type v → Type w} [Monad m]
    [LawfulMonad m] (f : ISize → β → m β) (init : β) (s : ISizeArray.Slice) :
    s.foldrM f init = s.copy.foldrM f init := by
  rw [Slice.foldrM, foldrM_loop_eq_foldrM, List.take_of_length_le (by simp), foldrM_toList]

@[simp] public theorem Slice.any_eq_any_copy (s : ISizeArray.Slice) (p : ISize → Bool) :
    s.any p = s.copy.any p := by
  rw [Slice.any, ← Std.Iter.any_toList, Std.Slice.toList_iter, toList_eq_toList_copy, any_toList]

@[simp] public theorem Slice.all_eq_all_copy (s : ISizeArray.Slice) (p : ISize → Bool) :
    s.all p = s.copy.all p := by
  rw [Slice.all, ← Std.Iter.all_toList, Std.Slice.toList_iter, toList_eq_toList_copy, all_toList]

@[simp] public theorem Slice.contains_eq_contains_copy (s : ISizeArray.Slice) (v : ISize) :
    s.contains v = s.copy.contains v := by
  rw [Slice.contains, any_eq_any_copy]
  rfl

@[simp] public theorem Slice.find?_eq_find?_toList_copy (s : ISizeArray.Slice)
    (p : ISize → Bool) : s.find? p = s.copy.toList.find? p := by
  rw [Slice.find?, ← Std.Iter.find?_toList, Std.Slice.toList_iter, toList_eq_toList_copy]

private theorem foldl_count_eq (p : ISize → Bool) (l : List ISize) (n : Nat) :
    l.foldl (fun n x => if p x then n + 1 else n) n = n + l.countP p := by
  induction l generalizing n with
  | nil => rfl
  | cons x l ih => by_cases hx : p x <;> simp [ih, hx] <;> omega

@[simp] public theorem Slice.count_eq_countP_toList_copy (s : ISizeArray.Slice)
    (p : ISize → Bool) : s.count p = s.copy.toList.countP p := by
  rw [Slice.count, ← Std.Iter.foldl_toList, Std.Slice.toList_iter, toList_eq_toList_copy,
    foldl_count_eq, Nat.zero_add]

private theorem Slice.findSomeRevM?_loop_eq (p : ISize → Bool) (s : ISizeArray.Slice) (i : Nat)
    (h : i ≤ s.size) :
    Slice.findSomeRevM?.loop (m := Id) s (fun x => pure (if p x then some x else none)) i h =
      (s.copy.toList.take i).reverse.find? p := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have hi : i < s.copy.toList.length := by simp; omega
    rw [Slice.findSomeRevM?.loop, List.take_add_one, List.getElem?_eq_getElem hi]
    by_cases hp : p s[i] <;> simp [ih, hp] <;> rfl

@[simp] public theorem Slice.findRev?_eq_find?_reverse_toList_copy (s : ISizeArray.Slice)
    (p : ISize → Bool) : s.findRev? p = s.copy.toList.reverse.find? p := by
  have := Slice.findSomeRevM?_loop_eq p s s.size (Nat.le_refl _)
  rw [List.take_of_length_le (by simp)] at this
  exact this

/-! ### Membership in slices -/

@[simp] public theorem Slice.mem_iff_mem_copy {x : ISize} {s : ISizeArray.Slice} :
    x ∈ s ↔ x ∈ s.copy := Iff.rfl

public theorem Slice.mem_iff_getElem {x : ISize} {s : ISizeArray.Slice} :
    x ∈ s ↔ ∃ (i : Nat) (h : i < s.size), s[i] = x := by
  rw [mem_iff_mem_copy, ISizeArray.mem_iff_getElem]
  simp

public theorem Slice.getElem_mem {s : ISizeArray.Slice} {i : Nat} (h : i < s.size) : s[i] ∈ s :=
  mem_iff_getElem.mpr ⟨i, h, rfl⟩

/-! ### Slice equality -/

@[simp] public theorem Slice.beq_eq_beq_copy (s t : ISizeArray.Slice) :
    (s == t) = (s.copy == t.copy) := by
  rfl

/-! ## In-place folds -/

@[specialize]
private unsafe def foldInPlaceImpl {β : Type v} (a : ISizeArray) (start len : USize) (init : β)
    (f : (k : USize) → k.toNat < len.toNat → ISize → β → ISize × β)
    (_ : start.toNat + len.toNat ≤ a.size) : ISizeArray × β :=
  loop (ensureExclusiveUnsafe a) 0 init
where
  @[specialize] loop (a : ISizeArray) (k : USize) (b : β) : ISizeArray × β :=
    if k < len then
      let p := f k lcProof (a.uget (start + k) lcProof) b
      loop (setUnsafe a (start + k) p.1) (k + 1) p.2
    else
      (a, b)

/-- The loop of `foldInPlace`, over `Nat` indices. -/
@[expose]
public def foldInPlace.loop {β : Type v} (len' : USize)
    (f : (k : USize) → k.toNat < len'.toNat → ISize → β → ISize × β)
    (start len : Nat) (a : ISizeArray) (h : start + len ≤ a.size) (hlen : len ≤ len'.toNat)
    (k : Nat) (b : β) : ISizeArray × β :=
  if hk : k < len then
    let p := f k.toUSize (by
      have := len'.toNat_lt_size
      rw [USize.toNat_ofNat_of_lt' (by omega)]
      omega) (a[start + k]'(by omega)) b
    foldInPlace.loop len' f start len (a.set (start + k) p.1 (by omega)) (by simpa using h) hlen
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
public def foldInPlace {β : Type v} (a : ISizeArray) (start len : USize) (init : β)
    (f : (k : USize) → k.toNat < len.toNat → ISize → β → ISize × β)
    (h : start.toNat + len.toNat ≤ a.size) : ISizeArray × β :=
  foldInPlace.loop len f start.toNat len.toNat a h (Nat.le_refl _) 0 init

public theorem size_foldInPlace_loop {β : Type v} (len' : USize)
    (f : (k : USize) → k.toNat < len'.toNat → ISize → β → ISize × β) (start len : Nat)
    (a : ISizeArray) (h : start + len ≤ a.size) (hlen : len ≤ len'.toNat) (k : Nat) (b : β) :
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

@[simp] public theorem size_foldInPlace {β : Type v} (a : ISizeArray) (start len : USize)
    (init : β) (f : (k : USize) → k.toNat < len.toNat → ISize → β → ISize × β)
    (h : start.toNat + len.toNat ≤ a.size) :
    (a.foldInPlace start len init f h).1.size = a.size :=
  size_foldInPlace_loop len f _ _ a h _ 0 init

/-! ### Decidable membership and slice hashing -/

@[simp] public theorem contains_iff_mem {a : ISizeArray} {x : ISize} :
    a.contains x = true ↔ x ∈ a := by
  simp only [contains, Array.contains_iff_mem, mem_data]

private def decMemImpl (x : ISize) (a : ISizeArray) : Decidable (x ∈ a) :=
  decidable_of_iff _ contains_iff_mem

/--
Decides membership with `contains`. Logically it decides membership in `a.toList`, so that `decide`
can evaluate it.
-/
@[implemented_by decMemImpl, expose]
public def decMem (x : ISize) (a : ISizeArray) : Decidable (x ∈ a) :=
  decidable_of_iff _ mem_toList

public instance (x : ISize) (a : ISizeArray) : Decidable (x ∈ a) := decMem x a

public theorem Slice.contains_iff_mem {s : ISizeArray.Slice} {x : ISize} :
    s.contains x = true ↔ x ∈ s := by
  simp

private def Slice.decMemImpl (x : ISize) (s : ISizeArray.Slice) : Decidable (x ∈ s) :=
  decidable_of_iff _ Slice.contains_iff_mem

/--
Decides membership with `contains`. Logically it decides membership in `s.copy.toList`, so that
`decide` can evaluate it.
-/
@[implemented_by Slice.decMemImpl, expose]
public def Slice.decMem (x : ISize) (s : ISizeArray.Slice) : Decidable (x ∈ s) :=
  decidable_of_iff (x ∈ s.copy.toList) (by simp)

public instance (x : ISize) (s : ISizeArray.Slice) : Decidable (x ∈ s) := Slice.decMem x s

private def Slice.hashImpl (s : ISizeArray.Slice) : UInt64 :=
  s.foldl (fun r x => mixHash r (Hashable.hash x)) 7

/-- The same hash as `s.copy`, so slices with the same elements have the same hash. -/
@[implemented_by Slice.hashImpl]
public def Slice.hash (s : ISizeArray.Slice) : UInt64 :=
  Hashable.hash s.copy

public instance : Hashable ISizeArray.Slice := ⟨Slice.hash⟩

public theorem Slice.hash_eq_hash_copy (s : ISizeArray.Slice) :
    Hashable.hash s = Hashable.hash s.copy := by
  rfl

public theorem Slice.beq_iff_copy_eq {s t : ISizeArray.Slice} :
    (s == t) = true ↔ s.copy = t.copy := by
  simp

public instance : EquivBEq ISizeArray.Slice where
  rfl := by simp
  symm h := by simp_all
  trans h₁ h₂ := by simp_all

public instance : LawfulHashable ISizeArray.Slice where
  hash_eq s t h := by
    rw [Slice.hash_eq_hash_copy, Slice.hash_eq_hash_copy, Slice.beq_iff_copy_eq.mp h]

end ISizeArray

end ScalarArray

/-- The array with the elements of `l`. -/
@[inline, expose]
public def List.toISizeArray (l : List ISize) : ScalarArray.ISizeArray :=
  ScalarArray.ISizeArray.ofList l
