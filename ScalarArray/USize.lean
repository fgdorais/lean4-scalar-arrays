/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import all ScalarArray.Internal

/-!
# Arrays of `USize`

`ScalarArray.USizeArray` stores `USize` values unboxed, one machine word per element, in a Lean runtime
scalar array. Its logical model is `Array USize`: `USizeArray.mk` and `USizeArray.data` convert
between the two, and every operation is specified by its effect on the model.

The runtime representation is a `ScalarArray` with element size `System.Platform.numBits / 8`. Reads and in-place writes
are inline C. `uset`, `set` and `push` update the array in place when it is not shared and copy
it otherwise, like `Array` and `ByteArray`.
-/

namespace ScalarArray

/--
Arrays of `USize` values, stored unboxed in a scalar array with element size `System.Platform.numBits / 8`.

The logical model is an `Array USize`. At runtime a `USizeArray` is a `ScalarArray`, so every
function that looks inside the constructor must be `extern` or `implemented_by`.
-/
public inductive USizeArray : Type
  | public mk (data : Array USize)

namespace USizeArray

-- `lean_byte_array_size` reads the size of any scalar array, whatever its element size.
@[extern "lean_byte_array_size", tagged_return, expose]
public def size : (a : @& USizeArray) → Nat
  | mk a => a.size

/--
The size of `a` as a `USize`. Since `USize` can address all memory, no array has more elements than
`USize` can count.
-/
@[extern "lean_sarray_size", simp, expose]
public def usize (a : @& USizeArray) : USize :=
  a.size.toUSize

@[extern c inline "((size_t*)lean_sarray_cptr(#1))[#2]", expose]
public def uget : (a : @& USizeArray) → (i : USize) → (h : i.toNat < a.size := by get_elem_tactic) →
    USize
  | mk a, i, h => a.uget i h

@[expose]
public def get : (a : @& USizeArray) → (i : @& Nat) → (h : i < a.size := by get_elem_tactic) → USize
  | mk a, i, h => a[i]

@[inline]
private unsafe def getImpl : type_of% @get :=
  fun a i _ => a.uget i.toUSize lcProof

attribute [implemented_by getImpl] get

/-- Stores `v` at index `i` in place. Only valid when `a` is exclusive and `i` is in bounds. -/
@[extern c inline "#1;\n((size_t*)lean_sarray_cptr(#1))[#2] = #3"]
private unsafe def setUSizeUnsafe : USizeArray → USize → USize → USizeArray
  | .mk a, i, v => .mk <| a.uset i v lcProof

private unsafe def toUSizeChecked (n : Nat) : USize :=
  if n < USize.size >>> 1 then n.toUSize else panic! "out of memory"

private unsafe def mkWithCapacityImpl (a : Array USize) (capacity : Nat := a.size) : USizeArray :=
  let cap := toUSizeChecked capacity
  let sz := toUSizeChecked a.size
  let r : USizeArray := unsafeCast <| ScalarArray.allocate (System.Platform.numBits / 8).toUInt32 sz (max sz cap) lcProof
  loop r 0
where
  loop (r : USizeArray) (i : Nat) : USizeArray :=
    if h : i < a.size then loop (setUSizeUnsafe r i.toUSize a[i]) (i + 1) else r

private unsafe def mkImpl (a : Array USize) : USizeArray :=
  mkWithCapacityImpl a a.size

attribute [implemented_by mkImpl] USizeArray.mk

private unsafe def dataImpl (a : @& USizeArray) : Array USize :=
  loop 0 (Array.emptyWithCapacity a.size)
where
  loop (i : USize) (r : Array USize) : Array USize :=
    if h : i.toNat < a.size then loop (i + 1) (r.push (a.uget i h)) else r

/-- The elements of `a` as an `Array USize`. -/
@[implemented_by dataImpl, expose]
public def data : (a : @& USizeArray) → Array USize
  | mk a => a

private unsafe def emptyWithCapacityImpl (capacity : Nat) : USizeArray :=
  mkWithCapacityImpl #[] capacity

/-- An empty array with room for `capacity` elements before reallocating. -/
@[implemented_by emptyWithCapacityImpl, expose]
public def emptyWithCapacity (capacity : Nat) : USizeArray :=
  mk #[]

@[expose] public def empty : USizeArray := emptyWithCapacity 0

public instance : EmptyCollection USizeArray := ⟨empty⟩

public instance : Inhabited USizeArray := ⟨empty⟩

@[expose]
public def uset :
    (a : USizeArray) → (i : USize) → (v : USize) → (h : i.toNat < a.size := by get_elem_tactic) →
    USizeArray
  | mk a, i, v, h => mk (a.uset i v h)

private unsafe def usetImpl : type_of% @uset :=
  fun a i v _ => setUSizeUnsafe (unsafeCast <| ScalarArray.ensureExclusive (unsafeCast a)) i v

attribute [implemented_by usetImpl] uset

@[expose]
public def set :
    (a : USizeArray) → (i : Nat) → (v : USize) → (h : i < a.size := by get_elem_tactic) →
    USizeArray
  | mk a, i, v, h => mk (a.set i v h)

private unsafe def setImpl : type_of% @set :=
  fun a i v _ => usetImpl a i.toUSize v lcProof

attribute [implemented_by setImpl] set

public def get! (a : @& USizeArray) (i : @& Nat) : USize :=
  if h : i < a.size then a.get i h else panic! "index out of bounds"

public def getD (a : @& USizeArray) (i : @& Nat) (v₀ : USize) : USize :=
  if h : i < a.size then a.get i h else v₀

private unsafe def setBangImpl (a : USizeArray) (i : Nat) (v : USize) : USizeArray :=
  if h : i < a.size then setImpl a i v h else a

/-- Replaces the element at index `i`. If `i` is out of bounds, the array is returned unmodified. -/
@[implemented_by setBangImpl, expose]
public def set! : USizeArray → Nat → USize → USizeArray
  | mk a, i, v => mk (a.set! i v)

public instance : GetElem USizeArray Nat USize fun a i => i < a.size where
  getElem a i h := a.get i h

public instance : GetElem USizeArray USize USize fun a i => i.toNat < a.size where
  getElem a i h := a.uget i h

private unsafe def pushImpl (a : USizeArray) (v : USize) : USizeArray :=
  let s : ScalarArray := unsafeCast a
  let cap := s.capacity
  if s.size < cap then
    loop s.ensureExclusive
  else if cap < cap + cap + 1 then
    loop (s.copyWithCapacity (cap + cap + 1) lcProof)
  else
    panic! "out of memory"
where
  loop (s : ScalarArray) : USizeArray :=
    let i := s.size
    setUSizeUnsafe (unsafeCast (s.resizeUnsafe (i + 1) lcProof lcProof)) i v

@[implemented_by pushImpl, expose]
public def push : USizeArray → USize → USizeArray
  | mk a, v => mk (a.push v)

/--
Copies `n` bytes of the data of `src`, starting at byte `srcOff`, into the data of `dest`, starting at
byte `destOff`. Only valid when `dest` is exclusive and both ranges are within the capacities.
-/
-- TODO: core has no runtime function that copies a slice of a scalar array with any element size;
-- `lean_byte_array_copy_slice` only works for bytes. Replace this once core has one.
@[extern c inline "#1;\n__builtin_memcpy(lean_sarray_cptr(#1) + #4, lean_sarray_cptr(#2) + #3, #5)"]
private unsafe def memcpyUnsafe : USizeArray → @& USizeArray → (srcOff destOff n : USize) → USizeArray
  | dest, _, _, _, _ => dest

/--
Copies the `n` elements of `src` starting at index `srcOff` into `dest` starting at index `destOff`,
in place, and grows the size of `dest` to `destOff + n` if it is smaller. Only valid when `dest` is
exclusive, has capacity for `destOff + n` elements, and is not the same object as `src`, and when
`destOff ≤ dest.size` and `srcOff + n ≤ src.size`.
-/
@[inline]
private unsafe def copySliceUnsafe (dest : USizeArray) (src : @& USizeArray) (srcOff destOff n : USize) :
    USizeArray :=
  let esz := (unsafeCast src : ScalarArray).elemSize.toUSize
  let d : ScalarArray := unsafeCast (memcpyUnsafe dest src (srcOff * esz) (destOff * esz) (n * esz))
  unsafeCast (d.resizeUnsafe (max d.size (destOff + n)) lcProof lcProof)

private unsafe def appendImpl (a b : USizeArray) : USizeArray :=
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
public def append : USizeArray → USizeArray → USizeArray
  | mk a, mk b => mk (a ++ b)

public instance : Append USizeArray := ⟨append⟩

private unsafe def copySliceImpl (src : @& USizeArray) (srcOff : Nat) (dest : USizeArray)
    (destOff len : Nat) (exact : Bool := true) : USizeArray :=
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
public def copySlice (src : @& USizeArray) (srcOff : Nat) (dest : USizeArray) (destOff len : Nat)
    (exact : Bool := true) : USizeArray :=
  mk (dest.data.extract 0 destOff ++ src.data.extract srcOff (srcOff + len) ++
    dest.data.extract (destOff + min len (src.data.size - srcOff)) dest.data.size)

/-! ## Removing elements -/

public def isEmpty (a : @& USizeArray) : Bool := a.size == 0

private unsafe def popImpl (a : USizeArray) : USizeArray :=
  if a.size == 0 then
    a
  else
    let s : ScalarArray := ScalarArray.ensureExclusive (unsafeCast a)
    unsafeCast (s.resizeUnsafe (s.size - 1) lcProof lcProof)

/-- Removes the last element of `a`, if any, in place when `a` is not shared. -/
@[implemented_by popImpl, expose]
public def pop : USizeArray → USizeArray
  | mk a => mk a.pop

public def back? (a : @& USizeArray) : Option USize := a[a.size - 1]?

public def back! (a : @& USizeArray) : USize := a[a.size - 1]!

public def back (a : @& USizeArray) (h : 0 < a.size) : USize := a[a.size - 1]'(Nat.sub_lt h Nat.one_pos)

private unsafe def extractImpl (a : @& USizeArray) (start stop : Nat) : USizeArray :=
  let stop := min stop a.size
  if start < stop then
    let n := (stop - start).toUSize
    let r : USizeArray := unsafeCast <| ScalarArray.allocate (System.Platform.numBits / 8).toUInt32 0 n lcProof
    copySliceUnsafe r a start.toUSize 0 n
  else
    empty

/--
The elements of `a` from index `start` up to, but not including, `min stop a.size`, copied into a
new array.
-/
@[implemented_by extractImpl, expose]
public def extract : (a : @& USizeArray) → (start stop : Nat) → USizeArray
  | mk a, start, stop => mk (a.extract start stop)

/-! ## Linearity -/

/--
Marks `a` as linear, a debugging aid: if a marked array is ever shared and then modified, the
runtime reports it. Logically this is the identity.
-/
@[never_extract, extern "lean_sarray_mark_linear", expose]
public def markLinear (a : USizeArray) : USizeArray := a

/-- Returns `b`, marking it as linear if `a` is marked. Logically this is `b`. -/
@[never_extract, extern "lean_sarray_propagate_mark", expose]
public def propagateMark (a : @& USizeArray) (b : USizeArray) : USizeArray := b

/-! ## Search -/

/--
The index of the first element at or after `start` that satisfies `p`, with a proof that it is in
bounds.
-/
@[inline]
public def findFinIdx? (a : USizeArray) (p : USize → Bool) (start := 0) : Option (Fin a.size) :=
  let rec @[specialize] loop (i : Nat) :=
    if h : i < a.size then
      if p a[i] then some ⟨i, h⟩ else loop (i + 1)
    else
      none
    termination_by a.size - i
  loop start

/-- The index of the first element at or after `start` that satisfies `p`. -/
@[inline]
public def findIdx? (a : USizeArray) (p : USize → Bool) (start := 0) : Option Nat :=
  let rec @[specialize] loop (i : Nat) :=
    if h : i < a.size then
      if p a[i] then some i else loop (i + 1)
    else
      none
    termination_by a.size - i
  loop start

/-! ## Building arrays -/

private unsafe def replicateImpl (n : Nat) (v : USize) : USizeArray :=
  let sz := toUSizeChecked n
  loop sz (unsafeCast <| ScalarArray.allocate (System.Platform.numBits / 8).toUInt32 sz sz lcProof) 0
where
  loop (sz : USize) (r : USizeArray) (i : USize) : USizeArray :=
    if i < sz then loop sz (setUSizeUnsafe r i v) (i + 1) else r

/-- An array of `n` copies of `v`. -/
@[implemented_by replicateImpl, expose]
public def replicate (n : Nat) (v : USize) : USizeArray :=
  mk (Array.replicate n v)

private unsafe def ofFnImpl {n : Nat} (f : Fin n → USize) : USizeArray :=
  let sz := toUSizeChecked n
  loop (unsafeCast <| ScalarArray.allocate (System.Platform.numBits / 8).toUInt32 sz sz lcProof) 0
where
  loop (r : USizeArray) (i : Nat) : USizeArray :=
    if h : i < n then loop (setUSizeUnsafe r i.toUSize (f ⟨i, h⟩)) (i + 1) else r

/-- The array `#[f 0, …, f (n - 1)]`. -/
@[implemented_by ofFnImpl, expose]
public def ofFn {n : Nat} (f : Fin n → USize) : USizeArray :=
  mk (Array.ofFn f)

private unsafe def ofListImpl (l : List USize) : USizeArray :=
  loop l (emptyWithCapacity l.length)
where
  loop : List USize → USizeArray → USizeArray
    | [], r => r
    | x :: xs, r => loop xs (r.push x)

/-- The array with the elements of `l`. -/
@[implemented_by ofListImpl, expose]
public def ofList (l : List USize) : USizeArray :=
  mk l.toArray

/-! ## Iteration -/

@[specialize]
private unsafe def foldlMImpl {β : Type v} {m : Type v → Type w} [Monad m] (f : β → USize → m β)
    (init : β) (a : @& USizeArray) (start := 0) (stop := a.size) : m β :=
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
public def foldlM {β : Type v} {m : Type v → Type w} [Monad m] (f : β → USize → m β) (init : β)
    (a : @& USizeArray) (start := 0) (stop := a.size) : m β :=
  a.data.foldlM f init start stop

@[specialize]
private unsafe def foldrMImpl {β : Type v} {m : Type v → Type w} [Monad m] (f : USize → β → m β)
    (init : β) (a : @& USizeArray) : m β :=
  loop a.usize init
where
  loop (i : USize) (b : β) : m β :=
    if h : 0 < i ∧ (i - 1).toNat < a.size then do loop (i - 1) (← f (a.uget (i - 1) h.2) b)
    else pure b

/-- Folds a monadic function over the elements of `a`, from last to first. -/
@[implemented_by foldrMImpl, expose]
public def foldrM {β : Type v} {m : Type v → Type w} [Monad m] (f : USize → β → m β) (init : β)
    (a : @& USizeArray) : m β :=
  a.data.foldrM f init

@[inline, expose]
public def foldl {β : Type v} (f : β → USize → β) (init : β) (a : @& USizeArray) (start := 0)
    (stop := a.size) : β :=
  Id.run <| a.foldlM (pure <| f · ·) init start stop

@[inline, expose]
public def foldr {β : Type v} (f : USize → β → β) (init : β) (a : @& USizeArray) : β :=
  Id.run <| a.foldrM (pure <| f · ·) init

@[inline]
public def forM {m : Type v → Type w} [Monad m] (f : USize → m PUnit) (a : @& USizeArray) :
    m PUnit :=
  a.foldlM (fun _ x => f x) ⟨⟩

@[specialize]
private unsafe def forInImpl {β : Type v} {m : Type v → Type w} [Monad m] (a : @& USizeArray)
    (init : β) (f : USize → β → m (ForInStep β)) : m β :=
  loop 0 init
where
  loop (i : USize) (b : β) : m β :=
    if h : i.toNat < a.size then do
      match ← f (a.uget i h) b with
      | .done b => pure b
      | .yield b => loop (i + 1) b
    else pure b

@[implemented_by forInImpl]
public def forIn {β : Type v} {m : Type v → Type w} [Monad m] (a : @& USizeArray) (init : β)
    (f : USize → β → m (ForInStep β)) : m β :=
  ForIn.forIn a.data init f

public instance [Monad m] : ForIn m USizeArray USize where
  forIn a b f := USizeArray.forIn a b f

@[specialize]
private unsafe def anyImpl (a : @& USizeArray) (p : USize → Bool) : Bool :=
  loop 0
where
  loop (i : USize) : Bool :=
    if h : i.toNat < a.size then p (a.uget i h) || loop (i + 1) else false

/-- Whether some element of `a` satisfies `p`. -/
@[implemented_by anyImpl]
public def any (a : @& USizeArray) (p : USize → Bool) : Bool :=
  a.data.any p

@[specialize]
private unsafe def allImpl (a : @& USizeArray) (p : USize → Bool) : Bool :=
  loop 0
where
  loop (i : USize) : Bool :=
    if h : i.toNat < a.size then p (a.uget i h) && loop (i + 1) else true

/-- Whether every element of `a` satisfies `p`. -/
@[implemented_by allImpl]
public def all (a : @& USizeArray) (p : USize → Bool) : Bool :=
  a.data.all p

private unsafe def containsImpl (a : @& USizeArray) (v : USize) : Bool :=
  anyImpl a (v == ·)

/-- Whether `v` is an element of `a`. -/
@[implemented_by containsImpl]
public def contains (a : @& USizeArray) (v : USize) : Bool :=
  a.data.contains v

/-! ## Equality and hashing -/

private theorem data_injective : {a b : USizeArray} → a.data = b.data → a = b
  | mk _, mk _, rfl => rfl

/-- Decides equality by comparing the two arrays' memory. -/
@[extern "lean_sarray_dec_eq"]
public def decEq (a b : @& USizeArray) : Decidable (a = b) :=
  decidable_of_iff (a.data = b.data) ⟨data_injective, fun h => h ▸ rfl⟩

public instance : DecidableEq USizeArray := decEq

private unsafe def hashImpl (a : @& USizeArray) : UInt64 :=
  foldlMImpl (m := Id) (fun r x => mixHash r (Hashable.hash x)) 7 a

/-- The same hash as `a.data`. -/
@[implemented_by hashImpl]
public def hash (a : @& USizeArray) : UInt64 :=
  Hashable.hash a.data

public instance : Hashable USizeArray := ⟨hash⟩

/-! ## Conversion and printing -/

@[expose] public def toList (a : USizeArray) : List USize := a.data.toList

public instance : Repr USizeArray where
  reprPrec a _ := "USizeArray.mk " ++ repr a.data

public instance : ToString USizeArray where
  toString a := "USizeArray.mk " ++ toString a.data

/-! ## Slices -/

/-- Internal representation of `USizeArray.Slice`. -/
public structure SliceData where
  /-- The underlying array. -/
  array : USizeArray
  /-- The starting index of the slice (inclusive). -/
  start : Nat
  /-- The ending index of the slice (exclusive). -/
  stop : Nat
  /-- The starting index is no later than the ending index. -/
  start_le_stop : start ≤ stop
  /-- The ending index is no later than the end of the array. -/
  stop_le_array_size : stop ≤ array.size

/--
A region of a `USizeArray`: the elements from index `start` up to, but not including, `stop`.
Taking a slice doesn't copy the array. Slices are written with core's slice notation, such as
`a[i...j]`, `a[i...*]` or `a[*...j]`.
-/
public abbrev Slice := Std.Slice SliceData

public instance : Std.Slice.Self (Std.Slice SliceData) Slice where

namespace Slice

@[always_inline, inline, expose, inherit_doc SliceData.array]
public def array (s : Slice) : USizeArray := s.internalRepresentation.array

@[always_inline, inline, expose, inherit_doc SliceData.start]
public def start (s : Slice) : Nat := s.internalRepresentation.start

@[always_inline, inline, expose, inherit_doc SliceData.stop]
public def stop (s : Slice) : Nat := s.internalRepresentation.stop

@[inherit_doc SliceData.start_le_stop]
public theorem start_le_stop (s : Slice) : s.start ≤ s.stop := s.internalRepresentation.start_le_stop

@[inherit_doc SliceData.stop_le_array_size]
public theorem stop_le_array_size (s : Slice) : s.stop ≤ s.array.size :=
  s.internalRepresentation.stop_le_array_size

public instance : Std.Slice.SliceSize SliceData where
  size s := s.internalRepresentation.stop - s.internalRepresentation.start

public theorem size_eq (s : Slice) : s.size = s.stop - s.start := rfl

/-- The element at index `i` of the slice, counted from the start of the slice. -/
@[inline, expose]
public def get (s : Slice) (i : Nat) (h : i < s.size := by get_elem_tactic) : USize :=
  s.array[s.start + i]'(by have := s.stop_le_array_size; rw [size_eq] at h; omega)

public instance : GetElem Slice Nat USize fun s i => i < s.size where
  getElem s i h := s.get i h

/-- The element at index `i` of the slice, or `v₀` if `i` is out of bounds. -/
@[inline]
public def getD (s : Slice) (i : Nat) (v₀ : USize) : USize :=
  if h : i < s.size then s[i] else v₀

/-- The element at index `i` of the slice, or `default` if `i` is out of bounds. -/
public abbrev get! (s : Slice) (i : Nat) : USize :=
  getD s i default

/-- Removes the first element of the slice, if any. -/
@[expose]
public def popFront (s : Slice) : Slice :=
  if h : s.start < s.stop then
    ⟨{ s.internalRepresentation with start := s.start + 1, start_le_stop := h }⟩
  else
    s

/-- The empty slice, backed by an empty array. -/
@[expose]
public protected def empty : Slice :=
  ⟨{ array := USizeArray.empty, start := 0, stop := 0, start_le_stop := Nat.le_refl 0,
     stop_le_array_size := Nat.le_refl 0 }⟩

public instance : EmptyCollection Slice := ⟨Slice.empty⟩

public instance : Inhabited Slice := ⟨Slice.empty⟩

/-- The elements of the slice, copied into a new array with a single `memcpy`. -/
@[expose]
public def copy (s : Slice) : USizeArray :=
  s.array.extract s.start s.stop

public instance : Coe Slice USizeArray := ⟨copy⟩

public theorem getElem_eq (s : Slice) (i : Nat) (h : i < s.size) :
    s[i] = s.array[s.start + i]'(by have := s.stop_le_array_size; rw [size_eq] at h; omega) := rfl

public instance : Repr Slice where
  reprPrec s _ := repr s.copy ++ ".toSlice"

public instance : ToString Slice where
  toString s := toString s.copy

end Slice

/--
The slice of `a` from index `start` up to, but not including, `stop`. If `start` or `stop` are not
valid bounds, they are clamped to the size of `a`, and `start` is clamped to `stop`.
-/
@[expose]
public def toSlice (a : USizeArray) (start : Nat := 0) (stop : Nat := a.size) : Slice :=
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

public instance : Std.Rcc.Sliceable USizeArray Nat Slice where
  mkSlice a range := a.toSlice range.lower (range.upper + 1)

public instance : Std.Rco.Sliceable USizeArray Nat Slice where
  mkSlice a range := a.toSlice range.lower range.upper

public instance : Std.Rci.Sliceable USizeArray Nat Slice where
  mkSlice a range := a.toSlice range.lower

public instance : Std.Roc.Sliceable USizeArray Nat Slice where
  mkSlice a range := a.toSlice (range.lower + 1) (range.upper + 1)

public instance : Std.Roo.Sliceable USizeArray Nat Slice where
  mkSlice a range := a.toSlice (range.lower + 1) range.upper

public instance : Std.Roi.Sliceable USizeArray Nat Slice where
  mkSlice a range := a.toSlice (range.lower + 1)

public instance : Std.Ric.Sliceable USizeArray Nat Slice where
  mkSlice a range := a.toSlice 0 (range.upper + 1)

public instance : Std.Rio.Sliceable USizeArray Nat Slice where
  mkSlice a range := a.toSlice 0 range.upper

public instance : Std.Rii.Sliceable USizeArray Nat Slice where
  mkSlice a _ := a.toSlice

namespace Slice

/-- The slice of `s` from index `start` up to, but not including, `stop`, clamped like `toSlice`. -/
@[expose]
public def slice (s : Slice) (start : Nat := 0) (stop : Nat := s.size) : Slice :=
  s.array.toSlice (s.start + min start s.size) (s.start + min stop s.size)

end Slice

public instance : Std.Rcc.Sliceable Slice Nat Slice where
  mkSlice s range := s.slice range.lower (range.upper + 1)

public instance : Std.Rco.Sliceable Slice Nat Slice where
  mkSlice s range := s.slice range.lower range.upper

public instance : Std.Rci.Sliceable Slice Nat Slice where
  mkSlice s range := s.slice range.lower

public instance : Std.Roc.Sliceable Slice Nat Slice where
  mkSlice s range := s.slice (range.lower + 1) (range.upper + 1)

public instance : Std.Roo.Sliceable Slice Nat Slice where
  mkSlice s range := s.slice (range.lower + 1) range.upper

public instance : Std.Roi.Sliceable Slice Nat Slice where
  mkSlice s range := s.slice (range.lower + 1)

public instance : Std.Ric.Sliceable Slice Nat Slice where
  mkSlice s range := s.slice 0 (range.upper + 1)

public instance : Std.Rio.Sliceable Slice Nat Slice where
  mkSlice s range := s.slice 0 range.upper

public instance : Std.Rii.Sliceable Slice Nat Slice where
  mkSlice s _ := s

/-- The iterator over the elements of a slice, used for `for` loops and the generic slice API. -/
public structure SliceIterator where
  /-- The rest of the slice. -/
  xs : Slice

@[inline, expose]
public def SliceIterator.step :
    Std.IterM (α := SliceIterator) Id USize →
      Std.IterStep (Std.IterM (α := SliceIterator) m USize) USize
  | ⟨⟨xs⟩⟩ =>
    if h : xs.start < xs.stop then
      have := xs.stop_le_array_size
      .yield ⟨⟨⟨xs.array, xs.start + 1, xs.stop, h, xs.stop_le_array_size⟩⟩⟩ xs.array[xs.start]
    else
      .done

public instance : Std.Iterator SliceIterator Id USize where
  IsPlausibleStep it step := step = SliceIterator.step it
  step it := pure <| .deflate ⟨SliceIterator.step it, rfl⟩

private def SliceIterator.finitenessRelation : Std.Iterators.FinitenessRelation SliceIterator Id where
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

public instance : Std.Iterators.Finite SliceIterator Id :=
  .of_finitenessRelation SliceIterator.finitenessRelation

public instance [Monad m] : Std.IteratorLoop SliceIterator Id m := .defaultImplementation

public instance : Std.ToIterator (Std.Slice SliceData) Id SliceIterator USize :=
  Std.ToIterator.of SliceIterator (⟨⟨·⟩⟩)

public instance [Monad m] : ForIn m Slice USize := inferInstance

@[simp] public theorem size_mk (a : Array USize) : (mk a).size = a.size := rfl

@[simp] public theorem data_mk (a : Array USize) : (mk a).data = a := rfl

@[simp] public theorem mk_data (a : USizeArray) : mk a.data = a := by cases a; rfl

public theorem size_eq_data_size (a : USizeArray) : a.size = a.data.size := by cases a; rfl

@[simp] public theorem size_data (a : USizeArray) : a.data.size = a.size :=
  (size_eq_data_size a).symm

@[simp] public theorem size_uset (a : USizeArray) (i : USize) (v : USize) (h) :
    (a.uset i v h).size = a.size := by
  cases a; exact Array.size_set ..

@[simp] public theorem size_set (a : USizeArray) (i : Nat) (v : USize) (h) :
    (a.set i v h).size = a.size := by
  cases a; exact Array.size_set ..

@[simp] public theorem size_push (a : USizeArray) (v : USize) : (a.push v).size = a.size + 1 := by
  cases a; simp [push, size]

@[simp] public theorem data_append (a b : USizeArray) : (a ++ b).data = a.data ++ b.data := by
  cases a; cases b; rfl

@[simp] public theorem size_append (a b : USizeArray) : (a ++ b).size = a.size + b.size := by
  simp [-size_data, size_eq_data_size]

@[ext] public theorem ext {a b : USizeArray} (h : a.data = b.data) : a = b := data_injective h

@[simp] public theorem getElem_mk (a : Array USize) (i : Nat) (h : i < (mk a).size) :
    (mk a)[i] = a[i] := rfl

public theorem getElem_eq_getElem_data (a : USizeArray) (i : Nat) (h : i < a.size) :
    a[i] = a.data[i]'(size_eq_data_size a ▸ h) := by
  cases a; rfl

@[simp] public theorem getElem_data (a : USizeArray) (i : Nat) (h : i < a.data.size) :
    a.data[i] = a[i]'(by simpa using h) := by
  cases a; rfl

public theorem ext_getElem {a b : USizeArray} (h₁ : a.size = b.size)
    (h₂ : ∀ (i : Nat) (hi₁ : i < a.size) (hi₂ : i < b.size), a[i] = b[i]) : a = b := by
  ext i hi₁ hi₂
  · simpa using h₁
  · simpa using h₂ i (by simpa using hi₁) (by simpa using hi₂)

@[simp] public theorem getElem_usize (a : USizeArray) (i : USize) (h : i.toNat < a.size) :
    a[i] = a[i.toNat] := by
  cases a; rfl

@[simp] public theorem data_uset (a : USizeArray) (i : USize) (v : USize) (h) :
    (a.uset i v h).data = a.data.set i.toNat v (size_eq_data_size a ▸ h) := by
  cases a; rfl

@[simp] public theorem data_set (a : USizeArray) (i : Nat) (v : USize) (h) :
    (a.set i v h).data = a.data.set i v (size_eq_data_size a ▸ h) := by
  cases a; rfl

@[simp] public theorem data_push (a : USizeArray) (v : USize) : (a.push v).data = a.data.push v := by
  cases a; rfl

@[simp] public theorem data_pop (a : USizeArray) : a.pop.data = a.data.pop := by
  cases a; rfl

@[simp] public theorem data_extract (a : USizeArray) (start stop : Nat) :
    (a.extract start stop).data = a.data.extract start stop := by
  cases a; rfl

@[simp] public theorem data_replicate (n : Nat) (v : USize) :
    (replicate n v).data = Array.replicate n v := rfl

@[simp] public theorem data_ofFn {n : Nat} (f : Fin n → USize) : (ofFn f).data = Array.ofFn f := rfl

@[simp] public theorem data_empty : (empty : USizeArray).data = #[] := rfl

@[simp] public theorem size_pop (a : USizeArray) : a.pop.size = a.size - 1 := by
  simp [-size_data, size_eq_data_size]

@[simp] public theorem size_extract (a : USizeArray) (start stop : Nat) :
    (a.extract start stop).size = min stop a.size - start := by
  simp [-size_data, size_eq_data_size]

@[simp] public theorem size_replicate (n : Nat) (v : USize) : (replicate n v).size = n := by
  simp [-size_data, size_eq_data_size]

@[simp] public theorem size_ofFn {n : Nat} (f : Fin n → USize) : (ofFn f).size = n := by
  simp [-size_data, size_eq_data_size]

@[simp] public theorem size_empty : (empty : USizeArray).size = 0 := rfl

@[simp] public theorem getElem_set (a : USizeArray) (i : Nat) (v : USize) (h) (j : Nat) (hj) :
    (a.set i v h)[j]'hj = if i = j then v else a[j]'(by simpa using hj) := by
  simp [-getElem_data, getElem_eq_getElem_data, Array.getElem_set]

@[simp] public theorem getElem_push (a : USizeArray) (v : USize) (i : Nat) (h) :
    (a.push v)[i]'h = if h' : i < a.size then a[i] else v := by
  simp [-getElem_data, getElem_eq_getElem_data, Array.getElem_push, -size_data, size_eq_data_size]

@[simp] public theorem getElem_pop (a : USizeArray) (i : Nat) (h) :
    a.pop[i]'h = a[i]'(by simp at h; omega) := by
  simp [-getElem_data, getElem_eq_getElem_data]

@[simp] public theorem getElem_append (a b : USizeArray) (i : Nat) (h) :
    (a ++ b)[i]'h = if h' : i < a.size then a[i] else b[i - a.size]'(by simp at h; omega) := by
  simp [-getElem_data, getElem_eq_getElem_data, Array.getElem_append, -size_data, size_eq_data_size]

@[simp] public theorem getElem_extract (a : USizeArray) (start stop i : Nat) (h) :
    (a.extract start stop)[i]'h = a[start + i]'(by simp at h; omega) := by
  simp [-getElem_data, getElem_eq_getElem_data]

@[simp] public theorem getElem_replicate (n : Nat) (v : USize) (i : Nat) (h) :
    (replicate n v)[i]'h = v := by
  simp [-getElem_data, getElem_eq_getElem_data]

@[simp] public theorem getElem_ofFn {n : Nat} (f : Fin n → USize) (i : Nat) (h) :
    (ofFn f)[i]'h = f ⟨i, by simpa using h⟩ := by
  simp [-getElem_data, getElem_eq_getElem_data]

public theorem foldl_eq_foldl_data {β : Type v} (f : β → USize → β) (init : β) (a : USizeArray) :
    a.foldl f init = a.data.foldl f init := by
  rfl

public theorem foldr_eq_foldr_data {β : Type v} (f : USize → β → β) (init : β) (a : USizeArray) :
    a.foldr f init = a.data.foldr f init := by
  rfl

@[simp] public theorem toList_data (a : USizeArray) : a.data.toList = a.toList := rfl

@[simp] public theorem emptyc_eq_empty : (∅ : USizeArray) = empty := rfl

@[simp] public theorem emptyWithCapacity_eq_empty (c : Nat) : emptyWithCapacity c = empty := rfl

public theorem size_eq_zero_iff {a : USizeArray} : a.size = 0 ↔ a = empty := by
  simp [USizeArray.ext_iff, ← Array.size_eq_zero_iff]

@[simp] public theorem data_set! (a : USizeArray) (i : Nat) (v : USize) :
    (a.set! i v).data = a.data.set! i v := by
  cases a; rfl

@[simp] public theorem size_set! (a : USizeArray) (i : Nat) (v : USize) :
    (a.set! i v).size = a.size := by
  simp [-size_data, size_eq_data_size]

public theorem getElem!_eq_getElem!_data (a : USizeArray) (i : Nat) : a[i]! = a.data[i]! := by
  rcases a with ⟨a⟩
  by_cases h : i < a.size <;> simp [getElem!_def, getElem?_def, h] <;> rfl

@[simp] public theorem data_ofList (l : List USize) : (ofList l).data = l.toArray := rfl

@[simp] public theorem size_ofList (l : List USize) : (ofList l).size = l.length := rfl

@[simp] public theorem getElem_ofList (l : List USize) (i : Nat) (h) :
    (ofList l)[i]'h = l[i]'(by simpa using h) := rfl

@[simp] public theorem toList_ofList (l : List USize) : (ofList l).toList = l := rfl

@[simp] public theorem ofList_toList (a : USizeArray) : ofList a.toList = a := by
  simp [USizeArray.ext_iff, ← toList_data]

@[simp] public theorem markLinear_eq (a : USizeArray) : a.markLinear = a := rfl

@[simp] public theorem propagateMark_eq (a b : USizeArray) : a.propagateMark b = b := rfl

@[simp] public theorem append_empty (a : USizeArray) : a ++ empty = a := by
  simp [USizeArray.ext_iff]

@[simp] public theorem empty_append (a : USizeArray) : empty ++ a = a := by
  simp [USizeArray.ext_iff]

public theorem append_assoc (a b c : USizeArray) : a ++ b ++ c = a ++ (b ++ c) := by
  simp [USizeArray.ext_iff]

@[simp] public theorem append_eq_empty_iff {a b : USizeArray} :
    a ++ b = empty ↔ a = empty ∧ b = empty := by
  simp only [USizeArray.ext_iff, data_append, data_empty, Array.append_eq_empty_iff]

@[simp] public theorem append_right_inj (a : USizeArray) {b c : USizeArray} :
    a ++ b = a ++ c ↔ b = c := by
  simp only [USizeArray.ext_iff, data_append, Array.append_right_inj]

@[simp] public theorem append_left_inj {a b : USizeArray} (c : USizeArray) :
    a ++ c = b ++ c ↔ a = b := by
  simp only [USizeArray.ext_iff, data_append, Array.append_left_inj]

public theorem getElem_append_left {a b : USizeArray} {i : Nat} (h : i < a.size) :
    (a ++ b)[i]'(by simp; omega) = a[i] := by
  simp [h]

public theorem getElem_append_right {a b : USizeArray} {i : Nat} (h : a.size ≤ i)
    (h' : i < (a ++ b).size) : (a ++ b)[i] = b[i - a.size]'(by simp at h'; omega) := by
  simp [Nat.not_lt.mpr h]

@[simp] public theorem extract_same (a : USizeArray) (i : Nat) : a.extract i i = empty := by
  simp [USizeArray.ext_iff]; omega

@[simp] public theorem extract_zero_size (a : USizeArray) : a.extract 0 a.size = a := by
  simp [USizeArray.ext_iff]

@[simp] public theorem extract_eq_empty_iff {a : USizeArray} {i j : Nat} :
    a.extract i j = empty ↔ min j a.size ≤ i := by
  simp [USizeArray.ext_iff]

public theorem extract_extract (a : USizeArray) (i j k l : Nat) :
    (a.extract i j).extract k l = a.extract (i + k) (min (i + l) j) := by
  simp [USizeArray.ext_iff]

public theorem extract_append_extract (a : USizeArray) (i j k : Nat) :
    a.extract i j ++ a.extract j k = a.extract (min i j) (max j k) := by
  simp [USizeArray.ext_iff]

@[simp] public theorem extract_append_eq_left (a b : USizeArray) : (a ++ b).extract 0 a.size = a := by
  simp [USizeArray.ext_iff]

@[simp] public theorem extract_append_eq_right (a b : USizeArray) :
    (a ++ b).extract a.size (a.size + b.size) = b := by
  simp [USizeArray.ext_iff, -size_data, size_eq_data_size]

@[simp] public theorem data_copySlice (src : USizeArray) (srcOff : Nat) (dest : USizeArray)
    (destOff len : Nat) (exact : Bool) :
    (src.copySlice srcOff dest destOff len exact).data =
      dest.data.extract 0 destOff ++ src.data.extract srcOff (srcOff + len) ++
        dest.data.extract (destOff + min len (src.size - srcOff)) dest.size := by
  simp [copySlice]

public theorem copySlice_eq_append (src : USizeArray) (srcOff : Nat) (dest : USizeArray)
    (destOff len : Nat) (exact : Bool) :
    src.copySlice srcOff dest destOff len exact =
      dest.extract 0 destOff ++ src.extract srcOff (srcOff + len) ++
        dest.extract (destOff + min len (src.size - srcOff)) dest.size := by
  simp [USizeArray.ext_iff]

@[simp] public theorem Slice.size_copy (s : Slice) : s.copy.size = s.size := by
  have := s.stop_le_array_size
  simp only [Slice.copy, size_extract, Slice.size_eq]
  omega

end USizeArray

end ScalarArray

/-- The array with the elements of `l`. -/
@[inline, expose]
public def List.toUSizeArray (l : List USize) : ScalarArray.USizeArray :=
  ScalarArray.USizeArray.ofList l
