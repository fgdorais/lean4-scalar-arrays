/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import all ScalarArray.Internal
public import Std.Data.Iterators

/-!
# Arrays of `Float`

`ScalarArray.Float64Array` stores `Float` values unboxed, 8 bytes per element, in a Lean runtime
scalar array. Its logical model is `Array Float`: `Float64Array.mk` and `Float64Array.data` convert
between the two, and every operation is specified by its effect on the model.

The runtime representation is a `ScalarArray` with element size 8. Reads and in-place writes
are inline C. `uset`, `set` and `push` update the array in place when it is not shared and copy
it otherwise, like `Array` and `ByteArray`.

`Float64Array` has the same runtime representation as the core `FloatArray`, with the same API
as the other arrays in this library.
-/

namespace ScalarArray

/--
Arrays of `Float` values, stored unboxed in a scalar array with element size 8.

The logical model is an `Array Float`. At runtime a `Float64Array` is a `ScalarArray`, so every
function that looks inside the constructor must be `extern` or `implemented_by`.
-/
public inductive Float64Array : Type
  | public mk (data : Array Float)

namespace Float64Array

-- `lean_byte_array_size` reads the size of any scalar array, whatever its element size.
@[extern "lean_byte_array_size", tagged_return, expose]
public def size : (a : @& Float64Array) → Nat
  | mk a => a.size

/--
The size of `a` as a `USize`. Since `USize` can address all memory, no array has more elements than
`USize` can count.
-/
@[extern "lean_sarray_size", simp, expose]
public def usize (a : @& Float64Array) : USize :=
  a.size.toUSize

@[extern c inline "((double*)lean_sarray_cptr(#1))[#2]", expose]
public def uget : (a : @& Float64Array) → (i : USize) → (h : i.toNat < a.size := by get_elem_tactic) →
    Float
  | mk a, i, h => a.uget i h

@[expose]
public def get : (a : @& Float64Array) → (i : @& Nat) → (h : i < a.size := by get_elem_tactic) → Float
  | mk a, i, h => a[i]

@[inline]
private unsafe def getImpl : type_of% @get :=
  fun a i _ => a.uget i.toUSize lcProof

attribute [implemented_by getImpl] get

/-- Stores `v` at index `i` in place. Only valid when `a` is exclusive and `i` is in bounds. -/
@[extern c inline "#1;\n((double*)lean_sarray_cptr(#1))[#2] = #3"]
private unsafe def setFloat64Unsafe : Float64Array → USize → Float → Float64Array
  | .mk a, i, v => .mk <| a.uset i v lcProof

private unsafe def toUSizeChecked (n : Nat) : USize :=
  if n < USize.size >>> 1 then n.toUSize else panic! "out of memory"

private unsafe def mkWithCapacityImpl (a : Array Float) (capacity : Nat := a.size) : Float64Array :=
  let cap := toUSizeChecked capacity
  let sz := toUSizeChecked a.size
  let r : Float64Array := unsafeCast <| ScalarArray.allocate 8 sz (max sz cap) lcProof
  loop r 0
where
  loop (r : Float64Array) (i : Nat) : Float64Array :=
    if h : i < a.size then loop (setFloat64Unsafe r i.toUSize a[i]) (i + 1) else r

private unsafe def mkImpl (a : Array Float) : Float64Array :=
  mkWithCapacityImpl a a.size

attribute [implemented_by mkImpl] Float64Array.mk

private unsafe def dataImpl (a : @& Float64Array) : Array Float :=
  loop 0 (Array.emptyWithCapacity a.size)
where
  loop (i : USize) (r : Array Float) : Array Float :=
    if h : i.toNat < a.size then loop (i + 1) (r.push (a.uget i h)) else r

/-- The elements of `a` as an `Array Float`. -/
@[implemented_by dataImpl, expose]
public def data : (a : @& Float64Array) → Array Float
  | mk a => a

private unsafe def emptyWithCapacityImpl (capacity : Nat) : Float64Array :=
  mkWithCapacityImpl #[] capacity

/-- An empty array with room for `capacity` elements before reallocating. -/
@[implemented_by emptyWithCapacityImpl, expose]
public def emptyWithCapacity (capacity : Nat) : Float64Array :=
  mk #[]

@[expose] public def empty : Float64Array := emptyWithCapacity 0

public instance : EmptyCollection Float64Array := ⟨empty⟩

public instance : Inhabited Float64Array := ⟨empty⟩

@[expose]
public def uset :
    (a : Float64Array) → (i : USize) → (v : Float) → (h : i.toNat < a.size := by get_elem_tactic) →
    Float64Array
  | mk a, i, v, h => mk (a.uset i v h)

private unsafe def usetImpl : type_of% @uset :=
  fun a i v _ => setFloat64Unsafe (unsafeCast <| ScalarArray.ensureExclusive (unsafeCast a)) i v

attribute [implemented_by usetImpl] uset

@[expose]
public def set :
    (a : Float64Array) → (i : Nat) → (v : Float) → (h : i < a.size := by get_elem_tactic) →
    Float64Array
  | mk a, i, v, h => mk (a.set i v h)

private unsafe def setImpl : type_of% @set :=
  fun a i v _ => usetImpl a i.toUSize v lcProof

attribute [implemented_by setImpl] set

public def get! (a : @& Float64Array) (i : @& Nat) : Float :=
  if h : i < a.size then a.get i h else panic! "index out of bounds"

public def getD (a : @& Float64Array) (i : @& Nat) (v₀ : Float) : Float :=
  if h : i < a.size then a.get i h else v₀

private unsafe def setBangImpl (a : Float64Array) (i : Nat) (v : Float) : Float64Array :=
  if h : i < a.size then setImpl a i v h else a

/-- Replaces the element at index `i`. If `i` is out of bounds, the array is returned unmodified. -/
@[implemented_by setBangImpl, expose]
public def set! : Float64Array → Nat → Float → Float64Array
  | mk a, i, v => mk (a.set! i v)

public instance : GetElem Float64Array Nat Float fun a i => i < a.size where
  getElem a i h := a.get i h

public instance : GetElem Float64Array USize Float fun a i => i.toNat < a.size where
  getElem a i h := a.uget i h

private unsafe def pushImpl (a : Float64Array) (v : Float) : Float64Array :=
  let s : ScalarArray := unsafeCast a
  let cap := s.capacity
  if s.size < cap then
    loop s.ensureExclusive
  else if cap < cap + cap + 1 then
    loop (s.copyWithCapacity (cap + cap + 1) lcProof)
  else
    panic! "out of memory"
where
  loop (s : ScalarArray) : Float64Array :=
    let i := s.size
    setFloat64Unsafe (unsafeCast (s.resizeUnsafe (i + 1) lcProof lcProof)) i v

@[implemented_by pushImpl, expose]
public def push : Float64Array → Float → Float64Array
  | mk a, v => mk (a.push v)

/--
Copies `n` bytes of the data of `src`, starting at byte `srcOff`, into the data of `dest`, starting at
byte `destOff`. Only valid when `dest` is exclusive and both ranges are within the capacities.
-/
-- TODO: core has no runtime function that copies a slice of a scalar array with any element size;
-- `lean_byte_array_copy_slice` only works for bytes. Replace this once core has one.
@[extern c inline "#1;\n__builtin_memcpy(lean_sarray_cptr(#1) + #4, lean_sarray_cptr(#2) + #3, #5)"]
private unsafe def memcpyUnsafe : Float64Array → @& Float64Array → (srcOff destOff n : USize) → Float64Array
  | dest, _, _, _, _ => dest

/--
Copies the `n` elements of `src` starting at index `srcOff` into `dest` starting at index `destOff`,
in place, and grows the size of `dest` to `destOff + n` if it is smaller. Only valid when `dest` is
exclusive, has capacity for `destOff + n` elements, and is not the same object as `src`, and when
`destOff ≤ dest.size` and `srcOff + n ≤ src.size`.
-/
@[inline]
private unsafe def copySliceUnsafe (dest : Float64Array) (src : @& Float64Array) (srcOff destOff n : USize) :
    Float64Array :=
  let esz := (unsafeCast src : ScalarArray).elemSize.toUSize
  let d : ScalarArray := unsafeCast (memcpyUnsafe dest src (srcOff * esz) (destOff * esz) (n * esz))
  unsafeCast (d.resizeUnsafe (max d.size (destOff + n)) lcProof lcProof)

private unsafe def appendImpl (a b : Float64Array) : Float64Array :=
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
public def append : Float64Array → Float64Array → Float64Array
  | mk a, mk b => mk (a ++ b)

public instance : Append Float64Array := ⟨append⟩

private unsafe def copySliceImpl (src : @& Float64Array) (srcOff : Nat) (dest : Float64Array)
    (destOff len : Nat) (exact : Bool := true) : Float64Array :=
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
public def copySlice (src : @& Float64Array) (srcOff : Nat) (dest : Float64Array) (destOff len : Nat)
    (exact : Bool := true) : Float64Array :=
  mk (dest.data.extract 0 destOff ++ src.data.extract srcOff (srcOff + len) ++
    dest.data.extract (destOff + min len (src.data.size - srcOff)) dest.data.size)

/-! ## Removing elements -/

public def isEmpty (a : @& Float64Array) : Bool := a.size == 0

private unsafe def popImpl (a : Float64Array) : Float64Array :=
  if a.size == 0 then
    a
  else
    let s : ScalarArray := ScalarArray.ensureExclusive (unsafeCast a)
    unsafeCast (s.resizeUnsafe (s.size - 1) lcProof lcProof)

/-- Removes the last element of `a`, if any, in place when `a` is not shared. -/
@[implemented_by popImpl, expose]
public def pop : Float64Array → Float64Array
  | mk a => mk a.pop

public def back? (a : @& Float64Array) : Option Float := a[a.size - 1]?

public def back! (a : @& Float64Array) : Float := a[a.size - 1]!

public def back (a : @& Float64Array) (h : 0 < a.size) : Float := a[a.size - 1]'(Nat.sub_lt h Nat.one_pos)

private unsafe def extractImpl (a : @& Float64Array) (start stop : Nat) : Float64Array :=
  let stop := min stop a.size
  if start < stop then
    let n := (stop - start).toUSize
    let r : Float64Array := unsafeCast <| ScalarArray.allocate 8 0 n lcProof
    copySliceUnsafe r a start.toUSize 0 n
  else
    empty

/--
The elements of `a` from index `start` up to, but not including, `min stop a.size`, copied into a
new array.
-/
@[implemented_by extractImpl, expose]
public def extract : (a : @& Float64Array) → (start stop : Nat) → Float64Array
  | mk a, start, stop => mk (a.extract start stop)

/-! ## Linearity -/

/--
Marks `a` as linear, a debugging aid: if a marked array is ever shared and then modified, the
runtime reports it. Logically this is the identity.
-/
@[never_extract, extern "lean_sarray_mark_linear", expose]
public def markLinear (a : Float64Array) : Float64Array := a

/-- Returns `b`, marking it as linear if `a` is marked. Logically this is `b`. -/
@[never_extract, extern "lean_sarray_propagate_mark", expose]
public def propagateMark (a : @& Float64Array) (b : Float64Array) : Float64Array := b

/-! ## Search -/

/--
The index of the first element at or after `start` that satisfies `p`, with a proof that it is in
bounds.
-/
@[inline]
public def findFinIdx? (a : Float64Array) (p : Float → Bool) (start := 0) : Option (Fin a.size) :=
  let rec @[specialize] loop (i : Nat) :=
    if h : i < a.size then
      if p a[i] then some ⟨i, h⟩ else loop (i + 1)
    else
      none
    termination_by a.size - i
  loop start

/-- The index of the first element at or after `start` that satisfies `p`. -/
@[inline]
public def findIdx? (a : Float64Array) (p : Float → Bool) (start := 0) : Option Nat :=
  let rec @[specialize] loop (i : Nat) :=
    if h : i < a.size then
      if p a[i] then some i else loop (i + 1)
    else
      none
    termination_by a.size - i
  loop start

/-! ## Building arrays -/

private unsafe def replicateImpl (n : Nat) (v : Float) : Float64Array :=
  let sz := toUSizeChecked n
  loop sz (unsafeCast <| ScalarArray.allocate 8 sz sz lcProof) 0
where
  loop (sz : USize) (r : Float64Array) (i : USize) : Float64Array :=
    if i < sz then loop sz (setFloat64Unsafe r i v) (i + 1) else r

/-- An array of `n` copies of `v`. -/
@[implemented_by replicateImpl, expose]
public def replicate (n : Nat) (v : Float) : Float64Array :=
  mk (Array.replicate n v)

private unsafe def ofFnImpl {n : Nat} (f : Fin n → Float) : Float64Array :=
  let sz := toUSizeChecked n
  loop (unsafeCast <| ScalarArray.allocate 8 sz sz lcProof) 0
where
  loop (r : Float64Array) (i : Nat) : Float64Array :=
    if h : i < n then loop (setFloat64Unsafe r i.toUSize (f ⟨i, h⟩)) (i + 1) else r

/-- The array `#[f 0, …, f (n - 1)]`. -/
@[implemented_by ofFnImpl, expose]
public def ofFn {n : Nat} (f : Fin n → Float) : Float64Array :=
  mk (Array.ofFn f)

private unsafe def ofListImpl (l : List Float) : Float64Array :=
  loop l (emptyWithCapacity l.length)
where
  loop : List Float → Float64Array → Float64Array
    | [], r => r
    | x :: xs, r => loop xs (r.push x)

/-- The array with the elements of `l`. -/
@[implemented_by ofListImpl, expose]
public def ofList (l : List Float) : Float64Array :=
  mk l.toArray

/-! ## Iteration -/

@[specialize]
private unsafe def foldlMImpl {β : Type v} {m : Type v → Type w} [Monad m] (f : β → Float → m β)
    (init : β) (a : @& Float64Array) (start := 0) (stop := a.size) : m β :=
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
public def foldlM {β : Type v} {m : Type v → Type w} [Monad m] (f : β → Float → m β) (init : β)
    (a : @& Float64Array) (start := 0) (stop := a.size) : m β :=
  a.data.foldlM f init start stop

@[specialize]
private unsafe def foldrMImpl {β : Type v} {m : Type v → Type w} [Monad m] (f : Float → β → m β)
    (init : β) (a : @& Float64Array) : m β :=
  loop a.usize init
where
  loop (i : USize) (b : β) : m β :=
    if h : 0 < i ∧ (i - 1).toNat < a.size then do loop (i - 1) (← f (a.uget (i - 1) h.2) b)
    else pure b

/-- Folds a monadic function over the elements of `a`, from last to first. -/
@[implemented_by foldrMImpl, expose]
public def foldrM {β : Type v} {m : Type v → Type w} [Monad m] (f : Float → β → m β) (init : β)
    (a : @& Float64Array) : m β :=
  a.data.foldrM f init

@[inline, expose]
public def foldl {β : Type v} (f : β → Float → β) (init : β) (a : @& Float64Array) (start := 0)
    (stop := a.size) : β :=
  Id.run <| a.foldlM (pure <| f · ·) init start stop

@[inline, expose]
public def foldr {β : Type v} (f : Float → β → β) (init : β) (a : @& Float64Array) : β :=
  Id.run <| a.foldrM (pure <| f · ·) init

@[inline]
public def forM {m : Type v → Type w} [Monad m] (f : Float → m PUnit) (a : @& Float64Array) :
    m PUnit :=
  a.foldlM (fun _ x => f x) ⟨⟩

@[specialize]
private unsafe def forInImpl {β : Type v} {m : Type v → Type w} [Monad m] (a : @& Float64Array)
    (init : β) (f : Float → β → m (ForInStep β)) : m β :=
  loop 0 init
where
  loop (i : USize) (b : β) : m β :=
    if h : i.toNat < a.size then do
      match ← f (a.uget i h) b with
      | .done b => pure b
      | .yield b => loop (i + 1) b
    else pure b

@[implemented_by forInImpl]
public def forIn {β : Type v} {m : Type v → Type w} [Monad m] (a : @& Float64Array) (init : β)
    (f : Float → β → m (ForInStep β)) : m β :=
  ForIn.forIn a.data init f

public instance [Monad m] : ForIn m Float64Array Float where
  forIn a b f := Float64Array.forIn a b f

@[specialize]
private unsafe def anyImpl (a : @& Float64Array) (p : Float → Bool) : Bool :=
  loop 0
where
  loop (i : USize) : Bool :=
    if h : i.toNat < a.size then p (a.uget i h) || loop (i + 1) else false

/-- Whether some element of `a` satisfies `p`. -/
@[implemented_by anyImpl]
public def any (a : @& Float64Array) (p : Float → Bool) : Bool :=
  a.data.any p

@[specialize]
private unsafe def allImpl (a : @& Float64Array) (p : Float → Bool) : Bool :=
  loop 0
where
  loop (i : USize) : Bool :=
    if h : i.toNat < a.size then p (a.uget i h) && loop (i + 1) else true

/-- Whether every element of `a` satisfies `p`. -/
@[implemented_by allImpl]
public def all (a : @& Float64Array) (p : Float → Bool) : Bool :=
  a.data.all p

private unsafe def containsImpl (a : @& Float64Array) (v : Float) : Bool :=
  anyImpl a (v == ·)

/-- Whether `v` is an element of `a`. -/
@[implemented_by containsImpl]
public def contains (a : @& Float64Array) (v : Float) : Bool :=
  a.data.contains v

/-! ## Equality -/

private theorem data_injective : {a b : Float64Array} → a.data = b.data → a = b
  | mk _, mk _, rfl => rfl

private unsafe def beqImpl (a b : @& Float64Array) : Bool :=
  a.usize == b.usize && loop 0
where
  loop (i : USize) : Bool :=
    if h : i.toNat < a.size then
      if h' : i.toNat < b.size then a.uget i h == b.uget i h' && loop (i + 1) else false
    else
      true

/--
Compares the elements with `==`, like `Array`. Floating-point equality is not decidable equality:
`NaN` is not equal to itself and `0.0 == -0.0`.
-/
@[implemented_by beqImpl]
public def beq (a b : @& Float64Array) : Bool :=
  a.data == b.data

public instance : BEq Float64Array := ⟨beq⟩

/-! ## Conversion and printing -/

@[expose] public def toList (a : Float64Array) : List Float := a.data.toList

public instance : Repr Float64Array where
  reprPrec a _ := "Float64Array.mk " ++ repr a.data

public instance : ToString Float64Array where
  toString a := "Float64Array.mk " ++ toString a.data

/-! ## Slices -/

/-- Internal representation of `Float64Array.Slice`. -/
public protected structure SliceData where
  /-- The underlying array. -/
  array : Float64Array
  /-- The starting index of the slice (inclusive). -/
  start : Nat
  /-- The ending index of the slice (exclusive). -/
  stop : Nat
  /-- The starting index is no later than the ending index. -/
  start_le_stop : start ≤ stop
  /-- The ending index is no later than the end of the array. -/
  stop_le_array_size : stop ≤ array.size

/--
A region of a `Float64Array`: the elements from index `start` up to, but not including, `stop`.
Taking a slice doesn't copy the array. Slices are written with core's slice notation, such as
`a[i...j]`, `a[i...*]` or `a[*...j]`.
-/
public protected abbrev Slice := Std.Slice Float64Array.SliceData

public instance : Std.Slice.Self (Std.Slice Float64Array.SliceData) Float64Array.Slice where

namespace Slice

@[always_inline, inline, expose, inherit_doc SliceData.array]
public def array (s : Float64Array.Slice) : Float64Array := s.internalRepresentation.array

@[always_inline, inline, expose, inherit_doc SliceData.start]
public def start (s : Float64Array.Slice) : Nat := s.internalRepresentation.start

@[always_inline, inline, expose, inherit_doc SliceData.stop]
public def stop (s : Float64Array.Slice) : Nat := s.internalRepresentation.stop

@[inherit_doc SliceData.start_le_stop]
public theorem start_le_stop (s : Float64Array.Slice) : s.start ≤ s.stop := s.internalRepresentation.start_le_stop

@[inherit_doc SliceData.stop_le_array_size]
public theorem stop_le_array_size (s : Float64Array.Slice) : s.stop ≤ s.array.size :=
  s.internalRepresentation.stop_le_array_size

public instance : Std.Slice.SliceSize Float64Array.SliceData where
  size s := s.internalRepresentation.stop - s.internalRepresentation.start

public theorem size_eq (s : Float64Array.Slice) : s.size = s.stop - s.start := rfl

/-- The element at index `i` of the slice, counted from the start of the slice. -/
@[inline, expose]
public def get (s : Float64Array.Slice) (i : Nat) (h : i < s.size := by get_elem_tactic) : Float :=
  s.array[s.start + i]'(by have := s.stop_le_array_size; rw [size_eq] at h; omega)

public instance : GetElem Float64Array.Slice Nat Float fun s i => i < s.size where
  getElem s i h := s.get i h

/-- The element at index `i` of the slice, or `v₀` if `i` is out of bounds. -/
@[inline]
public def getD (s : Float64Array.Slice) (i : Nat) (v₀ : Float) : Float :=
  if h : i < s.size then s[i] else v₀

/-- The element at index `i` of the slice, or `default` if `i` is out of bounds. -/
public abbrev get! (s : Float64Array.Slice) (i : Nat) : Float :=
  getD s i default

/-- Removes the first element of the slice, if any. -/
@[expose]
public def popFront (s : Float64Array.Slice) : Float64Array.Slice :=
  if h : s.start < s.stop then
    ⟨{ s.internalRepresentation with start := s.start + 1, start_le_stop := h }⟩
  else
    s

/-- The empty slice, backed by an empty array. -/
@[expose]
public protected def empty : Float64Array.Slice :=
  ⟨{ array := Float64Array.empty, start := 0, stop := 0, start_le_stop := Nat.le_refl 0,
     stop_le_array_size := Nat.le_refl 0 }⟩

public instance : EmptyCollection Float64Array.Slice := ⟨Slice.empty⟩

public instance : Inhabited Float64Array.Slice := ⟨Slice.empty⟩

/-- The elements of the slice, copied into a new array with a single `memcpy`. -/
@[expose]
public def copy (s : Float64Array.Slice) : Float64Array :=
  s.array.extract s.start s.stop

public instance : Coe Float64Array.Slice Float64Array := ⟨copy⟩

public theorem getElem_eq (s : Float64Array.Slice) (i : Nat) (h : i < s.size) :
    s[i] = s.array[s.start + i]'(by have := s.stop_le_array_size; rw [size_eq] at h; omega) := rfl

public instance : Repr Float64Array.Slice where
  reprPrec s _ := repr s.copy ++ ".toSlice"

public instance : ToString Float64Array.Slice where
  toString s := toString s.copy

end Slice

/--
The slice of `a` from index `start` up to, but not including, `stop`. If `start` or `stop` are not
valid bounds, they are clamped to the size of `a`, and `start` is clamped to `stop`.
-/
@[expose]
public def toSlice (a : Float64Array) (start : Nat := 0) (stop : Nat := a.size) : Float64Array.Slice :=
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

public instance : Std.Rcc.Sliceable Float64Array Nat Float64Array.Slice where
  mkSlice a range := a.toSlice range.lower (range.upper + 1)

public instance : Std.Rco.Sliceable Float64Array Nat Float64Array.Slice where
  mkSlice a range := a.toSlice range.lower range.upper

public instance : Std.Rci.Sliceable Float64Array Nat Float64Array.Slice where
  mkSlice a range := a.toSlice range.lower

public instance : Std.Roc.Sliceable Float64Array Nat Float64Array.Slice where
  mkSlice a range := a.toSlice (range.lower + 1) (range.upper + 1)

public instance : Std.Roo.Sliceable Float64Array Nat Float64Array.Slice where
  mkSlice a range := a.toSlice (range.lower + 1) range.upper

public instance : Std.Roi.Sliceable Float64Array Nat Float64Array.Slice where
  mkSlice a range := a.toSlice (range.lower + 1)

public instance : Std.Ric.Sliceable Float64Array Nat Float64Array.Slice where
  mkSlice a range := a.toSlice 0 (range.upper + 1)

public instance : Std.Rio.Sliceable Float64Array Nat Float64Array.Slice where
  mkSlice a range := a.toSlice 0 range.upper

public instance : Std.Rii.Sliceable Float64Array Nat Float64Array.Slice where
  mkSlice a _ := a.toSlice

namespace Slice

/-- The slice of `s` from index `start` up to, but not including, `stop`, clamped like `toSlice`. -/
@[expose]
public def slice (s : Float64Array.Slice) (start : Nat := 0) (stop : Nat := s.size) : Float64Array.Slice :=
  s.array.toSlice (s.start + min start s.size) (s.start + min stop s.size)

end Slice

public instance : Std.Rcc.Sliceable Float64Array.Slice Nat Float64Array.Slice where
  mkSlice s range := s.slice range.lower (range.upper + 1)

public instance : Std.Rco.Sliceable Float64Array.Slice Nat Float64Array.Slice where
  mkSlice s range := s.slice range.lower range.upper

public instance : Std.Rci.Sliceable Float64Array.Slice Nat Float64Array.Slice where
  mkSlice s range := s.slice range.lower

public instance : Std.Roc.Sliceable Float64Array.Slice Nat Float64Array.Slice where
  mkSlice s range := s.slice (range.lower + 1) (range.upper + 1)

public instance : Std.Roo.Sliceable Float64Array.Slice Nat Float64Array.Slice where
  mkSlice s range := s.slice (range.lower + 1) range.upper

public instance : Std.Roi.Sliceable Float64Array.Slice Nat Float64Array.Slice where
  mkSlice s range := s.slice (range.lower + 1)

public instance : Std.Ric.Sliceable Float64Array.Slice Nat Float64Array.Slice where
  mkSlice s range := s.slice 0 (range.upper + 1)

public instance : Std.Rio.Sliceable Float64Array.Slice Nat Float64Array.Slice where
  mkSlice s range := s.slice 0 range.upper

public instance : Std.Rii.Sliceable Float64Array.Slice Nat Float64Array.Slice where
  mkSlice s _ := s

/-- The iterator over the elements of a slice, used for `for` loops and the generic slice API. -/
public protected structure SliceIterator where
  /-- The rest of the slice. -/
  xs : Float64Array.Slice

@[inline, expose]
public def SliceIterator.step :
    Std.IterM (α := Float64Array.SliceIterator) Id Float →
      Std.IterStep (Std.IterM (α := Float64Array.SliceIterator) m Float) Float
  | ⟨⟨xs⟩⟩ =>
    if h : xs.start < xs.stop then
      have := xs.stop_le_array_size
      .yield ⟨⟨⟨xs.array, xs.start + 1, xs.stop, h, xs.stop_le_array_size⟩⟩⟩ xs.array[xs.start]
    else
      .done

public instance : Std.Iterator Float64Array.SliceIterator Id Float where
  IsPlausibleStep it step := step = SliceIterator.step it
  step it := pure <| .deflate ⟨SliceIterator.step it, rfl⟩

private def SliceIterator.finitenessRelation : Std.Iterators.FinitenessRelation Float64Array.SliceIterator Id where
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

public instance : Std.Iterators.Finite Float64Array.SliceIterator Id :=
  .of_finitenessRelation SliceIterator.finitenessRelation

public instance [Monad m] : Std.IteratorLoop Float64Array.SliceIterator Id m := .defaultImplementation

public instance : Std.ToIterator (Std.Slice Float64Array.SliceData) Id Float64Array.SliceIterator Float :=
  Std.ToIterator.of Float64Array.SliceIterator (⟨⟨·⟩⟩)

public instance [Monad m] : ForIn m Float64Array.Slice Float := inferInstance

/-- An iterator over the elements of `a`, for use with the `Std.Iterators` API. -/
@[inline, expose]
public def iter (a : Float64Array) : Std.Iter (α := Float64Array.SliceIterator) Float :=
  a.toSlice.iter

namespace Slice

/-- Folds a monadic function over the elements of `s`, from last to first. -/
@[inline, expose]
public def foldrM {β : Type v} {m : Type v → Type w} [Monad m] (f : Float → β → m β) (init : β)
    (s : Float64Array.Slice) : m β :=
  loop s.size (Nat.le_refl _) init
where
  @[specialize] loop : (i : Nat) → i ≤ s.size → β → m β
    | 0, _, b => pure b
    | i + 1, h, b => do loop i (Nat.le_of_succ_le h) (← f s[i] b)

/-- Folds a function over the elements of `s`, from last to first. -/
@[inline, expose]
public def foldr {β : Type v} (f : Float → β → β) (init : β) (s : Float64Array.Slice) : β :=
  Id.run <| s.foldrM (pure <| f · ·) init

/-- Runs a monadic action on each element of `s`, from last to first. -/
@[inline, expose]
public def forRevM {m : Type v → Type w} [Monad m] (f : Float → m PUnit) (s : Float64Array.Slice) : m PUnit :=
  s.foldrM (fun x _ => f x) ⟨⟩

/-- The result of the last element of `s` for which `f` returns `some`, searching from the end. -/
@[inline, expose]
public def findSomeRevM? {β : Type v} {m : Type v → Type w} [Monad m] (s : Float64Array.Slice)
    (f : Float → m (Option β)) : m (Option β) :=
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
public def findRevM? {m : Type → Type w} [Monad m] (s : Float64Array.Slice) (p : Float → m Bool) :
    m (Option Float) :=
  s.findSomeRevM? fun x => return if (← p x) then some x else none

/-- The last element of `s` that satisfies `p`. -/
@[inline, expose]
public def findRev? (s : Float64Array.Slice) (p : Float → Bool) : Option Float :=
  Id.run <| s.findRevM? (pure <| p ·)

/-- The first element of `s` that satisfies `p`. -/
@[inline, expose]
public def find? (s : Float64Array.Slice) (p : Float → Bool) : Option Float :=
  s.iter.find? p

/-- Whether some element of `s` satisfies `p`. -/
@[inline, expose]
public def any (s : Float64Array.Slice) (p : Float → Bool) : Bool :=
  s.iter.any p

/-- Whether every element of `s` satisfies `p`. -/
@[inline, expose]
public def all (s : Float64Array.Slice) (p : Float → Bool) : Bool :=
  s.iter.all p

/-- Whether `v` is an element of `s`. -/
@[inline, expose]
public def contains (s : Float64Array.Slice) (v : Float) : Bool :=
  s.any (v == ·)

/-- The number of elements of `s` that satisfy `p`. -/
@[inline, expose]
public def count (s : Float64Array.Slice) (p : Float → Bool) : Nat :=
  s.iter.fold (fun n x => if p x then n + 1 else n) 0

end Slice

/--
Collects the values emitted by an iterator into a new array. Together with the `Std.Iterators`
combinators, this gives functions such as `map`, `filter`, `take` and `zipWith`, for example
`(a.iter.map (· + 1)).toFloat64Array`.
-/
@[inline, expose]
public def _root_.Std.Iter.toFloat64Array {α : Type} [Std.Iterator α Id Float]
    [Std.IteratorLoop α Id Id] (it : Std.Iter (α := α) Float) : Float64Array :=
  it.fold (·.push ·) empty

@[simp] public theorem size_mk (a : Array Float) : (mk a).size = a.size := rfl

@[simp] public theorem data_mk (a : Array Float) : (mk a).data = a := rfl

@[simp] public theorem mk_data (a : Float64Array) : mk a.data = a := by cases a; rfl

public theorem size_eq_data_size (a : Float64Array) : a.size = a.data.size := by cases a; rfl

@[simp] public theorem size_data (a : Float64Array) : a.data.size = a.size :=
  (size_eq_data_size a).symm

@[simp] public theorem size_uset (a : Float64Array) (i : USize) (v : Float) (h) :
    (a.uset i v h).size = a.size := by
  cases a; exact Array.size_set ..

@[simp] public theorem size_set (a : Float64Array) (i : Nat) (v : Float) (h) :
    (a.set i v h).size = a.size := by
  cases a; exact Array.size_set ..

@[simp] public theorem size_push (a : Float64Array) (v : Float) : (a.push v).size = a.size + 1 := by
  cases a; simp [push, size]

@[simp] public theorem data_append (a b : Float64Array) : (a ++ b).data = a.data ++ b.data := by
  cases a; cases b; rfl

@[simp] public theorem size_append (a b : Float64Array) : (a ++ b).size = a.size + b.size := by
  simp [-size_data, size_eq_data_size]

@[ext] public theorem ext {a b : Float64Array} (h : a.data = b.data) : a = b := data_injective h

@[simp] public theorem getElem_mk (a : Array Float) (i : Nat) (h : i < (mk a).size) :
    (mk a)[i] = a[i] := rfl

public theorem getElem_eq_getElem_data (a : Float64Array) (i : Nat) (h : i < a.size) :
    a[i] = a.data[i]'(size_eq_data_size a ▸ h) := by
  cases a; rfl

@[simp] public theorem getElem_data (a : Float64Array) (i : Nat) (h : i < a.data.size) :
    a.data[i] = a[i]'(by simpa using h) := by
  cases a; rfl

public theorem ext_getElem {a b : Float64Array} (h₁ : a.size = b.size)
    (h₂ : ∀ (i : Nat) (hi₁ : i < a.size) (hi₂ : i < b.size), a[i] = b[i]) : a = b := by
  ext i hi₁ hi₂
  · simpa using h₁
  · simpa using h₂ i (by simpa using hi₁) (by simpa using hi₂)

@[simp] public theorem getElem_usize (a : Float64Array) (i : USize) (h : i.toNat < a.size) :
    a[i] = a[i.toNat] := by
  cases a; rfl

@[simp] public theorem data_uset (a : Float64Array) (i : USize) (v : Float) (h) :
    (a.uset i v h).data = a.data.set i.toNat v (size_eq_data_size a ▸ h) := by
  cases a; rfl

@[simp] public theorem data_set (a : Float64Array) (i : Nat) (v : Float) (h) :
    (a.set i v h).data = a.data.set i v (size_eq_data_size a ▸ h) := by
  cases a; rfl

@[simp] public theorem data_push (a : Float64Array) (v : Float) : (a.push v).data = a.data.push v := by
  cases a; rfl

@[simp] public theorem data_pop (a : Float64Array) : a.pop.data = a.data.pop := by
  cases a; rfl

@[simp] public theorem data_extract (a : Float64Array) (start stop : Nat) :
    (a.extract start stop).data = a.data.extract start stop := by
  cases a; rfl

@[simp] public theorem data_replicate (n : Nat) (v : Float) :
    (replicate n v).data = Array.replicate n v := rfl

@[simp] public theorem data_ofFn {n : Nat} (f : Fin n → Float) : (ofFn f).data = Array.ofFn f := rfl

@[simp] public theorem data_empty : (empty : Float64Array).data = #[] := rfl

@[simp] public theorem size_pop (a : Float64Array) : a.pop.size = a.size - 1 := by
  simp [-size_data, size_eq_data_size]

@[simp] public theorem size_extract (a : Float64Array) (start stop : Nat) :
    (a.extract start stop).size = min stop a.size - start := by
  simp [-size_data, size_eq_data_size]

@[simp] public theorem size_replicate (n : Nat) (v : Float) : (replicate n v).size = n := by
  simp [-size_data, size_eq_data_size]

@[simp] public theorem size_ofFn {n : Nat} (f : Fin n → Float) : (ofFn f).size = n := by
  simp [-size_data, size_eq_data_size]

@[simp] public theorem size_empty : (empty : Float64Array).size = 0 := rfl

@[simp] public theorem getElem_set (a : Float64Array) (i : Nat) (v : Float) (h) (j : Nat) (hj) :
    (a.set i v h)[j]'hj = if i = j then v else a[j]'(by simpa using hj) := by
  simp [-getElem_data, getElem_eq_getElem_data, Array.getElem_set]

@[simp] public theorem getElem_push (a : Float64Array) (v : Float) (i : Nat) (h) :
    (a.push v)[i]'h = if h' : i < a.size then a[i] else v := by
  simp [-getElem_data, getElem_eq_getElem_data, Array.getElem_push, -size_data, size_eq_data_size]

@[simp] public theorem getElem_pop (a : Float64Array) (i : Nat) (h) :
    a.pop[i]'h = a[i]'(by simp at h; omega) := by
  simp [-getElem_data, getElem_eq_getElem_data]

@[simp] public theorem getElem_append (a b : Float64Array) (i : Nat) (h) :
    (a ++ b)[i]'h = if h' : i < a.size then a[i] else b[i - a.size]'(by simp at h; omega) := by
  simp [-getElem_data, getElem_eq_getElem_data, Array.getElem_append, -size_data, size_eq_data_size]

@[simp] public theorem getElem_extract (a : Float64Array) (start stop i : Nat) (h) :
    (a.extract start stop)[i]'h = a[start + i]'(by simp at h; omega) := by
  simp [-getElem_data, getElem_eq_getElem_data]

@[simp] public theorem getElem_replicate (n : Nat) (v : Float) (i : Nat) (h) :
    (replicate n v)[i]'h = v := by
  simp [-getElem_data, getElem_eq_getElem_data]

@[simp] public theorem getElem_ofFn {n : Nat} (f : Fin n → Float) (i : Nat) (h) :
    (ofFn f)[i]'h = f ⟨i, by simpa using h⟩ := by
  simp [-getElem_data, getElem_eq_getElem_data]

public theorem foldl_eq_foldl_data {β : Type v} (f : β → Float → β) (init : β) (a : Float64Array) :
    a.foldl f init = a.data.foldl f init := by
  rfl

public theorem foldr_eq_foldr_data {β : Type v} (f : Float → β → β) (init : β) (a : Float64Array) :
    a.foldr f init = a.data.foldr f init := by
  rfl

@[simp] public theorem toList_data (a : Float64Array) : a.data.toList = a.toList := rfl

@[simp] public theorem emptyc_eq_empty : (∅ : Float64Array) = empty := rfl

@[simp] public theorem emptyWithCapacity_eq_empty (c : Nat) : emptyWithCapacity c = empty := rfl

public theorem size_eq_zero_iff {a : Float64Array} : a.size = 0 ↔ a = empty := by
  simp [Float64Array.ext_iff, ← Array.size_eq_zero_iff]

@[simp] public theorem data_set! (a : Float64Array) (i : Nat) (v : Float) :
    (a.set! i v).data = a.data.set! i v := by
  cases a; rfl

@[simp] public theorem size_set! (a : Float64Array) (i : Nat) (v : Float) :
    (a.set! i v).size = a.size := by
  simp [-size_data, size_eq_data_size]

public theorem getElem!_eq_getElem!_data (a : Float64Array) (i : Nat) : a[i]! = a.data[i]! := by
  rcases a with ⟨a⟩
  by_cases h : i < a.size <;> simp [getElem!_def, getElem?_def, h] <;> rfl

@[simp] public theorem data_ofList (l : List Float) : (ofList l).data = l.toArray := rfl

@[simp] public theorem size_ofList (l : List Float) : (ofList l).size = l.length := rfl

@[simp] public theorem getElem_ofList (l : List Float) (i : Nat) (h) :
    (ofList l)[i]'h = l[i]'(by simpa using h) := rfl

@[simp] public theorem toList_ofList (l : List Float) : (ofList l).toList = l := rfl

@[simp] public theorem ofList_toList (a : Float64Array) : ofList a.toList = a := by
  simp [Float64Array.ext_iff, ← toList_data]

@[simp] public theorem markLinear_eq (a : Float64Array) : a.markLinear = a := rfl

@[simp] public theorem propagateMark_eq (a b : Float64Array) : a.propagateMark b = b := rfl

@[simp] public theorem append_empty (a : Float64Array) : a ++ empty = a := by
  simp [Float64Array.ext_iff]

@[simp] public theorem empty_append (a : Float64Array) : empty ++ a = a := by
  simp [Float64Array.ext_iff]

public theorem append_assoc (a b c : Float64Array) : a ++ b ++ c = a ++ (b ++ c) := by
  simp [Float64Array.ext_iff]

@[simp] public theorem append_eq_empty_iff {a b : Float64Array} :
    a ++ b = empty ↔ a = empty ∧ b = empty := by
  simp only [Float64Array.ext_iff, data_append, data_empty, Array.append_eq_empty_iff]

@[simp] public theorem append_right_inj (a : Float64Array) {b c : Float64Array} :
    a ++ b = a ++ c ↔ b = c := by
  simp only [Float64Array.ext_iff, data_append, Array.append_right_inj]

@[simp] public theorem append_left_inj {a b : Float64Array} (c : Float64Array) :
    a ++ c = b ++ c ↔ a = b := by
  simp only [Float64Array.ext_iff, data_append, Array.append_left_inj]

public theorem getElem_append_left {a b : Float64Array} {i : Nat} (h : i < a.size) :
    (a ++ b)[i]'(by simp; omega) = a[i] := by
  simp [h]

public theorem getElem_append_right {a b : Float64Array} {i : Nat} (h : a.size ≤ i)
    (h' : i < (a ++ b).size) : (a ++ b)[i] = b[i - a.size]'(by simp at h'; omega) := by
  simp [Nat.not_lt.mpr h]

@[simp] public theorem extract_same (a : Float64Array) (i : Nat) : a.extract i i = empty := by
  simp [Float64Array.ext_iff]; omega

@[simp] public theorem extract_zero_size (a : Float64Array) : a.extract 0 a.size = a := by
  simp [Float64Array.ext_iff]

@[simp] public theorem extract_eq_empty_iff {a : Float64Array} {i j : Nat} :
    a.extract i j = empty ↔ min j a.size ≤ i := by
  simp [Float64Array.ext_iff]

public theorem extract_extract (a : Float64Array) (i j k l : Nat) :
    (a.extract i j).extract k l = a.extract (i + k) (min (i + l) j) := by
  simp [Float64Array.ext_iff]

public theorem extract_append_extract (a : Float64Array) (i j k : Nat) :
    a.extract i j ++ a.extract j k = a.extract (min i j) (max j k) := by
  simp [Float64Array.ext_iff]

@[simp] public theorem extract_append_eq_left (a b : Float64Array) : (a ++ b).extract 0 a.size = a := by
  simp [Float64Array.ext_iff]

@[simp] public theorem extract_append_eq_right (a b : Float64Array) :
    (a ++ b).extract a.size (a.size + b.size) = b := by
  simp [Float64Array.ext_iff, -size_data, size_eq_data_size]

@[simp] public theorem data_copySlice (src : Float64Array) (srcOff : Nat) (dest : Float64Array)
    (destOff len : Nat) (exact : Bool) :
    (src.copySlice srcOff dest destOff len exact).data =
      dest.data.extract 0 destOff ++ src.data.extract srcOff (srcOff + len) ++
        dest.data.extract (destOff + min len (src.size - srcOff)) dest.size := by
  simp [copySlice]

public theorem copySlice_eq_append (src : Float64Array) (srcOff : Nat) (dest : Float64Array)
    (destOff len : Nat) (exact : Bool) :
    src.copySlice srcOff dest destOff len exact =
      dest.extract 0 destOff ++ src.extract srcOff (srcOff + len) ++
        dest.extract (destOff + min len (src.size - srcOff)) dest.size := by
  simp [Float64Array.ext_iff]

@[simp] public theorem Slice.size_copy (s : Float64Array.Slice) : s.copy.size = s.size := by
  have := s.stop_le_array_size
  simp only [Slice.copy, size_extract, Slice.size_eq]
  omega


end Float64Array

end ScalarArray

/-- The array with the elements of `l`. -/
@[inline, expose]
public def List.toFloat64Array (l : List Float) : ScalarArray.Float64Array :=
  ScalarArray.Float64Array.ofList l
