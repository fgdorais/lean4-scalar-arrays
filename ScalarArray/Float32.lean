/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import all ScalarArray.Internal
public import Std.Data.Iterators

/-!
# Arrays of `Float32`

`ScalarArray.Float32Array` stores `Float32` values unboxed, 4 bytes per element, in a Lean runtime
scalar array. Its logical model is `Array Float32`: `Float32Array.mk` and `Float32Array.data` convert
between the two, and every operation is specified by its effect on the model.

The runtime representation is a `ScalarArray` with element size 4. Reads and in-place writes
are inline C. `uset`, `set` and `push` update the array in place when it is not shared and copy
it otherwise, like `Array` and `ByteArray`.
-/

namespace ScalarArray

/--
Arrays of `Float32` values, stored unboxed in a scalar array with element size 4.

The logical model is an `Array Float32`. At runtime a `Float32Array` is a `ScalarArray`, so every
function that looks inside the constructor must be `extern` or `implemented_by`.
-/
public inductive Float32Array : Type
  | public mk (data : Array Float32)

namespace Float32Array

-- `lean_byte_array_size` reads the size of any scalar array, whatever its element size.
@[extern "lean_byte_array_size", tagged_return, expose]
public def size : (a : @& Float32Array) → Nat
  | mk a => a.size

/--
The size of `a` as a `USize`. Since `USize` can address all memory, no array has more elements than
`USize` can count.
-/
@[extern "lean_sarray_size", simp, expose]
public def usize (a : @& Float32Array) : USize :=
  a.size.toUSize

@[extern c inline "((float*)lean_sarray_cptr(#1))[#2]", expose]
public def uget : (a : @& Float32Array) → (i : USize) → (h : i.toNat < a.size := by get_elem_tactic) →
    Float32
  | mk a, i, h => a.uget i h

@[expose]
public def get : (a : @& Float32Array) → (i : @& Nat) → (h : i < a.size := by get_elem_tactic) → Float32
  | mk a, i, h => a[i]

@[inline]
private unsafe def getImpl : type_of% @get :=
  fun a i _ => a.uget i.toUSize lcProof

attribute [implemented_by getImpl] get

/-- Stores `v` at index `i` in place. Only valid when `a` is exclusive and `i` is in bounds. -/
@[extern c inline "#1;\n((float*)lean_sarray_cptr(#1))[#2] = #3"]
private unsafe def setFloat32Unsafe : Float32Array → USize → Float32 → Float32Array
  | .mk a, i, v => .mk <| a.uset i v lcProof

private unsafe def toUSizeChecked (n : Nat) : USize :=
  if n < USize.size >>> 1 then n.toUSize else panic! "out of memory"

private unsafe def mkWithCapacityImpl (a : Array Float32) (capacity : Nat := a.size) : Float32Array :=
  let cap := toUSizeChecked capacity
  let sz := toUSizeChecked a.size
  let r : Float32Array := unsafeCast <| ScalarArray.allocate 4 sz (max sz cap) lcProof
  loop sz r 0
where
  loop (sz : USize) (r : Float32Array) (i : USize) : Float32Array :=
    if i < sz then loop sz (setFloat32Unsafe r i (a.uget i lcProof)) (i + 1) else r

private unsafe def mkImpl (a : Array Float32) : Float32Array :=
  mkWithCapacityImpl a a.size

attribute [implemented_by mkImpl] Float32Array.mk

private unsafe def dataImpl (a : @& Float32Array) : Array Float32 :=
  loop a.usize 0 (Array.replicate a.size default)
where
  loop (sz i : USize) (r : Array Float32) : Array Float32 :=
    if i < sz then loop sz (i + 1) (r.uset i (a.uget i lcProof) lcProof) else r

/-- The elements of `a` as an `Array Float32`. -/
@[implemented_by dataImpl, expose]
public def data : (a : @& Float32Array) → Array Float32
  | mk a => a

private unsafe def emptyWithCapacityImpl (capacity : Nat) : Float32Array :=
  mkWithCapacityImpl #[] capacity

/-- An empty array with room for `capacity` elements before reallocating. -/
@[implemented_by emptyWithCapacityImpl, expose]
public def emptyWithCapacity (capacity : Nat) : Float32Array :=
  mk #[]

@[expose] public def empty : Float32Array := emptyWithCapacity 0

public instance : EmptyCollection Float32Array := ⟨empty⟩

public instance : Inhabited Float32Array := ⟨empty⟩

@[expose]
public def uset :
    (a : Float32Array) → (i : USize) → (v : Float32) → (h : i.toNat < a.size := by get_elem_tactic) →
    Float32Array
  | mk a, i, v, h => mk (a.uset i v h)

private unsafe def usetImpl : type_of% @uset :=
  fun a i v _ => setFloat32Unsafe (unsafeCast <| ScalarArray.ensureExclusive (unsafeCast a)) i v

attribute [implemented_by usetImpl] uset

@[expose]
public def set :
    (a : Float32Array) → (i : Nat) → (v : Float32) → (h : i < a.size := by get_elem_tactic) →
    Float32Array
  | mk a, i, v, h => mk (a.set i v h)

private unsafe def setImpl : type_of% @set :=
  fun a i v _ => usetImpl a i.toUSize v lcProof

attribute [implemented_by setImpl] set

public def get! (a : @& Float32Array) (i : @& Nat) : Float32 :=
  if h : i < a.size then a.get i h else panic! "index out of bounds"

public def getD (a : @& Float32Array) (i : @& Nat) (v₀ : Float32) : Float32 :=
  if h : i < a.size then a.get i h else v₀

private unsafe def setBangImpl (a : Float32Array) (i : Nat) (v : Float32) : Float32Array :=
  if h : i < a.size then setImpl a i v h else a

/-- Replaces the element at index `i`. If `i` is out of bounds, the array is returned unmodified. -/
@[implemented_by setBangImpl, expose]
public def set! : Float32Array → Nat → Float32 → Float32Array
  | mk a, i, v => mk (a.set! i v)

public instance : GetElem Float32Array Nat Float32 fun a i => i < a.size where
  getElem a i h := a.get i h

public instance : GetElem Float32Array USize Float32 fun a i => i.toNat < a.size where
  getElem a i h := a.uget i h

private unsafe def pushImpl (a : Float32Array) (v : Float32) : Float32Array :=
  let s : ScalarArray := unsafeCast a
  let cap := s.capacity
  if s.size < cap then
    loop s.ensureExclusive
  else if cap < cap + cap + 1 then
    loop (s.copyWithCapacity (cap + cap + 1) lcProof)
  else
    panic! "out of memory"
where
  loop (s : ScalarArray) : Float32Array :=
    let i := s.size
    setFloat32Unsafe (unsafeCast (s.resizeUnsafe (i + 1) lcProof lcProof)) i v

@[implemented_by pushImpl, expose]
public def push : Float32Array → Float32 → Float32Array
  | mk a, v => mk (a.push v)

/--
Copies `n` bytes of the data of `src`, starting at byte `srcOff`, into the data of `dest`, starting at
byte `destOff`. Only valid when `dest` is exclusive and both ranges are within the capacities.
-/
-- TODO: core has no runtime function that copies a slice of a scalar array with any element size;
-- `lean_byte_array_copy_slice` only works for bytes. Replace this once core has one.
@[extern c inline "#1;\n__builtin_memcpy(lean_sarray_cptr(#1) + #4, lean_sarray_cptr(#2) + #3, #5)"]
private unsafe def memcpyUnsafe : Float32Array → @& Float32Array → (srcOff destOff n : USize) → Float32Array
  | dest, _, _, _, _ => dest

/--
Copies the `n` elements of `src` starting at index `srcOff` into `dest` starting at index `destOff`,
in place, and grows the size of `dest` to `destOff + n` if it is smaller. Only valid when `dest` is
exclusive, has capacity for `destOff + n` elements, and is not the same object as `src`, and when
`destOff ≤ dest.size` and `srcOff + n ≤ src.size`.
-/
@[inline]
private unsafe def copySliceUnsafe (dest : Float32Array) (src : @& Float32Array) (srcOff destOff n : USize) :
    Float32Array :=
  let esz := (unsafeCast src : ScalarArray).elemSize.toUSize
  let d : ScalarArray := unsafeCast (memcpyUnsafe dest src (srcOff * esz) (destOff * esz) (n * esz))
  unsafeCast (d.resizeUnsafe (max d.size (destOff + n)) lcProof lcProof)

private unsafe def appendImpl (a b : Float32Array) : Float32Array :=
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
public def append : Float32Array → Float32Array → Float32Array
  | mk a, mk b => mk (a ++ b)

public instance : Append Float32Array := ⟨append⟩

private unsafe def copySliceImpl (src : @& Float32Array) (srcOff : Nat) (dest : Float32Array)
    (destOff len : Nat) (exact : Bool := true) : Float32Array :=
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
public def copySlice (src : @& Float32Array) (srcOff : Nat) (dest : Float32Array) (destOff len : Nat)
    (exact : Bool := true) : Float32Array :=
  mk (dest.data.extract 0 destOff ++ src.data.extract srcOff (srcOff + len) ++
    dest.data.extract (destOff + min len (src.data.size - srcOff)) dest.data.size)

/-! ## Removing elements -/

public def isEmpty (a : @& Float32Array) : Bool := a.size == 0

private unsafe def popImpl (a : Float32Array) : Float32Array :=
  if a.size == 0 then
    a
  else
    let s : ScalarArray := ScalarArray.ensureExclusive (unsafeCast a)
    unsafeCast (s.resizeUnsafe (s.size - 1) lcProof lcProof)

/-- Removes the last element of `a`, if any, in place when `a` is not shared. -/
@[implemented_by popImpl, expose]
public def pop : Float32Array → Float32Array
  | mk a => mk a.pop

public def back? (a : @& Float32Array) : Option Float32 := a[a.size - 1]?

public def back! (a : @& Float32Array) : Float32 := a[a.size - 1]!

public def back (a : @& Float32Array) (h : 0 < a.size) : Float32 := a[a.size - 1]'(Nat.sub_lt h Nat.one_pos)

private def popWhileImpl (p : Float32 → Bool) (a : Float32Array) : Float32Array :=
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
public def popWhile (p : Float32 → Bool) : Float32Array → Float32Array
  | mk a => mk (a.popWhile p)

private unsafe def extractImpl (a : @& Float32Array) (start stop : Nat) : Float32Array :=
  let stop := min stop a.size
  if start < stop then
    let n := (stop - start).toUSize
    let r : Float32Array := unsafeCast <| ScalarArray.allocate 4 0 n lcProof
    copySliceUnsafe r a start.toUSize 0 n
  else
    empty

/--
The elements of `a` from index `start` up to, but not including, `min stop a.size`, copied into a
new array.
-/
@[implemented_by extractImpl, expose]
public def extract : (a : @& Float32Array) → (start stop : Nat) → Float32Array
  | mk a, start, stop => mk (a.extract start stop)

/-! ## Linearity -/

/--
Marks `a` as linear, a debugging aid: if a marked array is ever shared and then modified, the
runtime reports it. Logically this is the identity.
-/
@[never_extract, extern "lean_sarray_mark_linear", expose]
public def markLinear (a : Float32Array) : Float32Array := a

/-- Returns `b`, marking it as linear if `a` is marked. Logically this is `b`. -/
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
  loop sz (unsafeCast <| ScalarArray.allocate 4 sz sz lcProof) 0
where
  loop (sz : USize) (r : Float32Array) (i : USize) : Float32Array :=
    if i < sz then loop sz (setFloat32Unsafe r i v) (i + 1) else r

/-- An array of `n` copies of `v`. -/
@[implemented_by replicateImpl, expose]
public def replicate (n : Nat) (v : Float32) : Float32Array :=
  mk (Array.replicate n v)

private unsafe def ofFnImpl {n : Nat} (f : Fin n → Float32) : Float32Array :=
  let sz := toUSizeChecked n
  loop (unsafeCast <| ScalarArray.allocate 4 sz sz lcProof) 0
where
  loop (r : Float32Array) (i : Nat) : Float32Array :=
    if h : i < n then loop (setFloat32Unsafe r i.toUSize (f ⟨i, h⟩)) (i + 1) else r

/-- The array `#[f 0, …, f (n - 1)]`. -/
@[implemented_by ofFnImpl, expose]
public def ofFn {n : Nat} (f : Fin n → Float32) : Float32Array :=
  mk (Array.ofFn f)

private unsafe def ofListImpl (l : List Float32) : Float32Array :=
  loop l (emptyWithCapacity l.length)
where
  loop : List Float32 → Float32Array → Float32Array
    | [], r => r
    | x :: xs, r => loop xs (r.push x)

/-- The array with the elements of `l`. -/
@[implemented_by ofListImpl, expose]
public def ofList (l : List Float32) : Float32Array :=
  mk l.toArray

/-! ## Iteration -/

@[specialize]
private unsafe def foldlMImpl {β : Type v} {m : Type v → Type w} [Monad m] (f : β → Float32 → m β)
    (init : β) (a : @& Float32Array) (start := 0) (stop := a.size) : m β :=
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
public def foldlM {β : Type v} {m : Type v → Type w} [Monad m] (f : β → Float32 → m β) (init : β)
    (a : @& Float32Array) (start := 0) (stop := a.size) : m β :=
  a.data.foldlM f init start stop

@[specialize]
private unsafe def foldrMImpl {β : Type v} {m : Type v → Type w} [Monad m] (f : Float32 → β → m β)
    (init : β) (a : @& Float32Array) : m β :=
  loop a.usize init
where
  loop (i : USize) (b : β) : m β :=
    if h : 0 < i ∧ (i - 1).toNat < a.size then do loop (i - 1) (← f (a.uget (i - 1) h.2) b)
    else pure b

/-- Folds a monadic function over the elements of `a`, from last to first. -/
@[implemented_by foldrMImpl, expose]
public def foldrM {β : Type v} {m : Type v → Type w} [Monad m] (f : Float32 → β → m β) (init : β)
    (a : @& Float32Array) : m β :=
  a.data.foldrM f init

@[inline, expose]
public def foldl {β : Type v} (f : β → Float32 → β) (init : β) (a : @& Float32Array) (start := 0)
    (stop := a.size) : β :=
  Id.run <| a.foldlM (pure <| f · ·) init start stop

@[inline, expose]
public def foldr {β : Type v} (f : Float32 → β → β) (init : β) (a : @& Float32Array) : β :=
  Id.run <| a.foldrM (pure <| f · ·) init

@[inline]
public def forM {m : Type v → Type w} [Monad m] (f : Float32 → m PUnit) (a : @& Float32Array) :
    m PUnit :=
  a.foldlM (fun _ x => f x) ⟨⟩

@[specialize]
private unsafe def forInImpl {β : Type v} {m : Type v → Type w} [Monad m] (a : @& Float32Array)
    (init : β) (f : Float32 → β → m (ForInStep β)) : m β :=
  loop 0 init
where
  loop (i : USize) (b : β) : m β :=
    if h : i.toNat < a.size then do
      match ← f (a.uget i h) b with
      | .done b => pure b
      | .yield b => loop (i + 1) b
    else pure b

@[implemented_by forInImpl]
public def forIn {β : Type v} {m : Type v → Type w} [Monad m] (a : @& Float32Array) (init : β)
    (f : Float32 → β → m (ForInStep β)) : m β :=
  ForIn.forIn a.data init f

public instance [Monad m] : ForIn m Float32Array Float32 where
  forIn a b f := Float32Array.forIn a b f

@[specialize]
private unsafe def anyImpl (a : @& Float32Array) (p : Float32 → Bool) : Bool :=
  loop 0
where
  loop (i : USize) : Bool :=
    if h : i.toNat < a.size then p (a.uget i h) || loop (i + 1) else false

/-- Whether some element of `a` satisfies `p`. -/
@[implemented_by anyImpl]
public def any (a : @& Float32Array) (p : Float32 → Bool) : Bool :=
  a.data.any p

@[specialize]
private unsafe def allImpl (a : @& Float32Array) (p : Float32 → Bool) : Bool :=
  loop 0
where
  loop (i : USize) : Bool :=
    if h : i.toNat < a.size then p (a.uget i h) && loop (i + 1) else true

/-- Whether every element of `a` satisfies `p`. -/
@[implemented_by allImpl]
public def all (a : @& Float32Array) (p : Float32 → Bool) : Bool :=
  a.data.all p

private unsafe def containsImpl (a : @& Float32Array) (v : Float32) : Bool :=
  anyImpl a (v == ·)

/-- Whether `v` is an element of `a`. -/
@[implemented_by containsImpl]
public def contains (a : @& Float32Array) (v : Float32) : Bool :=
  a.data.contains v

/-! ## Equality -/

private theorem data_injective : {a b : Float32Array} → a.data = b.data → a = b
  | mk _, mk _, rfl => rfl

private unsafe def beqImpl (a b : @& Float32Array) : Bool :=
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
public def beq (a b : @& Float32Array) : Bool :=
  a.data == b.data

public instance : BEq Float32Array := ⟨beq⟩

/-! ## Conversion and printing -/

@[expose] public def toList (a : Float32Array) : List Float32 := a.data.toList

public instance : Repr Float32Array where
  reprPrec a _ := "Float32Array.mk " ++ repr a.data

public instance : ToString Float32Array where
  toString a := "Float32Array.mk " ++ toString a.data

/-! ## Slices -/

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
public theorem start_le_stop (s : Float32Array.Slice) : s.start ≤ s.stop := s.internalRepresentation.start_le_stop

@[inherit_doc SliceData.stop_le_array_size]
public theorem stop_le_array_size (s : Float32Array.Slice) : s.stop ≤ s.array.size :=
  s.internalRepresentation.stop_le_array_size

public instance : Std.Slice.SliceSize Float32Array.SliceData where
  size s := s.internalRepresentation.stop - s.internalRepresentation.start

public theorem size_eq (s : Float32Array.Slice) : s.size = s.stop - s.start := rfl

/-- The element at index `i` of the slice, counted from the start of the slice. -/
@[inline, expose]
public def get (s : Float32Array.Slice) (i : Nat) (h : i < s.size := by get_elem_tactic) : Float32 :=
  s.array[s.start + i]'(by have := s.stop_le_array_size; rw [size_eq] at h; omega)

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
@[expose]
public def popFront (s : Float32Array.Slice) : Float32Array.Slice :=
  if h : s.start < s.stop then
    ⟨{ s.internalRepresentation with start := s.start + 1, start_le_stop := h }⟩
  else
    s

/-- The empty slice, backed by an empty array. -/
@[expose]
public protected def empty : Float32Array.Slice :=
  ⟨{ array := Float32Array.empty, start := 0, stop := 0, start_le_stop := Nat.le_refl 0,
     stop_le_array_size := Nat.le_refl 0 }⟩

public instance : EmptyCollection Float32Array.Slice := ⟨Slice.empty⟩

public instance : Inhabited Float32Array.Slice := ⟨Slice.empty⟩

/-- The elements of the slice, copied into a new array with a single `memcpy`. -/
@[expose]
public def copy (s : Float32Array.Slice) : Float32Array :=
  s.array.extract s.start s.stop

public instance : Coe Float32Array.Slice Float32Array := ⟨copy⟩

public theorem getElem_eq (s : Float32Array.Slice) (i : Nat) (h : i < s.size) :
    s[i] = s.array[s.start + i]'(by have := s.stop_le_array_size; rw [size_eq] at h; omega) := rfl

public instance : Repr Float32Array.Slice where
  reprPrec s _ := repr s.copy ++ ".toSlice"

public instance : ToString Float32Array.Slice where
  toString s := toString s.copy

end Slice

/--
The slice of `a` from index `start` up to, but not including, `stop`. If `start` or `stop` are not
valid bounds, they are clamped to the size of `a`, and `start` is clamped to `stop`.
-/
@[expose]
public def toSlice (a : Float32Array) (start : Nat := 0) (stop : Nat := a.size) : Float32Array.Slice :=
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
@[expose]
public def slice (s : Float32Array.Slice) (start : Nat := 0) (stop : Nat := s.size) : Float32Array.Slice :=
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

/-- The iterator over the elements of a slice, used for `for` loops and the generic slice API. -/
public protected structure SliceIterator where
  /-- The rest of the slice. -/
  xs : Float32Array.Slice

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

private def SliceIterator.finitenessRelation : Std.Iterators.FinitenessRelation Float32Array.SliceIterator Id where
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

public instance : Std.Iterators.Finite Float32Array.SliceIterator Id :=
  .of_finitenessRelation SliceIterator.finitenessRelation

public instance [Monad m] : Std.IteratorLoop Float32Array.SliceIterator Id m := .defaultImplementation

public instance : Std.ToIterator (Std.Slice Float32Array.SliceData) Id Float32Array.SliceIterator Float32 :=
  Std.ToIterator.of Float32Array.SliceIterator (⟨⟨·⟩⟩)

public instance [Monad m] : ForIn m Float32Array.Slice Float32 := inferInstance

/-- An iterator over the elements of `a`, for use with the `Std.Iterators` API. -/
@[inline, expose]
public def iter (a : Float32Array) : Std.Iter (α := Float32Array.SliceIterator) Float32 :=
  a.toSlice.iter

namespace Slice

/-- Folds a monadic function over the elements of `s`, from last to first. -/
@[inline, expose]
public def foldrM {β : Type v} {m : Type v → Type w} [Monad m] (f : Float32 → β → m β) (init : β)
    (s : Float32Array.Slice) : m β :=
  loop s.size (Nat.le_refl _) init
where
  @[specialize] loop : (i : Nat) → i ≤ s.size → β → m β
    | 0, _, b => pure b
    | i + 1, h, b => do loop i (Nat.le_of_succ_le h) (← f s[i] b)

/-- Folds a function over the elements of `s`, from last to first. -/
@[inline, expose]
public def foldr {β : Type v} (f : Float32 → β → β) (init : β) (s : Float32Array.Slice) : β :=
  Id.run <| s.foldrM (pure <| f · ·) init

/-- Runs a monadic action on each element of `s`, from last to first. -/
@[inline, expose]
public def forRevM {m : Type v → Type w} [Monad m] (f : Float32 → m PUnit) (s : Float32Array.Slice) : m PUnit :=
  s.foldrM (fun x _ => f x) ⟨⟩

/-- The result of the last element of `s` for which `f` returns `some`, searching from the end. -/
@[inline, expose]
public def findSomeRevM? {β : Type v} {m : Type v → Type w} [Monad m] (s : Float32Array.Slice)
    (f : Float32 → m (Option β)) : m (Option β) :=
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

/-- Whether `v` is an element of `s`. -/
@[inline, expose]
public def contains (s : Float32Array.Slice) (v : Float32) : Bool :=
  s.any (v == ·)

/-- The number of elements of `s` that satisfy `p`. -/
@[inline, expose]
public def count (s : Float32Array.Slice) (p : Float32 → Bool) : Nat :=
  s.iter.fold (fun n x => if p x then n + 1 else n) 0

end Slice

/--
Collects the values emitted by an iterator into a new array. Together with the `Std.Iterators`
combinators, this gives functions such as `map`, `filter`, `take` and `zipWith`, for example
`(a.iter.map (· + 1)).toFloat32Array`.
-/
@[inline, expose]
public def _root_.Std.Iter.toFloat32Array {α : Type} [Std.Iterator α Id Float32]
    [Std.IteratorLoop α Id Id] (it : Std.Iter (α := α) Float32) : Float32Array :=
  it.fold (·.push ·) empty

@[simp] public theorem size_mk (a : Array Float32) : (mk a).size = a.size := rfl

@[simp] public theorem data_mk (a : Array Float32) : (mk a).data = a := rfl

@[simp] public theorem mk_data (a : Float32Array) : mk a.data = a := by cases a; rfl

public theorem size_eq_data_size (a : Float32Array) : a.size = a.data.size := by cases a; rfl

@[simp] public theorem size_data (a : Float32Array) : a.data.size = a.size :=
  (size_eq_data_size a).symm

@[simp] public theorem size_uset (a : Float32Array) (i : USize) (v : Float32) (h) :
    (a.uset i v h).size = a.size := by
  cases a; exact Array.size_set ..

@[simp] public theorem size_set (a : Float32Array) (i : Nat) (v : Float32) (h) :
    (a.set i v h).size = a.size := by
  cases a; exact Array.size_set ..

@[simp] public theorem size_push (a : Float32Array) (v : Float32) : (a.push v).size = a.size + 1 := by
  cases a; simp [push, size]

@[simp] public theorem data_append (a b : Float32Array) : (a ++ b).data = a.data ++ b.data := by
  cases a; cases b; rfl

@[simp] public theorem size_append (a b : Float32Array) : (a ++ b).size = a.size + b.size := by
  simp [-size_data, size_eq_data_size]

@[ext] public theorem ext {a b : Float32Array} (h : a.data = b.data) : a = b := data_injective h

@[simp] public theorem getElem_mk (a : Array Float32) (i : Nat) (h : i < (mk a).size) :
    (mk a)[i] = a[i] := rfl

public theorem getElem_eq_getElem_data (a : Float32Array) (i : Nat) (h : i < a.size) :
    a[i] = a.data[i]'(size_eq_data_size a ▸ h) := by
  cases a; rfl

@[simp] public theorem getElem_data (a : Float32Array) (i : Nat) (h : i < a.data.size) :
    a.data[i] = a[i]'(by simpa using h) := by
  cases a; rfl

public theorem ext_getElem {a b : Float32Array} (h₁ : a.size = b.size)
    (h₂ : ∀ (i : Nat) (hi₁ : i < a.size) (hi₂ : i < b.size), a[i] = b[i]) : a = b := by
  ext i hi₁ hi₂
  · simpa using h₁
  · simpa using h₂ i (by simpa using hi₁) (by simpa using hi₂)

@[simp] public theorem getElem_usize (a : Float32Array) (i : USize) (h : i.toNat < a.size) :
    a[i] = a[i.toNat] := by
  cases a; rfl

@[simp] public theorem data_uset (a : Float32Array) (i : USize) (v : Float32) (h) :
    (a.uset i v h).data = a.data.set i.toNat v (size_eq_data_size a ▸ h) := by
  cases a; rfl

@[simp] public theorem data_set (a : Float32Array) (i : Nat) (v : Float32) (h) :
    (a.set i v h).data = a.data.set i v (size_eq_data_size a ▸ h) := by
  cases a; rfl

@[simp] public theorem data_push (a : Float32Array) (v : Float32) : (a.push v).data = a.data.push v := by
  cases a; rfl

@[simp] public theorem data_pop (a : Float32Array) : a.pop.data = a.data.pop := by
  cases a; rfl

@[simp] public theorem data_extract (a : Float32Array) (start stop : Nat) :
    (a.extract start stop).data = a.data.extract start stop := by
  cases a; rfl

@[simp] public theorem data_replicate (n : Nat) (v : Float32) :
    (replicate n v).data = Array.replicate n v := rfl

@[simp] public theorem data_ofFn {n : Nat} (f : Fin n → Float32) : (ofFn f).data = Array.ofFn f := rfl

@[simp] public theorem data_empty : (empty : Float32Array).data = #[] := rfl

@[simp] public theorem size_pop (a : Float32Array) : a.pop.size = a.size - 1 := by
  simp [-size_data, size_eq_data_size]

@[simp] public theorem size_extract (a : Float32Array) (start stop : Nat) :
    (a.extract start stop).size = min stop a.size - start := by
  simp [-size_data, size_eq_data_size]

@[simp] public theorem size_replicate (n : Nat) (v : Float32) : (replicate n v).size = n := by
  simp [-size_data, size_eq_data_size]

@[simp] public theorem size_ofFn {n : Nat} (f : Fin n → Float32) : (ofFn f).size = n := by
  simp [-size_data, size_eq_data_size]

@[simp] public theorem size_empty : (empty : Float32Array).size = 0 := rfl

@[simp] public theorem getElem_set (a : Float32Array) (i : Nat) (v : Float32) (h) (j : Nat) (hj) :
    (a.set i v h)[j]'hj = if i = j then v else a[j]'(by simpa using hj) := by
  simp [-getElem_data, getElem_eq_getElem_data, Array.getElem_set]

@[simp] public theorem getElem_push (a : Float32Array) (v : Float32) (i : Nat) (h) :
    (a.push v)[i]'h = if h' : i < a.size then a[i] else v := by
  simp [-getElem_data, getElem_eq_getElem_data, Array.getElem_push, -size_data, size_eq_data_size]

@[simp] public theorem getElem_pop (a : Float32Array) (i : Nat) (h) :
    a.pop[i]'h = a[i]'(by simp at h; omega) := by
  simp [-getElem_data, getElem_eq_getElem_data]

@[simp] public theorem data_popWhile (p : Float32 → Bool) (a : Float32Array) :
    (a.popWhile p).data = a.data.popWhile p := by
  cases a; rfl

@[simp] public theorem getElem_append (a b : Float32Array) (i : Nat) (h) :
    (a ++ b)[i]'h = if h' : i < a.size then a[i] else b[i - a.size]'(by simp at h; omega) := by
  simp [-getElem_data, getElem_eq_getElem_data, Array.getElem_append, -size_data, size_eq_data_size]

@[simp] public theorem getElem_extract (a : Float32Array) (start stop i : Nat) (h) :
    (a.extract start stop)[i]'h = a[start + i]'(by simp at h; omega) := by
  simp [-getElem_data, getElem_eq_getElem_data]

@[simp] public theorem getElem_replicate (n : Nat) (v : Float32) (i : Nat) (h) :
    (replicate n v)[i]'h = v := by
  simp [-getElem_data, getElem_eq_getElem_data]

@[simp] public theorem getElem_ofFn {n : Nat} (f : Fin n → Float32) (i : Nat) (h) :
    (ofFn f)[i]'h = f ⟨i, by simpa using h⟩ := by
  simp [-getElem_data, getElem_eq_getElem_data]

public theorem foldl_eq_foldl_data {β : Type v} (f : β → Float32 → β) (init : β) (a : Float32Array) :
    a.foldl f init = a.data.foldl f init := by
  rfl

public theorem foldr_eq_foldr_data {β : Type v} (f : Float32 → β → β) (init : β) (a : Float32Array) :
    a.foldr f init = a.data.foldr f init := by
  rfl

@[simp] public theorem toList_data (a : Float32Array) : a.data.toList = a.toList := rfl

@[simp] public theorem emptyc_eq_empty : (∅ : Float32Array) = empty := rfl

@[simp] public theorem emptyWithCapacity_eq_empty (c : Nat) : emptyWithCapacity c = empty := rfl

public theorem size_eq_zero_iff {a : Float32Array} : a.size = 0 ↔ a = empty := by
  simp [Float32Array.ext_iff, ← Array.size_eq_zero_iff]

@[simp] public theorem data_set! (a : Float32Array) (i : Nat) (v : Float32) :
    (a.set! i v).data = a.data.set! i v := by
  cases a; rfl

@[simp] public theorem size_set! (a : Float32Array) (i : Nat) (v : Float32) :
    (a.set! i v).size = a.size := by
  simp [-size_data, size_eq_data_size]

public theorem getElem!_eq_getElem!_data (a : Float32Array) (i : Nat) : a[i]! = a.data[i]! := by
  rcases a with ⟨a⟩
  by_cases h : i < a.size <;> simp [getElem!_def, getElem?_def, h] <;> rfl

@[simp] public theorem data_ofList (l : List Float32) : (ofList l).data = l.toArray := rfl

@[simp] public theorem size_ofList (l : List Float32) : (ofList l).size = l.length := rfl

@[simp] public theorem getElem_ofList (l : List Float32) (i : Nat) (h) :
    (ofList l)[i]'h = l[i]'(by simpa using h) := rfl

@[simp] public theorem toList_ofList (l : List Float32) : (ofList l).toList = l := rfl

@[simp] public theorem ofList_toList (a : Float32Array) : ofList a.toList = a := by
  simp [Float32Array.ext_iff, ← toList_data]

@[simp] public theorem markLinear_eq (a : Float32Array) : a.markLinear = a := rfl

@[simp] public theorem propagateMark_eq (a b : Float32Array) : a.propagateMark b = b := rfl

@[simp] public theorem append_empty (a : Float32Array) : a ++ empty = a := by
  simp [Float32Array.ext_iff]

@[simp] public theorem empty_append (a : Float32Array) : empty ++ a = a := by
  simp [Float32Array.ext_iff]

public theorem append_assoc (a b c : Float32Array) : a ++ b ++ c = a ++ (b ++ c) := by
  simp [Float32Array.ext_iff]

@[simp] public theorem append_eq_empty_iff {a b : Float32Array} :
    a ++ b = empty ↔ a = empty ∧ b = empty := by
  simp only [Float32Array.ext_iff, data_append, data_empty, Array.append_eq_empty_iff]

@[simp] public theorem append_right_inj (a : Float32Array) {b c : Float32Array} :
    a ++ b = a ++ c ↔ b = c := by
  simp only [Float32Array.ext_iff, data_append, Array.append_right_inj]

@[simp] public theorem append_left_inj {a b : Float32Array} (c : Float32Array) :
    a ++ c = b ++ c ↔ a = b := by
  simp only [Float32Array.ext_iff, data_append, Array.append_left_inj]

public theorem getElem_append_left {a b : Float32Array} {i : Nat} (h : i < a.size) :
    (a ++ b)[i]'(by simp; omega) = a[i] := by
  simp [h]

public theorem getElem_append_right {a b : Float32Array} {i : Nat} (h : a.size ≤ i)
    (h' : i < (a ++ b).size) : (a ++ b)[i] = b[i - a.size]'(by simp at h'; omega) := by
  simp [Nat.not_lt.mpr h]

@[simp] public theorem extract_same (a : Float32Array) (i : Nat) : a.extract i i = empty := by
  simp [Float32Array.ext_iff]; omega

@[simp] public theorem extract_zero_size (a : Float32Array) : a.extract 0 a.size = a := by
  simp [Float32Array.ext_iff]

@[simp] public theorem extract_eq_empty_iff {a : Float32Array} {i j : Nat} :
    a.extract i j = empty ↔ min j a.size ≤ i := by
  simp [Float32Array.ext_iff]

public theorem extract_extract (a : Float32Array) (i j k l : Nat) :
    (a.extract i j).extract k l = a.extract (i + k) (min (i + l) j) := by
  simp [Float32Array.ext_iff]

public theorem extract_append_extract (a : Float32Array) (i j k : Nat) :
    a.extract i j ++ a.extract j k = a.extract (min i j) (max j k) := by
  simp [Float32Array.ext_iff]

@[simp] public theorem extract_append_eq_left (a b : Float32Array) : (a ++ b).extract 0 a.size = a := by
  simp [Float32Array.ext_iff]

@[simp] public theorem extract_append_eq_right (a b : Float32Array) :
    (a ++ b).extract a.size (a.size + b.size) = b := by
  simp [Float32Array.ext_iff, -size_data, size_eq_data_size]

@[simp] public theorem data_copySlice (src : Float32Array) (srcOff : Nat) (dest : Float32Array)
    (destOff len : Nat) (exact : Bool) :
    (src.copySlice srcOff dest destOff len exact).data =
      dest.data.extract 0 destOff ++ src.data.extract srcOff (srcOff + len) ++
        dest.data.extract (destOff + min len (src.size - srcOff)) dest.size := by
  simp [copySlice]

public theorem copySlice_eq_append (src : Float32Array) (srcOff : Nat) (dest : Float32Array)
    (destOff len : Nat) (exact : Bool) :
    src.copySlice srcOff dest destOff len exact =
      dest.extract 0 destOff ++ src.extract srcOff (srcOff + len) ++
        dest.extract (destOff + min len (src.size - srcOff)) dest.size := by
  simp [Float32Array.ext_iff]

@[simp] public theorem Slice.size_copy (s : Float32Array.Slice) : s.copy.size = s.size := by
  have := s.stop_le_array_size
  simp only [Slice.copy, size_extract, Slice.size_eq]
  omega


end Float32Array

end ScalarArray

/-- The array with the elements of `l`. -/
@[inline, expose]
public def List.toFloat32Array (l : List Float32) : ScalarArray.Float32Array :=
  ScalarArray.Float32Array.ofList l
