/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import all ScalarArray.Internal

/-!
# Arrays of `UInt16`

`ScalarArray.UInt16Array` stores `UInt16` values unboxed, 2 bytes per element, in a Lean runtime
scalar array. Its logical model is `Array UInt16`: `UInt16Array.mk` and `UInt16Array.data` convert
between the two, and every operation is specified by its effect on the model.

The runtime representation is a `ScalarArray` with element size 2. Reads and in-place writes
are inline C. `uset`, `set` and `push` update the array in place when it is not shared and copy
it otherwise, like `Array` and `ByteArray`.
-/

namespace ScalarArray

/--
Arrays of `UInt16` values, stored unboxed in a scalar array with element size 2.

The logical model is an `Array UInt16`. At runtime a `UInt16Array` is a `ScalarArray`, so every
function that looks inside the constructor must be `extern` or `implemented_by`.
-/
public inductive UInt16Array : Type
  | public mk (data : Array UInt16)

namespace UInt16Array

-- `lean_byte_array_size` reads the size of any scalar array, whatever its element size.
@[extern "lean_byte_array_size", tagged_return, expose]
public def size : (a : @& UInt16Array) → Nat
  | mk a => a.size

/--
The size of `a` as a `USize`. Since `USize` can address all memory, no array has more elements than
`USize` can count.
-/
@[extern "lean_sarray_size", simp, expose]
public def usize (a : @& UInt16Array) : USize :=
  a.size.toUSize

@[extern c inline "((uint16_t*)lean_sarray_cptr(#1))[#2]", expose]
public def uget : (a : @& UInt16Array) → (i : USize) → (h : i.toNat < a.size := by get_elem_tactic) →
    UInt16
  | mk a, i, h => a.uget i h

@[expose]
public def get : (a : @& UInt16Array) → (i : @& Nat) → (h : i < a.size := by get_elem_tactic) → UInt16
  | mk a, i, h => a[i]

@[inline]
private unsafe def getImpl : type_of% @get :=
  fun a i _ => a.uget i.toUSize lcProof

attribute [implemented_by getImpl] get

/-- Stores `v` at index `i` in place. Only valid when `a` is exclusive and `i` is in bounds. -/
@[extern c inline "#1;\n((uint16_t*)lean_sarray_cptr(#1))[#2] = #3"]
private unsafe def setUInt16Unsafe : UInt16Array → USize → UInt16 → UInt16Array
  | .mk a, i, v => .mk <| a.uset i v lcProof

private unsafe def toUSizeChecked (n : Nat) : USize :=
  if n < USize.size >>> 1 then n.toUSize else panic! "out of memory"

private unsafe def mkWithCapacityImpl (a : Array UInt16) (capacity : Nat := a.size) : UInt16Array :=
  let cap := toUSizeChecked capacity
  let sz := toUSizeChecked a.size
  let r : UInt16Array := unsafeCast <| ScalarArray.allocate 2 sz (max sz cap) lcProof
  loop r 0
where
  loop (r : UInt16Array) (i : Nat) : UInt16Array :=
    if h : i < a.size then loop (setUInt16Unsafe r i.toUSize a[i]) (i + 1) else r

private unsafe def mkImpl (a : Array UInt16) : UInt16Array :=
  mkWithCapacityImpl a a.size

attribute [implemented_by mkImpl] UInt16Array.mk

private unsafe def dataImpl (a : @& UInt16Array) : Array UInt16 :=
  loop 0 (Array.emptyWithCapacity a.size)
where
  loop (i : USize) (r : Array UInt16) : Array UInt16 :=
    if h : i.toNat < a.size then loop (i + 1) (r.push (a.uget i h)) else r

/-- The elements of `a` as an `Array UInt16`. -/
@[implemented_by dataImpl, expose]
public def data : (a : @& UInt16Array) → Array UInt16
  | mk a => a

private unsafe def emptyWithCapacityImpl (capacity : Nat) : UInt16Array :=
  mkWithCapacityImpl #[] capacity

/-- An empty array with room for `capacity` elements before reallocating. -/
@[implemented_by emptyWithCapacityImpl, expose]
public def emptyWithCapacity (capacity : Nat) : UInt16Array :=
  mk #[]

@[expose] public def empty : UInt16Array := emptyWithCapacity 0

public instance : EmptyCollection UInt16Array := ⟨empty⟩

public instance : Inhabited UInt16Array := ⟨empty⟩

@[expose]
public def uset :
    (a : UInt16Array) → (i : USize) → (v : UInt16) → (h : i.toNat < a.size := by get_elem_tactic) →
    UInt16Array
  | mk a, i, v, h => mk (a.uset i v h)

private unsafe def usetImpl : type_of% @uset :=
  fun a i v _ => setUInt16Unsafe (unsafeCast <| ScalarArray.ensureExclusive (unsafeCast a)) i v

attribute [implemented_by usetImpl] uset

@[expose]
public def set :
    (a : UInt16Array) → (i : Nat) → (v : UInt16) → (h : i < a.size := by get_elem_tactic) →
    UInt16Array
  | mk a, i, v, h => mk (a.set i v h)

private unsafe def setImpl : type_of% @set :=
  fun a i v _ => usetImpl a i.toUSize v lcProof

attribute [implemented_by setImpl] set

public def get! (a : @& UInt16Array) (i : @& Nat) : UInt16 :=
  if h : i < a.size then a.get i h else panic! "index out of bounds"

public def getD (a : @& UInt16Array) (i : @& Nat) (v₀ : UInt16) : UInt16 :=
  if h : i < a.size then a.get i h else v₀

private unsafe def setBangImpl (a : UInt16Array) (i : Nat) (v : UInt16) : UInt16Array :=
  if h : i < a.size then setImpl a i v h else a

/-- Replaces the element at index `i`. If `i` is out of bounds, the array is returned unmodified. -/
@[implemented_by setBangImpl, expose]
public def set! : UInt16Array → Nat → UInt16 → UInt16Array
  | mk a, i, v => mk (a.set! i v)

public instance : GetElem UInt16Array Nat UInt16 fun a i => i < a.size where
  getElem a i h := a.get i h

public instance : GetElem UInt16Array USize UInt16 fun a i => i.toNat < a.size where
  getElem a i h := a.uget i h

private unsafe def pushImpl (a : UInt16Array) (v : UInt16) : UInt16Array :=
  let s : ScalarArray := unsafeCast a
  let cap := s.capacity
  if s.size < cap then
    loop s.ensureExclusive
  else if cap < cap + cap + 1 then
    loop (s.copyWithCapacity (cap + cap + 1) lcProof)
  else
    panic! "out of memory"
where
  loop (s : ScalarArray) : UInt16Array :=
    let i := s.size
    setUInt16Unsafe (unsafeCast (s.resizeUnsafe (i + 1) lcProof lcProof)) i v

@[implemented_by pushImpl, expose]
public def push : UInt16Array → UInt16 → UInt16Array
  | mk a, v => mk (a.push v)

/--
Copies `n` bytes of the data of `src`, starting at byte `srcOff`, into the data of `dest`, starting at
byte `destOff`. Only valid when `dest` is exclusive and both ranges are within the capacities.
-/
-- TODO: core has no runtime function that copies a slice of a scalar array with any element size;
-- `lean_byte_array_copy_slice` only works for bytes. Replace this once core has one.
@[extern c inline "#1;\n__builtin_memcpy(lean_sarray_cptr(#1) + #4, lean_sarray_cptr(#2) + #3, #5)"]
private unsafe def memcpyUnsafe : UInt16Array → @& UInt16Array → (srcOff destOff n : USize) → UInt16Array
  | dest, _, _, _, _ => dest

/--
Copies the `n` elements of `src` starting at index `srcOff` into `dest` starting at index `destOff`,
in place, and grows the size of `dest` to `destOff + n` if it is smaller. Only valid when `dest` is
exclusive, has capacity for `destOff + n` elements, and is not the same object as `src`, and when
`destOff ≤ dest.size` and `srcOff + n ≤ src.size`.
-/
@[inline]
private unsafe def copySliceUnsafe (dest : UInt16Array) (src : @& UInt16Array) (srcOff destOff n : USize) :
    UInt16Array :=
  let esz := (unsafeCast src : ScalarArray).elemSize.toUSize
  let d : ScalarArray := unsafeCast (memcpyUnsafe dest src (srcOff * esz) (destOff * esz) (n * esz))
  unsafeCast (d.resizeUnsafe (max d.size (destOff + n)) lcProof lcProof)

private unsafe def appendImpl (a b : UInt16Array) : UInt16Array :=
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
public def append : UInt16Array → UInt16Array → UInt16Array
  | mk a, mk b => mk (a ++ b)

public instance : Append UInt16Array := ⟨append⟩

private unsafe def copySliceImpl (src : @& UInt16Array) (srcOff : Nat) (dest : UInt16Array)
    (destOff len : Nat) (exact : Bool := true) : UInt16Array :=
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
public def copySlice (src : @& UInt16Array) (srcOff : Nat) (dest : UInt16Array) (destOff len : Nat)
    (exact : Bool := true) : UInt16Array :=
  mk (dest.data.extract 0 destOff ++ src.data.extract srcOff (srcOff + len) ++
    dest.data.extract (destOff + min len (src.data.size - srcOff)) dest.data.size)

/-! ## Removing elements -/

public def isEmpty (a : @& UInt16Array) : Bool := a.size == 0

private unsafe def popImpl (a : UInt16Array) : UInt16Array :=
  if a.size == 0 then
    a
  else
    let s : ScalarArray := ScalarArray.ensureExclusive (unsafeCast a)
    unsafeCast (s.resizeUnsafe (s.size - 1) lcProof lcProof)

/-- Removes the last element of `a`, if any, in place when `a` is not shared. -/
@[implemented_by popImpl, expose]
public def pop : UInt16Array → UInt16Array
  | mk a => mk a.pop

public def back? (a : @& UInt16Array) : Option UInt16 := a[a.size - 1]?

public def back! (a : @& UInt16Array) : UInt16 := a[a.size - 1]!

public def back (a : @& UInt16Array) (h : 0 < a.size) : UInt16 := a[a.size - 1]'(Nat.sub_lt h Nat.one_pos)

private unsafe def extractImpl (a : @& UInt16Array) (start stop : Nat) : UInt16Array :=
  let stop := min stop a.size
  if start < stop then
    let n := (stop - start).toUSize
    let r : UInt16Array := unsafeCast <| ScalarArray.allocate 2 0 n lcProof
    copySliceUnsafe r a start.toUSize 0 n
  else
    empty

/--
The elements of `a` from index `start` up to, but not including, `min stop a.size`, copied into a
new array.
-/
@[implemented_by extractImpl, expose]
public def extract : (a : @& UInt16Array) → (start stop : Nat) → UInt16Array
  | mk a, start, stop => mk (a.extract start stop)

/-! ## Linearity -/

/--
Marks `a` as linear, a debugging aid: if a marked array is ever shared and then modified, the
runtime reports it. Logically this is the identity.
-/
@[never_extract, extern "lean_sarray_mark_linear", expose]
public def markLinear (a : UInt16Array) : UInt16Array := a

/-- Returns `b`, marking it as linear if `a` is marked. Logically this is `b`. -/
@[never_extract, extern "lean_sarray_propagate_mark", expose]
public def propagateMark (a : @& UInt16Array) (b : UInt16Array) : UInt16Array := b

/-! ## Search -/

/--
The index of the first element at or after `start` that satisfies `p`, with a proof that it is in
bounds.
-/
@[inline]
public def findFinIdx? (a : UInt16Array) (p : UInt16 → Bool) (start := 0) : Option (Fin a.size) :=
  let rec @[specialize] loop (i : Nat) :=
    if h : i < a.size then
      if p a[i] then some ⟨i, h⟩ else loop (i + 1)
    else
      none
    termination_by a.size - i
  loop start

/-- The index of the first element at or after `start` that satisfies `p`. -/
@[inline]
public def findIdx? (a : UInt16Array) (p : UInt16 → Bool) (start := 0) : Option Nat :=
  let rec @[specialize] loop (i : Nat) :=
    if h : i < a.size then
      if p a[i] then some i else loop (i + 1)
    else
      none
    termination_by a.size - i
  loop start

/-! ## Building arrays -/

private unsafe def replicateImpl (n : Nat) (v : UInt16) : UInt16Array :=
  let sz := toUSizeChecked n
  loop sz (unsafeCast <| ScalarArray.allocate 2 sz sz lcProof) 0
where
  loop (sz : USize) (r : UInt16Array) (i : USize) : UInt16Array :=
    if i < sz then loop sz (setUInt16Unsafe r i v) (i + 1) else r

/-- An array of `n` copies of `v`. -/
@[implemented_by replicateImpl, expose]
public def replicate (n : Nat) (v : UInt16) : UInt16Array :=
  mk (Array.replicate n v)

private unsafe def ofFnImpl {n : Nat} (f : Fin n → UInt16) : UInt16Array :=
  let sz := toUSizeChecked n
  loop (unsafeCast <| ScalarArray.allocate 2 sz sz lcProof) 0
where
  loop (r : UInt16Array) (i : Nat) : UInt16Array :=
    if h : i < n then loop (setUInt16Unsafe r i.toUSize (f ⟨i, h⟩)) (i + 1) else r

/-- The array `#[f 0, …, f (n - 1)]`. -/
@[implemented_by ofFnImpl, expose]
public def ofFn {n : Nat} (f : Fin n → UInt16) : UInt16Array :=
  mk (Array.ofFn f)

private unsafe def ofListImpl (l : List UInt16) : UInt16Array :=
  loop l (emptyWithCapacity l.length)
where
  loop : List UInt16 → UInt16Array → UInt16Array
    | [], r => r
    | x :: xs, r => loop xs (r.push x)

/-- The array with the elements of `l`. -/
@[implemented_by ofListImpl, expose]
public def ofList (l : List UInt16) : UInt16Array :=
  mk l.toArray

/-! ## Iteration -/

@[specialize]
private unsafe def foldlMImpl {β : Type v} {m : Type v → Type w} [Monad m] (f : β → UInt16 → m β)
    (init : β) (a : @& UInt16Array) (start := 0) (stop := a.size) : m β :=
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
public def foldlM {β : Type v} {m : Type v → Type w} [Monad m] (f : β → UInt16 → m β) (init : β)
    (a : @& UInt16Array) (start := 0) (stop := a.size) : m β :=
  a.data.foldlM f init start stop

@[specialize]
private unsafe def foldrMImpl {β : Type v} {m : Type v → Type w} [Monad m] (f : UInt16 → β → m β)
    (init : β) (a : @& UInt16Array) : m β :=
  loop a.usize init
where
  loop (i : USize) (b : β) : m β :=
    if h : 0 < i ∧ (i - 1).toNat < a.size then do loop (i - 1) (← f (a.uget (i - 1) h.2) b)
    else pure b

/-- Folds a monadic function over the elements of `a`, from last to first. -/
@[implemented_by foldrMImpl, expose]
public def foldrM {β : Type v} {m : Type v → Type w} [Monad m] (f : UInt16 → β → m β) (init : β)
    (a : @& UInt16Array) : m β :=
  a.data.foldrM f init

@[inline, expose]
public def foldl {β : Type v} (f : β → UInt16 → β) (init : β) (a : @& UInt16Array) (start := 0)
    (stop := a.size) : β :=
  Id.run <| a.foldlM (pure <| f · ·) init start stop

@[inline, expose]
public def foldr {β : Type v} (f : UInt16 → β → β) (init : β) (a : @& UInt16Array) : β :=
  Id.run <| a.foldrM (pure <| f · ·) init

@[inline]
public def forM {m : Type v → Type w} [Monad m] (f : UInt16 → m PUnit) (a : @& UInt16Array) :
    m PUnit :=
  a.foldlM (fun _ x => f x) ⟨⟩

@[specialize]
private unsafe def forInImpl {β : Type v} {m : Type v → Type w} [Monad m] (a : @& UInt16Array)
    (init : β) (f : UInt16 → β → m (ForInStep β)) : m β :=
  loop 0 init
where
  loop (i : USize) (b : β) : m β :=
    if h : i.toNat < a.size then do
      match ← f (a.uget i h) b with
      | .done b => pure b
      | .yield b => loop (i + 1) b
    else pure b

@[implemented_by forInImpl]
public def forIn {β : Type v} {m : Type v → Type w} [Monad m] (a : @& UInt16Array) (init : β)
    (f : UInt16 → β → m (ForInStep β)) : m β :=
  ForIn.forIn a.data init f

public instance [Monad m] : ForIn m UInt16Array UInt16 where
  forIn a b f := UInt16Array.forIn a b f

@[specialize]
private unsafe def anyImpl (a : @& UInt16Array) (p : UInt16 → Bool) : Bool :=
  loop 0
where
  loop (i : USize) : Bool :=
    if h : i.toNat < a.size then p (a.uget i h) || loop (i + 1) else false

/-- Whether some element of `a` satisfies `p`. -/
@[implemented_by anyImpl]
public def any (a : @& UInt16Array) (p : UInt16 → Bool) : Bool :=
  a.data.any p

@[specialize]
private unsafe def allImpl (a : @& UInt16Array) (p : UInt16 → Bool) : Bool :=
  loop 0
where
  loop (i : USize) : Bool :=
    if h : i.toNat < a.size then p (a.uget i h) && loop (i + 1) else true

/-- Whether every element of `a` satisfies `p`. -/
@[implemented_by allImpl]
public def all (a : @& UInt16Array) (p : UInt16 → Bool) : Bool :=
  a.data.all p

private unsafe def containsImpl (a : @& UInt16Array) (v : UInt16) : Bool :=
  anyImpl a (v == ·)

/-- Whether `v` is an element of `a`. -/
@[implemented_by containsImpl]
public def contains (a : @& UInt16Array) (v : UInt16) : Bool :=
  a.data.contains v

/-! ## Equality and hashing -/

private theorem data_injective : {a b : UInt16Array} → a.data = b.data → a = b
  | mk _, mk _, rfl => rfl

/-- Decides equality by comparing the two arrays' memory. -/
@[extern "lean_sarray_dec_eq"]
public def decEq (a b : @& UInt16Array) : Decidable (a = b) :=
  decidable_of_iff (a.data = b.data) ⟨data_injective, fun h => h ▸ rfl⟩

public instance : DecidableEq UInt16Array := decEq

private unsafe def hashImpl (a : @& UInt16Array) : UInt64 :=
  foldlMImpl (m := Id) (fun r x => mixHash r (Hashable.hash x)) 7 a

/-- The same hash as `a.data`. -/
@[implemented_by hashImpl]
public def hash (a : @& UInt16Array) : UInt64 :=
  Hashable.hash a.data

public instance : Hashable UInt16Array := ⟨hash⟩

/-! ## Iterators -/

/--
An iterator over the elements of an array: the array and a position in it.

An iterator is *valid* if its position `idx` satisfies `idx ≤ array.size`. Most operations return
arbitrary values on invalid iterators. The API only creates invalid iterators through `next` at
the end of the array, and through `forward` or `nextn` by more than the remaining elements.
-/
public structure Iterator where
  /-- The array the iterator is for. -/
  array : UInt16Array
  /--
  The current position. If it is not a valid position for the array, the current element is
  `(default : UInt16)`.
  -/
  idx : Nat
  deriving Inhabited

/-- An iterator at the beginning of `a`. -/
@[expose] public def mkIterator (a : UInt16Array) : Iterator :=
  ⟨a, 0⟩

@[inherit_doc mkIterator]
public abbrev iter := mkIterator

/-- The size of an iterator is the number of elements remaining. -/
public instance : SizeOf Iterator where
  sizeOf i := i.array.size - i.idx

public theorem Iterator.sizeOf_eq (i : Iterator) : sizeOf i = i.array.size - i.idx :=
  rfl

namespace Iterator

/-- The number of elements remaining. -/
@[inline, expose]
public def remaining : Iterator → Nat
  | ⟨a, i⟩ => a.size - i

@[inherit_doc Iterator.idx, expose]
public def pos := Iterator.idx

/-- Whether the iterator is past the last element of the array. -/
@[inline, expose]
public def atEnd : Iterator → Bool
  | ⟨a, i⟩ => i ≥ a.size

/-- The element at the current position, or `(default : UInt16)` if the position is invalid. -/
@[inline, expose]
public def curr : Iterator → UInt16
  | ⟨a, i⟩ => if h : i < a.size then a[i] else default

/--
Moves the position forward by one element, unconditionally. The result is only valid if the
iterator is not at the end of the array, that is, if `atEnd` is `false`.
-/
@[inline, expose]
public def next : Iterator → Iterator
  | ⟨a, i⟩ => ⟨a, i + 1⟩

/-- Moves the position back by one element. At position zero, this is the identity. -/
@[inline, expose]
public def prev : Iterator → Iterator
  | ⟨a, i⟩ => ⟨a, i - 1⟩

/-- Whether the iterator is not past the last element of the array. -/
@[inline, expose]
public def hasNext : Iterator → Bool
  | ⟨a, i⟩ => i < a.size

/-- The element at the current position. -/
@[inline, expose]
public def curr' (it : Iterator) (h : it.hasNext) : UInt16 :=
  match it with
  | ⟨a, i⟩ =>
    have : i < a.size := by
      simp only [hasNext, decide_eq_true_eq] at h
      assumption
    a[i]

/-- Moves the position forward by one element. -/
@[inline, expose]
public def next' (it : Iterator) (_h : it.hasNext) : Iterator :=
  match it with
  | ⟨a, i⟩ => ⟨a, i + 1⟩

/-- Whether the position is not zero. -/
@[inline, expose]
public def hasPrev : Iterator → Bool
  | ⟨_, i⟩ => i > 0

/-- Moves the position to the end of the array, so that `atEnd` is `true`. -/
@[inline, expose]
public def toEnd : Iterator → Iterator
  | ⟨a, _⟩ => ⟨a, a.size⟩

/--
Moves the position forward by `n` elements. The result is only valid if `n` is at most the number
of elements remaining.
-/
@[inline, expose]
public def forward : Iterator → Nat → Iterator
  | ⟨a, i⟩, n => ⟨a, i + n⟩

@[inherit_doc forward, inline, expose]
public def nextn : Iterator → Nat → Iterator := forward

/-- Moves the position back by `n` elements, stopping at the beginning of the array. -/
@[inline, expose]
public def prevn : Iterator → Nat → Iterator
  | ⟨a, i⟩, n => ⟨a, i - n⟩

end Iterator

/-! ## Conversion and printing -/

@[expose] public def toList (a : UInt16Array) : List UInt16 := a.data.toList

public instance : Repr UInt16Array where
  reprPrec a _ := "UInt16Array.mk " ++ repr a.data

public instance : ToString UInt16Array where
  toString a := "UInt16Array.mk " ++ toString a.data

@[simp] public theorem size_mk (a : Array UInt16) : (mk a).size = a.size := rfl

@[simp] public theorem data_mk (a : Array UInt16) : (mk a).data = a := rfl

@[simp] public theorem mk_data (a : UInt16Array) : mk a.data = a := by cases a; rfl

public theorem size_eq_data_size (a : UInt16Array) : a.size = a.data.size := by cases a; rfl

@[simp] public theorem size_data (a : UInt16Array) : a.data.size = a.size :=
  (size_eq_data_size a).symm

@[simp] public theorem size_uset (a : UInt16Array) (i : USize) (v : UInt16) (h) :
    (a.uset i v h).size = a.size := by
  cases a; exact Array.size_set ..

@[simp] public theorem size_set (a : UInt16Array) (i : Nat) (v : UInt16) (h) :
    (a.set i v h).size = a.size := by
  cases a; exact Array.size_set ..

@[simp] public theorem size_push (a : UInt16Array) (v : UInt16) : (a.push v).size = a.size + 1 := by
  cases a; simp [push, size]

@[simp] public theorem data_append (a b : UInt16Array) : (a ++ b).data = a.data ++ b.data := by
  cases a; cases b; rfl

@[simp] public theorem size_append (a b : UInt16Array) : (a ++ b).size = a.size + b.size := by
  simp [-size_data, size_eq_data_size]

@[ext] public theorem ext {a b : UInt16Array} (h : a.data = b.data) : a = b := data_injective h

@[simp] public theorem getElem_mk (a : Array UInt16) (i : Nat) (h : i < (mk a).size) :
    (mk a)[i] = a[i] := rfl

public theorem getElem_eq_getElem_data (a : UInt16Array) (i : Nat) (h : i < a.size) :
    a[i] = a.data[i]'(size_eq_data_size a ▸ h) := by
  cases a; rfl

@[simp] public theorem getElem_data (a : UInt16Array) (i : Nat) (h : i < a.data.size) :
    a.data[i] = a[i]'(by simpa using h) := by
  cases a; rfl

public theorem ext_getElem {a b : UInt16Array} (h₁ : a.size = b.size)
    (h₂ : ∀ (i : Nat) (hi₁ : i < a.size) (hi₂ : i < b.size), a[i] = b[i]) : a = b := by
  ext i hi₁ hi₂
  · simpa using h₁
  · simpa using h₂ i (by simpa using hi₁) (by simpa using hi₂)

@[simp] public theorem getElem_usize (a : UInt16Array) (i : USize) (h : i.toNat < a.size) :
    a[i] = a[i.toNat] := by
  cases a; rfl

@[simp] public theorem data_uset (a : UInt16Array) (i : USize) (v : UInt16) (h) :
    (a.uset i v h).data = a.data.set i.toNat v (size_eq_data_size a ▸ h) := by
  cases a; rfl

@[simp] public theorem data_set (a : UInt16Array) (i : Nat) (v : UInt16) (h) :
    (a.set i v h).data = a.data.set i v (size_eq_data_size a ▸ h) := by
  cases a; rfl

@[simp] public theorem data_push (a : UInt16Array) (v : UInt16) : (a.push v).data = a.data.push v := by
  cases a; rfl

@[simp] public theorem data_pop (a : UInt16Array) : a.pop.data = a.data.pop := by
  cases a; rfl

@[simp] public theorem data_extract (a : UInt16Array) (start stop : Nat) :
    (a.extract start stop).data = a.data.extract start stop := by
  cases a; rfl

@[simp] public theorem data_replicate (n : Nat) (v : UInt16) :
    (replicate n v).data = Array.replicate n v := rfl

@[simp] public theorem data_ofFn {n : Nat} (f : Fin n → UInt16) : (ofFn f).data = Array.ofFn f := rfl

@[simp] public theorem data_empty : (empty : UInt16Array).data = #[] := rfl

@[simp] public theorem size_pop (a : UInt16Array) : a.pop.size = a.size - 1 := by
  simp [-size_data, size_eq_data_size]

@[simp] public theorem size_extract (a : UInt16Array) (start stop : Nat) :
    (a.extract start stop).size = min stop a.size - start := by
  simp [-size_data, size_eq_data_size]

@[simp] public theorem size_replicate (n : Nat) (v : UInt16) : (replicate n v).size = n := by
  simp [-size_data, size_eq_data_size]

@[simp] public theorem size_ofFn {n : Nat} (f : Fin n → UInt16) : (ofFn f).size = n := by
  simp [-size_data, size_eq_data_size]

@[simp] public theorem size_empty : (empty : UInt16Array).size = 0 := rfl

@[simp] public theorem getElem_set (a : UInt16Array) (i : Nat) (v : UInt16) (h) (j : Nat) (hj) :
    (a.set i v h)[j]'hj = if i = j then v else a[j]'(by simpa using hj) := by
  simp [-getElem_data, getElem_eq_getElem_data, Array.getElem_set]

@[simp] public theorem getElem_push (a : UInt16Array) (v : UInt16) (i : Nat) (h) :
    (a.push v)[i]'h = if h' : i < a.size then a[i] else v := by
  simp [-getElem_data, getElem_eq_getElem_data, Array.getElem_push, -size_data, size_eq_data_size]

@[simp] public theorem getElem_pop (a : UInt16Array) (i : Nat) (h) :
    a.pop[i]'h = a[i]'(by simp at h; omega) := by
  simp [-getElem_data, getElem_eq_getElem_data]

@[simp] public theorem getElem_append (a b : UInt16Array) (i : Nat) (h) :
    (a ++ b)[i]'h = if h' : i < a.size then a[i] else b[i - a.size]'(by simp at h; omega) := by
  simp [-getElem_data, getElem_eq_getElem_data, Array.getElem_append, -size_data, size_eq_data_size]

@[simp] public theorem getElem_extract (a : UInt16Array) (start stop i : Nat) (h) :
    (a.extract start stop)[i]'h = a[start + i]'(by simp at h; omega) := by
  simp [-getElem_data, getElem_eq_getElem_data]

@[simp] public theorem getElem_replicate (n : Nat) (v : UInt16) (i : Nat) (h) :
    (replicate n v)[i]'h = v := by
  simp [-getElem_data, getElem_eq_getElem_data]

@[simp] public theorem getElem_ofFn {n : Nat} (f : Fin n → UInt16) (i : Nat) (h) :
    (ofFn f)[i]'h = f ⟨i, by simpa using h⟩ := by
  simp [-getElem_data, getElem_eq_getElem_data]

public theorem foldl_eq_foldl_data {β : Type v} (f : β → UInt16 → β) (init : β) (a : UInt16Array) :
    a.foldl f init = a.data.foldl f init := by
  rfl

public theorem foldr_eq_foldr_data {β : Type v} (f : UInt16 → β → β) (init : β) (a : UInt16Array) :
    a.foldr f init = a.data.foldr f init := by
  rfl

@[simp] public theorem toList_data (a : UInt16Array) : a.data.toList = a.toList := rfl

@[simp] public theorem emptyc_eq_empty : (∅ : UInt16Array) = empty := rfl

@[simp] public theorem emptyWithCapacity_eq_empty (c : Nat) : emptyWithCapacity c = empty := rfl

public theorem size_eq_zero_iff {a : UInt16Array} : a.size = 0 ↔ a = empty := by
  simp [UInt16Array.ext_iff, ← Array.size_eq_zero_iff]

@[simp] public theorem data_set! (a : UInt16Array) (i : Nat) (v : UInt16) :
    (a.set! i v).data = a.data.set! i v := by
  cases a; rfl

@[simp] public theorem size_set! (a : UInt16Array) (i : Nat) (v : UInt16) :
    (a.set! i v).size = a.size := by
  simp [-size_data, size_eq_data_size]

public theorem getElem!_eq_getElem!_data (a : UInt16Array) (i : Nat) : a[i]! = a.data[i]! := by
  rcases a with ⟨a⟩
  by_cases h : i < a.size <;> simp [getElem!_def, getElem?_def, h] <;> rfl

@[simp] public theorem data_ofList (l : List UInt16) : (ofList l).data = l.toArray := rfl

@[simp] public theorem size_ofList (l : List UInt16) : (ofList l).size = l.length := rfl

@[simp] public theorem getElem_ofList (l : List UInt16) (i : Nat) (h) :
    (ofList l)[i]'h = l[i]'(by simpa using h) := rfl

@[simp] public theorem toList_ofList (l : List UInt16) : (ofList l).toList = l := rfl

@[simp] public theorem ofList_toList (a : UInt16Array) : ofList a.toList = a := by
  simp [UInt16Array.ext_iff, ← toList_data]

@[simp] public theorem markLinear_eq (a : UInt16Array) : a.markLinear = a := rfl

@[simp] public theorem propagateMark_eq (a b : UInt16Array) : a.propagateMark b = b := rfl

@[simp] public theorem append_empty (a : UInt16Array) : a ++ empty = a := by
  simp [UInt16Array.ext_iff]

@[simp] public theorem empty_append (a : UInt16Array) : empty ++ a = a := by
  simp [UInt16Array.ext_iff]

public theorem append_assoc (a b c : UInt16Array) : a ++ b ++ c = a ++ (b ++ c) := by
  simp [UInt16Array.ext_iff]

@[simp] public theorem append_eq_empty_iff {a b : UInt16Array} :
    a ++ b = empty ↔ a = empty ∧ b = empty := by
  simp only [UInt16Array.ext_iff, data_append, data_empty, Array.append_eq_empty_iff]

@[simp] public theorem append_right_inj (a : UInt16Array) {b c : UInt16Array} :
    a ++ b = a ++ c ↔ b = c := by
  simp only [UInt16Array.ext_iff, data_append, Array.append_right_inj]

@[simp] public theorem append_left_inj {a b : UInt16Array} (c : UInt16Array) :
    a ++ c = b ++ c ↔ a = b := by
  simp only [UInt16Array.ext_iff, data_append, Array.append_left_inj]

public theorem getElem_append_left {a b : UInt16Array} {i : Nat} (h : i < a.size) :
    (a ++ b)[i]'(by simp; omega) = a[i] := by
  simp [h]

public theorem getElem_append_right {a b : UInt16Array} {i : Nat} (h : a.size ≤ i)
    (h' : i < (a ++ b).size) : (a ++ b)[i] = b[i - a.size]'(by simp at h'; omega) := by
  simp [Nat.not_lt.mpr h]

@[simp] public theorem extract_same (a : UInt16Array) (i : Nat) : a.extract i i = empty := by
  simp [UInt16Array.ext_iff]; omega

@[simp] public theorem extract_zero_size (a : UInt16Array) : a.extract 0 a.size = a := by
  simp [UInt16Array.ext_iff]

@[simp] public theorem extract_eq_empty_iff {a : UInt16Array} {i j : Nat} :
    a.extract i j = empty ↔ min j a.size ≤ i := by
  simp [UInt16Array.ext_iff]

public theorem extract_extract (a : UInt16Array) (i j k l : Nat) :
    (a.extract i j).extract k l = a.extract (i + k) (min (i + l) j) := by
  simp [UInt16Array.ext_iff]

public theorem extract_append_extract (a : UInt16Array) (i j k : Nat) :
    a.extract i j ++ a.extract j k = a.extract (min i j) (max j k) := by
  simp [UInt16Array.ext_iff]

@[simp] public theorem extract_append_eq_left (a b : UInt16Array) : (a ++ b).extract 0 a.size = a := by
  simp [UInt16Array.ext_iff]

@[simp] public theorem extract_append_eq_right (a b : UInt16Array) :
    (a ++ b).extract a.size (a.size + b.size) = b := by
  simp [UInt16Array.ext_iff, -size_data, size_eq_data_size]

@[simp] public theorem data_copySlice (src : UInt16Array) (srcOff : Nat) (dest : UInt16Array)
    (destOff len : Nat) (exact : Bool) :
    (src.copySlice srcOff dest destOff len exact).data =
      dest.data.extract 0 destOff ++ src.data.extract srcOff (srcOff + len) ++
        dest.data.extract (destOff + min len (src.size - srcOff)) dest.size := by
  simp [copySlice]

public theorem copySlice_eq_append (src : UInt16Array) (srcOff : Nat) (dest : UInt16Array)
    (destOff len : Nat) (exact : Bool) :
    src.copySlice srcOff dest destOff len exact =
      dest.extract 0 destOff ++ src.extract srcOff (srcOff + len) ++
        dest.extract (destOff + min len (src.size - srcOff)) dest.size := by
  simp [UInt16Array.ext_iff]

end UInt16Array

end ScalarArray

/-- The array with the elements of `l`. -/
@[inline, expose]
public def List.toUInt16Array (l : List UInt16) : ScalarArray.UInt16Array :=
  ScalarArray.UInt16Array.ofList l
