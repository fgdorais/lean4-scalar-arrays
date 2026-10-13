/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import all ScalarArray.Internal

/-!
# Arrays of `ISize`

`ScalarArray.ISizeArray` stores `ISize` values unboxed, one machine word per element, in a Lean runtime
scalar array. Its logical model is `Array ISize`: `ISizeArray.mk` and `ISizeArray.data` convert
between the two, and every operation is specified by its effect on the model.

The runtime representation is a `ScalarArray` with element size `System.Platform.numBits / 8`. Reads and in-place writes
are inline C. `uset`, `set` and `push` update the array in place when it is not shared and copy
it otherwise, like `Array` and `ByteArray`.
-/

namespace ScalarArray

/--
Arrays of `ISize` values, stored unboxed in a scalar array with element size `System.Platform.numBits / 8`.

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
public def uget : (a : @& ISizeArray) → (i : USize) → (h : i.toNat < a.size := by get_elem_tactic) →
    ISize
  | mk a, i, h => a.uget i h

@[expose]
public def get : (a : @& ISizeArray) → (i : @& Nat) → (h : i < a.size := by get_elem_tactic) → ISize
  | mk a, i, h => a[i]

@[inline]
private unsafe def getImpl : type_of% @get :=
  fun a i _ => a.uget i.toUSize lcProof

attribute [implemented_by getImpl] get

/-- Stores `v` at index `i` in place. Only valid when `a` is exclusive and `i` is in bounds. -/
@[extern c inline "#1;\n((size_t*)lean_sarray_cptr(#1))[#2] = #3"]
private unsafe def setISizeUnsafe : ISizeArray → USize → ISize → ISizeArray
  | .mk a, i, v => .mk <| a.uset i v lcProof

private unsafe def toUSizeChecked (n : Nat) : USize :=
  if n < USize.size >>> 1 then n.toUSize else panic! "out of memory"

private unsafe def mkWithCapacityImpl (a : Array ISize) (capacity : Nat := a.size) : ISizeArray :=
  let cap := toUSizeChecked capacity
  let sz := toUSizeChecked a.size
  let r : ISizeArray := unsafeCast <| ScalarArray.allocate (System.Platform.numBits / 8).toUInt32 sz (max sz cap) lcProof
  loop r 0
where
  loop (r : ISizeArray) (i : Nat) : ISizeArray :=
    if h : i < a.size then loop (setISizeUnsafe r i.toUSize a[i]) (i + 1) else r

private unsafe def mkImpl (a : Array ISize) : ISizeArray :=
  mkWithCapacityImpl a a.size

attribute [implemented_by mkImpl] ISizeArray.mk

private unsafe def dataImpl (a : @& ISizeArray) : Array ISize :=
  loop 0 (Array.emptyWithCapacity a.size)
where
  loop (i : USize) (r : Array ISize) : Array ISize :=
    if h : i.toNat < a.size then loop (i + 1) (r.push (a.uget i h)) else r

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

@[expose]
public def uset :
    (a : ISizeArray) → (i : USize) → (v : ISize) → (h : i.toNat < a.size := by get_elem_tactic) →
    ISizeArray
  | mk a, i, v, h => mk (a.uset i v h)

private unsafe def usetImpl : type_of% @uset :=
  fun a i v _ => setISizeUnsafe (unsafeCast <| ScalarArray.ensureExclusive (unsafeCast a)) i v

attribute [implemented_by usetImpl] uset

@[expose]
public def set :
    (a : ISizeArray) → (i : Nat) → (v : ISize) → (h : i < a.size := by get_elem_tactic) →
    ISizeArray
  | mk a, i, v, h => mk (a.set i v h)

private unsafe def setImpl : type_of% @set :=
  fun a i v _ => usetImpl a i.toUSize v lcProof

attribute [implemented_by setImpl] set

public def get! (a : @& ISizeArray) (i : @& Nat) : ISize :=
  if h : i < a.size then a.get i h else panic! "index out of bounds"

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
    setISizeUnsafe (unsafeCast (s.resizeUnsafe (i + 1) lcProof lcProof)) i v

@[implemented_by pushImpl, expose]
public def push : ISizeArray → ISize → ISizeArray
  | mk a, v => mk (a.push v)

/--
Copies `n` bytes of the data of `src`, starting at byte `srcOff`, into the data of `dest`, starting at
byte `destOff`. Only valid when `dest` is exclusive and both ranges are within the capacities.
-/
-- TODO: core has no runtime function that copies a slice of a scalar array with any element size;
-- `lean_byte_array_copy_slice` only works for bytes. Replace this once core has one.
@[extern c inline "#1;\n__builtin_memcpy(lean_sarray_cptr(#1) + #4, lean_sarray_cptr(#2) + #3, #5)"]
private unsafe def memcpyUnsafe : ISizeArray → @& ISizeArray → (srcOff destOff n : USize) → ISizeArray
  | dest, _, _, _, _ => dest

/--
Copies the `n` elements of `src` starting at index `srcOff` into `dest` starting at index `destOff`,
in place, and grows the size of `dest` to `destOff + n` if it is smaller. Only valid when `dest` is
exclusive, has capacity for `destOff + n` elements, and is not the same object as `src`, and when
`destOff ≤ dest.size` and `srcOff + n ≤ src.size`.
-/
@[inline]
private unsafe def copySliceUnsafe (dest : ISizeArray) (src : @& ISizeArray) (srcOff destOff n : USize) :
    ISizeArray :=
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
public def copySlice (src : @& ISizeArray) (srcOff : Nat) (dest : ISizeArray) (destOff len : Nat)
    (exact : Bool := true) : ISizeArray :=
  mk (dest.data.extract 0 destOff ++ src.data.extract srcOff (srcOff + len) ++
    dest.data.extract (destOff + min len (src.data.size - srcOff)) dest.data.size)

/-! ## Removing elements -/

public def isEmpty (a : @& ISizeArray) : Bool := a.size == 0

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

public def back (a : @& ISizeArray) (h : 0 < a.size) : ISize := a[a.size - 1]'(Nat.sub_lt h Nat.one_pos)

private unsafe def extractImpl (a : @& ISizeArray) (start stop : Nat) : ISizeArray :=
  let stop := min stop a.size
  if start < stop then
    let n := (stop - start).toUSize
    let r : ISizeArray := unsafeCast <| ScalarArray.allocate (System.Platform.numBits / 8).toUInt32 0 n lcProof
    copySliceUnsafe r a start.toUSize 0 n
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
  loop sz (unsafeCast <| ScalarArray.allocate (System.Platform.numBits / 8).toUInt32 sz sz lcProof) 0
where
  loop (sz : USize) (r : ISizeArray) (i : USize) : ISizeArray :=
    if i < sz then loop sz (setISizeUnsafe r i v) (i + 1) else r

/-- An array of `n` copies of `v`. -/
@[implemented_by replicateImpl, expose]
public def replicate (n : Nat) (v : ISize) : ISizeArray :=
  mk (Array.replicate n v)

private unsafe def ofFnImpl {n : Nat} (f : Fin n → ISize) : ISizeArray :=
  let sz := toUSizeChecked n
  loop (unsafeCast <| ScalarArray.allocate (System.Platform.numBits / 8).toUInt32 sz sz lcProof) 0
where
  loop (r : ISizeArray) (i : Nat) : ISizeArray :=
    if h : i < n then loop (setISizeUnsafe r i.toUSize (f ⟨i, h⟩)) (i + 1) else r

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
  loop (stop i : USize) (b : β) : m β :=
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
  loop (i : USize) (b : β) : m β :=
    if h : 0 < i ∧ (i - 1).toNat < a.size then do loop (i - 1) (← f (a.uget (i - 1) h.2) b)
    else pure b

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

@[inline]
public def forM {m : Type v → Type w} [Monad m] (f : ISize → m PUnit) (a : @& ISizeArray) :
    m PUnit :=
  a.foldlM (fun _ x => f x) ⟨⟩

@[specialize]
private unsafe def forInImpl {β : Type v} {m : Type v → Type w} [Monad m] (a : @& ISizeArray)
    (init : β) (f : ISize → β → m (ForInStep β)) : m β :=
  loop 0 init
where
  loop (i : USize) (b : β) : m β :=
    if h : i.toNat < a.size then do
      match ← f (a.uget i h) b with
      | .done b => pure b
      | .yield b => loop (i + 1) b
    else pure b

@[implemented_by forInImpl]
public def forIn {β : Type v} {m : Type v → Type w} [Monad m] (a : @& ISizeArray) (init : β)
    (f : ISize → β → m (ForInStep β)) : m β :=
  ForIn.forIn a.data init f

public instance [Monad m] : ForIn m ISizeArray ISize where
  forIn a b f := ISizeArray.forIn a b f

@[specialize]
private unsafe def anyImpl (a : @& ISizeArray) (p : ISize → Bool) : Bool :=
  loop 0
where
  loop (i : USize) : Bool :=
    if h : i.toNat < a.size then p (a.uget i h) || loop (i + 1) else false

/-- Whether some element of `a` satisfies `p`. -/
@[implemented_by anyImpl]
public def any (a : @& ISizeArray) (p : ISize → Bool) : Bool :=
  a.data.any p

@[specialize]
private unsafe def allImpl (a : @& ISizeArray) (p : ISize → Bool) : Bool :=
  loop 0
where
  loop (i : USize) : Bool :=
    if h : i.toNat < a.size then p (a.uget i h) && loop (i + 1) else true

/-- Whether every element of `a` satisfies `p`. -/
@[implemented_by allImpl]
public def all (a : @& ISizeArray) (p : ISize → Bool) : Bool :=
  a.data.all p

private unsafe def containsImpl (a : @& ISizeArray) (v : ISize) : Bool :=
  anyImpl a (v == ·)

/-- Whether `v` is an element of `a`. -/
@[implemented_by containsImpl]
public def contains (a : @& ISizeArray) (v : ISize) : Bool :=
  a.data.contains v

/-! ## Equality and hashing -/

private theorem data_injective : {a b : ISizeArray} → a.data = b.data → a = b
  | mk _, mk _, rfl => rfl

/-- Decides equality by comparing the two arrays' memory. -/
@[extern "lean_sarray_dec_eq"]
public def decEq (a b : @& ISizeArray) : Decidable (a = b) :=
  decidable_of_iff (a.data = b.data) ⟨data_injective, fun h => h ▸ rfl⟩

public instance : DecidableEq ISizeArray := decEq

private unsafe def hashImpl (a : @& ISizeArray) : UInt64 :=
  foldlMImpl (m := Id) (fun r x => mixHash r (Hashable.hash x)) 7 a

/-- The same hash as `a.data`. -/
@[implemented_by hashImpl]
public def hash (a : @& ISizeArray) : UInt64 :=
  Hashable.hash a.data

public instance : Hashable ISizeArray := ⟨hash⟩

/-! ## Conversion and printing -/

@[expose] public def toList (a : ISizeArray) : List ISize := a.data.toList

public instance : Repr ISizeArray where
  reprPrec a _ := "ISizeArray.mk " ++ repr a.data

public instance : ToString ISizeArray where
  toString a := "ISizeArray.mk " ++ toString a.data

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

@[simp] public theorem size_push (a : ISizeArray) (v : ISize) : (a.push v).size = a.size + 1 := by
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

@[simp] public theorem data_push (a : ISizeArray) (v : ISize) : (a.push v).data = a.data.push v := by
  cases a; rfl

@[simp] public theorem data_pop (a : ISizeArray) : a.pop.data = a.data.pop := by
  cases a; rfl

@[simp] public theorem data_extract (a : ISizeArray) (start stop : Nat) :
    (a.extract start stop).data = a.data.extract start stop := by
  cases a; rfl

@[simp] public theorem data_replicate (n : Nat) (v : ISize) :
    (replicate n v).data = Array.replicate n v := rfl

@[simp] public theorem data_ofFn {n : Nat} (f : Fin n → ISize) : (ofFn f).data = Array.ofFn f := rfl

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

public theorem foldl_eq_foldl_data {β : Type v} (f : β → ISize → β) (init : β) (a : ISizeArray) :
    a.foldl f init = a.data.foldl f init := by
  rfl

public theorem foldr_eq_foldr_data {β : Type v} (f : ISize → β → β) (init : β) (a : ISizeArray) :
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

@[simp] public theorem extract_append_eq_left (a b : ISizeArray) : (a ++ b).extract 0 a.size = a := by
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

end ISizeArray

end ScalarArray

/-- The array with the elements of `l`. -/
@[inline, expose]
public def List.toISizeArray (l : List ISize) : ScalarArray.ISizeArray :=
  ScalarArray.ISizeArray.ofList l
