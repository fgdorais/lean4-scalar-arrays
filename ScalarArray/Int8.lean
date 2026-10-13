/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import all ScalarArray.Internal

/-!
# Arrays of `Int8`

`ScalarArray.Int8Array` stores `Int8` values unboxed, 1 byte per element, in a Lean runtime
scalar array. Its logical model is `Array Int8`: `Int8Array.mk` and `Int8Array.data` convert
between the two, and every operation is specified by its effect on the model.

The runtime representation is a `ScalarArray` with element size 1. Reads and in-place writes
are inline C. `uset`, `set` and `push` update the array in place when it is not shared and copy
it otherwise, like `Array` and `ByteArray`.
-/

namespace ScalarArray

/--
Arrays of `Int8` values, stored unboxed in a scalar array with element size 1.

The logical model is an `Array Int8`. At runtime a `Int8Array` is a `ScalarArray`, so every
function that looks inside the constructor must be `extern` or `implemented_by`.
-/
public inductive Int8Array : Type
  | public mk (data : Array Int8)

namespace Int8Array

-- `lean_byte_array_size` reads the size of any scalar array, whatever its element size.
@[extern "lean_byte_array_size", tagged_return, expose]
public def size : (a : @& Int8Array) → Nat
  | mk a => a.size

/--
The size of `a` as a `USize`. Since `USize` can address all memory, no array has more elements than
`USize` can count.
-/
@[extern "lean_sarray_size", simp, expose]
public def usize (a : @& Int8Array) : USize :=
  a.size.toUSize

@[extern c inline "((uint8_t*)lean_sarray_cptr(#1))[#2]", expose]
public def uget : (a : @& Int8Array) → (i : USize) → (h : i.toNat < a.size := by get_elem_tactic) →
    Int8
  | mk a, i, h => a.uget i h

@[expose]
public def get : (a : @& Int8Array) → (i : @& Nat) → (h : i < a.size := by get_elem_tactic) → Int8
  | mk a, i, h => a[i]

@[inline]
private unsafe def getImpl : type_of% @get :=
  fun a i _ => a.uget i.toUSize lcProof

attribute [implemented_by getImpl] get

/-- Stores `v` at index `i` in place. Only valid when `a` is exclusive and `i` is in bounds. -/
@[extern c inline "#1;\n((uint8_t*)lean_sarray_cptr(#1))[#2] = #3"]
private unsafe def setInt8Unsafe : Int8Array → USize → Int8 → Int8Array
  | .mk a, i, v => .mk <| a.uset i v lcProof

private unsafe def toUSizeChecked (n : Nat) : USize :=
  if n < USize.size >>> 1 then n.toUSize else panic! "out of memory"

private unsafe def mkWithCapacityImpl (a : Array Int8) (capacity : Nat := a.size) : Int8Array :=
  let cap := toUSizeChecked capacity
  let sz := toUSizeChecked a.size
  let r : Int8Array := unsafeCast <| ScalarArray.allocate 1 sz (max sz cap) lcProof
  loop r 0
where
  loop (r : Int8Array) (i : Nat) : Int8Array :=
    if h : i < a.size then loop (setInt8Unsafe r i.toUSize a[i]) (i + 1) else r

private unsafe def mkImpl (a : Array Int8) : Int8Array :=
  mkWithCapacityImpl a a.size

attribute [implemented_by mkImpl] Int8Array.mk

private unsafe def dataImpl (a : @& Int8Array) : Array Int8 :=
  loop 0 (Array.emptyWithCapacity a.size)
where
  loop (i : USize) (r : Array Int8) : Array Int8 :=
    if h : i.toNat < a.size then loop (i + 1) (r.push (a.uget i h)) else r

/-- The elements of `a` as an `Array Int8`. -/
@[implemented_by dataImpl, expose]
public def data : (a : @& Int8Array) → Array Int8
  | mk a => a

private unsafe def emptyWithCapacityImpl (capacity : Nat) : Int8Array :=
  mkWithCapacityImpl #[] capacity

/-- An empty array with room for `capacity` elements before reallocating. -/
@[implemented_by emptyWithCapacityImpl, expose]
public def emptyWithCapacity (capacity : Nat) : Int8Array :=
  mk #[]

@[expose] public def empty : Int8Array := emptyWithCapacity 0

public instance : EmptyCollection Int8Array := ⟨empty⟩

public instance : Inhabited Int8Array := ⟨empty⟩

@[expose]
public def uset :
    (a : Int8Array) → (i : USize) → (v : Int8) → (h : i.toNat < a.size := by get_elem_tactic) →
    Int8Array
  | mk a, i, v, h => mk (a.uset i v h)

private unsafe def usetImpl : type_of% @uset :=
  fun a i v _ => setInt8Unsafe (unsafeCast <| ScalarArray.ensureExclusive (unsafeCast a)) i v

attribute [implemented_by usetImpl] uset

@[expose]
public def set :
    (a : Int8Array) → (i : Nat) → (v : Int8) → (h : i < a.size := by get_elem_tactic) →
    Int8Array
  | mk a, i, v, h => mk (a.set i v h)

private unsafe def setImpl : type_of% @set :=
  fun a i v _ => usetImpl a i.toUSize v lcProof

attribute [implemented_by setImpl] set

public def get! (a : @& Int8Array) (i : @& Nat) : Int8 :=
  if h : i < a.size then a.get i h else panic! "index out of bounds"

public def getD (a : @& Int8Array) (i : @& Nat) (v₀ : Int8) : Int8 :=
  if h : i < a.size then a.get i h else v₀

private unsafe def setBangImpl (a : Int8Array) (i : Nat) (v : Int8) : Int8Array :=
  if h : i < a.size then setImpl a i v h else a

/-- Replaces the element at index `i`. If `i` is out of bounds, the array is returned unmodified. -/
@[implemented_by setBangImpl, expose]
public def set! : Int8Array → Nat → Int8 → Int8Array
  | mk a, i, v => mk (a.set! i v)

public instance : GetElem Int8Array Nat Int8 fun a i => i < a.size where
  getElem a i h := a.get i h

public instance : GetElem Int8Array USize Int8 fun a i => i.toNat < a.size where
  getElem a i h := a.uget i h

private unsafe def pushImpl (a : Int8Array) (v : Int8) : Int8Array :=
  let s : ScalarArray := unsafeCast a
  let cap := s.capacity
  if s.size < cap then
    loop s.ensureExclusive
  else if cap < cap + cap + 1 then
    loop (s.copyWithCapacity (cap + cap + 1) lcProof)
  else
    panic! "out of memory"
where
  loop (s : ScalarArray) : Int8Array :=
    let i := s.size
    setInt8Unsafe (unsafeCast (s.resizeUnsafe (i + 1) lcProof lcProof)) i v

@[implemented_by pushImpl, expose]
public def push : Int8Array → Int8 → Int8Array
  | mk a, v => mk (a.push v)

/--
Copies `n` bytes of the data of `src`, starting at byte `srcOff`, into the data of `dest`, starting at
byte `destOff`. Only valid when `dest` is exclusive and both ranges are within the capacities.
-/
-- TODO: core has no runtime function that copies a slice of a scalar array with any element size;
-- `lean_byte_array_copy_slice` only works for bytes. Replace this once core has one.
@[extern c inline "#1;\n__builtin_memcpy(lean_sarray_cptr(#1) + #4, lean_sarray_cptr(#2) + #3, #5)"]
private unsafe def memcpyUnsafe : Int8Array → @& Int8Array → (srcOff destOff n : USize) → Int8Array
  | dest, _, _, _, _ => dest

/--
Copies the `n` elements of `src` starting at index `srcOff` into `dest` starting at index `destOff`,
in place, and grows the size of `dest` to `destOff + n` if it is smaller. Only valid when `dest` is
exclusive, has capacity for `destOff + n` elements, and is not the same object as `src`, and when
`destOff ≤ dest.size` and `srcOff + n ≤ src.size`.
-/
@[inline]
private unsafe def copySliceUnsafe (dest : Int8Array) (src : @& Int8Array) (srcOff destOff n : USize) :
    Int8Array :=
  let esz := (unsafeCast src : ScalarArray).elemSize.toUSize
  let d : ScalarArray := unsafeCast (memcpyUnsafe dest src (srcOff * esz) (destOff * esz) (n * esz))
  unsafeCast (d.resizeUnsafe (max d.size (destOff + n)) lcProof lcProof)

private unsafe def appendImpl (a b : Int8Array) : Int8Array :=
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
public def append : Int8Array → Int8Array → Int8Array
  | mk a, mk b => mk (a ++ b)

public instance : Append Int8Array := ⟨append⟩

private unsafe def copySliceImpl (src : @& Int8Array) (srcOff : Nat) (dest : Int8Array)
    (destOff len : Nat) (exact : Bool := true) : Int8Array :=
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
public def copySlice (src : @& Int8Array) (srcOff : Nat) (dest : Int8Array) (destOff len : Nat)
    (exact : Bool := true) : Int8Array :=
  mk (dest.data.extract 0 destOff ++ src.data.extract srcOff (srcOff + len) ++
    dest.data.extract (destOff + min len (src.data.size - srcOff)) dest.data.size)

/-! ## Removing elements -/

public def isEmpty (a : @& Int8Array) : Bool := a.size == 0

private unsafe def popImpl (a : Int8Array) : Int8Array :=
  if a.size == 0 then
    a
  else
    let s : ScalarArray := ScalarArray.ensureExclusive (unsafeCast a)
    unsafeCast (s.resizeUnsafe (s.size - 1) lcProof lcProof)

/-- Removes the last element of `a`, if any, in place when `a` is not shared. -/
@[implemented_by popImpl, expose]
public def pop : Int8Array → Int8Array
  | mk a => mk a.pop

public def back? (a : @& Int8Array) : Option Int8 := a[a.size - 1]?

public def back! (a : @& Int8Array) : Int8 := a[a.size - 1]!

public def back (a : @& Int8Array) (h : 0 < a.size) : Int8 := a[a.size - 1]'(Nat.sub_lt h Nat.one_pos)

private unsafe def extractImpl (a : @& Int8Array) (start stop : Nat) : Int8Array :=
  let stop := min stop a.size
  if start < stop then
    let n := (stop - start).toUSize
    let r : Int8Array := unsafeCast <| ScalarArray.allocate 1 0 n lcProof
    copySliceUnsafe r a start.toUSize 0 n
  else
    empty

/--
The elements of `a` from index `start` up to, but not including, `min stop a.size`, copied into a
new array.
-/
@[implemented_by extractImpl, expose]
public def extract : (a : @& Int8Array) → (start stop : Nat) → Int8Array
  | mk a, start, stop => mk (a.extract start stop)

/-! ## Linearity -/

/--
Marks `a` as linear, a debugging aid: if a marked array is ever shared and then modified, the
runtime reports it. Logically this is the identity.
-/
@[never_extract, extern "lean_sarray_mark_linear", expose]
public def markLinear (a : Int8Array) : Int8Array := a

/-- Returns `b`, marking it as linear if `a` is marked. Logically this is `b`. -/
@[never_extract, extern "lean_sarray_propagate_mark", expose]
public def propagateMark (a : @& Int8Array) (b : Int8Array) : Int8Array := b

/-! ## Search -/

/--
The index of the first element at or after `start` that satisfies `p`, with a proof that it is in
bounds.
-/
@[inline]
public def findFinIdx? (a : Int8Array) (p : Int8 → Bool) (start := 0) : Option (Fin a.size) :=
  let rec @[specialize] loop (i : Nat) :=
    if h : i < a.size then
      if p a[i] then some ⟨i, h⟩ else loop (i + 1)
    else
      none
    termination_by a.size - i
  loop start

/-- The index of the first element at or after `start` that satisfies `p`. -/
@[inline]
public def findIdx? (a : Int8Array) (p : Int8 → Bool) (start := 0) : Option Nat :=
  let rec @[specialize] loop (i : Nat) :=
    if h : i < a.size then
      if p a[i] then some i else loop (i + 1)
    else
      none
    termination_by a.size - i
  loop start

/-! ## Building arrays -/

private unsafe def replicateImpl (n : Nat) (v : Int8) : Int8Array :=
  let sz := toUSizeChecked n
  loop sz (unsafeCast <| ScalarArray.allocate 1 sz sz lcProof) 0
where
  loop (sz : USize) (r : Int8Array) (i : USize) : Int8Array :=
    if i < sz then loop sz (setInt8Unsafe r i v) (i + 1) else r

/-- An array of `n` copies of `v`. -/
@[implemented_by replicateImpl, expose]
public def replicate (n : Nat) (v : Int8) : Int8Array :=
  mk (Array.replicate n v)

private unsafe def ofFnImpl {n : Nat} (f : Fin n → Int8) : Int8Array :=
  let sz := toUSizeChecked n
  loop (unsafeCast <| ScalarArray.allocate 1 sz sz lcProof) 0
where
  loop (r : Int8Array) (i : Nat) : Int8Array :=
    if h : i < n then loop (setInt8Unsafe r i.toUSize (f ⟨i, h⟩)) (i + 1) else r

/-- The array `#[f 0, …, f (n - 1)]`. -/
@[implemented_by ofFnImpl, expose]
public def ofFn {n : Nat} (f : Fin n → Int8) : Int8Array :=
  mk (Array.ofFn f)

private unsafe def ofListImpl (l : List Int8) : Int8Array :=
  loop l (emptyWithCapacity l.length)
where
  loop : List Int8 → Int8Array → Int8Array
    | [], r => r
    | x :: xs, r => loop xs (r.push x)

/-- The array with the elements of `l`. -/
@[implemented_by ofListImpl, expose]
public def ofList (l : List Int8) : Int8Array :=
  mk l.toArray

/-! ## Iteration -/

@[specialize]
private unsafe def foldlMImpl {β : Type v} {m : Type v → Type w} [Monad m] (f : β → Int8 → m β)
    (init : β) (a : @& Int8Array) (start := 0) (stop := a.size) : m β :=
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
public def foldlM {β : Type v} {m : Type v → Type w} [Monad m] (f : β → Int8 → m β) (init : β)
    (a : @& Int8Array) (start := 0) (stop := a.size) : m β :=
  a.data.foldlM f init start stop

@[specialize]
private unsafe def foldrMImpl {β : Type v} {m : Type v → Type w} [Monad m] (f : Int8 → β → m β)
    (init : β) (a : @& Int8Array) : m β :=
  loop a.usize init
where
  loop (i : USize) (b : β) : m β :=
    if h : 0 < i ∧ (i - 1).toNat < a.size then do loop (i - 1) (← f (a.uget (i - 1) h.2) b)
    else pure b

/-- Folds a monadic function over the elements of `a`, from last to first. -/
@[implemented_by foldrMImpl, expose]
public def foldrM {β : Type v} {m : Type v → Type w} [Monad m] (f : Int8 → β → m β) (init : β)
    (a : @& Int8Array) : m β :=
  a.data.foldrM f init

@[inline, expose]
public def foldl {β : Type v} (f : β → Int8 → β) (init : β) (a : @& Int8Array) (start := 0)
    (stop := a.size) : β :=
  Id.run <| a.foldlM (pure <| f · ·) init start stop

@[inline, expose]
public def foldr {β : Type v} (f : Int8 → β → β) (init : β) (a : @& Int8Array) : β :=
  Id.run <| a.foldrM (pure <| f · ·) init

@[inline]
public def forM {m : Type v → Type w} [Monad m] (f : Int8 → m PUnit) (a : @& Int8Array) :
    m PUnit :=
  a.foldlM (fun _ x => f x) ⟨⟩

@[specialize]
private unsafe def forInImpl {β : Type v} {m : Type v → Type w} [Monad m] (a : @& Int8Array)
    (init : β) (f : Int8 → β → m (ForInStep β)) : m β :=
  loop 0 init
where
  loop (i : USize) (b : β) : m β :=
    if h : i.toNat < a.size then do
      match ← f (a.uget i h) b with
      | .done b => pure b
      | .yield b => loop (i + 1) b
    else pure b

@[implemented_by forInImpl]
public def forIn {β : Type v} {m : Type v → Type w} [Monad m] (a : @& Int8Array) (init : β)
    (f : Int8 → β → m (ForInStep β)) : m β :=
  ForIn.forIn a.data init f

public instance [Monad m] : ForIn m Int8Array Int8 where
  forIn a b f := Int8Array.forIn a b f

@[specialize]
private unsafe def anyImpl (a : @& Int8Array) (p : Int8 → Bool) : Bool :=
  loop 0
where
  loop (i : USize) : Bool :=
    if h : i.toNat < a.size then p (a.uget i h) || loop (i + 1) else false

/-- Whether some element of `a` satisfies `p`. -/
@[implemented_by anyImpl]
public def any (a : @& Int8Array) (p : Int8 → Bool) : Bool :=
  a.data.any p

@[specialize]
private unsafe def allImpl (a : @& Int8Array) (p : Int8 → Bool) : Bool :=
  loop 0
where
  loop (i : USize) : Bool :=
    if h : i.toNat < a.size then p (a.uget i h) && loop (i + 1) else true

/-- Whether every element of `a` satisfies `p`. -/
@[implemented_by allImpl]
public def all (a : @& Int8Array) (p : Int8 → Bool) : Bool :=
  a.data.all p

private unsafe def containsImpl (a : @& Int8Array) (v : Int8) : Bool :=
  anyImpl a (v == ·)

/-- Whether `v` is an element of `a`. -/
@[implemented_by containsImpl]
public def contains (a : @& Int8Array) (v : Int8) : Bool :=
  a.data.contains v

/-! ## Equality and hashing -/

private theorem data_injective : {a b : Int8Array} → a.data = b.data → a = b
  | mk _, mk _, rfl => rfl

/-- Decides equality by comparing the two arrays' memory. -/
@[extern "lean_sarray_dec_eq"]
public def decEq (a b : @& Int8Array) : Decidable (a = b) :=
  decidable_of_iff (a.data = b.data) ⟨data_injective, fun h => h ▸ rfl⟩

public instance : DecidableEq Int8Array := decEq

private unsafe def hashImpl (a : @& Int8Array) : UInt64 :=
  foldlMImpl (m := Id) (fun r x => mixHash r (Hashable.hash x)) 7 a

/-- The same hash as `a.data`. -/
@[implemented_by hashImpl]
public def hash (a : @& Int8Array) : UInt64 :=
  Hashable.hash a.data

public instance : Hashable Int8Array := ⟨hash⟩

/-! ## Conversion and printing -/

@[expose] public def toList (a : Int8Array) : List Int8 := a.data.toList

public instance : Repr Int8Array where
  reprPrec a _ := "Int8Array.mk " ++ repr a.data

public instance : ToString Int8Array where
  toString a := "Int8Array.mk " ++ toString a.data

@[simp] public theorem size_mk (a : Array Int8) : (mk a).size = a.size := rfl

@[simp] public theorem data_mk (a : Array Int8) : (mk a).data = a := rfl

@[simp] public theorem mk_data (a : Int8Array) : mk a.data = a := by cases a; rfl

public theorem size_eq_data_size (a : Int8Array) : a.size = a.data.size := by cases a; rfl

@[simp] public theorem size_data (a : Int8Array) : a.data.size = a.size :=
  (size_eq_data_size a).symm

@[simp] public theorem size_uset (a : Int8Array) (i : USize) (v : Int8) (h) :
    (a.uset i v h).size = a.size := by
  cases a; exact Array.size_set ..

@[simp] public theorem size_set (a : Int8Array) (i : Nat) (v : Int8) (h) :
    (a.set i v h).size = a.size := by
  cases a; exact Array.size_set ..

@[simp] public theorem size_push (a : Int8Array) (v : Int8) : (a.push v).size = a.size + 1 := by
  cases a; simp [push, size]

@[simp] public theorem data_append (a b : Int8Array) : (a ++ b).data = a.data ++ b.data := by
  cases a; cases b; rfl

@[simp] public theorem size_append (a b : Int8Array) : (a ++ b).size = a.size + b.size := by
  simp [-size_data, size_eq_data_size]

@[ext] public theorem ext {a b : Int8Array} (h : a.data = b.data) : a = b := data_injective h

@[simp] public theorem getElem_mk (a : Array Int8) (i : Nat) (h : i < (mk a).size) :
    (mk a)[i] = a[i] := rfl

public theorem getElem_eq_getElem_data (a : Int8Array) (i : Nat) (h : i < a.size) :
    a[i] = a.data[i]'(size_eq_data_size a ▸ h) := by
  cases a; rfl

@[simp] public theorem getElem_data (a : Int8Array) (i : Nat) (h : i < a.data.size) :
    a.data[i] = a[i]'(by simpa using h) := by
  cases a; rfl

public theorem ext_getElem {a b : Int8Array} (h₁ : a.size = b.size)
    (h₂ : ∀ (i : Nat) (hi₁ : i < a.size) (hi₂ : i < b.size), a[i] = b[i]) : a = b := by
  ext i hi₁ hi₂
  · simpa using h₁
  · simpa using h₂ i (by simpa using hi₁) (by simpa using hi₂)

@[simp] public theorem getElem_usize (a : Int8Array) (i : USize) (h : i.toNat < a.size) :
    a[i] = a[i.toNat] := by
  cases a; rfl

@[simp] public theorem data_uset (a : Int8Array) (i : USize) (v : Int8) (h) :
    (a.uset i v h).data = a.data.set i.toNat v (size_eq_data_size a ▸ h) := by
  cases a; rfl

@[simp] public theorem data_set (a : Int8Array) (i : Nat) (v : Int8) (h) :
    (a.set i v h).data = a.data.set i v (size_eq_data_size a ▸ h) := by
  cases a; rfl

@[simp] public theorem data_push (a : Int8Array) (v : Int8) : (a.push v).data = a.data.push v := by
  cases a; rfl

@[simp] public theorem data_pop (a : Int8Array) : a.pop.data = a.data.pop := by
  cases a; rfl

@[simp] public theorem data_extract (a : Int8Array) (start stop : Nat) :
    (a.extract start stop).data = a.data.extract start stop := by
  cases a; rfl

@[simp] public theorem data_replicate (n : Nat) (v : Int8) :
    (replicate n v).data = Array.replicate n v := rfl

@[simp] public theorem data_ofFn {n : Nat} (f : Fin n → Int8) : (ofFn f).data = Array.ofFn f := rfl

@[simp] public theorem data_empty : (empty : Int8Array).data = #[] := rfl

@[simp] public theorem size_pop (a : Int8Array) : a.pop.size = a.size - 1 := by
  simp [-size_data, size_eq_data_size]

@[simp] public theorem size_extract (a : Int8Array) (start stop : Nat) :
    (a.extract start stop).size = min stop a.size - start := by
  simp [-size_data, size_eq_data_size]

@[simp] public theorem size_replicate (n : Nat) (v : Int8) : (replicate n v).size = n := by
  simp [-size_data, size_eq_data_size]

@[simp] public theorem size_ofFn {n : Nat} (f : Fin n → Int8) : (ofFn f).size = n := by
  simp [-size_data, size_eq_data_size]

@[simp] public theorem size_empty : (empty : Int8Array).size = 0 := rfl

@[simp] public theorem getElem_set (a : Int8Array) (i : Nat) (v : Int8) (h) (j : Nat) (hj) :
    (a.set i v h)[j]'hj = if i = j then v else a[j]'(by simpa using hj) := by
  simp [-getElem_data, getElem_eq_getElem_data, Array.getElem_set]

@[simp] public theorem getElem_push (a : Int8Array) (v : Int8) (i : Nat) (h) :
    (a.push v)[i]'h = if h' : i < a.size then a[i] else v := by
  simp [-getElem_data, getElem_eq_getElem_data, Array.getElem_push, -size_data, size_eq_data_size]

@[simp] public theorem getElem_pop (a : Int8Array) (i : Nat) (h) :
    a.pop[i]'h = a[i]'(by simp at h; omega) := by
  simp [-getElem_data, getElem_eq_getElem_data]

@[simp] public theorem getElem_append (a b : Int8Array) (i : Nat) (h) :
    (a ++ b)[i]'h = if h' : i < a.size then a[i] else b[i - a.size]'(by simp at h; omega) := by
  simp [-getElem_data, getElem_eq_getElem_data, Array.getElem_append, -size_data, size_eq_data_size]

@[simp] public theorem getElem_extract (a : Int8Array) (start stop i : Nat) (h) :
    (a.extract start stop)[i]'h = a[start + i]'(by simp at h; omega) := by
  simp [-getElem_data, getElem_eq_getElem_data]

@[simp] public theorem getElem_replicate (n : Nat) (v : Int8) (i : Nat) (h) :
    (replicate n v)[i]'h = v := by
  simp [-getElem_data, getElem_eq_getElem_data]

@[simp] public theorem getElem_ofFn {n : Nat} (f : Fin n → Int8) (i : Nat) (h) :
    (ofFn f)[i]'h = f ⟨i, by simpa using h⟩ := by
  simp [-getElem_data, getElem_eq_getElem_data]

public theorem foldl_eq_foldl_data {β : Type v} (f : β → Int8 → β) (init : β) (a : Int8Array) :
    a.foldl f init = a.data.foldl f init := by
  rfl

public theorem foldr_eq_foldr_data {β : Type v} (f : Int8 → β → β) (init : β) (a : Int8Array) :
    a.foldr f init = a.data.foldr f init := by
  rfl

@[simp] public theorem toList_data (a : Int8Array) : a.data.toList = a.toList := rfl

@[simp] public theorem emptyc_eq_empty : (∅ : Int8Array) = empty := rfl

@[simp] public theorem emptyWithCapacity_eq_empty (c : Nat) : emptyWithCapacity c = empty := rfl

public theorem size_eq_zero_iff {a : Int8Array} : a.size = 0 ↔ a = empty := by
  simp [Int8Array.ext_iff, ← Array.size_eq_zero_iff]

@[simp] public theorem data_set! (a : Int8Array) (i : Nat) (v : Int8) :
    (a.set! i v).data = a.data.set! i v := by
  cases a; rfl

@[simp] public theorem size_set! (a : Int8Array) (i : Nat) (v : Int8) :
    (a.set! i v).size = a.size := by
  simp [-size_data, size_eq_data_size]

public theorem getElem!_eq_getElem!_data (a : Int8Array) (i : Nat) : a[i]! = a.data[i]! := by
  rcases a with ⟨a⟩
  by_cases h : i < a.size <;> simp [getElem!_def, getElem?_def, h] <;> rfl

@[simp] public theorem data_ofList (l : List Int8) : (ofList l).data = l.toArray := rfl

@[simp] public theorem size_ofList (l : List Int8) : (ofList l).size = l.length := rfl

@[simp] public theorem getElem_ofList (l : List Int8) (i : Nat) (h) :
    (ofList l)[i]'h = l[i]'(by simpa using h) := rfl

@[simp] public theorem toList_ofList (l : List Int8) : (ofList l).toList = l := rfl

@[simp] public theorem ofList_toList (a : Int8Array) : ofList a.toList = a := by
  simp [Int8Array.ext_iff, ← toList_data]

@[simp] public theorem markLinear_eq (a : Int8Array) : a.markLinear = a := rfl

@[simp] public theorem propagateMark_eq (a b : Int8Array) : a.propagateMark b = b := rfl

@[simp] public theorem append_empty (a : Int8Array) : a ++ empty = a := by
  simp [Int8Array.ext_iff]

@[simp] public theorem empty_append (a : Int8Array) : empty ++ a = a := by
  simp [Int8Array.ext_iff]

public theorem append_assoc (a b c : Int8Array) : a ++ b ++ c = a ++ (b ++ c) := by
  simp [Int8Array.ext_iff]

@[simp] public theorem append_eq_empty_iff {a b : Int8Array} :
    a ++ b = empty ↔ a = empty ∧ b = empty := by
  simp only [Int8Array.ext_iff, data_append, data_empty, Array.append_eq_empty_iff]

@[simp] public theorem append_right_inj (a : Int8Array) {b c : Int8Array} :
    a ++ b = a ++ c ↔ b = c := by
  simp only [Int8Array.ext_iff, data_append, Array.append_right_inj]

@[simp] public theorem append_left_inj {a b : Int8Array} (c : Int8Array) :
    a ++ c = b ++ c ↔ a = b := by
  simp only [Int8Array.ext_iff, data_append, Array.append_left_inj]

public theorem getElem_append_left {a b : Int8Array} {i : Nat} (h : i < a.size) :
    (a ++ b)[i]'(by simp; omega) = a[i] := by
  simp [h]

public theorem getElem_append_right {a b : Int8Array} {i : Nat} (h : a.size ≤ i)
    (h' : i < (a ++ b).size) : (a ++ b)[i] = b[i - a.size]'(by simp at h'; omega) := by
  simp [Nat.not_lt.mpr h]

@[simp] public theorem extract_same (a : Int8Array) (i : Nat) : a.extract i i = empty := by
  simp [Int8Array.ext_iff]; omega

@[simp] public theorem extract_zero_size (a : Int8Array) : a.extract 0 a.size = a := by
  simp [Int8Array.ext_iff]

@[simp] public theorem extract_eq_empty_iff {a : Int8Array} {i j : Nat} :
    a.extract i j = empty ↔ min j a.size ≤ i := by
  simp [Int8Array.ext_iff]

public theorem extract_extract (a : Int8Array) (i j k l : Nat) :
    (a.extract i j).extract k l = a.extract (i + k) (min (i + l) j) := by
  simp [Int8Array.ext_iff]

public theorem extract_append_extract (a : Int8Array) (i j k : Nat) :
    a.extract i j ++ a.extract j k = a.extract (min i j) (max j k) := by
  simp [Int8Array.ext_iff]

@[simp] public theorem extract_append_eq_left (a b : Int8Array) : (a ++ b).extract 0 a.size = a := by
  simp [Int8Array.ext_iff]

@[simp] public theorem extract_append_eq_right (a b : Int8Array) :
    (a ++ b).extract a.size (a.size + b.size) = b := by
  simp [Int8Array.ext_iff, -size_data, size_eq_data_size]

@[simp] public theorem data_copySlice (src : Int8Array) (srcOff : Nat) (dest : Int8Array)
    (destOff len : Nat) (exact : Bool) :
    (src.copySlice srcOff dest destOff len exact).data =
      dest.data.extract 0 destOff ++ src.data.extract srcOff (srcOff + len) ++
        dest.data.extract (destOff + min len (src.size - srcOff)) dest.size := by
  simp [copySlice]

public theorem copySlice_eq_append (src : Int8Array) (srcOff : Nat) (dest : Int8Array)
    (destOff len : Nat) (exact : Bool) :
    src.copySlice srcOff dest destOff len exact =
      dest.extract 0 destOff ++ src.extract srcOff (srcOff + len) ++
        dest.extract (destOff + min len (src.size - srcOff)) dest.size := by
  simp [Int8Array.ext_iff]

end Int8Array

end ScalarArray

/-- The array with the elements of `l`. -/
@[inline, expose]
public def List.toInt8Array (l : List Int8) : ScalarArray.Int8Array :=
  ScalarArray.Int8Array.ofList l
