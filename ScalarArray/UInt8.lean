/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import all ScalarArray.Internal

/-!
# Arrays of `UInt8`

`ScalarArray.UInt8Array` stores `UInt8` values unboxed, 1 byte per element, in a Lean runtime
scalar array. Its logical model is `Array UInt8`: `UInt8Array.mk` and `UInt8Array.data` convert
between the two, and every operation is specified by its effect on the model.

The runtime representation is a `ScalarArray` with element size 1. Reads and in-place writes
are inline C. `uset`, `set` and `push` update the array in place when it is not shared and copy
it otherwise, like `Array` and `ByteArray`.
-/

namespace ScalarArray

/--
Arrays of `UInt8` values, stored unboxed in a scalar array with element size 1.

The logical model is an `Array UInt8`. At runtime a `UInt8Array` is a `ScalarArray`, so every
function that looks inside the constructor must be `extern` or `implemented_by`.
-/
public inductive UInt8Array : Type
  | public mk (data : Array UInt8)

namespace UInt8Array

-- `lean_byte_array_size` reads the size of any scalar array, whatever its element size.
@[extern "lean_byte_array_size", tagged_return, expose]
public def size : (a : @& UInt8Array) → Nat
  | mk a => a.size

/--
The size of `a` as a `USize`. Since `USize` can address all memory, no array has more elements than
`USize` can count.
-/
@[extern "lean_sarray_size", simp, expose]
public def usize (a : @& UInt8Array) : USize :=
  a.size.toUSize

@[extern c inline "((uint8_t*)lean_sarray_cptr(#1))[#2]", expose]
public def uget : (a : @& UInt8Array) → (i : USize) → (h : i.toNat < a.size := by get_elem_tactic) →
    UInt8
  | mk a, i, h => a.uget i h

@[expose]
public def get : (a : @& UInt8Array) → (i : @& Nat) → (h : i < a.size := by get_elem_tactic) → UInt8
  | mk a, i, h => a[i]

@[inline]
private unsafe def getImpl : type_of% @get :=
  fun a i _ => a.uget i.toUSize lcProof

attribute [implemented_by getImpl] get

/-- Stores `v` at index `i` in place. Only valid when `a` is exclusive and `i` is in bounds. -/
@[extern c inline "#1;\n((uint8_t*)lean_sarray_cptr(#1))[#2] = #3"]
private unsafe def setUInt8Unsafe : UInt8Array → USize → UInt8 → UInt8Array
  | .mk a, i, v => .mk <| a.uset i v lcProof

private unsafe def toUSizeChecked (n : Nat) : USize :=
  if n < USize.size >>> 1 then n.toUSize else panic! "out of memory"

private unsafe def mkWithCapacityImpl (a : Array UInt8) (capacity : Nat := a.size) : UInt8Array :=
  let cap := toUSizeChecked capacity
  let sz := toUSizeChecked a.size
  let r : UInt8Array := unsafeCast <| ScalarArray.allocate 1 sz (max sz cap) lcProof
  loop r 0
where
  loop (r : UInt8Array) (i : Nat) : UInt8Array :=
    if h : i < a.size then loop (setUInt8Unsafe r i.toUSize a[i]) (i + 1) else r

private unsafe def mkImpl (a : Array UInt8) : UInt8Array :=
  mkWithCapacityImpl a a.size

attribute [implemented_by mkImpl] UInt8Array.mk

private unsafe def dataImpl (a : @& UInt8Array) : Array UInt8 :=
  loop 0 (Array.emptyWithCapacity a.size)
where
  loop (i : USize) (r : Array UInt8) : Array UInt8 :=
    if h : i.toNat < a.size then loop (i + 1) (r.push (a.uget i h)) else r

/-- The elements of `a` as an `Array UInt8`. -/
@[implemented_by dataImpl, expose]
public def data : (a : @& UInt8Array) → Array UInt8
  | mk a => a

private unsafe def emptyWithCapacityImpl (capacity : Nat) : UInt8Array :=
  mkWithCapacityImpl #[] capacity

/-- An empty array with room for `capacity` elements before reallocating. -/
@[implemented_by emptyWithCapacityImpl, expose]
public def emptyWithCapacity (capacity : Nat) : UInt8Array :=
  mk #[]

@[expose] public def empty : UInt8Array := emptyWithCapacity 0

public instance : EmptyCollection UInt8Array := ⟨empty⟩

public instance : Inhabited UInt8Array := ⟨empty⟩

@[expose]
public def uset :
    (a : UInt8Array) → (i : USize) → (v : UInt8) → (h : i.toNat < a.size := by get_elem_tactic) →
    UInt8Array
  | mk a, i, v, h => mk (a.uset i v h)

private unsafe def usetImpl : type_of% @uset :=
  fun a i v _ => setUInt8Unsafe (unsafeCast <| ScalarArray.ensureExclusive (unsafeCast a)) i v

attribute [implemented_by usetImpl] uset

@[expose]
public def set :
    (a : UInt8Array) → (i : Nat) → (v : UInt8) → (h : i < a.size := by get_elem_tactic) →
    UInt8Array
  | mk a, i, v, h => mk (a.set i v h)

private unsafe def setImpl : type_of% @set :=
  fun a i v _ => usetImpl a i.toUSize v lcProof

attribute [implemented_by setImpl] set

public def get! (a : @& UInt8Array) (i : @& Nat) : UInt8 :=
  if h : i < a.size then a.get i h else panic! "index out of bounds"

public def getD (a : @& UInt8Array) (i : @& Nat) (v₀ : UInt8) : UInt8 :=
  if h : i < a.size then a.get i h else v₀

private unsafe def setBangImpl (a : UInt8Array) (i : Nat) (v : UInt8) : UInt8Array :=
  if h : i < a.size then setImpl a i v h else a

/-- Replaces the element at index `i`. If `i` is out of bounds, the array is returned unmodified. -/
@[implemented_by setBangImpl, expose]
public def set! : UInt8Array → Nat → UInt8 → UInt8Array
  | mk a, i, v => mk (a.set! i v)

public instance : GetElem UInt8Array Nat UInt8 fun a i => i < a.size where
  getElem a i h := a.get i h

public instance : GetElem UInt8Array USize UInt8 fun a i => i.toNat < a.size where
  getElem a i h := a.uget i h

private unsafe def pushImpl (a : UInt8Array) (v : UInt8) : UInt8Array :=
  let s : ScalarArray := unsafeCast a
  let cap := s.capacity
  if s.size < cap then
    loop s.ensureExclusive
  else if cap < cap + cap + 1 then
    loop (s.copyWithCapacity (cap + cap + 1) lcProof)
  else
    panic! "out of memory"
where
  loop (s : ScalarArray) : UInt8Array :=
    let i := s.size
    setUInt8Unsafe (unsafeCast (s.resizeUnsafe (i + 1) lcProof lcProof)) i v

@[implemented_by pushImpl, expose]
public def push : UInt8Array → UInt8 → UInt8Array
  | mk a, v => mk (a.push v)

/--
Copies `n` bytes of the data of `src`, starting at byte `srcOff`, into the data of `dest`, starting at
byte `destOff`. Only valid when `dest` is exclusive and both ranges are within the capacities.
-/
-- TODO: core has no runtime function that copies a slice of a scalar array with any element size;
-- `lean_byte_array_copy_slice` only works for bytes. Replace this once core has one.
@[extern c inline "#1;\n__builtin_memcpy(lean_sarray_cptr(#1) + #4, lean_sarray_cptr(#2) + #3, #5)"]
private unsafe def memcpyUnsafe : UInt8Array → @& UInt8Array → (srcOff destOff n : USize) → UInt8Array
  | dest, _, _, _, _ => dest

/--
Copies the `n` elements of `src` starting at index `srcOff` into `dest` starting at index `destOff`,
in place, and grows the size of `dest` to `destOff + n` if it is smaller. Only valid when `dest` is
exclusive, has capacity for `destOff + n` elements, and is not the same object as `src`, and when
`destOff ≤ dest.size` and `srcOff + n ≤ src.size`.
-/
@[inline]
private unsafe def copySliceUnsafe (dest : UInt8Array) (src : @& UInt8Array) (srcOff destOff n : USize) :
    UInt8Array :=
  let esz := (unsafeCast src : ScalarArray).elemSize.toUSize
  let d : ScalarArray := unsafeCast (memcpyUnsafe dest src (srcOff * esz) (destOff * esz) (n * esz))
  unsafeCast (d.resizeUnsafe (max d.size (destOff + n)) lcProof lcProof)

private unsafe def appendImpl (a b : UInt8Array) : UInt8Array :=
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
public def append : UInt8Array → UInt8Array → UInt8Array
  | mk a, mk b => mk (a ++ b)

public instance : Append UInt8Array := ⟨append⟩

private unsafe def copySliceImpl (src : @& UInt8Array) (srcOff : Nat) (dest : UInt8Array)
    (destOff len : Nat) (exact : Bool := true) : UInt8Array :=
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
public def copySlice (src : @& UInt8Array) (srcOff : Nat) (dest : UInt8Array) (destOff len : Nat)
    (exact : Bool := true) : UInt8Array :=
  mk (dest.data.extract 0 destOff ++ src.data.extract srcOff (srcOff + len) ++
    dest.data.extract (destOff + min len (src.data.size - srcOff)) dest.data.size)

/-! ## Removing elements -/

public def isEmpty (a : @& UInt8Array) : Bool := a.size == 0

private unsafe def popImpl (a : UInt8Array) : UInt8Array :=
  if a.size == 0 then
    a
  else
    let s : ScalarArray := ScalarArray.ensureExclusive (unsafeCast a)
    unsafeCast (s.resizeUnsafe (s.size - 1) lcProof lcProof)

/-- Removes the last element of `a`, if any, in place when `a` is not shared. -/
@[implemented_by popImpl, expose]
public def pop : UInt8Array → UInt8Array
  | mk a => mk a.pop

public def back? (a : @& UInt8Array) : Option UInt8 := a[a.size - 1]?

public def back! (a : @& UInt8Array) : UInt8 := a[a.size - 1]!

public def back (a : @& UInt8Array) (h : 0 < a.size) : UInt8 := a[a.size - 1]'(Nat.sub_lt h Nat.one_pos)

private unsafe def extractImpl (a : @& UInt8Array) (start stop : Nat) : UInt8Array :=
  let stop := min stop a.size
  if start < stop then
    let n := (stop - start).toUSize
    let r : UInt8Array := unsafeCast <| ScalarArray.allocate 1 0 n lcProof
    copySliceUnsafe r a start.toUSize 0 n
  else
    empty

/--
The elements of `a` from index `start` up to, but not including, `min stop a.size`, copied into a
new array.
-/
@[implemented_by extractImpl, expose]
public def extract : (a : @& UInt8Array) → (start stop : Nat) → UInt8Array
  | mk a, start, stop => mk (a.extract start stop)

/-! ## Linearity -/

/--
Marks `a` as linear, a debugging aid: if a marked array is ever shared and then modified, the
runtime reports it. Logically this is the identity.
-/
@[never_extract, extern "lean_sarray_mark_linear", expose]
public def markLinear (a : UInt8Array) : UInt8Array := a

/-- Returns `b`, marking it as linear if `a` is marked. Logically this is `b`. -/
@[never_extract, extern "lean_sarray_propagate_mark", expose]
public def propagateMark (a : @& UInt8Array) (b : UInt8Array) : UInt8Array := b

/-! ## Search -/

/--
The index of the first element at or after `start` that satisfies `p`, with a proof that it is in
bounds.
-/
@[inline]
public def findFinIdx? (a : UInt8Array) (p : UInt8 → Bool) (start := 0) : Option (Fin a.size) :=
  let rec @[specialize] loop (i : Nat) :=
    if h : i < a.size then
      if p a[i] then some ⟨i, h⟩ else loop (i + 1)
    else
      none
    termination_by a.size - i
  loop start

/-- The index of the first element at or after `start` that satisfies `p`. -/
@[inline]
public def findIdx? (a : UInt8Array) (p : UInt8 → Bool) (start := 0) : Option Nat :=
  let rec @[specialize] loop (i : Nat) :=
    if h : i < a.size then
      if p a[i] then some i else loop (i + 1)
    else
      none
    termination_by a.size - i
  loop start

/-! ## Building arrays -/

private unsafe def replicateImpl (n : Nat) (v : UInt8) : UInt8Array :=
  let sz := toUSizeChecked n
  loop sz (unsafeCast <| ScalarArray.allocate 1 sz sz lcProof) 0
where
  loop (sz : USize) (r : UInt8Array) (i : USize) : UInt8Array :=
    if i < sz then loop sz (setUInt8Unsafe r i v) (i + 1) else r

/-- An array of `n` copies of `v`. -/
@[implemented_by replicateImpl, expose]
public def replicate (n : Nat) (v : UInt8) : UInt8Array :=
  mk (Array.replicate n v)

private unsafe def ofFnImpl {n : Nat} (f : Fin n → UInt8) : UInt8Array :=
  let sz := toUSizeChecked n
  loop (unsafeCast <| ScalarArray.allocate 1 sz sz lcProof) 0
where
  loop (r : UInt8Array) (i : Nat) : UInt8Array :=
    if h : i < n then loop (setUInt8Unsafe r i.toUSize (f ⟨i, h⟩)) (i + 1) else r

/-- The array `#[f 0, …, f (n - 1)]`. -/
@[implemented_by ofFnImpl, expose]
public def ofFn {n : Nat} (f : Fin n → UInt8) : UInt8Array :=
  mk (Array.ofFn f)

private unsafe def ofListImpl (l : List UInt8) : UInt8Array :=
  loop l (emptyWithCapacity l.length)
where
  loop : List UInt8 → UInt8Array → UInt8Array
    | [], r => r
    | x :: xs, r => loop xs (r.push x)

/-- The array with the elements of `l`. -/
@[implemented_by ofListImpl, expose]
public def ofList (l : List UInt8) : UInt8Array :=
  mk l.toArray

/-! ## Iteration -/

@[specialize]
private unsafe def foldlMImpl {β : Type v} {m : Type v → Type w} [Monad m] (f : β → UInt8 → m β)
    (init : β) (a : @& UInt8Array) (start := 0) (stop := a.size) : m β :=
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
public def foldlM {β : Type v} {m : Type v → Type w} [Monad m] (f : β → UInt8 → m β) (init : β)
    (a : @& UInt8Array) (start := 0) (stop := a.size) : m β :=
  a.data.foldlM f init start stop

@[specialize]
private unsafe def foldrMImpl {β : Type v} {m : Type v → Type w} [Monad m] (f : UInt8 → β → m β)
    (init : β) (a : @& UInt8Array) : m β :=
  loop a.usize init
where
  loop (i : USize) (b : β) : m β :=
    if h : 0 < i ∧ (i - 1).toNat < a.size then do loop (i - 1) (← f (a.uget (i - 1) h.2) b)
    else pure b

/-- Folds a monadic function over the elements of `a`, from last to first. -/
@[implemented_by foldrMImpl, expose]
public def foldrM {β : Type v} {m : Type v → Type w} [Monad m] (f : UInt8 → β → m β) (init : β)
    (a : @& UInt8Array) : m β :=
  a.data.foldrM f init

@[inline, expose]
public def foldl {β : Type v} (f : β → UInt8 → β) (init : β) (a : @& UInt8Array) (start := 0)
    (stop := a.size) : β :=
  Id.run <| a.foldlM (pure <| f · ·) init start stop

@[inline, expose]
public def foldr {β : Type v} (f : UInt8 → β → β) (init : β) (a : @& UInt8Array) : β :=
  Id.run <| a.foldrM (pure <| f · ·) init

@[inline]
public def forM {m : Type v → Type w} [Monad m] (f : UInt8 → m PUnit) (a : @& UInt8Array) :
    m PUnit :=
  a.foldlM (fun _ x => f x) ⟨⟩

@[specialize]
private unsafe def forInImpl {β : Type v} {m : Type v → Type w} [Monad m] (a : @& UInt8Array)
    (init : β) (f : UInt8 → β → m (ForInStep β)) : m β :=
  loop 0 init
where
  loop (i : USize) (b : β) : m β :=
    if h : i.toNat < a.size then do
      match ← f (a.uget i h) b with
      | .done b => pure b
      | .yield b => loop (i + 1) b
    else pure b

@[implemented_by forInImpl]
public def forIn {β : Type v} {m : Type v → Type w} [Monad m] (a : @& UInt8Array) (init : β)
    (f : UInt8 → β → m (ForInStep β)) : m β :=
  ForIn.forIn a.data init f

public instance [Monad m] : ForIn m UInt8Array UInt8 where
  forIn a b f := UInt8Array.forIn a b f

@[specialize]
private unsafe def anyImpl (a : @& UInt8Array) (p : UInt8 → Bool) : Bool :=
  loop 0
where
  loop (i : USize) : Bool :=
    if h : i.toNat < a.size then p (a.uget i h) || loop (i + 1) else false

/-- Whether some element of `a` satisfies `p`. -/
@[implemented_by anyImpl]
public def any (a : @& UInt8Array) (p : UInt8 → Bool) : Bool :=
  a.data.any p

@[specialize]
private unsafe def allImpl (a : @& UInt8Array) (p : UInt8 → Bool) : Bool :=
  loop 0
where
  loop (i : USize) : Bool :=
    if h : i.toNat < a.size then p (a.uget i h) && loop (i + 1) else true

/-- Whether every element of `a` satisfies `p`. -/
@[implemented_by allImpl]
public def all (a : @& UInt8Array) (p : UInt8 → Bool) : Bool :=
  a.data.all p

private unsafe def containsImpl (a : @& UInt8Array) (v : UInt8) : Bool :=
  anyImpl a (v == ·)

/-- Whether `v` is an element of `a`. -/
@[implemented_by containsImpl]
public def contains (a : @& UInt8Array) (v : UInt8) : Bool :=
  a.data.contains v

/-! ## Equality and hashing -/

private theorem data_injective : {a b : UInt8Array} → a.data = b.data → a = b
  | mk _, mk _, rfl => rfl

/-- Decides equality by comparing the two arrays' memory. -/
@[extern "lean_sarray_dec_eq"]
public def decEq (a b : @& UInt8Array) : Decidable (a = b) :=
  decidable_of_iff (a.data = b.data) ⟨data_injective, fun h => h ▸ rfl⟩

public instance : DecidableEq UInt8Array := decEq

private unsafe def hashImpl (a : @& UInt8Array) : UInt64 :=
  foldlMImpl (m := Id) (fun r x => mixHash r (Hashable.hash x)) 7 a

/-- The same hash as `a.data`. -/
@[implemented_by hashImpl]
public def hash (a : @& UInt8Array) : UInt64 :=
  Hashable.hash a.data

public instance : Hashable UInt8Array := ⟨hash⟩

/-! ## Conversion and printing -/

@[expose] public def toList (a : UInt8Array) : List UInt8 := a.data.toList

public instance : Repr UInt8Array where
  reprPrec a _ := "UInt8Array.mk " ++ repr a.data

public instance : ToString UInt8Array where
  toString a := "UInt8Array.mk " ++ toString a.data

@[simp] public theorem size_mk (a : Array UInt8) : (mk a).size = a.size := rfl

@[simp] public theorem data_mk (a : Array UInt8) : (mk a).data = a := rfl

@[simp] public theorem mk_data (a : UInt8Array) : mk a.data = a := by cases a; rfl

public theorem size_eq_data_size (a : UInt8Array) : a.size = a.data.size := by cases a; rfl

@[simp] public theorem size_data (a : UInt8Array) : a.data.size = a.size :=
  (size_eq_data_size a).symm

@[simp] public theorem size_uset (a : UInt8Array) (i : USize) (v : UInt8) (h) :
    (a.uset i v h).size = a.size := by
  cases a; exact Array.size_set ..

@[simp] public theorem size_set (a : UInt8Array) (i : Nat) (v : UInt8) (h) :
    (a.set i v h).size = a.size := by
  cases a; exact Array.size_set ..

@[simp] public theorem size_push (a : UInt8Array) (v : UInt8) : (a.push v).size = a.size + 1 := by
  cases a; simp [push, size]

@[simp] public theorem data_append (a b : UInt8Array) : (a ++ b).data = a.data ++ b.data := by
  cases a; cases b; rfl

@[simp] public theorem size_append (a b : UInt8Array) : (a ++ b).size = a.size + b.size := by
  simp [-size_data, size_eq_data_size]

@[ext] public theorem ext {a b : UInt8Array} (h : a.data = b.data) : a = b := data_injective h

@[simp] public theorem getElem_mk (a : Array UInt8) (i : Nat) (h : i < (mk a).size) :
    (mk a)[i] = a[i] := rfl

public theorem getElem_eq_getElem_data (a : UInt8Array) (i : Nat) (h : i < a.size) :
    a[i] = a.data[i]'(size_eq_data_size a ▸ h) := by
  cases a; rfl

@[simp] public theorem getElem_data (a : UInt8Array) (i : Nat) (h : i < a.data.size) :
    a.data[i] = a[i]'(by simpa using h) := by
  cases a; rfl

public theorem ext_getElem {a b : UInt8Array} (h₁ : a.size = b.size)
    (h₂ : ∀ (i : Nat) (hi₁ : i < a.size) (hi₂ : i < b.size), a[i] = b[i]) : a = b := by
  ext i hi₁ hi₂
  · simpa using h₁
  · simpa using h₂ i (by simpa using hi₁) (by simpa using hi₂)

@[simp] public theorem getElem_usize (a : UInt8Array) (i : USize) (h : i.toNat < a.size) :
    a[i] = a[i.toNat] := by
  cases a; rfl

@[simp] public theorem data_uset (a : UInt8Array) (i : USize) (v : UInt8) (h) :
    (a.uset i v h).data = a.data.set i.toNat v (size_eq_data_size a ▸ h) := by
  cases a; rfl

@[simp] public theorem data_set (a : UInt8Array) (i : Nat) (v : UInt8) (h) :
    (a.set i v h).data = a.data.set i v (size_eq_data_size a ▸ h) := by
  cases a; rfl

@[simp] public theorem data_push (a : UInt8Array) (v : UInt8) : (a.push v).data = a.data.push v := by
  cases a; rfl

@[simp] public theorem data_pop (a : UInt8Array) : a.pop.data = a.data.pop := by
  cases a; rfl

@[simp] public theorem data_extract (a : UInt8Array) (start stop : Nat) :
    (a.extract start stop).data = a.data.extract start stop := by
  cases a; rfl

@[simp] public theorem data_replicate (n : Nat) (v : UInt8) :
    (replicate n v).data = Array.replicate n v := rfl

@[simp] public theorem data_ofFn {n : Nat} (f : Fin n → UInt8) : (ofFn f).data = Array.ofFn f := rfl

@[simp] public theorem data_empty : (empty : UInt8Array).data = #[] := rfl

@[simp] public theorem size_pop (a : UInt8Array) : a.pop.size = a.size - 1 := by
  simp [-size_data, size_eq_data_size]

@[simp] public theorem size_extract (a : UInt8Array) (start stop : Nat) :
    (a.extract start stop).size = min stop a.size - start := by
  simp [-size_data, size_eq_data_size]

@[simp] public theorem size_replicate (n : Nat) (v : UInt8) : (replicate n v).size = n := by
  simp [-size_data, size_eq_data_size]

@[simp] public theorem size_ofFn {n : Nat} (f : Fin n → UInt8) : (ofFn f).size = n := by
  simp [-size_data, size_eq_data_size]

@[simp] public theorem size_empty : (empty : UInt8Array).size = 0 := rfl

@[simp] public theorem getElem_set (a : UInt8Array) (i : Nat) (v : UInt8) (h) (j : Nat) (hj) :
    (a.set i v h)[j]'hj = if i = j then v else a[j]'(by simpa using hj) := by
  simp [-getElem_data, getElem_eq_getElem_data, Array.getElem_set]

@[simp] public theorem getElem_push (a : UInt8Array) (v : UInt8) (i : Nat) (h) :
    (a.push v)[i]'h = if h' : i < a.size then a[i] else v := by
  simp [-getElem_data, getElem_eq_getElem_data, Array.getElem_push, -size_data, size_eq_data_size]

@[simp] public theorem getElem_pop (a : UInt8Array) (i : Nat) (h) :
    a.pop[i]'h = a[i]'(by simp at h; omega) := by
  simp [-getElem_data, getElem_eq_getElem_data]

@[simp] public theorem getElem_append (a b : UInt8Array) (i : Nat) (h) :
    (a ++ b)[i]'h = if h' : i < a.size then a[i] else b[i - a.size]'(by simp at h; omega) := by
  simp [-getElem_data, getElem_eq_getElem_data, Array.getElem_append, -size_data, size_eq_data_size]

@[simp] public theorem getElem_extract (a : UInt8Array) (start stop i : Nat) (h) :
    (a.extract start stop)[i]'h = a[start + i]'(by simp at h; omega) := by
  simp [-getElem_data, getElem_eq_getElem_data]

@[simp] public theorem getElem_replicate (n : Nat) (v : UInt8) (i : Nat) (h) :
    (replicate n v)[i]'h = v := by
  simp [-getElem_data, getElem_eq_getElem_data]

@[simp] public theorem getElem_ofFn {n : Nat} (f : Fin n → UInt8) (i : Nat) (h) :
    (ofFn f)[i]'h = f ⟨i, by simpa using h⟩ := by
  simp [-getElem_data, getElem_eq_getElem_data]

public theorem foldl_eq_foldl_data {β : Type v} (f : β → UInt8 → β) (init : β) (a : UInt8Array) :
    a.foldl f init = a.data.foldl f init := by
  rfl

public theorem foldr_eq_foldr_data {β : Type v} (f : UInt8 → β → β) (init : β) (a : UInt8Array) :
    a.foldr f init = a.data.foldr f init := by
  rfl

@[simp] public theorem toList_data (a : UInt8Array) : a.data.toList = a.toList := rfl

@[simp] public theorem emptyc_eq_empty : (∅ : UInt8Array) = empty := rfl

@[simp] public theorem emptyWithCapacity_eq_empty (c : Nat) : emptyWithCapacity c = empty := rfl

public theorem size_eq_zero_iff {a : UInt8Array} : a.size = 0 ↔ a = empty := by
  simp [UInt8Array.ext_iff, ← Array.size_eq_zero_iff]

@[simp] public theorem data_set! (a : UInt8Array) (i : Nat) (v : UInt8) :
    (a.set! i v).data = a.data.set! i v := by
  cases a; rfl

@[simp] public theorem size_set! (a : UInt8Array) (i : Nat) (v : UInt8) :
    (a.set! i v).size = a.size := by
  simp [-size_data, size_eq_data_size]

public theorem getElem!_eq_getElem!_data (a : UInt8Array) (i : Nat) : a[i]! = a.data[i]! := by
  rcases a with ⟨a⟩
  by_cases h : i < a.size <;> simp [getElem!_def, getElem?_def, h] <;> rfl

@[simp] public theorem data_ofList (l : List UInt8) : (ofList l).data = l.toArray := rfl

@[simp] public theorem size_ofList (l : List UInt8) : (ofList l).size = l.length := rfl

@[simp] public theorem getElem_ofList (l : List UInt8) (i : Nat) (h) :
    (ofList l)[i]'h = l[i]'(by simpa using h) := rfl

@[simp] public theorem toList_ofList (l : List UInt8) : (ofList l).toList = l := rfl

@[simp] public theorem ofList_toList (a : UInt8Array) : ofList a.toList = a := by
  simp [UInt8Array.ext_iff, ← toList_data]

@[simp] public theorem markLinear_eq (a : UInt8Array) : a.markLinear = a := rfl

@[simp] public theorem propagateMark_eq (a b : UInt8Array) : a.propagateMark b = b := rfl

@[simp] public theorem append_empty (a : UInt8Array) : a ++ empty = a := by
  simp [UInt8Array.ext_iff]

@[simp] public theorem empty_append (a : UInt8Array) : empty ++ a = a := by
  simp [UInt8Array.ext_iff]

public theorem append_assoc (a b c : UInt8Array) : a ++ b ++ c = a ++ (b ++ c) := by
  simp [UInt8Array.ext_iff]

@[simp] public theorem append_eq_empty_iff {a b : UInt8Array} :
    a ++ b = empty ↔ a = empty ∧ b = empty := by
  simp only [UInt8Array.ext_iff, data_append, data_empty, Array.append_eq_empty_iff]

@[simp] public theorem append_right_inj (a : UInt8Array) {b c : UInt8Array} :
    a ++ b = a ++ c ↔ b = c := by
  simp only [UInt8Array.ext_iff, data_append, Array.append_right_inj]

@[simp] public theorem append_left_inj {a b : UInt8Array} (c : UInt8Array) :
    a ++ c = b ++ c ↔ a = b := by
  simp only [UInt8Array.ext_iff, data_append, Array.append_left_inj]

public theorem getElem_append_left {a b : UInt8Array} {i : Nat} (h : i < a.size) :
    (a ++ b)[i]'(by simp; omega) = a[i] := by
  simp [h]

public theorem getElem_append_right {a b : UInt8Array} {i : Nat} (h : a.size ≤ i)
    (h' : i < (a ++ b).size) : (a ++ b)[i] = b[i - a.size]'(by simp at h'; omega) := by
  simp [Nat.not_lt.mpr h]

@[simp] public theorem extract_same (a : UInt8Array) (i : Nat) : a.extract i i = empty := by
  simp [UInt8Array.ext_iff]; omega

@[simp] public theorem extract_zero_size (a : UInt8Array) : a.extract 0 a.size = a := by
  simp [UInt8Array.ext_iff]

@[simp] public theorem extract_eq_empty_iff {a : UInt8Array} {i j : Nat} :
    a.extract i j = empty ↔ min j a.size ≤ i := by
  simp [UInt8Array.ext_iff]

public theorem extract_extract (a : UInt8Array) (i j k l : Nat) :
    (a.extract i j).extract k l = a.extract (i + k) (min (i + l) j) := by
  simp [UInt8Array.ext_iff]

public theorem extract_append_extract (a : UInt8Array) (i j k : Nat) :
    a.extract i j ++ a.extract j k = a.extract (min i j) (max j k) := by
  simp [UInt8Array.ext_iff]

@[simp] public theorem extract_append_eq_left (a b : UInt8Array) : (a ++ b).extract 0 a.size = a := by
  simp [UInt8Array.ext_iff]

@[simp] public theorem extract_append_eq_right (a b : UInt8Array) :
    (a ++ b).extract a.size (a.size + b.size) = b := by
  simp [UInt8Array.ext_iff, -size_data, size_eq_data_size]

@[simp] public theorem data_copySlice (src : UInt8Array) (srcOff : Nat) (dest : UInt8Array)
    (destOff len : Nat) (exact : Bool) :
    (src.copySlice srcOff dest destOff len exact).data =
      dest.data.extract 0 destOff ++ src.data.extract srcOff (srcOff + len) ++
        dest.data.extract (destOff + min len (src.size - srcOff)) dest.size := by
  simp [copySlice]

public theorem copySlice_eq_append (src : UInt8Array) (srcOff : Nat) (dest : UInt8Array)
    (destOff len : Nat) (exact : Bool) :
    src.copySlice srcOff dest destOff len exact =
      dest.extract 0 destOff ++ src.extract srcOff (srcOff + len) ++
        dest.extract (destOff + min len (src.size - srcOff)) dest.size := by
  simp [UInt8Array.ext_iff]

end UInt8Array

end ScalarArray

/-- The array with the elements of `l`. -/
@[inline, expose]
public def List.toUInt8Array (l : List UInt8) : ScalarArray.UInt8Array :=
  ScalarArray.UInt8Array.ofList l
