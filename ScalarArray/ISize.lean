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
public def uget : (a : @& ISizeArray) → (i : USize) → (i.toNat < a.size) → ISize
  | mk a, i, h => a.uget i h

@[inline]
private unsafe def getImpl (a : @& ISizeArray) (i : @& Nat) (_ : i < a.size) : ISize :=
  a.uget i.toUSize lcProof

@[implemented_by getImpl, expose]
public def get : (a : @& ISizeArray) → (i : @& Nat) → (i < a.size) → ISize
  | mk a, i, h => a[i]

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

private unsafe def usetImpl (a : ISizeArray) (i : USize) (v : ISize) (_ : i.toNat < a.size) :
    ISizeArray :=
  let a : ISizeArray := unsafeCast <| ScalarArray.ensureExclusive (unsafeCast a)
  setISizeUnsafe a i v

@[implemented_by usetImpl, expose]
public def uset : (a : ISizeArray) → (i : USize) → (v : ISize) → (i.toNat < a.size) → ISizeArray
  | mk a, i, v, h => mk (a.uset i v h)

private unsafe def setImpl (a : ISizeArray) (i : Nat) (v : ISize) (h : i < a.size) : ISizeArray :=
  usetImpl a i.toUSize v (Nat.lt_of_le_of_lt (Nat.mod_le ..) h)

@[implemented_by setImpl, expose]
public def set : (a : ISizeArray) → (i : Nat) → (v : ISize) → (i < a.size) → ISizeArray
  | mk a, i, v, h => mk (a.set i v h)

public def get! (a : @& ISizeArray) (i : @& Nat) : ISize :=
  if h : i < a.size then a.get i h else panic! "index out of bounds"

public def getD (a : @& ISizeArray) (i : @& Nat) (v₀ : ISize) : ISize :=
  if h : i < a.size then a.get i h else v₀

public def set! (a : ISizeArray) (i : Nat) (v : ISize) : ISizeArray :=
  if h : i < a.size then a.set i v h else panic! "index out of bounds"

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
Copies the `n` elements of `b` starting at index `start` to the end of `a` in place. Only valid
when `a` is exclusive, has room for `n` more elements, is not the same object as `b`, and
`start + n ≤ b.size`.
-/
@[extern c inline "#1;\n__builtin_memcpy(lean_sarray_cptr(#1) + lean_sarray_elem_size(#1) * lean_sarray_size(#1), lean_sarray_cptr(#2) + lean_sarray_elem_size(#2) * #3, lean_sarray_elem_size(#2) * #4);\nlean_sarray_set_size(#1, lean_sarray_size(#1) + #4)"]
private unsafe def appendSliceUnsafe : ISizeArray → @& ISizeArray → USize → USize → ISizeArray
  | mk a, mk b, start, n => mk (a ++ b.extract start.toNat (start.toNat + n.toNat))

private unsafe def appendImpl (a b : ISizeArray) : ISizeArray :=
  let s : ScalarArray := unsafeCast a
  let m := (unsafeCast b : ScalarArray).size
  let n := s.size + m
  let cap := s.capacity
  if n < s.size then
    panic! "out of memory"
  else if n ≤ cap then
    appendSliceUnsafe (unsafeCast s.ensureExclusive) b 0 m
  else
    let cap := if cap < cap + cap && n ≤ cap + cap then cap + cap else n
    appendSliceUnsafe (unsafeCast (s.copyWithCapacity cap lcProof)) b 0 m

/-- Appends the elements of `b` to `a`, in place when `a` is not shared and has room. -/
@[implemented_by appendImpl, expose]
public def append : ISizeArray → ISizeArray → ISizeArray
  | mk a, mk b => mk (a ++ b)

public instance : Append ISizeArray := ⟨append⟩

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
    appendSliceUnsafe r a start.toUSize n
  else
    empty

/--
The elements of `a` from index `start` up to, but not including, `min stop a.size`, copied into a
new array.
-/
@[implemented_by extractImpl, expose]
public def extract : (a : @& ISizeArray) → (start stop : Nat) → ISizeArray
  | mk a, start, stop => mk (a.extract start stop)

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

/-! ## Iteration -/

@[specialize]
private unsafe def foldlMImpl {β : Type v} {m : Type v → Type w} [Monad m] (f : β → ISize → m β)
    (init : β) (a : @& ISizeArray) : m β :=
  loop 0 init
where
  loop (i : USize) (b : β) : m β :=
    if h : i.toNat < a.size then do loop (i + 1) (← f b (a.uget i h)) else pure b

/-- Folds a monadic function over the elements of `a`, from first to last. -/
@[implemented_by foldlMImpl, expose]
public def foldlM {β : Type v} {m : Type v → Type w} [Monad m] (f : β → ISize → m β) (init : β)
    (a : @& ISizeArray) : m β :=
  a.data.foldlM f init

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
public def foldl {β : Type v} (f : β → ISize → β) (init : β) (a : @& ISizeArray) : β :=
  Id.run <| a.foldlM (pure <| f · ·) init

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

end ISizeArray

end ScalarArray
