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

@[extern c inline "lean_box(lean_sarray_size(#1))", expose]
public def size : (a : @& USizeArray) → Nat
  | mk a => a.size

@[extern "lean_sarray_size", expose]
public def usize : (a : @& USizeArray) → USize
  | mk a => a.usize

@[extern c inline "((size_t*)lean_sarray_cptr(#1))[#2]", expose]
public def uget : (a : @& USizeArray) → (i : USize) → (i.toNat < a.size) → USize
  | mk a, i, h => a.uget i h

@[extern c inline "((size_t*)lean_sarray_cptr(#1))[lean_unbox(#2)]", expose]
public def get : (a : @& USizeArray) → (i : @& Nat) → (i < a.size) → USize
  | mk a, i, h => a[i]

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

private unsafe def usetImpl (a : USizeArray) (i : USize) (v : USize) (_ : i.toNat < a.size) :
    USizeArray :=
  let a : USizeArray := unsafeCast <| ScalarArray.ensureExclusive (unsafeCast a)
  setUSizeUnsafe a i v

@[implemented_by usetImpl, expose]
public def uset : (a : USizeArray) → (i : USize) → (v : USize) → (i.toNat < a.size) → USizeArray
  | mk a, i, v, h => mk (a.uset i v h)

private unsafe def setImpl (a : USizeArray) (i : Nat) (v : USize) (h : i < a.size) : USizeArray :=
  usetImpl a i.toUSize v (Nat.lt_of_le_of_lt (Nat.mod_le ..) h)

@[implemented_by setImpl, expose]
public def set : (a : USizeArray) → (i : Nat) → (v : USize) → (i < a.size) → USizeArray
  | mk a, i, v, h => mk (a.set i v h)

public def get! (a : @& USizeArray) (i : @& Nat) : USize :=
  if h : i < a.size then a.get i h else panic! "index out of bounds"

public def getD (a : @& USizeArray) (i : @& Nat) (v₀ : USize) : USize :=
  if h : i < a.size then a.get i h else v₀

public def set! (a : USizeArray) (i : Nat) (v : USize) : USizeArray :=
  if h : i < a.size then a.set i v h else panic! "index out of bounds"

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
Copies the `n` elements of `b` starting at index `start` to the end of `a` in place. Only valid
when `a` is exclusive, has room for `n` more elements, is not the same object as `b`, and
`start + n ≤ b.size`.
-/
@[extern c inline "#1;\n__builtin_memcpy(lean_sarray_cptr(#1) + lean_sarray_elem_size(#1) * lean_sarray_size(#1), lean_sarray_cptr(#2) + lean_sarray_elem_size(#2) * #3, lean_sarray_elem_size(#2) * #4);\nlean_sarray_set_size(#1, lean_sarray_size(#1) + #4)"]
private unsafe def appendSliceUnsafe : USizeArray → @& USizeArray → USize → USize → USizeArray
  | mk a, mk b, start, n => mk (a ++ b.extract start.toNat (start.toNat + n.toNat))

private unsafe def appendImpl (a b : USizeArray) : USizeArray :=
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
public def append : USizeArray → USizeArray → USizeArray
  | mk a, mk b => mk (a ++ b)

public instance : Append USizeArray := ⟨append⟩

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
    appendSliceUnsafe r a start.toUSize n
  else
    empty

/--
The elements of `a` from index `start` up to, but not including, `min stop a.size`, copied into a
new array.
-/
@[implemented_by extractImpl, expose]
public def extract : (a : @& USizeArray) → (start stop : Nat) → USizeArray
  | mk a, start, stop => mk (a.extract start stop)

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

/-! ## Iteration -/

@[specialize]
private unsafe def foldlMImpl {β : Type v} {m : Type v → Type w} [Monad m] (f : β → USize → m β)
    (init : β) (a : @& USizeArray) : m β :=
  loop 0 init
where
  loop (i : USize) (b : β) : m β :=
    if h : i.toNat < a.size then do loop (i + 1) (← f b (a.uget i h)) else pure b

/-- Folds a monadic function over the elements of `a`, from first to last. -/
@[implemented_by foldlMImpl, expose]
public def foldlM {β : Type v} {m : Type v → Type w} [Monad m] (f : β → USize → m β) (init : β)
    (a : @& USizeArray) : m β :=
  a.data.foldlM f init

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
public def foldl {β : Type v} (f : β → USize → β) (init : β) (a : @& USizeArray) : β :=
  Id.run <| a.foldlM (pure <| f · ·) init

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

end USizeArray

end ScalarArray
