/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import all ScalarArray.Internal

/-!
# Arrays of `Int16`

`ScalarArray.Int16Array` stores `Int16` values unboxed, 2 bytes per element, in a Lean runtime
scalar array. Its logical model is `Array Int16`: `Int16Array.mk` and `Int16Array.data` convert
between the two, and every operation is specified by its effect on the model.

The runtime representation is a `ScalarArray` with element size 2. Reads and in-place writes
are inline C. `uset`, `set` and `push` update the array in place when it is not shared and copy
it otherwise, like `Array` and `ByteArray`.
-/

namespace ScalarArray

/--
Arrays of `Int16` values, stored unboxed in a scalar array with element size 2.

The logical model is an `Array Int16`. At runtime a `Int16Array` is a `ScalarArray`, so every
function that looks inside the constructor must be `extern` or `implemented_by`.
-/
public inductive Int16Array : Type
  | public mk (data : Array Int16)

namespace Int16Array

@[extern c inline "lean_box(lean_sarray_size(#1))", tagged_return, expose]
public def size : (a : @& Int16Array) → Nat
  | mk a => a.size

/--
The size of `a` as a `USize`. Since `USize` can address all memory, no array has more elements than
`USize` can count.
-/
@[extern "lean_sarray_size", simp, expose]
public def usize (a : @& Int16Array) : USize :=
  a.size.toUSize

@[extern c inline "((uint16_t*)lean_sarray_cptr(#1))[#2]", expose]
public def uget : (a : @& Int16Array) → (i : USize) → (i.toNat < a.size) → Int16
  | mk a, i, h => a.uget i h

@[extern c inline "((uint16_t*)lean_sarray_cptr(#1))[lean_unbox(#2)]", expose]
public def get : (a : @& Int16Array) → (i : @& Nat) → (i < a.size) → Int16
  | mk a, i, h => a[i]

/-- Stores `v` at index `i` in place. Only valid when `a` is exclusive and `i` is in bounds. -/
@[extern c inline "#1;\n((uint16_t*)lean_sarray_cptr(#1))[#2] = #3"]
private unsafe def setInt16Unsafe : Int16Array → USize → Int16 → Int16Array
  | .mk a, i, v => .mk <| a.uset i v lcProof

private unsafe def toUSizeChecked (n : Nat) : USize :=
  if n < USize.size >>> 1 then n.toUSize else panic! "out of memory"

private unsafe def mkWithCapacityImpl (a : Array Int16) (capacity : Nat := a.size) : Int16Array :=
  let cap := toUSizeChecked capacity
  let sz := toUSizeChecked a.size
  let r : Int16Array := unsafeCast <| ScalarArray.allocate 2 sz (max sz cap) lcProof
  loop r 0
where
  loop (r : Int16Array) (i : Nat) : Int16Array :=
    if h : i < a.size then loop (setInt16Unsafe r i.toUSize a[i]) (i + 1) else r

private unsafe def mkImpl (a : Array Int16) : Int16Array :=
  mkWithCapacityImpl a a.size

attribute [implemented_by mkImpl] Int16Array.mk

private unsafe def dataImpl (a : @& Int16Array) : Array Int16 :=
  loop 0 (Array.emptyWithCapacity a.size)
where
  loop (i : USize) (r : Array Int16) : Array Int16 :=
    if h : i.toNat < a.size then loop (i + 1) (r.push (a.uget i h)) else r

/-- The elements of `a` as an `Array Int16`. -/
@[implemented_by dataImpl, expose]
public def data : (a : @& Int16Array) → Array Int16
  | mk a => a

private unsafe def emptyWithCapacityImpl (capacity : Nat) : Int16Array :=
  mkWithCapacityImpl #[] capacity

/-- An empty array with room for `capacity` elements before reallocating. -/
@[implemented_by emptyWithCapacityImpl, expose]
public def emptyWithCapacity (capacity : Nat) : Int16Array :=
  mk #[]

@[expose] public def empty : Int16Array := emptyWithCapacity 0

public instance : EmptyCollection Int16Array := ⟨empty⟩

public instance : Inhabited Int16Array := ⟨empty⟩

private unsafe def usetImpl (a : Int16Array) (i : USize) (v : Int16) (_ : i.toNat < a.size) :
    Int16Array :=
  let a : Int16Array := unsafeCast <| ScalarArray.ensureExclusive (unsafeCast a)
  setInt16Unsafe a i v

@[implemented_by usetImpl, expose]
public def uset : (a : Int16Array) → (i : USize) → (v : Int16) → (i.toNat < a.size) → Int16Array
  | mk a, i, v, h => mk (a.uset i v h)

private unsafe def setImpl (a : Int16Array) (i : Nat) (v : Int16) (h : i < a.size) : Int16Array :=
  usetImpl a i.toUSize v (Nat.lt_of_le_of_lt (Nat.mod_le ..) h)

@[implemented_by setImpl, expose]
public def set : (a : Int16Array) → (i : Nat) → (v : Int16) → (i < a.size) → Int16Array
  | mk a, i, v, h => mk (a.set i v h)

public def get! (a : @& Int16Array) (i : @& Nat) : Int16 :=
  if h : i < a.size then a.get i h else panic! "index out of bounds"

public def getD (a : @& Int16Array) (i : @& Nat) (v₀ : Int16) : Int16 :=
  if h : i < a.size then a.get i h else v₀

public def set! (a : Int16Array) (i : Nat) (v : Int16) : Int16Array :=
  if h : i < a.size then a.set i v h else panic! "index out of bounds"

public instance : GetElem Int16Array Nat Int16 fun a i => i < a.size where
  getElem a i h := a.get i h

public instance : GetElem Int16Array USize Int16 fun a i => i.toNat < a.size where
  getElem a i h := a.uget i h

private unsafe def pushImpl (a : Int16Array) (v : Int16) : Int16Array :=
  let s : ScalarArray := unsafeCast a
  let cap := s.capacity
  if s.size < cap then
    loop s.ensureExclusive
  else if cap < cap + cap + 1 then
    loop (s.copyWithCapacity (cap + cap + 1) lcProof)
  else
    panic! "out of memory"
where
  loop (s : ScalarArray) : Int16Array :=
    let i := s.size
    setInt16Unsafe (unsafeCast (s.resizeUnsafe (i + 1) lcProof lcProof)) i v

@[implemented_by pushImpl, expose]
public def push : Int16Array → Int16 → Int16Array
  | mk a, v => mk (a.push v)

/--
Copies the `n` elements of `b` starting at index `start` to the end of `a` in place. Only valid
when `a` is exclusive, has room for `n` more elements, is not the same object as `b`, and
`start + n ≤ b.size`.
-/
@[extern c inline "#1;\n__builtin_memcpy(lean_sarray_cptr(#1) + lean_sarray_elem_size(#1) * lean_sarray_size(#1), lean_sarray_cptr(#2) + lean_sarray_elem_size(#2) * #3, lean_sarray_elem_size(#2) * #4);\nlean_sarray_set_size(#1, lean_sarray_size(#1) + #4)"]
private unsafe def appendSliceUnsafe : Int16Array → @& Int16Array → USize → USize → Int16Array
  | mk a, mk b, start, n => mk (a ++ b.extract start.toNat (start.toNat + n.toNat))

private unsafe def appendImpl (a b : Int16Array) : Int16Array :=
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
public def append : Int16Array → Int16Array → Int16Array
  | mk a, mk b => mk (a ++ b)

public instance : Append Int16Array := ⟨append⟩

/-! ## Removing elements -/

public def isEmpty (a : @& Int16Array) : Bool := a.size == 0

private unsafe def popImpl (a : Int16Array) : Int16Array :=
  if a.size == 0 then
    a
  else
    let s : ScalarArray := ScalarArray.ensureExclusive (unsafeCast a)
    unsafeCast (s.resizeUnsafe (s.size - 1) lcProof lcProof)

/-- Removes the last element of `a`, if any, in place when `a` is not shared. -/
@[implemented_by popImpl, expose]
public def pop : Int16Array → Int16Array
  | mk a => mk a.pop

public def back? (a : @& Int16Array) : Option Int16 := a[a.size - 1]?

public def back! (a : @& Int16Array) : Int16 := a[a.size - 1]!

public def back (a : @& Int16Array) (h : 0 < a.size) : Int16 := a[a.size - 1]'(Nat.sub_lt h Nat.one_pos)

private unsafe def extractImpl (a : @& Int16Array) (start stop : Nat) : Int16Array :=
  let stop := min stop a.size
  if start < stop then
    let n := (stop - start).toUSize
    let r : Int16Array := unsafeCast <| ScalarArray.allocate 2 0 n lcProof
    appendSliceUnsafe r a start.toUSize n
  else
    empty

/--
The elements of `a` from index `start` up to, but not including, `min stop a.size`, copied into a
new array.
-/
@[implemented_by extractImpl, expose]
public def extract : (a : @& Int16Array) → (start stop : Nat) → Int16Array
  | mk a, start, stop => mk (a.extract start stop)

/-! ## Building arrays -/

private unsafe def replicateImpl (n : Nat) (v : Int16) : Int16Array :=
  let sz := toUSizeChecked n
  loop sz (unsafeCast <| ScalarArray.allocate 2 sz sz lcProof) 0
where
  loop (sz : USize) (r : Int16Array) (i : USize) : Int16Array :=
    if i < sz then loop sz (setInt16Unsafe r i v) (i + 1) else r

/-- An array of `n` copies of `v`. -/
@[implemented_by replicateImpl, expose]
public def replicate (n : Nat) (v : Int16) : Int16Array :=
  mk (Array.replicate n v)

private unsafe def ofFnImpl {n : Nat} (f : Fin n → Int16) : Int16Array :=
  let sz := toUSizeChecked n
  loop (unsafeCast <| ScalarArray.allocate 2 sz sz lcProof) 0
where
  loop (r : Int16Array) (i : Nat) : Int16Array :=
    if h : i < n then loop (setInt16Unsafe r i.toUSize (f ⟨i, h⟩)) (i + 1) else r

/-- The array `#[f 0, …, f (n - 1)]`. -/
@[implemented_by ofFnImpl, expose]
public def ofFn {n : Nat} (f : Fin n → Int16) : Int16Array :=
  mk (Array.ofFn f)

/-! ## Iteration -/

@[specialize]
private unsafe def foldlMImpl {β : Type v} {m : Type v → Type w} [Monad m] (f : β → Int16 → m β)
    (init : β) (a : @& Int16Array) : m β :=
  loop 0 init
where
  loop (i : USize) (b : β) : m β :=
    if h : i.toNat < a.size then do loop (i + 1) (← f b (a.uget i h)) else pure b

/-- Folds a monadic function over the elements of `a`, from first to last. -/
@[implemented_by foldlMImpl, expose]
public def foldlM {β : Type v} {m : Type v → Type w} [Monad m] (f : β → Int16 → m β) (init : β)
    (a : @& Int16Array) : m β :=
  a.data.foldlM f init

@[specialize]
private unsafe def foldrMImpl {β : Type v} {m : Type v → Type w} [Monad m] (f : Int16 → β → m β)
    (init : β) (a : @& Int16Array) : m β :=
  loop a.usize init
where
  loop (i : USize) (b : β) : m β :=
    if h : 0 < i ∧ (i - 1).toNat < a.size then do loop (i - 1) (← f (a.uget (i - 1) h.2) b)
    else pure b

/-- Folds a monadic function over the elements of `a`, from last to first. -/
@[implemented_by foldrMImpl, expose]
public def foldrM {β : Type v} {m : Type v → Type w} [Monad m] (f : Int16 → β → m β) (init : β)
    (a : @& Int16Array) : m β :=
  a.data.foldrM f init

@[inline, expose]
public def foldl {β : Type v} (f : β → Int16 → β) (init : β) (a : @& Int16Array) : β :=
  Id.run <| a.foldlM (pure <| f · ·) init

@[inline, expose]
public def foldr {β : Type v} (f : Int16 → β → β) (init : β) (a : @& Int16Array) : β :=
  Id.run <| a.foldrM (pure <| f · ·) init

@[inline]
public def forM {m : Type v → Type w} [Monad m] (f : Int16 → m PUnit) (a : @& Int16Array) :
    m PUnit :=
  a.foldlM (fun _ x => f x) ⟨⟩

@[specialize]
private unsafe def forInImpl {β : Type v} {m : Type v → Type w} [Monad m] (a : @& Int16Array)
    (init : β) (f : Int16 → β → m (ForInStep β)) : m β :=
  loop 0 init
where
  loop (i : USize) (b : β) : m β :=
    if h : i.toNat < a.size then do
      match ← f (a.uget i h) b with
      | .done b => pure b
      | .yield b => loop (i + 1) b
    else pure b

@[implemented_by forInImpl]
public def forIn {β : Type v} {m : Type v → Type w} [Monad m] (a : @& Int16Array) (init : β)
    (f : Int16 → β → m (ForInStep β)) : m β :=
  ForIn.forIn a.data init f

public instance [Monad m] : ForIn m Int16Array Int16 where
  forIn a b f := Int16Array.forIn a b f

@[specialize]
private unsafe def anyImpl (a : @& Int16Array) (p : Int16 → Bool) : Bool :=
  loop 0
where
  loop (i : USize) : Bool :=
    if h : i.toNat < a.size then p (a.uget i h) || loop (i + 1) else false

/-- Whether some element of `a` satisfies `p`. -/
@[implemented_by anyImpl]
public def any (a : @& Int16Array) (p : Int16 → Bool) : Bool :=
  a.data.any p

@[specialize]
private unsafe def allImpl (a : @& Int16Array) (p : Int16 → Bool) : Bool :=
  loop 0
where
  loop (i : USize) : Bool :=
    if h : i.toNat < a.size then p (a.uget i h) && loop (i + 1) else true

/-- Whether every element of `a` satisfies `p`. -/
@[implemented_by allImpl]
public def all (a : @& Int16Array) (p : Int16 → Bool) : Bool :=
  a.data.all p

private unsafe def containsImpl (a : @& Int16Array) (v : Int16) : Bool :=
  anyImpl a (v == ·)

/-- Whether `v` is an element of `a`. -/
@[implemented_by containsImpl]
public def contains (a : @& Int16Array) (v : Int16) : Bool :=
  a.data.contains v

/-! ## Equality and hashing -/

private theorem data_injective : {a b : Int16Array} → a.data = b.data → a = b
  | mk _, mk _, rfl => rfl

/-- Decides equality by comparing the two arrays' memory. -/
@[extern "lean_sarray_dec_eq"]
public def decEq (a b : @& Int16Array) : Decidable (a = b) :=
  decidable_of_iff (a.data = b.data) ⟨data_injective, fun h => h ▸ rfl⟩

public instance : DecidableEq Int16Array := decEq

private unsafe def hashImpl (a : @& Int16Array) : UInt64 :=
  foldlMImpl (m := Id) (fun r x => mixHash r (Hashable.hash x)) 7 a

/-- The same hash as `a.data`. -/
@[implemented_by hashImpl]
public def hash (a : @& Int16Array) : UInt64 :=
  Hashable.hash a.data

public instance : Hashable Int16Array := ⟨hash⟩

/-! ## Conversion and printing -/

@[expose] public def toList (a : Int16Array) : List Int16 := a.data.toList

public instance : Repr Int16Array where
  reprPrec a _ := "Int16Array.mk " ++ repr a.data

public instance : ToString Int16Array where
  toString a := "Int16Array.mk " ++ toString a.data

@[simp] public theorem size_mk (a : Array Int16) : (mk a).size = a.size := rfl

@[simp] public theorem data_mk (a : Array Int16) : (mk a).data = a := rfl

@[simp] public theorem mk_data (a : Int16Array) : mk a.data = a := by cases a; rfl

public theorem size_eq_data_size (a : Int16Array) : a.size = a.data.size := by cases a; rfl

@[simp] public theorem size_data (a : Int16Array) : a.data.size = a.size :=
  (size_eq_data_size a).symm

@[simp] public theorem size_uset (a : Int16Array) (i : USize) (v : Int16) (h) :
    (a.uset i v h).size = a.size := by
  cases a; exact Array.size_set ..

@[simp] public theorem size_set (a : Int16Array) (i : Nat) (v : Int16) (h) :
    (a.set i v h).size = a.size := by
  cases a; exact Array.size_set ..

@[simp] public theorem size_push (a : Int16Array) (v : Int16) : (a.push v).size = a.size + 1 := by
  cases a; simp [push, size]

@[simp] public theorem data_append (a b : Int16Array) : (a ++ b).data = a.data ++ b.data := by
  cases a; cases b; rfl

@[simp] public theorem size_append (a b : Int16Array) : (a ++ b).size = a.size + b.size := by
  simp [-size_data, size_eq_data_size]

@[ext] public theorem ext {a b : Int16Array} (h : a.data = b.data) : a = b := data_injective h

@[simp] public theorem getElem_mk (a : Array Int16) (i : Nat) (h : i < (mk a).size) :
    (mk a)[i] = a[i] := rfl

public theorem getElem_eq_getElem_data (a : Int16Array) (i : Nat) (h : i < a.size) :
    a[i] = a.data[i]'(size_eq_data_size a ▸ h) := by
  cases a; rfl

@[simp] public theorem getElem_data (a : Int16Array) (i : Nat) (h : i < a.data.size) :
    a.data[i] = a[i]'(by simpa using h) := by
  cases a; rfl

public theorem ext_getElem {a b : Int16Array} (h₁ : a.size = b.size)
    (h₂ : ∀ (i : Nat) (hi₁ : i < a.size) (hi₂ : i < b.size), a[i] = b[i]) : a = b := by
  ext i hi₁ hi₂
  · simpa using h₁
  · simpa using h₂ i (by simpa using hi₁) (by simpa using hi₂)

@[simp] public theorem getElem_usize (a : Int16Array) (i : USize) (h : i.toNat < a.size) :
    a[i] = a[i.toNat] := by
  cases a; rfl

@[simp] public theorem data_uset (a : Int16Array) (i : USize) (v : Int16) (h) :
    (a.uset i v h).data = a.data.set i.toNat v (size_eq_data_size a ▸ h) := by
  cases a; rfl

@[simp] public theorem data_set (a : Int16Array) (i : Nat) (v : Int16) (h) :
    (a.set i v h).data = a.data.set i v (size_eq_data_size a ▸ h) := by
  cases a; rfl

@[simp] public theorem data_push (a : Int16Array) (v : Int16) : (a.push v).data = a.data.push v := by
  cases a; rfl

@[simp] public theorem data_pop (a : Int16Array) : a.pop.data = a.data.pop := by
  cases a; rfl

@[simp] public theorem data_extract (a : Int16Array) (start stop : Nat) :
    (a.extract start stop).data = a.data.extract start stop := by
  cases a; rfl

@[simp] public theorem data_replicate (n : Nat) (v : Int16) :
    (replicate n v).data = Array.replicate n v := rfl

@[simp] public theorem data_ofFn {n : Nat} (f : Fin n → Int16) : (ofFn f).data = Array.ofFn f := rfl

@[simp] public theorem data_empty : (empty : Int16Array).data = #[] := rfl

@[simp] public theorem size_pop (a : Int16Array) : a.pop.size = a.size - 1 := by
  simp [-size_data, size_eq_data_size]

@[simp] public theorem size_extract (a : Int16Array) (start stop : Nat) :
    (a.extract start stop).size = min stop a.size - start := by
  simp [-size_data, size_eq_data_size]

@[simp] public theorem size_replicate (n : Nat) (v : Int16) : (replicate n v).size = n := by
  simp [-size_data, size_eq_data_size]

@[simp] public theorem size_ofFn {n : Nat} (f : Fin n → Int16) : (ofFn f).size = n := by
  simp [-size_data, size_eq_data_size]

@[simp] public theorem size_empty : (empty : Int16Array).size = 0 := rfl

@[simp] public theorem getElem_set (a : Int16Array) (i : Nat) (v : Int16) (h) (j : Nat) (hj) :
    (a.set i v h)[j]'hj = if i = j then v else a[j]'(by simpa using hj) := by
  simp [-getElem_data, getElem_eq_getElem_data, Array.getElem_set]

@[simp] public theorem getElem_push (a : Int16Array) (v : Int16) (i : Nat) (h) :
    (a.push v)[i]'h = if h' : i < a.size then a[i] else v := by
  simp [-getElem_data, getElem_eq_getElem_data, Array.getElem_push, -size_data, size_eq_data_size]

@[simp] public theorem getElem_pop (a : Int16Array) (i : Nat) (h) :
    a.pop[i]'h = a[i]'(by simp at h; omega) := by
  simp [-getElem_data, getElem_eq_getElem_data]

@[simp] public theorem getElem_append (a b : Int16Array) (i : Nat) (h) :
    (a ++ b)[i]'h = if h' : i < a.size then a[i] else b[i - a.size]'(by simp at h; omega) := by
  simp [-getElem_data, getElem_eq_getElem_data, Array.getElem_append, -size_data, size_eq_data_size]

@[simp] public theorem getElem_extract (a : Int16Array) (start stop i : Nat) (h) :
    (a.extract start stop)[i]'h = a[start + i]'(by simp at h; omega) := by
  simp [-getElem_data, getElem_eq_getElem_data]

@[simp] public theorem getElem_replicate (n : Nat) (v : Int16) (i : Nat) (h) :
    (replicate n v)[i]'h = v := by
  simp [-getElem_data, getElem_eq_getElem_data]

@[simp] public theorem getElem_ofFn {n : Nat} (f : Fin n → Int16) (i : Nat) (h) :
    (ofFn f)[i]'h = f ⟨i, by simpa using h⟩ := by
  simp [-getElem_data, getElem_eq_getElem_data]

public theorem foldl_eq_foldl_data {β : Type v} (f : β → Int16 → β) (init : β) (a : Int16Array) :
    a.foldl f init = a.data.foldl f init := by
  rfl

public theorem foldr_eq_foldr_data {β : Type v} (f : Int16 → β → β) (init : β) (a : Int16Array) :
    a.foldr f init = a.data.foldr f init := by
  rfl

@[simp] public theorem toList_data (a : Int16Array) : a.data.toList = a.toList := rfl

end Int16Array

end ScalarArray
