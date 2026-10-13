/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import all ScalarArray.Internal

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
public def uget : (a : @& Float32Array) → (i : USize) → (i.toNat < a.size) → Float32
  | mk a, i, h => a.uget i h

@[inline]
private unsafe def getImpl (a : @& Float32Array) (i : @& Nat) (_ : i < a.size) : Float32 :=
  a.uget i.toUSize lcProof

@[implemented_by getImpl, expose]
public def get : (a : @& Float32Array) → (i : @& Nat) → (i < a.size) → Float32
  | mk a, i, h => a[i]

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
  loop r 0
where
  loop (r : Float32Array) (i : Nat) : Float32Array :=
    if h : i < a.size then loop (setFloat32Unsafe r i.toUSize a[i]) (i + 1) else r

private unsafe def mkImpl (a : Array Float32) : Float32Array :=
  mkWithCapacityImpl a a.size

attribute [implemented_by mkImpl] Float32Array.mk

private unsafe def dataImpl (a : @& Float32Array) : Array Float32 :=
  loop 0 (Array.emptyWithCapacity a.size)
where
  loop (i : USize) (r : Array Float32) : Array Float32 :=
    if h : i.toNat < a.size then loop (i + 1) (r.push (a.uget i h)) else r

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

private unsafe def usetImpl (a : Float32Array) (i : USize) (v : Float32) (_ : i.toNat < a.size) :
    Float32Array :=
  let a : Float32Array := unsafeCast <| ScalarArray.ensureExclusive (unsafeCast a)
  setFloat32Unsafe a i v

@[implemented_by usetImpl, expose]
public def uset : (a : Float32Array) → (i : USize) → (v : Float32) → (i.toNat < a.size) → Float32Array
  | mk a, i, v, h => mk (a.uset i v h)

private unsafe def setImpl (a : Float32Array) (i : Nat) (v : Float32) (h : i < a.size) : Float32Array :=
  usetImpl a i.toUSize v (Nat.lt_of_le_of_lt (Nat.mod_le ..) h)

@[implemented_by setImpl, expose]
public def set : (a : Float32Array) → (i : Nat) → (v : Float32) → (i < a.size) → Float32Array
  | mk a, i, v, h => mk (a.set i v h)

public def get! (a : @& Float32Array) (i : @& Nat) : Float32 :=
  if h : i < a.size then a.get i h else panic! "index out of bounds"

public def getD (a : @& Float32Array) (i : @& Nat) (v₀ : Float32) : Float32 :=
  if h : i < a.size then a.get i h else v₀

public def set! (a : Float32Array) (i : Nat) (v : Float32) : Float32Array :=
  if h : i < a.size then a.set i v h else panic! "index out of bounds"

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
Copies the `n` elements of `b` starting at index `start` to the end of `a` in place. Only valid
when `a` is exclusive, has room for `n` more elements, is not the same object as `b`, and
`start + n ≤ b.size`.
-/
@[extern c inline "#1;\n__builtin_memcpy(lean_sarray_cptr(#1) + lean_sarray_elem_size(#1) * lean_sarray_size(#1), lean_sarray_cptr(#2) + lean_sarray_elem_size(#2) * #3, lean_sarray_elem_size(#2) * #4);\nlean_sarray_set_size(#1, lean_sarray_size(#1) + #4)"]
private unsafe def appendSliceUnsafe : Float32Array → @& Float32Array → USize → USize → Float32Array
  | mk a, mk b, start, n => mk (a ++ b.extract start.toNat (start.toNat + n.toNat))

private unsafe def appendImpl (a b : Float32Array) : Float32Array :=
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
public def append : Float32Array → Float32Array → Float32Array
  | mk a, mk b => mk (a ++ b)

public instance : Append Float32Array := ⟨append⟩

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

private unsafe def extractImpl (a : @& Float32Array) (start stop : Nat) : Float32Array :=
  let stop := min stop a.size
  if start < stop then
    let n := (stop - start).toUSize
    let r : Float32Array := unsafeCast <| ScalarArray.allocate 4 0 n lcProof
    appendSliceUnsafe r a start.toUSize n
  else
    empty

/--
The elements of `a` from index `start` up to, but not including, `min stop a.size`, copied into a
new array.
-/
@[implemented_by extractImpl, expose]
public def extract : (a : @& Float32Array) → (start stop : Nat) → Float32Array
  | mk a, start, stop => mk (a.extract start stop)

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

/-! ## Iteration -/

@[specialize]
private unsafe def foldlMImpl {β : Type v} {m : Type v → Type w} [Monad m] (f : β → Float32 → m β)
    (init : β) (a : @& Float32Array) : m β :=
  loop 0 init
where
  loop (i : USize) (b : β) : m β :=
    if h : i.toNat < a.size then do loop (i + 1) (← f b (a.uget i h)) else pure b

/-- Folds a monadic function over the elements of `a`, from first to last. -/
@[implemented_by foldlMImpl, expose]
public def foldlM {β : Type v} {m : Type v → Type w} [Monad m] (f : β → Float32 → m β) (init : β)
    (a : @& Float32Array) : m β :=
  a.data.foldlM f init

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
public def foldl {β : Type v} (f : β → Float32 → β) (init : β) (a : @& Float32Array) : β :=
  Id.run <| a.foldlM (pure <| f · ·) init

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

end Float32Array

end ScalarArray
