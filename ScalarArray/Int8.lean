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

@[extern c inline "lean_box(lean_sarray_size(#1))", expose]
public def size : (a : @& Int8Array) → Nat
  | mk a => a.size

@[extern "lean_sarray_size", expose]
public def usize : (a : @& Int8Array) → USize
  | mk a => a.usize

@[extern c inline "((uint8_t*)lean_sarray_cptr(#1))[#2]", expose]
public def uget : (a : @& Int8Array) → (i : USize) → (i.toNat < a.size) → Int8
  | mk a, i, h => a.uget i h

@[extern c inline "((uint8_t*)lean_sarray_cptr(#1))[lean_unbox(#2)]", expose]
public def get : (a : @& Int8Array) → (i : @& Nat) → (i < a.size) → Int8
  | mk a, i, h => a[i]

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
@[implemented_by emptyWithCapacityImpl]
public def emptyWithCapacity (capacity : Nat) : Int8Array :=
  mk #[]

public def empty : Int8Array := emptyWithCapacity 0

public instance : EmptyCollection Int8Array := ⟨empty⟩

public instance : Inhabited Int8Array := ⟨empty⟩

private unsafe def usetImpl (a : Int8Array) (i : USize) (v : Int8) (_ : i.toNat < a.size) :
    Int8Array :=
  let a : Int8Array := unsafeCast <| ScalarArray.ensureExclusive (unsafeCast a)
  setInt8Unsafe a i v

@[implemented_by usetImpl, expose]
public def uset : (a : Int8Array) → (i : USize) → (v : Int8) → (i.toNat < a.size) → Int8Array
  | mk a, i, v, h => mk (a.uset i v h)

public def set (a : Int8Array) (i : Nat) (v : Int8) (h : i < a.size) : Int8Array :=
  a.uset i.toUSize v (Nat.lt_of_le_of_lt (Nat.mod_le ..) h)

public def get! (a : @& Int8Array) (i : @& Nat) : Int8 :=
  if h : i < a.size then a.get i h else panic! "index out of bounds"

public def getD (a : @& Int8Array) (i : @& Nat) (v₀ : Int8) : Int8 :=
  if h : i < a.size then a.get i h else v₀

public def set! (a : Int8Array) (i : Nat) (v : Int8) : Int8Array :=
  if h : i < a.size then a.set i v h else panic! "index out of bounds"

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
Copies the elements of `b` to the end of `a` in place. Only valid when `a` is exclusive, has room
for the elements of `b`, and is not the same object as `b`.
-/
@[extern c inline "#1;\n__builtin_memcpy(lean_sarray_cptr(#1) + lean_sarray_elem_size(#1) * lean_sarray_size(#1), lean_sarray_cptr(#2), lean_sarray_elem_size(#2) * lean_sarray_size(#2));\nlean_sarray_set_size(#1, lean_sarray_size(#1) + lean_sarray_size(#2))"]
private unsafe def appendUnsafe : Int8Array → @& Int8Array → Int8Array
  | mk a, mk b => mk (a ++ b)

private unsafe def appendImpl (a b : Int8Array) : Int8Array :=
  let s : ScalarArray := unsafeCast a
  let n := s.size + (unsafeCast b : ScalarArray).size
  let cap := s.capacity
  if n < s.size then
    panic! "out of memory"
  else if n ≤ cap then
    appendUnsafe (unsafeCast s.ensureExclusive) b
  else
    let cap := if cap < cap + cap && n ≤ cap + cap then cap + cap else n
    appendUnsafe (unsafeCast (s.copyWithCapacity cap lcProof)) b

/-- Appends the elements of `b` to `a`, in place when `a` is not shared and has room. -/
@[implemented_by appendImpl, expose]
public def append : Int8Array → Int8Array → Int8Array
  | mk a, mk b => mk (a ++ b)

public instance : Append Int8Array := ⟨append⟩

public def toList (a : Int8Array) : List Int8 := a.data.toList

public instance : Repr Int8Array where
  reprPrec a _ := "Int8Array.mk " ++ repr a.data

public instance : ToString Int8Array where
  toString a := "Int8Array.mk " ++ toString a.data

@[simp] public theorem size_mk (a : Array Int8) : (mk a).size = a.size := rfl

@[simp] public theorem data_mk (a : Array Int8) : (mk a).data = a := rfl

@[simp] public theorem mk_data (a : Int8Array) : mk a.data = a := by cases a; rfl

public theorem size_eq_data_size (a : Int8Array) : a.size = a.data.size := by cases a; rfl

@[simp] public theorem size_uset (a : Int8Array) (i : USize) (v : Int8) (h) :
    (a.uset i v h).size = a.size := by
  cases a; exact Array.size_set ..

@[simp] public theorem size_set (a : Int8Array) (i : Nat) (v : Int8) (h) :
    (a.set i v h).size = a.size := size_uset ..

@[simp] public theorem size_push (a : Int8Array) (v : Int8) : (a.push v).size = a.size + 1 := by
  cases a; simp [push, size]

@[simp] public theorem data_append (a b : Int8Array) : (a ++ b).data = a.data ++ b.data := by
  cases a; cases b; rfl

@[simp] public theorem size_append (a b : Int8Array) : (a ++ b).size = a.size + b.size := by
  simp [size_eq_data_size]

end Int8Array

end ScalarArray
