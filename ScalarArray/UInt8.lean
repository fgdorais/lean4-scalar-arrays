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

@[extern c inline "lean_box(lean_sarray_size(#1))", expose]
public def size : (a : @& UInt8Array) → Nat
  | mk a => a.size

@[extern "lean_sarray_size", expose]
public def usize : (a : @& UInt8Array) → USize
  | mk a => a.usize

@[extern c inline "((uint8_t*)lean_sarray_cptr(#1))[#2]", expose]
public def uget : (a : @& UInt8Array) → (i : USize) → (i.toNat < a.size) → UInt8
  | mk a, i, h => a.uget i h

@[extern c inline "((uint8_t*)lean_sarray_cptr(#1))[lean_unbox(#2)]", expose]
public def get : (a : @& UInt8Array) → (i : @& Nat) → (i < a.size) → UInt8
  | mk a, i, h => a[i]

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
@[implemented_by emptyWithCapacityImpl]
public def emptyWithCapacity (capacity : Nat) : UInt8Array :=
  mk #[]

public def empty : UInt8Array := emptyWithCapacity 0

public instance : EmptyCollection UInt8Array := ⟨empty⟩

public instance : Inhabited UInt8Array := ⟨empty⟩

private unsafe def usetImpl (a : UInt8Array) (i : USize) (v : UInt8) (_ : i.toNat < a.size) :
    UInt8Array :=
  let a : UInt8Array := unsafeCast <| ScalarArray.ensureExclusive (unsafeCast a)
  setUInt8Unsafe a i v

@[implemented_by usetImpl, expose]
public def uset : (a : UInt8Array) → (i : USize) → (v : UInt8) → (i.toNat < a.size) → UInt8Array
  | mk a, i, v, h => mk (a.uset i v h)

public def set (a : UInt8Array) (i : Nat) (v : UInt8) (h : i < a.size) : UInt8Array :=
  a.uset i.toUSize v (Nat.lt_of_le_of_lt (Nat.mod_le ..) h)

public def get! (a : @& UInt8Array) (i : @& Nat) : UInt8 :=
  if h : i < a.size then a.get i h else panic! "index out of bounds"

public def getD (a : @& UInt8Array) (i : @& Nat) (v₀ : UInt8) : UInt8 :=
  if h : i < a.size then a.get i h else v₀

public def set! (a : UInt8Array) (i : Nat) (v : UInt8) : UInt8Array :=
  if h : i < a.size then a.set i v h else panic! "index out of bounds"

public def setD (a : UInt8Array) (i : Nat) (v : UInt8) : UInt8Array :=
  if h : i < a.size then a.set i v h else a

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
Copies the elements of `b` to the end of `a` in place. Only valid when `a` is exclusive, has room
for the elements of `b`, and is not the same object as `b`.
-/
@[extern c inline "#1;\n__builtin_memcpy(lean_sarray_cptr(#1) + lean_sarray_elem_size(#1) * lean_sarray_size(#1), lean_sarray_cptr(#2), lean_sarray_elem_size(#2) * lean_sarray_size(#2));\nlean_sarray_set_size(#1, lean_sarray_size(#1) + lean_sarray_size(#2))"]
private unsafe def appendUnsafe : UInt8Array → @& UInt8Array → UInt8Array
  | mk a, mk b => mk (a ++ b)

private unsafe def appendImpl (a b : UInt8Array) : UInt8Array :=
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
public def append : UInt8Array → UInt8Array → UInt8Array
  | mk a, mk b => mk (a ++ b)

public instance : Append UInt8Array := ⟨append⟩

public def toList (a : UInt8Array) : List UInt8 := a.data.toList

public instance : Repr UInt8Array where
  reprPrec a _ := "UInt8Array.mk " ++ repr a.data

public instance : ToString UInt8Array where
  toString a := "UInt8Array.mk " ++ toString a.data

@[simp] public theorem size_mk (a : Array UInt8) : (mk a).size = a.size := rfl

@[simp] public theorem data_mk (a : Array UInt8) : (mk a).data = a := rfl

@[simp] public theorem mk_data (a : UInt8Array) : mk a.data = a := by cases a; rfl

public theorem size_eq_data_size (a : UInt8Array) : a.size = a.data.size := by cases a; rfl

@[simp] public theorem size_uset (a : UInt8Array) (i : USize) (v : UInt8) (h) :
    (a.uset i v h).size = a.size := by
  cases a; exact Array.size_set ..

@[simp] public theorem size_set (a : UInt8Array) (i : Nat) (v : UInt8) (h) :
    (a.set i v h).size = a.size := size_uset ..

@[simp] public theorem size_push (a : UInt8Array) (v : UInt8) : (a.push v).size = a.size + 1 := by
  cases a; simp [push, size]

@[simp] public theorem data_append (a b : UInt8Array) : (a ++ b).data = a.data ++ b.data := by
  cases a; cases b; rfl

@[simp] public theorem size_append (a b : UInt8Array) : (a ++ b).size = a.size + b.size := by
  simp [size_eq_data_size]

end UInt8Array

end ScalarArray
