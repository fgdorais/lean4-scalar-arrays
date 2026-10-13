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

@[extern c inline "lean_box(lean_sarray_size(#1))", expose]
public def size : (a : @& Int16Array) → Nat
  | mk a => a.size

@[extern "lean_sarray_size", expose]
public def usize : (a : @& Int16Array) → USize
  | mk a => a.usize

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
@[implemented_by emptyWithCapacityImpl]
public def emptyWithCapacity (capacity : Nat) : Int16Array :=
  mk #[]

public def empty : Int16Array := emptyWithCapacity 0

public instance : EmptyCollection Int16Array := ⟨empty⟩

public instance : Inhabited Int16Array := ⟨empty⟩

private unsafe def usetImpl (a : Int16Array) (i : USize) (v : Int16) (_ : i.toNat < a.size) :
    Int16Array :=
  let a : Int16Array := unsafeCast <| ScalarArray.ensureExclusive (unsafeCast a)
  setInt16Unsafe a i v

@[implemented_by usetImpl, expose]
public def uset : (a : Int16Array) → (i : USize) → (v : Int16) → (i.toNat < a.size) → Int16Array
  | mk a, i, v, h => mk (a.uset i v h)

public def set (a : Int16Array) (i : Nat) (v : Int16) (h : i < a.size) : Int16Array :=
  a.uset i.toUSize v (Nat.lt_of_le_of_lt (Nat.mod_le ..) h)

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

public def toList (a : Int16Array) : List Int16 := a.data.toList

public instance : Repr Int16Array where
  reprPrec a _ := "Int16Array.mk " ++ repr a.data

public instance : ToString Int16Array where
  toString a := "Int16Array.mk " ++ toString a.data

@[simp] public theorem size_mk (a : Array Int16) : (mk a).size = a.size := rfl

@[simp] public theorem data_mk (a : Array Int16) : (mk a).data = a := rfl

@[simp] public theorem mk_data (a : Int16Array) : mk a.data = a := by cases a; rfl

public theorem size_eq_data_size (a : Int16Array) : a.size = a.data.size := by cases a; rfl

@[simp] public theorem size_uset (a : Int16Array) (i : USize) (v : Int16) (h) :
    (a.uset i v h).size = a.size := by
  cases a; exact Array.size_set ..

@[simp] public theorem size_set (a : Int16Array) (i : Nat) (v : Int16) (h) :
    (a.set i v h).size = a.size := size_uset ..

@[simp] public theorem size_push (a : Int16Array) (v : Int16) : (a.push v).size = a.size + 1 := by
  cases a; simp [push, size]

end Int16Array

end ScalarArray
