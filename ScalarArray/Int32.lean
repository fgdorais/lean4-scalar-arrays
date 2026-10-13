/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import all ScalarArray.Internal

/-!
# Arrays of `Int32`

`ScalarArray.Int32Array` stores `Int32` values unboxed, 4 bytes per element, in a Lean runtime
scalar array. Its logical model is `Array Int32`: `Int32Array.mk` and `Int32Array.data` convert
between the two, and every operation is specified by its effect on the model.

The runtime representation is a `ScalarArray` with element size 4. Reads and in-place writes
are inline C. `uset`, `set` and `push` update the array in place when it is not shared and copy
it otherwise, like `Array` and `ByteArray`.
-/

namespace ScalarArray

/--
Arrays of `Int32` values, stored unboxed in a scalar array with element size 4.

The logical model is an `Array Int32`. At runtime a `Int32Array` is a `ScalarArray`, so every
function that looks inside the constructor must be `extern` or `implemented_by`.
-/
public inductive Int32Array : Type
  | public mk (data : Array Int32)

namespace Int32Array

@[extern c inline "lean_box(lean_sarray_size(#1))", expose]
public def size : (a : @& Int32Array) → Nat
  | mk a => a.size

@[extern "lean_sarray_size", expose]
public def usize : (a : @& Int32Array) → USize
  | mk a => a.usize

@[extern c inline "((uint32_t*)lean_sarray_cptr(#1))[#2]", expose]
public def uget : (a : @& Int32Array) → (i : USize) → (i.toNat < a.size) → Int32
  | mk a, i, h => a.uget i h

@[extern c inline "((uint32_t*)lean_sarray_cptr(#1))[lean_unbox(#2)]", expose]
public def get : (a : @& Int32Array) → (i : @& Nat) → (i < a.size) → Int32
  | mk a, i, h => a[i]

/-- Stores `v` at index `i` in place. Only valid when `a` is exclusive and `i` is in bounds. -/
@[extern c inline "#1;\n((uint32_t*)lean_sarray_cptr(#1))[#2] = #3"]
private unsafe def setInt32Unsafe : Int32Array → USize → Int32 → Int32Array
  | .mk a, i, v => .mk <| a.uset i v lcProof

private unsafe def toUSizeChecked (n : Nat) : USize :=
  if n < USize.size >>> 1 then n.toUSize else panic! "out of memory"

private unsafe def mkWithCapacityImpl (a : Array Int32) (capacity : Nat := a.size) : Int32Array :=
  let cap := toUSizeChecked capacity
  let sz := toUSizeChecked a.size
  let r : Int32Array := unsafeCast <| ScalarArray.allocate 4 sz (max sz cap) lcProof
  loop r 0
where
  loop (r : Int32Array) (i : Nat) : Int32Array :=
    if h : i < a.size then loop (setInt32Unsafe r i.toUSize a[i]) (i + 1) else r

private unsafe def mkImpl (a : Array Int32) : Int32Array :=
  mkWithCapacityImpl a a.size

attribute [implemented_by mkImpl] Int32Array.mk

private unsafe def dataImpl (a : @& Int32Array) : Array Int32 :=
  loop 0 (Array.emptyWithCapacity a.size)
where
  loop (i : USize) (r : Array Int32) : Array Int32 :=
    if h : i.toNat < a.size then loop (i + 1) (r.push (a.uget i h)) else r

/-- The elements of `a` as an `Array Int32`. -/
@[implemented_by dataImpl, expose]
public def data : (a : @& Int32Array) → Array Int32
  | mk a => a

private unsafe def emptyWithCapacityImpl (capacity : Nat) : Int32Array :=
  mkWithCapacityImpl #[] capacity

/-- An empty array with room for `capacity` elements before reallocating. -/
@[implemented_by emptyWithCapacityImpl]
public def emptyWithCapacity (capacity : Nat) : Int32Array :=
  mk #[]

public def empty : Int32Array := emptyWithCapacity 0

public instance : EmptyCollection Int32Array := ⟨empty⟩

public instance : Inhabited Int32Array := ⟨empty⟩

private unsafe def usetImpl (a : Int32Array) (i : USize) (v : Int32) (_ : i.toNat < a.size) :
    Int32Array :=
  let a : Int32Array := unsafeCast <| ScalarArray.ensureExclusive (unsafeCast a)
  setInt32Unsafe a i v

@[implemented_by usetImpl, expose]
public def uset : (a : Int32Array) → (i : USize) → (v : Int32) → (i.toNat < a.size) → Int32Array
  | mk a, i, v, h => mk (a.uset i v h)

public def set (a : Int32Array) (i : Nat) (v : Int32) (h : i < a.size) : Int32Array :=
  a.uset i.toUSize v (Nat.lt_of_le_of_lt (Nat.mod_le ..) h)

public def get! (a : @& Int32Array) (i : @& Nat) : Int32 :=
  if h : i < a.size then a.get i h else panic! "index out of bounds"

public def getD (a : @& Int32Array) (i : @& Nat) (v₀ : Int32) : Int32 :=
  if h : i < a.size then a.get i h else v₀

public def set! (a : Int32Array) (i : Nat) (v : Int32) : Int32Array :=
  if h : i < a.size then a.set i v h else panic! "index out of bounds"

public instance : GetElem Int32Array Nat Int32 fun a i => i < a.size where
  getElem a i h := a.get i h

public instance : GetElem Int32Array USize Int32 fun a i => i.toNat < a.size where
  getElem a i h := a.uget i h

private unsafe def pushImpl (a : Int32Array) (v : Int32) : Int32Array :=
  let s : ScalarArray := unsafeCast a
  let cap := s.capacity
  if s.size < cap then
    loop s.ensureExclusive
  else if cap < cap + cap + 1 then
    loop (s.copyWithCapacity (cap + cap + 1) lcProof)
  else
    panic! "out of memory"
where
  loop (s : ScalarArray) : Int32Array :=
    let i := s.size
    setInt32Unsafe (unsafeCast (s.resizeUnsafe (i + 1) lcProof lcProof)) i v

@[implemented_by pushImpl, expose]
public def push : Int32Array → Int32 → Int32Array
  | mk a, v => mk (a.push v)

public def toList (a : Int32Array) : List Int32 := a.data.toList

public instance : Repr Int32Array where
  reprPrec a _ := "Int32Array.mk " ++ repr a.data

public instance : ToString Int32Array where
  toString a := "Int32Array.mk " ++ toString a.data

@[simp] public theorem size_mk (a : Array Int32) : (mk a).size = a.size := rfl

@[simp] public theorem data_mk (a : Array Int32) : (mk a).data = a := rfl

@[simp] public theorem mk_data (a : Int32Array) : mk a.data = a := by cases a; rfl

public theorem size_eq_data_size (a : Int32Array) : a.size = a.data.size := by cases a; rfl

@[simp] public theorem size_uset (a : Int32Array) (i : USize) (v : Int32) (h) :
    (a.uset i v h).size = a.size := by
  cases a; exact Array.size_set ..

@[simp] public theorem size_set (a : Int32Array) (i : Nat) (v : Int32) (h) :
    (a.set i v h).size = a.size := size_uset ..

@[simp] public theorem size_push (a : Int32Array) (v : Int32) : (a.push v).size = a.size + 1 := by
  cases a; simp [push, size]

end Int32Array

end ScalarArray
