/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import all ScalarArray.Internal

/-!
# Arrays of `Float`

`ScalarArray.Float64Array` stores `Float` values unboxed, 8 bytes per element, in a Lean runtime
scalar array. Its logical model is `Array Float`: `Float64Array.mk` and `Float64Array.data` convert
between the two, and every operation is specified by its effect on the model.

The runtime representation is a `ScalarArray` with element size 8. Reads and in-place writes
are inline C. `uset`, `set` and `push` update the array in place when it is not shared and copy
it otherwise, like `Array` and `ByteArray`.

`Float64Array` has the same runtime representation as the core `FloatArray`, with the same API
as the other arrays in this library.
-/

namespace ScalarArray

/--
Arrays of `Float` values, stored unboxed in a scalar array with element size 8.

The logical model is an `Array Float`. At runtime a `Float64Array` is a `ScalarArray`, so every
function that looks inside the constructor must be `extern` or `implemented_by`.
-/
public inductive Float64Array : Type
  | public mk (data : Array Float)

namespace Float64Array

@[extern c inline "lean_box(lean_sarray_size(#1))", expose]
public def size : (a : @& Float64Array) → Nat
  | mk a => a.size

@[extern "lean_sarray_size", expose]
public def usize : (a : @& Float64Array) → USize
  | mk a => a.usize

@[extern c inline "((double*)lean_sarray_cptr(#1))[#2]", expose]
public def uget : (a : @& Float64Array) → (i : USize) → (i.toNat < a.size) → Float
  | mk a, i, h => a.uget i h

@[extern c inline "((double*)lean_sarray_cptr(#1))[lean_unbox(#2)]", expose]
public def get : (a : @& Float64Array) → (i : @& Nat) → (i < a.size) → Float
  | mk a, i, h => a[i]

/-- Stores `v` at index `i` in place. Only valid when `a` is exclusive and `i` is in bounds. -/
@[extern c inline "#1;\n((double*)lean_sarray_cptr(#1))[#2] = #3"]
private unsafe def setFloat64Unsafe : Float64Array → USize → Float → Float64Array
  | .mk a, i, v => .mk <| a.uset i v lcProof

private unsafe def toUSizeChecked (n : Nat) : USize :=
  if n < USize.size >>> 1 then n.toUSize else panic! "out of memory"

private unsafe def mkWithCapacityImpl (a : Array Float) (capacity : Nat := a.size) : Float64Array :=
  let cap := toUSizeChecked capacity
  let sz := toUSizeChecked a.size
  let r : Float64Array := unsafeCast <| ScalarArray.allocate 8 sz (max sz cap) lcProof
  loop r 0
where
  loop (r : Float64Array) (i : Nat) : Float64Array :=
    if h : i < a.size then loop (setFloat64Unsafe r i.toUSize a[i]) (i + 1) else r

private unsafe def mkImpl (a : Array Float) : Float64Array :=
  mkWithCapacityImpl a a.size

attribute [implemented_by mkImpl] Float64Array.mk

private unsafe def dataImpl (a : @& Float64Array) : Array Float :=
  loop 0 (Array.emptyWithCapacity a.size)
where
  loop (i : USize) (r : Array Float) : Array Float :=
    if h : i.toNat < a.size then loop (i + 1) (r.push (a.uget i h)) else r

/-- The elements of `a` as an `Array Float`. -/
@[implemented_by dataImpl, expose]
public def data : (a : @& Float64Array) → Array Float
  | mk a => a

private unsafe def emptyWithCapacityImpl (capacity : Nat) : Float64Array :=
  mkWithCapacityImpl #[] capacity

/-- An empty array with room for `capacity` elements before reallocating. -/
@[implemented_by emptyWithCapacityImpl]
public def emptyWithCapacity (capacity : Nat) : Float64Array :=
  mk #[]

public def empty : Float64Array := emptyWithCapacity 0

public instance : EmptyCollection Float64Array := ⟨empty⟩

public instance : Inhabited Float64Array := ⟨empty⟩

private unsafe def usetImpl (a : Float64Array) (i : USize) (v : Float) (_ : i.toNat < a.size) :
    Float64Array :=
  let a : Float64Array := unsafeCast <| ScalarArray.ensureExclusive (unsafeCast a)
  setFloat64Unsafe a i v

@[implemented_by usetImpl, expose]
public def uset : (a : Float64Array) → (i : USize) → (v : Float) → (i.toNat < a.size) → Float64Array
  | mk a, i, v, h => mk (a.uset i v h)

public def set (a : Float64Array) (i : Nat) (v : Float) (h : i < a.size) : Float64Array :=
  a.uset i.toUSize v (Nat.lt_of_le_of_lt (Nat.mod_le ..) h)

public def get! (a : @& Float64Array) (i : @& Nat) : Float :=
  if h : i < a.size then a.get i h else panic! "index out of bounds"

public def getD (a : @& Float64Array) (i : @& Nat) (v₀ : Float) : Float :=
  if h : i < a.size then a.get i h else v₀

public def set! (a : Float64Array) (i : Nat) (v : Float) : Float64Array :=
  if h : i < a.size then a.set i v h else panic! "index out of bounds"

public instance : GetElem Float64Array Nat Float fun a i => i < a.size where
  getElem a i h := a.get i h

public instance : GetElem Float64Array USize Float fun a i => i.toNat < a.size where
  getElem a i h := a.uget i h

private unsafe def pushImpl (a : Float64Array) (v : Float) : Float64Array :=
  let s : ScalarArray := unsafeCast a
  let cap := s.capacity
  if s.size < cap then
    loop s.ensureExclusive
  else if cap < cap + cap + 1 then
    loop (s.copyWithCapacity (cap + cap + 1) lcProof)
  else
    panic! "out of memory"
where
  loop (s : ScalarArray) : Float64Array :=
    let i := s.size
    setFloat64Unsafe (unsafeCast (s.resizeUnsafe (i + 1) lcProof lcProof)) i v

@[implemented_by pushImpl, expose]
public def push : Float64Array → Float → Float64Array
  | mk a, v => mk (a.push v)

public def toList (a : Float64Array) : List Float := a.data.toList

public instance : Repr Float64Array where
  reprPrec a _ := "Float64Array.mk " ++ repr a.data

public instance : ToString Float64Array where
  toString a := "Float64Array.mk " ++ toString a.data

@[simp] public theorem size_mk (a : Array Float) : (mk a).size = a.size := rfl

@[simp] public theorem data_mk (a : Array Float) : (mk a).data = a := rfl

@[simp] public theorem mk_data (a : Float64Array) : mk a.data = a := by cases a; rfl

public theorem size_eq_data_size (a : Float64Array) : a.size = a.data.size := by cases a; rfl

@[simp] public theorem size_uset (a : Float64Array) (i : USize) (v : Float) (h) :
    (a.uset i v h).size = a.size := by
  cases a; exact Array.size_set ..

@[simp] public theorem size_set (a : Float64Array) (i : Nat) (v : Float) (h) :
    (a.set i v h).size = a.size := size_uset ..

@[simp] public theorem size_push (a : Float64Array) (v : Float) : (a.push v).size = a.size + 1 := by
  cases a; simp [push, size]

end Float64Array

end ScalarArray
