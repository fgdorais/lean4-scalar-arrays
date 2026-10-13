/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import all ScalarArray.Internal

/-!
# Arrays of `UInt64`

`ScalarArray.UInt64Array` stores `UInt64` values unboxed, 8 bytes per element, in a Lean runtime
scalar array. Its logical model is `Array UInt64`: `UInt64Array.mk` and `UInt64Array.data` convert
between the two, and every operation is specified by its effect on the model.

The runtime representation is a `ScalarArray` with element size 8. Reads and in-place writes
are inline C. `uset`, `set` and `push` update the array in place when it is not shared and copy
it otherwise, like `Array` and `ByteArray`.
-/

namespace ScalarArray

/--
Arrays of `UInt64` values, stored unboxed in a scalar array with element size 8.

The logical model is an `Array UInt64`. At runtime a `UInt64Array` is a `ScalarArray`, so every
function that looks inside the constructor must be `extern` or `implemented_by`.
-/
public inductive UInt64Array : Type
  | public mk (data : Array UInt64)

namespace UInt64Array

@[extern c inline "lean_box(lean_sarray_size(#1))", expose]
public def size : (a : @& UInt64Array) → Nat
  | mk a => a.size

@[extern "lean_sarray_size", expose]
public def usize : (a : @& UInt64Array) → USize
  | mk a => a.usize

@[extern c inline "((uint64_t*)lean_sarray_cptr(#1))[#2]", expose]
public def uget : (a : @& UInt64Array) → (i : USize) → (i.toNat < a.size) → UInt64
  | mk a, i, h => a.uget i h

@[extern c inline "((uint64_t*)lean_sarray_cptr(#1))[lean_unbox(#2)]", expose]
public def get : (a : @& UInt64Array) → (i : @& Nat) → (i < a.size) → UInt64
  | mk a, i, h => a[i]

/-- Stores `v` at index `i` in place. Only valid when `a` is exclusive and `i` is in bounds. -/
@[extern c inline "#1;\n((uint64_t*)lean_sarray_cptr(#1))[#2] = #3"]
private unsafe def setUInt64Unsafe : UInt64Array → USize → UInt64 → UInt64Array
  | .mk a, i, v => .mk <| a.uset i v lcProof

private unsafe def toUSizeChecked (n : Nat) : USize :=
  if n < USize.size >>> 1 then n.toUSize else panic! "out of memory"

private unsafe def mkWithCapacityImpl (a : Array UInt64) (capacity : Nat := a.size) : UInt64Array :=
  let cap := toUSizeChecked capacity
  let sz := toUSizeChecked a.size
  let r : UInt64Array := unsafeCast <| ScalarArray.allocate 8 sz (max sz cap) lcProof
  loop r 0
where
  loop (r : UInt64Array) (i : Nat) : UInt64Array :=
    if h : i < a.size then loop (setUInt64Unsafe r i.toUSize a[i]) (i + 1) else r

private unsafe def mkImpl (a : Array UInt64) : UInt64Array :=
  mkWithCapacityImpl a a.size

attribute [implemented_by mkImpl] UInt64Array.mk

private unsafe def dataImpl (a : @& UInt64Array) : Array UInt64 :=
  loop 0 (Array.emptyWithCapacity a.size)
where
  loop (i : USize) (r : Array UInt64) : Array UInt64 :=
    if h : i.toNat < a.size then loop (i + 1) (r.push (a.uget i h)) else r

/-- The elements of `a` as an `Array UInt64`. -/
@[implemented_by dataImpl, expose]
public def data : (a : @& UInt64Array) → Array UInt64
  | mk a => a

private unsafe def emptyWithCapacityImpl (capacity : Nat) : UInt64Array :=
  mkWithCapacityImpl #[] capacity

/-- An empty array with room for `capacity` elements before reallocating. -/
@[implemented_by emptyWithCapacityImpl]
public def emptyWithCapacity (capacity : Nat) : UInt64Array :=
  mk #[]

public def empty : UInt64Array := emptyWithCapacity 0

public instance : EmptyCollection UInt64Array := ⟨empty⟩

public instance : Inhabited UInt64Array := ⟨empty⟩

private unsafe def usetImpl (a : UInt64Array) (i : USize) (v : UInt64) (_ : i.toNat < a.size) :
    UInt64Array :=
  let a : UInt64Array := unsafeCast <| ScalarArray.ensureExclusive (unsafeCast a)
  setUInt64Unsafe a i v

@[implemented_by usetImpl, expose]
public def uset : (a : UInt64Array) → (i : USize) → (v : UInt64) → (i.toNat < a.size) → UInt64Array
  | mk a, i, v, h => mk (a.uset i v h)

public def set (a : UInt64Array) (i : Nat) (v : UInt64) (h : i < a.size) : UInt64Array :=
  a.uset i.toUSize v (Nat.lt_of_le_of_lt (Nat.mod_le ..) h)

public def get! (a : @& UInt64Array) (i : @& Nat) : UInt64 :=
  if h : i < a.size then a.get i h else panic! "index out of bounds"

public def getD (a : @& UInt64Array) (i : @& Nat) (v₀ : UInt64) : UInt64 :=
  if h : i < a.size then a.get i h else v₀

public def set! (a : UInt64Array) (i : Nat) (v : UInt64) : UInt64Array :=
  if h : i < a.size then a.set i v h else panic! "index out of bounds"

public instance : GetElem UInt64Array Nat UInt64 fun a i => i < a.size where
  getElem a i h := a.get i h

public instance : GetElem UInt64Array USize UInt64 fun a i => i.toNat < a.size where
  getElem a i h := a.uget i h

private unsafe def pushImpl (a : UInt64Array) (v : UInt64) : UInt64Array :=
  let s : ScalarArray := unsafeCast a
  let cap := s.capacity
  if s.size < cap then
    loop s.ensureExclusive
  else if cap < cap + cap + 1 then
    loop (s.copyWithCapacity (cap + cap + 1) lcProof)
  else
    panic! "out of memory"
where
  loop (s : ScalarArray) : UInt64Array :=
    let i := s.size
    setUInt64Unsafe (unsafeCast (s.resizeUnsafe (i + 1) lcProof lcProof)) i v

@[implemented_by pushImpl, expose]
public def push : UInt64Array → UInt64 → UInt64Array
  | mk a, v => mk (a.push v)

public def toList (a : UInt64Array) : List UInt64 := a.data.toList

public instance : Repr UInt64Array where
  reprPrec a _ := "UInt64Array.mk " ++ repr a.data

public instance : ToString UInt64Array where
  toString a := "UInt64Array.mk " ++ toString a.data

@[simp] public theorem size_mk (a : Array UInt64) : (mk a).size = a.size := rfl

@[simp] public theorem data_mk (a : Array UInt64) : (mk a).data = a := rfl

@[simp] public theorem mk_data (a : UInt64Array) : mk a.data = a := by cases a; rfl

public theorem size_eq_data_size (a : UInt64Array) : a.size = a.data.size := by cases a; rfl

@[simp] public theorem size_uset (a : UInt64Array) (i : USize) (v : UInt64) (h) :
    (a.uset i v h).size = a.size := by
  cases a; exact Array.size_set ..

@[simp] public theorem size_set (a : UInt64Array) (i : Nat) (v : UInt64) (h) :
    (a.set i v h).size = a.size := size_uset ..

@[simp] public theorem size_push (a : UInt64Array) (v : UInt64) : (a.push v).size = a.size + 1 := by
  cases a; simp [push, size]

end UInt64Array

end ScalarArray
