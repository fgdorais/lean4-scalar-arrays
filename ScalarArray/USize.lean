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
@[implemented_by emptyWithCapacityImpl]
public def emptyWithCapacity (capacity : Nat) : USizeArray :=
  mk #[]

public def empty : USizeArray := emptyWithCapacity 0

public instance : EmptyCollection USizeArray := ⟨empty⟩

public instance : Inhabited USizeArray := ⟨empty⟩

private unsafe def usetImpl (a : USizeArray) (i : USize) (v : USize) (_ : i.toNat < a.size) :
    USizeArray :=
  let a : USizeArray := unsafeCast <| ScalarArray.ensureExclusive (unsafeCast a)
  setUSizeUnsafe a i v

@[implemented_by usetImpl, expose]
public def uset : (a : USizeArray) → (i : USize) → (v : USize) → (i.toNat < a.size) → USizeArray
  | mk a, i, v, h => mk (a.uset i v h)

public def set (a : USizeArray) (i : Nat) (v : USize) (h : i < a.size) : USizeArray :=
  a.uset i.toUSize v (Nat.lt_of_le_of_lt (Nat.mod_le ..) h)

public def get! (a : @& USizeArray) (i : @& Nat) : USize :=
  if h : i < a.size then a.get i h else panic! "index out of bounds"

public def getD (a : @& USizeArray) (i : @& Nat) (v₀ : USize) : USize :=
  if h : i < a.size then a.get i h else v₀

public def set! (a : USizeArray) (i : Nat) (v : USize) : USizeArray :=
  if h : i < a.size then a.set i v h else panic! "index out of bounds"

public def setD (a : USizeArray) (i : Nat) (v : USize) : USizeArray :=
  if h : i < a.size then a.set i v h else a

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

public def toList (a : USizeArray) : List USize := a.data.toList

public instance : Repr USizeArray where
  reprPrec a _ := "USizeArray.mk " ++ repr a.data

public instance : ToString USizeArray where
  toString a := "USizeArray.mk " ++ toString a.data

@[simp] public theorem size_mk (a : Array USize) : (mk a).size = a.size := rfl

@[simp] public theorem data_mk (a : Array USize) : (mk a).data = a := rfl

@[simp] public theorem mk_data (a : USizeArray) : mk a.data = a := by cases a; rfl

public theorem size_eq_data_size (a : USizeArray) : a.size = a.data.size := by cases a; rfl

@[simp] public theorem size_uset (a : USizeArray) (i : USize) (v : USize) (h) :
    (a.uset i v h).size = a.size := by
  cases a; exact Array.size_set ..

@[simp] public theorem size_set (a : USizeArray) (i : Nat) (v : USize) (h) :
    (a.set i v h).size = a.size := size_uset ..

@[simp] public theorem size_push (a : USizeArray) (v : USize) : (a.push v).size = a.size + 1 := by
  cases a; simp [push, size]

end USizeArray

end ScalarArray
