/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import all ScalarArray.Internal

/-!
# Arrays of `ISize`

`ScalarArray.ISizeArray` stores `ISize` values unboxed, one machine word per element, in a Lean runtime
scalar array. Its logical model is `Array ISize`: `ISizeArray.mk` and `ISizeArray.data` convert
between the two, and every operation is specified by its effect on the model.

The runtime representation is a `ScalarArray` with element size `System.Platform.numBits / 8`. Reads and in-place writes
are inline C. `uset`, `set` and `push` update the array in place when it is not shared and copy
it otherwise, like `Array` and `ByteArray`.
-/

namespace ScalarArray

/--
Arrays of `ISize` values, stored unboxed in a scalar array with element size `System.Platform.numBits / 8`.

The logical model is an `Array ISize`. At runtime a `ISizeArray` is a `ScalarArray`, so every
function that looks inside the constructor must be `extern` or `implemented_by`.
-/
public inductive ISizeArray : Type
  | public mk (data : Array ISize)

namespace ISizeArray

@[extern c inline "lean_box(lean_sarray_size(#1))", expose]
public def size : (a : @& ISizeArray) → Nat
  | mk a => a.size

@[extern "lean_sarray_size", expose]
public def usize : (a : @& ISizeArray) → USize
  | mk a => a.usize

@[extern c inline "((size_t*)lean_sarray_cptr(#1))[#2]", expose]
public def uget : (a : @& ISizeArray) → (i : USize) → (i.toNat < a.size) → ISize
  | mk a, i, h => a.uget i h

@[extern c inline "((size_t*)lean_sarray_cptr(#1))[lean_unbox(#2)]", expose]
public def get : (a : @& ISizeArray) → (i : @& Nat) → (i < a.size) → ISize
  | mk a, i, h => a[i]

/-- Stores `v` at index `i` in place. Only valid when `a` is exclusive and `i` is in bounds. -/
@[extern c inline "#1;\n((size_t*)lean_sarray_cptr(#1))[#2] = #3"]
private unsafe def setISizeUnsafe : ISizeArray → USize → ISize → ISizeArray
  | .mk a, i, v => .mk <| a.uset i v lcProof

private unsafe def toUSizeChecked (n : Nat) : USize :=
  if n < USize.size >>> 1 then n.toUSize else panic! "out of memory"

private unsafe def mkWithCapacityImpl (a : Array ISize) (capacity : Nat := a.size) : ISizeArray :=
  let cap := toUSizeChecked capacity
  let sz := toUSizeChecked a.size
  let r : ISizeArray := unsafeCast <| ScalarArray.allocate (System.Platform.numBits / 8).toUInt32 sz (max sz cap) lcProof
  loop r 0
where
  loop (r : ISizeArray) (i : Nat) : ISizeArray :=
    if h : i < a.size then loop (setISizeUnsafe r i.toUSize a[i]) (i + 1) else r

private unsafe def mkImpl (a : Array ISize) : ISizeArray :=
  mkWithCapacityImpl a a.size

attribute [implemented_by mkImpl] ISizeArray.mk

private unsafe def dataImpl (a : @& ISizeArray) : Array ISize :=
  loop 0 (Array.emptyWithCapacity a.size)
where
  loop (i : USize) (r : Array ISize) : Array ISize :=
    if h : i.toNat < a.size then loop (i + 1) (r.push (a.uget i h)) else r

/-- The elements of `a` as an `Array ISize`. -/
@[implemented_by dataImpl, expose]
public def data : (a : @& ISizeArray) → Array ISize
  | mk a => a

private unsafe def emptyWithCapacityImpl (capacity : Nat) : ISizeArray :=
  mkWithCapacityImpl #[] capacity

/-- An empty array with room for `capacity` elements before reallocating. -/
@[implemented_by emptyWithCapacityImpl]
public def emptyWithCapacity (capacity : Nat) : ISizeArray :=
  mk #[]

public def empty : ISizeArray := emptyWithCapacity 0

public instance : EmptyCollection ISizeArray := ⟨empty⟩

public instance : Inhabited ISizeArray := ⟨empty⟩

private unsafe def usetImpl (a : ISizeArray) (i : USize) (v : ISize) (_ : i.toNat < a.size) :
    ISizeArray :=
  let a : ISizeArray := unsafeCast <| ScalarArray.ensureExclusive (unsafeCast a)
  setISizeUnsafe a i v

@[implemented_by usetImpl, expose]
public def uset : (a : ISizeArray) → (i : USize) → (v : ISize) → (i.toNat < a.size) → ISizeArray
  | mk a, i, v, h => mk (a.uset i v h)

public def set (a : ISizeArray) (i : Nat) (v : ISize) (h : i < a.size) : ISizeArray :=
  a.uset i.toUSize v (Nat.lt_of_le_of_lt (Nat.mod_le ..) h)

public def get! (a : @& ISizeArray) (i : @& Nat) : ISize :=
  if h : i < a.size then a.get i h else panic! "index out of bounds"

public def getD (a : @& ISizeArray) (i : @& Nat) (v₀ : ISize) : ISize :=
  if h : i < a.size then a.get i h else v₀

public def set! (a : ISizeArray) (i : Nat) (v : ISize) : ISizeArray :=
  if h : i < a.size then a.set i v h else panic! "index out of bounds"

public instance : GetElem ISizeArray Nat ISize fun a i => i < a.size where
  getElem a i h := a.get i h

public instance : GetElem ISizeArray USize ISize fun a i => i.toNat < a.size where
  getElem a i h := a.uget i h

private unsafe def pushImpl (a : ISizeArray) (v : ISize) : ISizeArray :=
  let s : ScalarArray := unsafeCast a
  let cap := s.capacity
  if s.size < cap then
    loop s.ensureExclusive
  else if cap < cap + cap + 1 then
    loop (s.copyWithCapacity (cap + cap + 1) lcProof)
  else
    panic! "out of memory"
where
  loop (s : ScalarArray) : ISizeArray :=
    let i := s.size
    setISizeUnsafe (unsafeCast (s.resizeUnsafe (i + 1) lcProof lcProof)) i v

@[implemented_by pushImpl, expose]
public def push : ISizeArray → ISize → ISizeArray
  | mk a, v => mk (a.push v)

public def toList (a : ISizeArray) : List ISize := a.data.toList

public instance : Repr ISizeArray where
  reprPrec a _ := "ISizeArray.mk " ++ repr a.data

public instance : ToString ISizeArray where
  toString a := "ISizeArray.mk " ++ toString a.data

@[simp] public theorem size_mk (a : Array ISize) : (mk a).size = a.size := rfl

@[simp] public theorem data_mk (a : Array ISize) : (mk a).data = a := rfl

@[simp] public theorem mk_data (a : ISizeArray) : mk a.data = a := by cases a; rfl

public theorem size_eq_data_size (a : ISizeArray) : a.size = a.data.size := by cases a; rfl

@[simp] public theorem size_uset (a : ISizeArray) (i : USize) (v : ISize) (h) :
    (a.uset i v h).size = a.size := by
  cases a; exact Array.size_set ..

@[simp] public theorem size_set (a : ISizeArray) (i : Nat) (v : ISize) (h) :
    (a.set i v h).size = a.size := size_uset ..

@[simp] public theorem size_push (a : ISizeArray) (v : ISize) : (a.push v).size = a.size + 1 := by
  cases a; simp [push, size]

end ISizeArray

end ScalarArray
