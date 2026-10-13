/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import all ScalarArray.Internal

/-!
# Arrays of `Int64`

`ScalarArray.Int64Array` stores `Int64` values unboxed, 8 bytes per element, in a Lean runtime
scalar array. Its logical model is `Array Int64`: `Int64Array.mk` and `Int64Array.data` convert
between the two, and every operation is specified by its effect on the model.

The runtime representation is a `ScalarArray` with element size 8. Reads and in-place writes
are inline C. `uset`, `set` and `push` update the array in place when it is not shared and copy
it otherwise, like `Array` and `ByteArray`.
-/

namespace ScalarArray

/--
Arrays of `Int64` values, stored unboxed in a scalar array with element size 8.

The logical model is an `Array Int64`. At runtime a `Int64Array` is a `ScalarArray`, so every
function that looks inside the constructor must be `extern` or `implemented_by`.
-/
public inductive Int64Array : Type
  | public mk (data : Array Int64)

namespace Int64Array

@[extern c inline "lean_box(lean_sarray_size(#1))", expose]
public def size : (a : @& Int64Array) → Nat
  | mk a => a.size

@[extern "lean_sarray_size", expose]
public def usize : (a : @& Int64Array) → USize
  | mk a => a.usize

@[extern c inline "((uint64_t*)lean_sarray_cptr(#1))[#2]", expose]
public def uget : (a : @& Int64Array) → (i : USize) → (i.toNat < a.size) → Int64
  | mk a, i, h => a.uget i h

@[extern c inline "((uint64_t*)lean_sarray_cptr(#1))[lean_unbox(#2)]", expose]
public def get : (a : @& Int64Array) → (i : @& Nat) → (i < a.size) → Int64
  | mk a, i, h => a[i]

/-- Stores `v` at index `i` in place. Only valid when `a` is exclusive and `i` is in bounds. -/
@[extern c inline "#1;\n((uint64_t*)lean_sarray_cptr(#1))[#2] = #3"]
private unsafe def setInt64Unsafe : Int64Array → USize → Int64 → Int64Array
  | .mk a, i, v => .mk <| a.uset i v lcProof

private unsafe def toUSizeChecked (n : Nat) : USize :=
  if n < USize.size >>> 1 then n.toUSize else panic! "out of memory"

private unsafe def mkWithCapacityImpl (a : Array Int64) (capacity : Nat := a.size) : Int64Array :=
  let cap := toUSizeChecked capacity
  let sz := toUSizeChecked a.size
  let r : Int64Array := unsafeCast <| ScalarArray.allocate 8 sz (max sz cap) lcProof
  loop r 0
where
  loop (r : Int64Array) (i : Nat) : Int64Array :=
    if h : i < a.size then loop (setInt64Unsafe r i.toUSize a[i]) (i + 1) else r

private unsafe def mkImpl (a : Array Int64) : Int64Array :=
  mkWithCapacityImpl a a.size

attribute [implemented_by mkImpl] Int64Array.mk

private unsafe def dataImpl (a : @& Int64Array) : Array Int64 :=
  loop 0 (Array.emptyWithCapacity a.size)
where
  loop (i : USize) (r : Array Int64) : Array Int64 :=
    if h : i.toNat < a.size then loop (i + 1) (r.push (a.uget i h)) else r

/-- The elements of `a` as an `Array Int64`. -/
@[implemented_by dataImpl, expose]
public def data : (a : @& Int64Array) → Array Int64
  | mk a => a

private unsafe def emptyWithCapacityImpl (capacity : Nat) : Int64Array :=
  mkWithCapacityImpl #[] capacity

/-- An empty array with room for `capacity` elements before reallocating. -/
@[implemented_by emptyWithCapacityImpl]
public def emptyWithCapacity (capacity : Nat) : Int64Array :=
  mk #[]

public def empty : Int64Array := emptyWithCapacity 0

public instance : EmptyCollection Int64Array := ⟨empty⟩

public instance : Inhabited Int64Array := ⟨empty⟩

private unsafe def usetImpl (a : Int64Array) (i : USize) (v : Int64) (_ : i.toNat < a.size) :
    Int64Array :=
  let a : Int64Array := unsafeCast <| ScalarArray.ensureExclusive (unsafeCast a)
  setInt64Unsafe a i v

@[implemented_by usetImpl, expose]
public def uset : (a : Int64Array) → (i : USize) → (v : Int64) → (i.toNat < a.size) → Int64Array
  | mk a, i, v, h => mk (a.uset i v h)

public def set (a : Int64Array) (i : Nat) (v : Int64) (h : i < a.size) : Int64Array :=
  a.uset i.toUSize v (Nat.lt_of_le_of_lt (Nat.mod_le ..) h)

public def get! (a : @& Int64Array) (i : @& Nat) : Int64 :=
  if h : i < a.size then a.get i h else panic! "index out of bounds"

public def getD (a : @& Int64Array) (i : @& Nat) (v₀ : Int64) : Int64 :=
  if h : i < a.size then a.get i h else v₀

public def set! (a : Int64Array) (i : Nat) (v : Int64) : Int64Array :=
  if h : i < a.size then a.set i v h else panic! "index out of bounds"

public def setD (a : Int64Array) (i : Nat) (v : Int64) : Int64Array :=
  if h : i < a.size then a.set i v h else a

public instance : GetElem Int64Array Nat Int64 fun a i => i < a.size where
  getElem a i h := a.get i h

public instance : GetElem Int64Array USize Int64 fun a i => i.toNat < a.size where
  getElem a i h := a.uget i h

private unsafe def pushImpl (a : Int64Array) (v : Int64) : Int64Array :=
  let s : ScalarArray := unsafeCast a
  let cap := s.capacity
  if s.size < cap then
    loop s.ensureExclusive
  else if cap < cap + cap + 1 then
    loop (s.copyWithCapacity (cap + cap + 1) lcProof)
  else
    panic! "out of memory"
where
  loop (s : ScalarArray) : Int64Array :=
    let i := s.size
    setInt64Unsafe (unsafeCast (s.resizeUnsafe (i + 1) lcProof lcProof)) i v

@[implemented_by pushImpl, expose]
public def push : Int64Array → Int64 → Int64Array
  | mk a, v => mk (a.push v)

/--
Copies the elements of `b` to the end of `a` in place. Only valid when `a` is exclusive, has room
for the elements of `b`, and is not the same object as `b`.
-/
@[extern c inline "#1;\n__builtin_memcpy(lean_sarray_cptr(#1) + lean_sarray_elem_size(#1) * lean_sarray_size(#1), lean_sarray_cptr(#2), lean_sarray_elem_size(#2) * lean_sarray_size(#2));\nlean_sarray_set_size(#1, lean_sarray_size(#1) + lean_sarray_size(#2))"]
private unsafe def appendUnsafe : Int64Array → @& Int64Array → Int64Array
  | mk a, mk b => mk (a ++ b)

private unsafe def appendImpl (a b : Int64Array) : Int64Array :=
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
public def append : Int64Array → Int64Array → Int64Array
  | mk a, mk b => mk (a ++ b)

public instance : Append Int64Array := ⟨append⟩

public def toList (a : Int64Array) : List Int64 := a.data.toList

public instance : Repr Int64Array where
  reprPrec a _ := "Int64Array.mk " ++ repr a.data

public instance : ToString Int64Array where
  toString a := "Int64Array.mk " ++ toString a.data

@[simp] public theorem size_mk (a : Array Int64) : (mk a).size = a.size := rfl

@[simp] public theorem data_mk (a : Array Int64) : (mk a).data = a := rfl

@[simp] public theorem mk_data (a : Int64Array) : mk a.data = a := by cases a; rfl

public theorem size_eq_data_size (a : Int64Array) : a.size = a.data.size := by cases a; rfl

@[simp] public theorem size_uset (a : Int64Array) (i : USize) (v : Int64) (h) :
    (a.uset i v h).size = a.size := by
  cases a; exact Array.size_set ..

@[simp] public theorem size_set (a : Int64Array) (i : Nat) (v : Int64) (h) :
    (a.set i v h).size = a.size := size_uset ..

@[simp] public theorem size_push (a : Int64Array) (v : Int64) : (a.push v).size = a.size + 1 := by
  cases a; simp [push, size]

@[simp] public theorem data_append (a b : Int64Array) : (a ++ b).data = a.data ++ b.data := by
  cases a; cases b; rfl

@[simp] public theorem size_append (a b : Int64Array) : (a ++ b).size = a.size + b.size := by
  simp [size_eq_data_size]

end Int64Array

end ScalarArray
