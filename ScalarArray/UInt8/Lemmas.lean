/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ScalarArray.UInt8.Slice
import all ScalarArray.Internal
import all ScalarArray.UInt8.Basic
import all ScalarArray.UInt8.Array
import all ScalarArray.UInt8.Slice
import Init.Data.Iterators.Lemmas.Basic
import Init.Data.Slice.InternalLemmas

/-!
# Lemmas about `UInt8Array`

Lemmas about arrays and slices, stated in terms of the model `Array UInt8` and
`List UInt8`.
-/

namespace ScalarArray

namespace UInt8Array

/-! ## Arrays -/

@[simp] public theorem size_mk (a : Array UInt8) : (mk a).size = a.size := rfl

public theorem size_eq_toArray_size (a : UInt8Array) : a.size = a.toArray.size := by cases a; rfl

@[simp] public theorem size_toArray (a : UInt8Array) : a.toArray.size = a.size :=
  (size_eq_toArray_size a).symm

@[simp, grind =] public theorem size_uset (a : UInt8Array) (i : USize) (v : UInt8) (h) :
    (a.uset i v h).size = a.size :=
  Array.size_set (h := h)

@[simp, grind =] public theorem size_set (a : UInt8Array) (i : Nat) (v : UInt8) (h) :
    (a.set i v h).size = a.size :=
  Array.size_set (h := h)

@[simp, grind =] public theorem size_push (a : UInt8Array) (v : UInt8) :
    (a.push v).size = a.size + 1 := by
  cases a; simp [push, size]

@[simp] public theorem toArray_append (a b : UInt8Array) :
    (a ++ b).toArray = a.toArray ++ b.toArray := by
  cases a; cases b; rfl

@[simp, grind =] public theorem size_append (a b : UInt8Array) : (a ++ b).size = a.size + b.size := by
  simp [-size_toArray, size_eq_toArray_size]

@[ext] public theorem ext {a b : UInt8Array} (h : a.toArray = b.toArray) : a = b :=
  toArray_injective h

@[simp] public theorem toArray_inj {a b : UInt8Array} : a.toArray = b.toArray ↔ a = b :=
  ⟨toArray_injective, fun h => h ▸ rfl⟩

@[simp] public theorem getElem_mk (a : Array UInt8) (i : Nat) (h : i < (mk a).size) :
    (mk a)[i] = a[i] := rfl

public theorem getElem_eq_getElem_toArray (a : UInt8Array) (i : Nat) (h : i < a.size) :
    a[i] = a.toArray[i]'(size_eq_toArray_size a ▸ h) := by
  cases a; rfl

@[simp] public theorem getElem_toArray (a : UInt8Array) (i : Nat) (h : i < a.toArray.size) :
    a.toArray[i] = a[i]'(by simpa using h) := by
  cases a; rfl

public theorem ext_getElem {a b : UInt8Array} (h₁ : a.size = b.size)
    (h₂ : ∀ (i : Nat) (hi₁ : i < a.size) (hi₂ : i < b.size), a[i] = b[i]) : a = b := by
  ext i hi₁ hi₂
  · simpa using h₁
  · simpa using h₂ i (by simpa using hi₁) (by simpa using hi₂)

@[simp] public theorem getElem_usize (a : UInt8Array) (i : USize) (h : i.toNat < a.size) :
    a[i] = a[i.toNat] := by
  cases a; rfl

@[simp] public theorem toArray_uset (a : UInt8Array) (i : USize) (v : UInt8) (h) :
    (a.uset i v h).toArray = a.toArray.set i.toNat v (size_eq_toArray_size a ▸ h) := by
  cases a; rfl

@[simp] public theorem toArray_set (a : UInt8Array) (i : Nat) (v : UInt8) (h) :
    (a.set i v h).toArray = a.toArray.set i v (size_eq_toArray_size a ▸ h) := by
  cases a; rfl

@[simp] public theorem toArray_push (a : UInt8Array) (v : UInt8) :
    (a.push v).toArray = a.toArray.push v := by
  cases a; rfl

@[simp] public theorem toArray_pop (a : UInt8Array) : a.pop.toArray = a.toArray.pop := by
  cases a; rfl

@[simp] public theorem toArray_extract (a : UInt8Array) (start stop : Nat) :
    (a.extract start stop).toArray = a.toArray.extract start stop := by
  cases a; rfl

@[simp] public theorem toArray_replicate (n : Nat) (v : UInt8) :
    (replicate n v).toArray = Array.replicate n v := rfl

@[simp] public theorem toArray_ofFn {n : Nat} (f : Fin n → UInt8) :
    (ofFn f).toArray = Array.ofFn f := rfl

@[simp] public theorem toArray_empty : (empty : UInt8Array).toArray = #[] := rfl

@[simp, grind =] public theorem size_pop (a : UInt8Array) : a.pop.size = a.size - 1 := by
  simp [-size_toArray, size_eq_toArray_size]

@[simp, grind =] public theorem size_extract (a : UInt8Array) (start stop : Nat) :
    (a.extract start stop).size = min stop a.size - start := by
  simp [-size_toArray, size_eq_toArray_size]

@[simp, grind =] public theorem size_replicate (n : Nat) (v : UInt8) : (replicate n v).size = n := by
  simp [-size_toArray, size_eq_toArray_size]

@[simp] public theorem size_ofFn {n : Nat} (f : Fin n → UInt8) : (ofFn f).size = n := by
  simp [-size_toArray, size_eq_toArray_size]

@[simp, grind =] public theorem size_empty : (empty : UInt8Array).size = 0 := rfl

@[simp, grind =] public theorem getElem_set (a : UInt8Array) (i : Nat) (v : UInt8) (h) (j : Nat) (hj) :
    (a.set i v h)[j]'hj = if i = j then v else a[j]'(by simpa using hj) := by
  simp [-getElem_toArray, getElem_eq_getElem_toArray, Array.getElem_set]

@[simp, grind =] public theorem getElem_push (a : UInt8Array) (v : UInt8) (i : Nat) (h) :
    (a.push v)[i]'h = if h' : i < a.size then a[i] else v := by
  simp [-getElem_toArray, getElem_eq_getElem_toArray, Array.getElem_push, -size_toArray,
    size_eq_toArray_size]

@[simp, grind =] public theorem getElem_pop (a : UInt8Array) (i : Nat) (h) :
    a.pop[i]'h = a[i]'(by simp at h; lia) := by
  simp [-getElem_toArray, getElem_eq_getElem_toArray]

@[simp] public theorem toArray_popWhile (p : UInt8 → Bool) (a : UInt8Array) :
    (a.popWhile p).toArray = a.toArray.popWhile p := by
  cases a; rfl

@[simp, grind =] public theorem getElem_append (a b : UInt8Array) (i : Nat) (h) :
    (a ++ b)[i]'h = if h' : i < a.size then a[i] else b[i - a.size]'(by simp at h; lia) := by
  simp [-getElem_toArray, getElem_eq_getElem_toArray, Array.getElem_append, -size_toArray,
    size_eq_toArray_size]

@[simp, grind =] public theorem getElem_extract (a : UInt8Array) (start stop i : Nat) (h) :
    (a.extract start stop)[i]'h = a[start + i]'(by simp at h; lia) := by
  simp [-getElem_toArray, getElem_eq_getElem_toArray]

@[simp, grind =] public theorem getElem_replicate (n : Nat) (v : UInt8) (i : Nat) (h) :
    (replicate n v)[i]'h = v := by
  simp [-getElem_toArray, getElem_eq_getElem_toArray]

@[simp] public theorem getElem_ofFn {n : Nat} (f : Fin n → UInt8) (i : Nat) (h) :
    (ofFn f)[i]'h = f ⟨i, by simpa using h⟩ := by
  simp [-getElem_toArray, getElem_eq_getElem_toArray]

public theorem foldl_eq_foldl_toArray {β : Type v} (f : β → UInt8 → β) (init : β)
    (a : UInt8Array) :
    a.foldl f init = a.toArray.foldl f init := by
  rfl

public theorem foldr_eq_foldr_toArray {β : Type v} (f : UInt8 → β → β) (init : β)
    (a : UInt8Array) :
    a.foldr f init = a.toArray.foldr f init := by
  rfl

@[simp] public theorem toList_toArray (a : UInt8Array) : a.toArray.toList = a.toList := rfl

@[simp] public theorem emptyc_eq_empty : (∅ : UInt8Array) = empty := rfl

@[simp] public theorem emptyWithCapacity_eq_empty (c : Nat) : emptyWithCapacity c = empty := rfl

public theorem size_eq_zero_iff {a : UInt8Array} : a.size = 0 ↔ a = empty := by
  simp [UInt8Array.ext_iff, ← Array.size_eq_zero_iff]

@[simp] public theorem toArray_set! (a : UInt8Array) (i : Nat) (v : UInt8) :
    (a.set! i v).toArray = a.toArray.set! i v := by
  simp only [set!, Array.set!_eq_setIfInBounds, Array.setIfInBounds, size_eq_toArray_size]
  split <;> rfl

@[simp, grind =] public theorem size_set! (a : UInt8Array) (i : Nat) (v : UInt8) :
    (a.set! i v).size = a.size := by
  simp [-size_toArray, size_eq_toArray_size]

public theorem getElem!_eq_getElem!_toArray (a : UInt8Array) (i : Nat) :
    a[i]! = a.toArray[i]! := by
  by_cases h : i < a.size <;> simp [h]

@[simp] public theorem toArray_ofList (l : List UInt8) : (ofList l).toArray = l.toArray := rfl

@[simp] public theorem size_ofList (l : List UInt8) : (ofList l).size = l.length := rfl

@[simp] public theorem getElem_ofList (l : List UInt8) (i : Nat) (h) :
    (ofList l)[i]'h = l[i]'(by simpa using h) := rfl

@[simp] public theorem toList_ofList (l : List UInt8) : (ofList l).toList = l := rfl

@[simp] public theorem ofList_toList (a : UInt8Array) : ofList a.toList = a := by
  simp [UInt8Array.ext_iff, ← toList_toArray]

@[simp] public theorem ensureExclusive_eq (a : UInt8Array) : a.ensureExclusive = a := rfl

@[simp] public theorem ensureCapacity_eq (a : UInt8Array) (n : Nat) :
    a.ensureCapacity n = a := rfl

@[simp] public theorem ensureExclusiveWithCapacity_eq (a : UInt8Array) (n : Nat) :
    a.ensureExclusiveWithCapacity n = a := rfl

@[simp, grind =] public theorem markLinear_eq (a : UInt8Array) : a.markLinear = a := rfl

@[simp, grind =] public theorem propagateMark_eq (a b : UInt8Array) : a.propagateMark b = b := rfl

@[simp] public theorem append_empty (a : UInt8Array) : a ++ empty = a := by
  simp [UInt8Array.ext_iff]

@[simp] public theorem empty_append (a : UInt8Array) : empty ++ a = a := by
  simp [UInt8Array.ext_iff]

public theorem append_assoc (a b c : UInt8Array) : a ++ b ++ c = a ++ (b ++ c) := by
  simp [UInt8Array.ext_iff]

@[simp] public theorem append_eq_empty_iff {a b : UInt8Array} :
    a ++ b = empty ↔ a = empty ∧ b = empty := by
  simp only [UInt8Array.ext_iff, toArray_append, toArray_empty, Array.append_eq_empty_iff]

@[simp] public theorem append_right_inj (a : UInt8Array) {b c : UInt8Array} :
    a ++ b = a ++ c ↔ b = c := by
  simp only [UInt8Array.ext_iff, toArray_append, Array.append_right_inj]

@[simp] public theorem append_left_inj {a b : UInt8Array} (c : UInt8Array) :
    a ++ c = b ++ c ↔ a = b := by
  simp only [UInt8Array.ext_iff, toArray_append, Array.append_left_inj]

public theorem getElem_append_left {a b : UInt8Array} {i : Nat} (h : i < a.size) :
    (a ++ b)[i]'(by simp; lia) = a[i] := by
  simp [h]

public theorem getElem_append_right {a b : UInt8Array} {i : Nat} (h : a.size ≤ i)
    (h' : i < (a ++ b).size) : (a ++ b)[i] = b[i - a.size]'(by simp at h'; lia) := by
  simp [Nat.not_lt.mpr h]

@[simp] public theorem extract_same (a : UInt8Array) (i : Nat) : a.extract i i = empty := by
  simp [UInt8Array.ext_iff]; lia

@[simp] public theorem extract_zero_size (a : UInt8Array) : a.extract 0 a.size = a := by
  simp [UInt8Array.ext_iff]

@[simp] public theorem extract_eq_empty_iff {a : UInt8Array} {i j : Nat} :
    a.extract i j = empty ↔ min j a.size ≤ i := by
  simp [UInt8Array.ext_iff]

public theorem extract_extract (a : UInt8Array) (i j k l : Nat) :
    (a.extract i j).extract k l = a.extract (i + k) (min (i + l) j) := by
  simp [UInt8Array.ext_iff]

public theorem extract_append_extract (a : UInt8Array) (i j k : Nat) :
    a.extract i j ++ a.extract j k = a.extract (min i j) (max j k) := by
  simp [UInt8Array.ext_iff]

@[simp] public theorem extract_append_eq_left (a b : UInt8Array) :
    (a ++ b).extract 0 a.size = a := by
  simp [UInt8Array.ext_iff]

@[simp] public theorem extract_append_eq_right (a b : UInt8Array) :
    (a ++ b).extract a.size (a.size + b.size) = b := by
  simp [UInt8Array.ext_iff, -size_toArray, size_eq_toArray_size]

@[simp] public theorem toArray_copySlice (src : UInt8Array) (srcOff : Nat) (dest : UInt8Array)
    (destOff len : Nat) (exact : Bool) :
    (src.copySlice srcOff dest destOff len exact).toArray =
      dest.toArray.extract 0 destOff ++ src.toArray.extract srcOff (srcOff + len) ++
        dest.toArray.extract (destOff + min len (src.size - srcOff)) dest.size := by
  simp [copySlice]

public theorem copySlice_eq_append (src : UInt8Array) (srcOff : Nat) (dest : UInt8Array)
    (destOff len : Nat) (exact : Bool) :
    src.copySlice srcOff dest destOff len exact =
      dest.extract 0 destOff ++ src.extract srcOff (srcOff + len) ++
        dest.extract (destOff + min len (src.size - srcOff)) dest.size := by
  simp [UInt8Array.ext_iff]

/-! ## Lists -/

@[simp] public theorem toList_mk (a : Array UInt8) : (mk a).toList = a.toList := rfl

@[simp, grind =] public theorem length_toList (a : UInt8Array) : a.toList.length = a.size := by
  simp [← toList_toArray]

@[simp, grind =] public theorem getElem_toList (a : UInt8Array) (i : Nat) (h : i < a.toList.length) :
    a.toList[i] = a[i]'(by simpa using h) := by
  simp [← toList_toArray]

@[simp, grind =] public theorem getElem?_toList (a : UInt8Array) (i : Nat) : a.toList[i]? = a[i]? := by
  by_cases h : i < a.size <;> simp [h, ← toList_toArray]

@[simp] public theorem toList_inj {a b : UInt8Array} : a.toList = b.toList ↔ a = b :=
  ⟨fun h => by rw [← ofList_toList a, h, ofList_toList], fun h => h ▸ rfl⟩

public theorem ext_getElem? {a b : UInt8Array} (h : ∀ i : Nat, a[i]? = b[i]?) : a = b :=
  toList_inj.1 (List.ext_getElem? fun i => by simp [h])

@[simp] public theorem toList_empty : (empty : UInt8Array).toList = [] := rfl

@[simp, grind =] public theorem toList_push (a : UInt8Array) (v : UInt8) :
    (a.push v).toList = a.toList ++ [v] := by
  simp [← toList_toArray]

@[simp] public theorem toList_pop (a : UInt8Array) : a.pop.toList = a.toList.dropLast := by
  simp [← toList_toArray]

@[simp, grind =] public theorem toList_append (a b : UInt8Array) :
    (a ++ b).toList = a.toList ++ b.toList := by
  simp [← toList_toArray]

@[simp] public theorem toList_set (a : UInt8Array) (i : Nat) (v : UInt8) (h) :
    (a.set i v h).toList = a.toList.set i v := by
  simp [← toList_toArray]

@[simp] public theorem toList_set! (a : UInt8Array) (i : Nat) (v : UInt8) :
    (a.set! i v).toList = a.toList.set i v := by
  simp [← toList_toArray]

@[simp] public theorem toList_extract (a : UInt8Array) (start stop : Nat) :
    (a.extract start stop).toList = a.toList.extract start stop := by
  simp [← toList_toArray]

@[simp] public theorem toList_replicate (n : Nat) (v : UInt8) :
    (replicate n v).toList = List.replicate n v := by
  simp [← toList_toArray]

@[simp] public theorem toList_ofFn {n : Nat} (f : Fin n → UInt8) :
    (ofFn f).toList = List.ofFn f := by
  simp [← toList_toArray]

@[simp] public theorem toList_popWhile (p : UInt8 → Bool) (a : UInt8Array) :
    (a.popWhile p).toList = (a.toList.reverse.dropWhile p).reverse := by
  rw [← toList_toArray, toArray_popWhile, ← Array.toArray_toList (xs := a.toArray),
    List.popWhile_toArray]
  simp

@[simp] public theorem toList_uset (a : UInt8Array) (i : USize) (v : UInt8) (h) :
    (a.uset i v h).toList = a.toList.set i.toNat v := by
  simp [← toList_toArray]

@[simp] public theorem toList_copySlice (src : UInt8Array) (srcOff : Nat) (dest : UInt8Array)
    (destOff len : Nat) (exact : Bool) :
    (src.copySlice srcOff dest destOff len exact).toList =
      dest.toList.extract 0 destOff ++ src.toList.extract srcOff (srcOff + len) ++
        dest.toList.extract (destOff + min len (src.size - srcOff)) dest.size := by
  simp [copySlice_eq_append]

/-! ## Accessors -/

@[simp] public theorem get_eq_getElem (a : UInt8Array) (i : Nat) (h) : a.get i h = a[i] := rfl

@[simp] public theorem uget_eq_getElem (a : UInt8Array) (i : USize) (h) :
    a.uget i h = a[i.toNat] := by
  cases a; rfl

@[simp] public theorem get!_eq_getElem! (a : UInt8Array) (i : Nat) : a.get! i = a[i]! := by
  rw [get!]
  split
  · simp_all [getElem!_pos]
  · simp_all [getElem!_neg]

@[simp] public theorem getD_eq_getD_getElem? (a : UInt8Array) (i : Nat) (v₀ : UInt8) :
    a.getD i v₀ = a[i]?.getD v₀ := by
  rw [getD]
  split <;> simp_all

@[simp] public theorem isEmpty_iff {a : UInt8Array} : a.isEmpty ↔ a = empty := by
  simp [isEmpty, ← size_eq_zero_iff]

/-! ## Last element -/

public theorem back?_eq_getElem? (a : UInt8Array) : a.back? = a[a.size - 1]? := by
  simp only [back?]

public theorem back!_eq_getElem! (a : UInt8Array) : a.back! = a[a.size - 1]! := by
  simp only [back!]

public theorem back_eq_getElem (a : UInt8Array) (h : 0 < a.size) :
    a.back h = a[a.size - 1]'(Nat.sub_lt h Nat.one_pos) := by
  simp only [back]

@[simp] public theorem getLast?_toList (a : UInt8Array) : a.toList.getLast? = a.back? := by
  rw [List.getLast?_eq_getElem?, getElem?_toList, length_toList, back?_eq_getElem?]

@[simp] public theorem back?_empty : (empty : UInt8Array).back? = none := by
  rw [← getLast?_toList, toList_empty, List.getLast?_nil]

@[simp, grind =] public theorem back?_push (a : UInt8Array) (v : UInt8) :
    (a.push v).back? = some v := by
  rw [← getLast?_toList, toList_push, List.getLast?_concat]

@[simp] public theorem back!_push (a : UInt8Array) (v : UInt8) : (a.push v).back! = v := by
  simp [back!_eq_getElem!]

@[simp] public theorem back_push (a : UInt8Array) (v : UInt8) (h) : (a.push v).back h = v := by
  simp [back_eq_getElem]

/-! ## Writes -/

@[simp, grind =] public theorem getElem_uset (a : UInt8Array) (i : USize) (v : UInt8) (h) (j : Nat)
    (hj) : (a.uset i v h)[j]'hj = if i.toNat = j then v else a[j]'(by simpa using hj) := by
  simp [-getElem_toArray, getElem_eq_getElem_toArray, Array.getElem_set]

@[simp, grind =] public theorem getElem_set! (a : UInt8Array) (i : Nat) (v : UInt8) (j : Nat) (hj) :
    (a.set! i v)[j]'hj = if i = j then v else a[j]'(by simpa using hj) := by
  simp only [getElem_eq_getElem_toArray, toArray_set!, Array.set!_eq_setIfInBounds]
  rw [Array.getElem_setIfInBounds]

@[simp] public theorem getElem?_set! (a : UInt8Array) (i : Nat) (v : UInt8) (j : Nat) :
    (a.set! i v)[j]? = if i = j then if i < a.size then some v else none else a[j]? := by
  by_cases hj : j < a.size <;> by_cases hij : i = j <;> simp_all

public theorem size_popWhile_le (p : UInt8 → Bool) (a : UInt8Array) :
    (a.popWhile p).size ≤ a.size := by
  rw [← length_toList, ← length_toList, toList_popWhile, List.length_reverse]
  simpa using (List.dropWhile_sublist (l := a.toList.reverse) p).length_le

@[simp] public theorem size_copySlice (src : UInt8Array) (srcOff : Nat) (dest : UInt8Array)
    (destOff len : Nat) (exact : Bool) :
    (src.copySlice srcOff dest destOff len exact).size =
      max dest.size (min destOff dest.size + min len (src.size - srcOff)) := by
  simp [-size_toArray, size_eq_toArray_size]
  lia

public theorem getElem_copySlice (src : UInt8Array) (srcOff : Nat) (dest : UInt8Array)
    (destOff len : Nat) (exact : Bool) (i : Nat) (h) :
    (src.copySlice srcOff dest destOff len exact)[i]'h =
      if h₁ : i < min destOff dest.size then dest[i]'(by lia)
      else if h₂ : i - min destOff dest.size < min len (src.size - srcOff) then
        src[srcOff + (i - min destOff dest.size)]'(by lia)
      else dest[i]'(by simp at h; lia) := by
  have hs := size_copySlice src srcOff dest destOff len exact
  simp only [copySlice_eq_append, getElem_append, getElem_extract, size_append, size_extract,
    Nat.sub_zero, Nat.zero_add]
  by_cases h₁ : i < min destOff dest.size
  · have : i < min destOff dest.size + (min (srcOff + len) src.size - srcOff) := by lia
    simp [h₁, this]
  · by_cases h₂ : i - min destOff dest.size < min len (src.size - srcOff)
    · have : i < min destOff dest.size + (min (srcOff + len) src.size - srcOff) := by lia
      simp [h₁, h₂, this]
    · have : ¬i < min destOff dest.size + (min (srcOff + len) src.size - srcOff) := by lia
      simp only [h₁, h₂, this, ↓reduceDIte]
      congr 1
      lia

/-! ## Machine-word indices -/

/--
`usize` is the size when the size fits in a `USize`, which holds for every array in memory. Loops
over `USize` indices take this as a hypothesis, since the model `Array` has no bound on its size.
-/
public theorem toNat_usize_of_lt (a : UInt8Array) (h : a.size < USize.size) :
    a.usize.toNat = a.size := by
  simp [Nat.mod_eq_of_lt h]

/-- The guard `i < a.usize` of a loop over `USize` indices bounds the index. -/
public theorem lt_usize_iff (a : UInt8Array) (h : a.size < USize.size) {i : USize} :
    i < a.usize ↔ i.toNat < a.size := by
  rw [USize.lt_iff_toNat_lt, toNat_usize_of_lt a h]

/-! ## Folds and queries -/

@[simp, grind =] public theorem any_toList (a : UInt8Array) (p : UInt8 → Bool) :
    a.toList.any p = a.any p := by
  simp [any, ← toList_toArray]

@[simp] public theorem all_toList (a : UInt8Array) (p : UInt8 → Bool) :
    a.toList.all p = a.all p := by
  simp [all, ← toList_toArray]

@[simp] public theorem contains_toList (a : UInt8Array) (v : UInt8) :
    a.toList.contains v = a.contains v := by
  simp [contains, ← toList_toArray]

@[simp, grind =] public theorem foldl_toList {β : Type v} (f : β → UInt8 → β) (init : β)
    (a : UInt8Array) : a.toList.foldl f init = a.foldl f init := by
  simp [foldl_eq_foldl_toArray, ← toList_toArray]

@[simp] public theorem foldr_toList {β : Type v} (f : UInt8 → β → β) (init : β)
    (a : UInt8Array) : a.toList.foldr f init = a.foldr f init := by
  simp [foldr_eq_foldr_toArray, ← toList_toArray]

@[simp] public theorem forIn_toList {β : Type v} {m : Type v → Type w} [Monad m] [LawfulMonad m]
    (a : UInt8Array) (init : β) (f : UInt8 → β → m (ForInStep β)) :
    ForIn.forIn a.toList init f = ForIn.forIn a init f := by
  rw [← toList_toArray, Array.forIn_toList]
  rfl

private theorem findIdx?_loop_eq (a : UInt8Array) (p : UInt8 → Bool) (i : Nat) :
    findIdx?.loop a p i = ((a.toList.drop i).findIdx? p).map (· + i) := by
  fun_induction findIdx?.loop a p i with
  | case1 i h hp =>
    rw [List.drop_eq_getElem_cons (by simpa using h), List.findIdx?_cons]
    simp [hp]
  | case2 i h hp ih =>
    rw [ih, List.drop_eq_getElem_cons (l := a.toList) (i := i) (by simpa using h),
      List.findIdx?_cons]
    simp [hp, Option.map_map, Function.comp_def, Nat.add_assoc, Nat.add_comm 1]
  | case3 i h =>
    rw [List.drop_of_length_le (by simpa using h)]
    rfl

public theorem findIdx?_eq (a : UInt8Array) (p : UInt8 → Bool) (start : Nat) :
    a.findIdx? p start = ((a.toList.drop start).findIdx? p).map (· + start) := by
  simp [findIdx?, findIdx?_loop_eq]

@[simp] public theorem findIdx?_toList (a : UInt8Array) (p : UInt8 → Bool) :
    a.toList.findIdx? p = a.findIdx? p := by
  simp [findIdx?_eq]

private theorem findFinIdx?_loop_eq (a : UInt8Array) (p : UInt8 → Bool) (i : Nat) :
    (findFinIdx?.loop a p i).map Fin.val = findIdx?.loop a p i := by
  fun_induction findFinIdx?.loop a p i <;> rw [findIdx?.loop] <;> simp_all
  lia

@[simp] public theorem map_val_findFinIdx? (a : UInt8Array) (p : UInt8 → Bool) (start : Nat) :
    (a.findFinIdx? p start).map Fin.val = a.findIdx? p start := by
  simp [findFinIdx?, findIdx?, findFinIdx?_loop_eq]

@[simp] public theorem foldlM_toList {β : Type v} {m : Type v → Type w} [Monad m]
    (f : β → UInt8 → m β) (init : β) (a : UInt8Array) :
    a.toList.foldlM f init = a.foldlM f init := by
  rw [← toList_toArray, Array.foldlM_toList, foldlM, size_eq_toArray_size]

@[simp] public theorem foldrM_toList {β : Type v} {m : Type v → Type w} [Monad m]
    (f : UInt8 → β → m β) (init : β) (a : UInt8Array) :
    a.toList.foldrM f init = a.foldrM f init := by
  rw [← toList_toArray, Array.foldrM_toList]
  rfl

@[simp] public theorem forM_eq_forM {m : Type v → Type w} [Monad m] (f : UInt8 → m PUnit)
    (a : UInt8Array) : a.forM f = ForM.forM a f := rfl

@[simp] public theorem forM_toList {m : Type v → Type w} [Monad m] (f : UInt8 → m PUnit)
    (a : UInt8Array) : ForM.forM a.toList f = ForM.forM a f := by
  cases a with | mk a
  rcases a with ⟨l⟩
  exact (List.forM_toArray l f).symm

/-! ## Membership -/

public theorem mem_def {x : UInt8} {a : UInt8Array} : x ∈ a ↔ x ∈ a.toArray := Iff.rfl

@[simp] public theorem mem_toArray {x : UInt8} {a : UInt8Array} : x ∈ a.toArray ↔ x ∈ a :=
  Iff.rfl

@[simp] public theorem mem_mk {x : UInt8} {xs : Array UInt8} : x ∈ mk xs ↔ x ∈ xs := Iff.rfl

@[simp] public theorem mem_toList {x : UInt8} {a : UInt8Array} : x ∈ a.toList ↔ x ∈ a := by
  rw [← toList_toArray, Array.mem_toList_iff, mem_toArray]

public theorem mem_iff_getElem {x : UInt8} {a : UInt8Array} :
    x ∈ a ↔ ∃ (i : Nat) (h : i < a.size), a[i] = x := by
  rw [← mem_toArray, Array.mem_iff_getElem]
  simp

public theorem getElem_mem {a : UInt8Array} {i : Nat} (h : i < a.size) : a[i] ∈ a :=
  mem_iff_getElem.mpr ⟨i, h, rfl⟩

@[simp, grind ←] public theorem not_mem_empty (x : UInt8) : ¬x ∈ (empty : UInt8Array) := by
  simp [← mem_toArray]

@[simp, grind =] public theorem mem_push {x v : UInt8} {a : UInt8Array} :
    x ∈ a.push v ↔ x ∈ a ∨ x = v := by
  simp [← mem_toArray]

@[simp, grind =] public theorem mem_append {x : UInt8} {a b : UInt8Array} :
    x ∈ a ++ b ↔ x ∈ a ∨ x ∈ b := by
  simp [← mem_toArray]

/-! ## Collecting iterators -/

private theorem toList_foldl_push (a : UInt8Array) (l : List UInt8) :
    (l.foldl (·.push ·) a).toList = a.toList ++ l := by
  induction l generalizing a <;> simp_all

@[simp] public theorem _root_.Std.Iter.toList_toUInt8Array {α : Type} [Std.Iterator α Id UInt8]
    [Std.Iterators.Finite α Id] [Std.IteratorLoop α Id Id] [Std.LawfulIteratorLoop α Id Id]
    (it : Std.Iter (α := α) UInt8) : it.toUInt8Array.toList = it.toList := by
  rw [Std.Iter.toUInt8Array, ← Std.Iter.foldl_toList, toList_foldl_push, toList_empty,
    List.nil_append]

/-! ## Slices -/

@[simp] public theorem Slice.size_copy (s : UInt8Array.Slice) : s.copy.size = s.size := by
  have := s.stop_le_array_size
  simp only [Slice.copy, size_extract, Slice.size_eq]
  lia

@[simp] public theorem Slice.getElem_copy (s : UInt8Array.Slice) (i : Nat)
    (h : i < s.copy.size) :
    s.copy[i] = s[i]'(by simpa using h) := by
  simp [Slice.copy, Slice.getElem_eq]

/-- Copying the slice from `start` to `stop` is the same as extracting those elements. -/
@[simp] public theorem copy_toSlice (a : UInt8Array) (start stop : Nat) :
    (a.toSlice start stop).copy = a.extract start stop := by
  rw [← toList_inj]
  unfold toSlice
  split <;> split <;>
    simp [Slice.copy, Slice.array, Slice.start, Slice.stop] <;> lia

@[simp] public theorem array_toSlice (a : UInt8Array) (start stop : Nat) :
    (a.toSlice start stop).array = a := by
  unfold toSlice
  split <;> split <;> rfl

@[simp] public theorem start_toSlice (a : UInt8Array) (start stop : Nat) :
    (a.toSlice start stop).start = min start (min stop a.size) := by
  unfold toSlice
  split <;> split <;> simp only [Slice.start] <;> lia

@[simp] public theorem stop_toSlice (a : UInt8Array) (start stop : Nat) :
    (a.toSlice start stop).stop = min stop a.size := by
  unfold toSlice
  split <;> split <;> simp only [Slice.stop] <;> lia

@[simp] public theorem size_toSlice (a : UInt8Array) (start stop : Nat) :
    (a.toSlice start stop).size = min stop a.size - start := by
  rw [Slice.size_eq, start_toSlice, stop_toSlice]
  lia

@[simp] public theorem getElem_toSlice (a : UInt8Array) (start stop i : Nat) (h) :
    (a.toSlice start stop)[i]'h = a[start + i]'(by simp at h; lia) := by
  simp only [size_toSlice] at h
  simp only [Slice.getElem_eq, array_toSlice, start_toSlice]
  congr 1
  lia

@[simp] public theorem Slice.size_slice (s : UInt8Array.Slice) (start stop : Nat) :
    (s.slice start stop).size = min stop s.size - start := by
  have := s.stop_le_array_size
  rw [slice, size_toSlice, size_eq]
  lia

@[simp] public theorem Slice.getElem_slice (s : UInt8Array.Slice) (start stop i : Nat) (h) :
    (s.slice start stop)[i]'h = s[start + i]'(by simp at h; lia) := by
  have := s.stop_le_array_size
  have := s.size_eq
  have h' := h
  rw [size_slice, size_eq] at h'
  simp only [Slice.getElem_eq, slice, array_toSlice, start_toSlice]
  congr 1
  lia

@[simp] public theorem Slice.copy_slice (s : UInt8Array.Slice) (start stop : Nat) :
    (s.slice start stop).copy = s.copy.extract start stop := by
  apply ext_getElem
  · simp
  · intro i _ _
    simp

@[simp] public theorem Slice.array_popFront (s : UInt8Array.Slice) :
    s.popFront.array = s.array := by
  simp only [popFront]
  split <;> rfl

@[simp] public theorem Slice.start_popFront (s : UInt8Array.Slice) :
    s.popFront.start = min (s.start + 1) s.stop := by
  rcases s with ⟨⟨_, start, stop, h, _⟩⟩
  simp only [popFront, Slice.start, Slice.stop]
  by_cases hc : start < stop <;> simp [hc] <;> lia

@[simp] public theorem Slice.stop_popFront (s : UInt8Array.Slice) :
    s.popFront.stop = s.stop := by
  simp only [popFront]
  split <;> rfl

@[simp] public theorem Slice.size_popFront (s : UInt8Array.Slice) :
    s.popFront.size = s.size - 1 := by
  rw [size_eq, size_eq, start_popFront, stop_popFront]
  lia

@[simp] public theorem Slice.getElem_popFront (s : UInt8Array.Slice) (i : Nat) (h) :
    s.popFront[i]'h = s[i + 1]'(by simp at h; lia) := by
  have : s.start < s.stop := by rw [size_popFront, size_eq] at h; lia
  simp only [Slice.getElem_eq, array_popFront, start_popFront]
  congr 1
  lia

public theorem Slice.getD_eq (s : UInt8Array.Slice) (i : Nat) (v₀ : UInt8) :
    s.getD i v₀ = if h : i < s.size then s[i] else v₀ := by
  rw [Slice.getD]

public theorem Slice.get!_eq (s : UInt8Array.Slice) (i : Nat) :
    s.get! i = if h : i < s.size then s[i] else default := by
  rw [Slice.get!, Slice.getD]

private theorem Slice.foldrM_loop_eq {β : Type v} (f : UInt8 → β → β)
    (s : UInt8Array.Slice) (i : Nat) (h : i ≤ s.size) (b : β) :
    Slice.foldrM.loop (m := Id) (pure <| f · ·) s i h b = (s.copy.toList.take i).foldr f b := by
  induction i generalizing b with
  | zero => rfl
  | succ i ih =>
    have hi : i < s.copy.toList.length := by simp; lia
    rw [Slice.foldrM.loop, List.take_add_one, List.getElem?_eq_getElem hi]
    simp [ih]

/-- Folding over a slice is folding over the list of its elements. -/
public theorem Slice.foldr_eq_foldr_toList_copy {β : Type v} (f : UInt8 → β → β)
    (init : β) (s : UInt8Array.Slice) : s.foldr f init = s.copy.toList.foldr f init := by
  rw [Slice.foldr, Slice.foldrM, Id.run, Slice.foldrM_loop_eq,
    List.take_of_length_le (by simp)]

/-! ## Slices as copies -/

private theorem Slice.cons_take_drop (a : UInt8Array) (s t : Nat) (h : s < t)
    (h' : s < a.size) :
    a[s] :: (a.toList.drop (s + 1)).take (t - (s + 1)) = (a.toList.drop s).take (t - s) := by
  rw [List.drop_eq_getElem_cons (by simpa using h' : s < a.toList.length),
    show t - s = t - (s + 1) + 1 by lia, List.take_succ_cons, getElem_toList]

private theorem SliceIterator.toList_eq (it : Std.Iter (α := UInt8Array.SliceIterator) UInt8) :
    it.toList = it.internalState.xs.copy.toList := by
  induction it using Std.Iter.inductSteps with | step it ihy ihs
  rw [Std.Iter.toList_eq_match_step]
  have hs : it.step.val = (SliceIterator.step it.toIterM).mapIterator Std.IterM.toIter := by
    simp [Std.Iter.step, Std.IterM.step, Std.Iterator.step, Std.IterM.Step.toPure]
  rw [hs]
  have h₂ := it.internalState.xs.stop_le_array_size
  by_cases h : it.internalState.xs.start < it.internalState.xs.stop
  · simp only [SliceIterator.step, Std.Iter.toIterM, h, ↓reduceDIte,
      Std.IterStep.mapIterator_yield]
    rw [ihy (out := it.internalState.xs.array[it.internalState.xs.start])]
    · simp only [Slice.copy, Slice.array, Slice.start, Slice.stop, toList_extract,
        List.extract_eq_take_drop, Std.IterM.toIter] at h h₂ ⊢
      exact Slice.cons_take_drop _ _ _ h (by lia)
    · show _ = SliceIterator.step _
      simp only [SliceIterator.step, Std.Iter.toIterM, h, ↓reduceDIte]
      rfl
  · simp only [SliceIterator.step, Std.Iter.toIterM, h, ↓reduceDIte,
      Std.IterStep.mapIterator_done]
    simp [Slice.copy]
    lia

@[simp] public theorem Slice.size_empty : (Slice.empty : UInt8Array.Slice).size = 0 := rfl

@[simp] public theorem Slice.emptyc_eq_empty : (∅ : UInt8Array.Slice) = Slice.empty := rfl

@[simp] public theorem Slice.copy_empty : (Slice.empty : UInt8Array.Slice).copy = empty := by
  simp [Slice.copy, Slice.empty, Slice.array, Slice.start, Slice.stop]

@[simp] public theorem Slice.toList_eq_toList_copy (s : UInt8Array.Slice) :
    s.toList = s.copy.toList := by
  rw [Std.Slice.Internal.toList_eq_toList_iter, SliceIterator.toList_eq,
    Std.Slice.Internal.iter_eq_toIteratorIter, Std.ToIterator.iter_eq]
  rfl

@[simp] public theorem Slice.toUInt8Slice_iter (s : UInt8Array.Slice) :
    s.iter.toUInt8Slice = s := by
  rw [Std.Slice.iter, Std.Slice.Internal.iter_eq_toIteratorIter, Std.ToIterator.iter_eq]
  rfl

@[simp] public theorem Slice.toUInt8Array_iter (s : UInt8Array.Slice) :
    s.iter.toUInt8Array = s.copy := by
  rw [← toList_inj, Std.Iter.toList_toUInt8Array, Std.Slice.toList_iter, toList_eq_toList_copy]

@[simp] public theorem toUInt8Array_iter (a : UInt8Array) : a.iter.toUInt8Array = a := by
  rw [iter, Slice.toUInt8Array_iter, copy_toSlice, extract_zero_size]

@[simp] public theorem Slice.foldl_eq_foldl_copy {β : Type v} (f : β → UInt8 → β) (init : β)
    (s : UInt8Array.Slice) : s.foldl f init = s.copy.foldl f init := by
  rw [← Std.Slice.foldl_toList, toList_eq_toList_copy, foldl_toList]

@[simp] public theorem Slice.foldlM_eq_foldlM_copy {β : Type v} {m : Type v → Type w} [Monad m]
    [LawfulMonad m] (f : β → UInt8 → m β) (init : β) (s : UInt8Array.Slice) :
    s.foldlM f init = s.copy.foldlM f init := by
  rw [← Std.Slice.foldlM_toList, toList_eq_toList_copy, foldlM_toList]

@[simp] public theorem Slice.forIn_eq_forIn_copy {β : Type v} {m : Type v → Type w} [Monad m]
    [LawfulMonad m] (s : UInt8Array.Slice) (init : β) (f : UInt8 → β → m (ForInStep β)) :
    ForIn.forIn s init f = ForIn.forIn s.copy init f := by
  rw [← Std.Slice.forIn_toList, toList_eq_toList_copy, forIn_toList]

@[simp] public theorem Slice.forM_eq_forM_copy {m : Type v → Type w} [Monad m] [LawfulMonad m]
    (s : UInt8Array.Slice) (f : UInt8 → m PUnit) : ForM.forM s f = ForM.forM s.copy f :=
  foldlM_eq_foldlM_copy ..

@[simp] public theorem Slice.foldr_eq_foldr_copy {β : Type v} (f : UInt8 → β → β) (init : β)
    (s : UInt8Array.Slice) : s.foldr f init = s.copy.foldr f init := by
  rw [foldr_eq_foldr_toList_copy, foldr_toList]

private theorem Slice.foldrM_loop_eq_foldrM {β : Type v} {m : Type v → Type w} [Monad m]
    [LawfulMonad m] (f : UInt8 → β → m β) (s : UInt8Array.Slice) (i : Nat) (h : i ≤ s.size)
    (b : β) : Slice.foldrM.loop f s i h b = (s.copy.toList.take i).foldrM f b := by
  induction i generalizing b with
  | zero => simp [Slice.foldrM.loop]
  | succ i ih =>
    have hi : i < s.copy.toList.length := by simp; lia
    rw [Slice.foldrM.loop, List.take_add_one, List.getElem?_eq_getElem hi]
    simp [ih]

@[simp] public theorem Slice.foldrM_eq_foldrM_copy {β : Type v} {m : Type v → Type w} [Monad m]
    [LawfulMonad m] (f : UInt8 → β → m β) (init : β) (s : UInt8Array.Slice) :
    s.foldrM f init = s.copy.foldrM f init := by
  rw [Slice.foldrM, foldrM_loop_eq_foldrM, List.take_of_length_le (by simp), foldrM_toList]

@[simp] public theorem Slice.any_eq_any_copy (s : UInt8Array.Slice) (p : UInt8 → Bool) :
    s.any p = s.copy.any p := by
  rw [Slice.any, ← Std.Iter.any_toList, Std.Slice.toList_iter, toList_eq_toList_copy, any_toList]

@[simp] public theorem Slice.all_eq_all_copy (s : UInt8Array.Slice) (p : UInt8 → Bool) :
    s.all p = s.copy.all p := by
  rw [Slice.all, ← Std.Iter.all_toList, Std.Slice.toList_iter, toList_eq_toList_copy, all_toList]

@[simp] public theorem Slice.contains_eq_contains_copy (s : UInt8Array.Slice) (v : UInt8) :
    s.contains v = s.copy.contains v := by
  rw [Slice.contains, any_eq_any_copy]
  rfl

@[simp] public theorem Slice.find?_eq_find?_toList_copy (s : UInt8Array.Slice)
    (p : UInt8 → Bool) : s.find? p = s.copy.toList.find? p := by
  rw [Slice.find?, ← Std.Iter.find?_toList, Std.Slice.toList_iter, toList_eq_toList_copy]

private theorem foldl_count_eq (p : UInt8 → Bool) (l : List UInt8) (n : Nat) :
    l.foldl (fun n x => if p x then n + 1 else n) n = n + l.countP p := by
  induction l generalizing n with
  | nil => rfl
  | cons x l ih =>
    by_cases hx : p x <;> simp [ih, hx]
    lia

@[simp] public theorem Slice.count_eq_countP_toList_copy (s : UInt8Array.Slice)
    (p : UInt8 → Bool) : s.count p = s.copy.toList.countP p := by
  rw [Slice.count, ← Std.Iter.foldl_toList, Std.Slice.toList_iter, toList_eq_toList_copy,
    foldl_count_eq, Nat.zero_add]

private theorem Slice.findSomeRevM?_loop_eq (p : UInt8 → Bool) (s : UInt8Array.Slice) (i : Nat)
    (h : i ≤ s.size) :
    Slice.findSomeRevM?.loop (m := Id) s (fun x => pure (if p x then some x else none)) i h =
      (s.copy.toList.take i).reverse.find? p := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have hi : i < s.copy.toList.length := by simp; lia
    rw [Slice.findSomeRevM?.loop, List.take_add_one, List.getElem?_eq_getElem hi]
    by_cases hp : p s[i] <;> simp [ih, hp]
    rfl

@[simp] public theorem Slice.findRev?_eq_find?_reverse_toList_copy (s : UInt8Array.Slice)
    (p : UInt8 → Bool) : s.findRev? p = s.copy.toList.reverse.find? p := by
  have := Slice.findSomeRevM?_loop_eq p s s.size (Nat.le_refl _)
  rw [List.take_of_length_le (by simp)] at this
  exact this

/-! ## Membership in slices -/

@[simp] public theorem Slice.mem_iff_mem_copy {x : UInt8} {s : UInt8Array.Slice} :
    x ∈ s ↔ x ∈ s.copy := Iff.rfl

public theorem Slice.mem_iff_getElem {x : UInt8} {s : UInt8Array.Slice} :
    x ∈ s ↔ ∃ (i : Nat) (h : i < s.size), s[i] = x := by
  rw [mem_iff_mem_copy, UInt8Array.mem_iff_getElem]
  simp

public theorem Slice.getElem_mem {s : UInt8Array.Slice} {i : Nat} (h : i < s.size) : s[i] ∈ s :=
  mem_iff_getElem.mpr ⟨i, h, rfl⟩

/-! ## Slice equality -/

@[simp] public theorem Slice.beq_eq_beq_copy (s t : UInt8Array.Slice) :
    (s == t) = (s.copy == t.copy) := by
  rfl

end UInt8Array

end ScalarArray
