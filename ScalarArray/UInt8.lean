/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import all ScalarArray.Internal
public import Std.Data.Iterators
import Init.Data.Iterators.Lemmas.Basic
import Init.Data.Slice.InternalLemmas

/-!
# Arrays of `UInt8`

`ScalarArray.UInt8Array` stores `UInt8` values unboxed in a Lean runtime scalar array,
1 byte per element. Its logical model is `Array UInt8`: `UInt8Array.mk` and
`UInt8Array.data` convert between the two, and every operation is specified by its effect on
the model.

Reads and in-place writes are inline C. `uset`, `set` and `push` update the array in place when it
is not shared and copy it otherwise, like `Array` and `ByteArray`.
-/

namespace ScalarArray

/--
Arrays of `UInt8` values, stored unboxed in a scalar array, 1 byte per element.

The logical model is an `Array UInt8`. At runtime a `UInt8Array` is a `ScalarArray`, so every
function that looks inside the constructor must be `extern` or `implemented_by`.
-/
public inductive UInt8Array : Type
  | public mk (data : Array UInt8)

namespace UInt8Array

-- `lean_byte_array_size` reads the size of any scalar array, whatever its element size.
@[extern "lean_byte_array_size", tagged_return, expose]
public def size : (a : @& UInt8Array) → Nat
  | mk a => a.size

/--
The size of `a` as a `USize`. Since `USize` can address all memory, no array has more elements than
`USize` can count.
-/
@[extern "lean_sarray_size", simp, expose]
public def usize (a : @& UInt8Array) : USize :=
  a.size.toUSize

@[extern c inline "((uint8_t*)lean_sarray_cptr(#1))[#2]", expose]
public def uget :
    (a : @& UInt8Array) → (i : USize) → (h : i.toNat < a.size := by get_elem_tactic) → UInt8
  | mk a, i, h => a.uget i h

@[expose]
public def get :
    (a : @& UInt8Array) → (i : @& Nat) → (h : i < a.size := by get_elem_tactic) → UInt8
  | mk a, i, h => a[i]

-- Public, like `mkImpl`, `usetImpl`, `setImpl` and `pushImpl` below: a private `implemented_by`
-- target attached with a separate `attribute` command is not visible to other modules, so code
-- there that uses `get`, `mk`, `uset` or `set` would fail to compile.
@[inline]
public unsafe def getImpl : type_of% @get :=
  fun a i _ => a.uget i.toUSize lcProof

attribute [implemented_by getImpl] get

/--
Stores `v` at index `i` in place. Only valid when `a` is exclusive and `i` is in bounds. Public only
so that `uset` can be inlined into code in other modules.
-/
@[never_extract, extern c inline "#1;\n((uint8_t*)lean_sarray_cptr(#1))[#2] = #3"]
public unsafe def setUnsafe : UInt8Array → USize → UInt8 → UInt8Array
  | .mk a, i, v => .mk <| a.uset i v lcProof

/--
`a` itself when it is not shared, and a copy otherwise. Public only so that `uset` can be inlined
into code in other modules.
-/
-- The same runtime function as the private `ScalarArray.ensureExclusive`, which code in other
-- modules can't reach. `never_extract`: once `uset` or `push` is inlined, `ensureExclusiveUnsafe c`
-- on a closed array `c` would otherwise be hoisted into a shared constant, which the following
-- in-place write would then modify.
@[never_extract, extern "lean_sarray_ensure_exclusive"]
public unsafe def ensureExclusiveUnsafe (a : UInt8Array) : UInt8Array := a

private unsafe def toUSizeChecked (n : Nat) : USize :=
  if n < USize.size >>> 1 then n.toUSize else panic! "out of memory"

/-- A new array of size `size` with room for `capacity` elements. Requires `size ≤ capacity`. -/
private unsafe def allocUnsafe (size capacity : USize) : UInt8Array :=
  unsafeCast <| ScalarArray.allocate 1 size capacity lcProof

private unsafe def mkWithCapacityImpl (a : Array UInt8) (capacity : Nat := a.size) :
    UInt8Array :=
  let cap := toUSizeChecked capacity
  let sz := toUSizeChecked a.size
  let r := allocUnsafe sz (max sz cap)
  loop sz r 0
where
  loop (sz : USize) (r : UInt8Array) (i : USize) : UInt8Array :=
    if i < sz then loop sz (setUnsafe r i (a.uget i lcProof)) (i + 1) else r

public unsafe def mkImpl (a : Array UInt8) : UInt8Array :=
  mkWithCapacityImpl a a.size

attribute [implemented_by mkImpl] UInt8Array.mk

private unsafe def dataImpl (a : @& UInt8Array) : Array UInt8 :=
  loop a.usize 0 (Array.replicate a.size default)
where
  loop (sz i : USize) (r : Array UInt8) : Array UInt8 :=
    if i < sz then loop sz (i + 1) (r.uset i (a.uget i lcProof) lcProof) else r

/-- The elements of `a` as an `Array UInt8`. -/
@[implemented_by dataImpl, expose]
public def data : (a : @& UInt8Array) → Array UInt8
  | mk a => a

private unsafe def emptyWithCapacityImpl (capacity : Nat) : UInt8Array :=
  mkWithCapacityImpl #[] capacity

/-- An empty array with room for `capacity` elements before reallocating. -/
@[implemented_by emptyWithCapacityImpl, expose]
public def emptyWithCapacity (capacity : Nat) : UInt8Array :=
  mk #[]

@[expose] public def empty : UInt8Array := emptyWithCapacity 0

public instance : EmptyCollection UInt8Array := ⟨empty⟩

public instance : Inhabited UInt8Array := ⟨empty⟩

/--
Replaces the element at index `i`, in place when `a` is not shared. It compiles to inline C: one
check that `a` is exclusive, copying it if not, and one store.
-/
@[expose]
public def uset :
    (a : UInt8Array) → (i : USize) → (v : UInt8) →
    (h : i.toNat < a.size := by get_elem_tactic) → UInt8Array
  | mk a, i, v, h => mk (a.uset i v h)

-- Inline, and made of public inline externs, so that it compiles to inline C in other modules.
@[inline]
public unsafe def usetImpl : type_of% @uset :=
  fun a i v _ => setUnsafe (ensureExclusiveUnsafe a) i v

attribute [implemented_by usetImpl] uset

@[expose]
public def set :
    (a : UInt8Array) → (i : Nat) → (v : UInt8) → (h : i < a.size := by get_elem_tactic) →
    UInt8Array
  | mk a, i, v, h => mk (a.set i v h)

@[inline]
public unsafe def setImpl : type_of% @set :=
  fun a i v _ => a.uset i.toUSize v lcProof

attribute [implemented_by setImpl] set

@[expose]
public def get! (a : @& UInt8Array) (i : @& Nat) : UInt8 :=
  if h : i < a.size then a.get i h else panic! "index out of bounds"

@[expose]
public def getD (a : @& UInt8Array) (i : @& Nat) (v₀ : UInt8) : UInt8 :=
  if h : i < a.size then a.get i h else v₀

private unsafe def setBangImpl (a : UInt8Array) (i : Nat) (v : UInt8) : UInt8Array :=
  if h : i < a.size then setImpl a i v h else a

/-- Replaces the element at index `i`. If `i` is out of bounds, the array is returned unmodified. -/
@[implemented_by setBangImpl, expose]
public def set! : UInt8Array → Nat → UInt8 → UInt8Array
  | mk a, i, v => mk (a.set! i v)

public instance : GetElem UInt8Array Nat UInt8 fun a i => i < a.size where
  getElem a i h := a.get i h

public instance : GetElem UInt8Array USize UInt8 fun a i => i.toNat < a.size where
  getElem a i h := a.uget i h

/--
The number of elements `a` has room for before it must be reallocated. Public only so that `push`
can be inlined into code in other modules.
-/
@[extern "lean_sarray_capacity"]
public unsafe def capacityUnsafe (a : @& UInt8Array) : USize := a.usize

/--
Sets the size of `a` to `_n`. Only valid when `a` is exclusive and `_n` is at most its capacity;
the elements past the old size are uninitialized until stored. Public only so that `push` can be
inlined into code in other modules.
-/
-- The same C as the private `ScalarArray.resizeUnsafe`, which code in other modules can't reach.
@[never_extract, extern c inline "#1;\nlean_sarray_set_size(#1, #2)"]
public unsafe def setSizeUnsafe (a : UInt8Array) (_n : USize) : UInt8Array := a

/--
`push` when `a` is full: copies `a` with capacity `2 * capacity + 1`, then appends `v`. Out of
line so that inlined `push` call sites stay small. Public only so that `push` can be inlined into
code in other modules.
-/
public unsafe def pushGrowUnsafe (a : UInt8Array) (v : UInt8) : UInt8Array :=
  let s : ScalarArray := unsafeCast a
  let cap := s.capacity
  if cap < cap + cap + 1 then
    let a : UInt8Array := unsafeCast (s.copyWithCapacity (cap + cap + 1) lcProof)
    let i := a.usize
    setUnsafe (setSizeUnsafe a (i + 1)) i v
  else
    panic! "out of memory"

-- Inline, and made of public inline externs, so that the common path compiles to inline C in other
-- modules: one capacity check, one exclusivity check, a size bump and one store.
@[inline]
public unsafe def pushImpl (a : UInt8Array) (v : UInt8) : UInt8Array :=
  if a.usize < capacityUnsafe a then
    let a := ensureExclusiveUnsafe a
    let i := a.usize
    setUnsafe (setSizeUnsafe a (i + 1)) i v
  else
    pushGrowUnsafe a v

@[implemented_by pushImpl, expose]
public def push : UInt8Array → UInt8 → UInt8Array
  | mk a, v => mk (a.push v)

/--
Copies `n` bytes of the data of `src`, starting at byte `srcOff`, into the data of `dest`, starting
at byte `destOff`. Only valid when `dest` is exclusive and both ranges are within the capacities.
-/
-- TODO: core has no runtime function that copies a slice of a scalar array with any element size;
-- `lean_byte_array_copy_slice` only works for bytes. Replace this once core has one.
@[extern c inline "#1;\n__builtin_memcpy(lean_sarray_cptr(#1) + #4, lean_sarray_cptr(#2) + #3, #5)"]
private unsafe def memcpyUnsafe :
    UInt8Array → @& UInt8Array → (srcOff destOff n : USize) → UInt8Array
  | dest, _, _, _, _ => dest

/--
Copies the `n` elements of `src` starting at index `srcOff` into `dest` starting at index `destOff`,
in place, and grows the size of `dest` to `destOff + n` if it is smaller. Only valid when `dest` is
exclusive, has capacity for `destOff + n` elements, and is not the same object as `src`, and when
`destOff ≤ dest.size` and `srcOff + n ≤ src.size`.
-/
@[inline]
private unsafe def copySliceUnsafe (dest : UInt8Array) (src : @& UInt8Array)
    (srcOff destOff n : USize) : UInt8Array :=
  let esz := (unsafeCast src : ScalarArray).elemSize.toUSize
  let d : ScalarArray := unsafeCast (memcpyUnsafe dest src (srcOff * esz) (destOff * esz) (n * esz))
  unsafeCast (d.resizeUnsafe (max d.size (destOff + n)) lcProof lcProof)

private unsafe def appendImpl (a b : UInt8Array) : UInt8Array :=
  let s : ScalarArray := unsafeCast a
  let m := (unsafeCast b : ScalarArray).size
  let n := s.size + m
  let cap := s.capacity
  if n < s.size then
    panic! "out of memory"
  else if n ≤ cap then
    let s := s.ensureExclusive
    copySliceUnsafe (unsafeCast s) b 0 s.size m
  else
    let cap := if cap < cap + cap && n ≤ cap + cap then cap + cap else n
    let s := s.copyWithCapacity cap lcProof
    copySliceUnsafe (unsafeCast s) b 0 s.size m

/-- Appends the elements of `b` to `a`, in place when `a` is not shared and has room. -/
@[implemented_by appendImpl, expose]
public def append : UInt8Array → UInt8Array → UInt8Array
  | mk a, mk b => mk (a ++ b)

public instance : Append UInt8Array := ⟨append⟩

private unsafe def copySliceImpl (src : @& UInt8Array) (srcOff : Nat) (dest : UInt8Array)
    (destOff len : Nat) (exact : Bool := true) : UInt8Array :=
  let srcOff := min srcOff src.size
  let n := min len (src.size - srcOff)
  let destOff := min destOff dest.size
  let newSize := max dest.size (destOff + n)
  let s : ScalarArray := unsafeCast dest
  let cap := s.capacity.toNat
  let s :=
    if newSize ≤ cap then
      s.ensureExclusive
    else
      let cap := if exact then newSize else max newSize (cap + cap)
      s.copyWithCapacity (toUSizeChecked cap) lcProof
  copySliceUnsafe (unsafeCast s) src srcOff.toUSize destOff.toUSize n.toUSize

/--
Copies the elements of `src` from index `srcOff` up to, but not including, `srcOff + len` into
`dest` starting at index `destOff`, growing `dest` if necessary. The copy works in place when `dest`
is not shared and has room. If `exact` is `false`, the capacity is doubled when `dest` grows.
-/
@[implemented_by copySliceImpl, expose]
public def copySlice (src : @& UInt8Array) (srcOff : Nat) (dest : UInt8Array)
    (destOff len : Nat) (exact : Bool := true) : UInt8Array :=
  mk (dest.data.extract 0 destOff ++ src.data.extract srcOff (srcOff + len) ++
    dest.data.extract (destOff + min len (src.data.size - srcOff)) dest.data.size)

/-! ## Removing elements -/

@[expose] public def isEmpty (a : @& UInt8Array) : Bool := a.size == 0

private unsafe def popImpl (a : UInt8Array) : UInt8Array :=
  if a.size == 0 then
    a
  else
    let s : ScalarArray := ScalarArray.ensureExclusive (unsafeCast a)
    unsafeCast (s.resizeUnsafe (s.size - 1) lcProof lcProof)

/-- Removes the last element of `a`, if any, in place when `a` is not shared. -/
@[implemented_by popImpl, expose]
public def pop : UInt8Array → UInt8Array
  | mk a => mk a.pop

public def back? (a : @& UInt8Array) : Option UInt8 := a[a.size - 1]?

public def back! (a : @& UInt8Array) : UInt8 := a[a.size - 1]!

public def back (a : @& UInt8Array) (h : 0 < a.size) : UInt8 :=
  a[a.size - 1]'(Nat.sub_lt h Nat.one_pos)

private def popWhileImpl (p : UInt8 → Bool) (a : UInt8Array) : UInt8Array :=
  if h : 0 < a.size then
    if p (a.back h) then popWhileImpl p a.pop else a
  else
    a
termination_by a.size
decreasing_by
  have : a.pop.size = a.size - 1 := by cases a; exact Array.size_pop ..
  lia

/--
Removes the longest run of elements at the end of `a` that satisfy `p`, in place when `a` is not
shared.
-/
@[implemented_by popWhileImpl, expose]
public def popWhile (p : UInt8 → Bool) : UInt8Array → UInt8Array
  | mk a => mk (a.popWhile p)

private unsafe def extractImpl (a : @& UInt8Array) (start stop : Nat) : UInt8Array :=
  let stop := min stop a.size
  if start < stop then
    let n := (stop - start).toUSize
    copySliceUnsafe (allocUnsafe 0 n) a start.toUSize 0 n
  else
    empty

/--
The elements of `a` from index `start` up to, but not including, `min stop a.size`, copied into a
new array.
-/
@[implemented_by extractImpl, expose]
public def extract : (a : @& UInt8Array) → (start stop : Nat) → UInt8Array
  | mk a, start, stop => mk (a.extract start stop)

/-! ## Linearity -/

/--
Marks `a` as linear, a debugging aid: if a marked array is ever shared and then modified, the
runtime reports it. Logically this is the identity.
-/
@[never_extract, extern "lean_sarray_mark_linear", expose]
public def markLinear (a : UInt8Array) : UInt8Array := a

/-- Returns `b`, marking it as linear if `a` is marked. Logically this is `b`. -/
@[never_extract, extern "lean_sarray_propagate_mark", expose]
public def propagateMark (a : @& UInt8Array) (b : UInt8Array) : UInt8Array := b

/-! ## Search -/

/--
The index of the first element at or after `start` that satisfies `p`, with a proof that it is in
bounds.
-/
@[inline]
public def findFinIdx? (a : UInt8Array) (p : UInt8 → Bool) (start := 0) : Option (Fin a.size) :=
  let rec @[specialize] loop (i : Nat) :=
    if h : i < a.size then
      if p a[i] then some ⟨i, h⟩ else loop (i + 1)
    else
      none
    termination_by a.size - i
  loop start

/-- The index of the first element at or after `start` that satisfies `p`. -/
@[inline]
public def findIdx? (a : UInt8Array) (p : UInt8 → Bool) (start := 0) : Option Nat :=
  let rec @[specialize] loop (i : Nat) :=
    if h : i < a.size then
      if p a[i] then some i else loop (i + 1)
    else
      none
    termination_by a.size - i
  loop start

/-! ## Building arrays -/

private unsafe def replicateImpl (n : Nat) (v : UInt8) : UInt8Array :=
  let sz := toUSizeChecked n
  loop sz (allocUnsafe sz sz) 0
where
  loop (sz : USize) (r : UInt8Array) (i : USize) : UInt8Array :=
    if i < sz then loop sz (setUnsafe r i v) (i + 1) else r

/-- An array of `n` copies of `v`. -/
@[implemented_by replicateImpl, expose]
public def replicate (n : Nat) (v : UInt8) : UInt8Array :=
  mk (Array.replicate n v)

private unsafe def ofFnImpl {n : Nat} (f : Fin n → UInt8) : UInt8Array :=
  let sz := toUSizeChecked n
  loop (allocUnsafe sz sz) 0
where
  loop (r : UInt8Array) (i : Nat) : UInt8Array :=
    if h : i < n then loop (setUnsafe r i.toUSize (f ⟨i, h⟩)) (i + 1) else r

/-- The array `#[f 0, …, f (n - 1)]`. -/
@[implemented_by ofFnImpl, expose]
public def ofFn {n : Nat} (f : Fin n → UInt8) : UInt8Array :=
  mk (Array.ofFn f)

private unsafe def ofListImpl (l : List UInt8) : UInt8Array :=
  loop l (emptyWithCapacity l.length)
where
  loop : List UInt8 → UInt8Array → UInt8Array
    | [], r => r
    | x :: xs, r => loop xs (r.push x)

/-- The array with the elements of `l`. -/
@[implemented_by ofListImpl, expose]
public def ofList (l : List UInt8) : UInt8Array :=
  mk l.toArray

/-! ## Iteration -/

@[specialize]
private unsafe def foldlMImpl {β : Type v} {m : Type v → Type w} [Monad m] (f : β → UInt8 → m β)
    (init : β) (a : @& UInt8Array) (start := 0) (stop := a.size) : m β :=
  let stop := min stop a.size
  if start < stop then loop stop.toUSize start.toUSize init else pure init
where
  @[specialize] loop (stop i : USize) (b : β) : m β :=
    if i < stop then do loop stop (i + 1) (← f b (a.uget i lcProof)) else pure b

/--
Folds a monadic function over the elements of `a` from index `start` up to, but not including,
`stop`, from first to last.
-/
@[implemented_by foldlMImpl, expose]
public def foldlM {β : Type v} {m : Type v → Type w} [Monad m] (f : β → UInt8 → m β) (init : β)
    (a : @& UInt8Array) (start := 0) (stop := a.size) : m β :=
  a.data.foldlM f init start stop

@[specialize]
private unsafe def foldrMImpl {β : Type v} {m : Type v → Type w} [Monad m] (f : UInt8 → β → m β)
    (init : β) (a : @& UInt8Array) : m β :=
  loop a.usize init
where
  @[specialize] loop (i : USize) (b : β) : m β :=
    if 0 < i then do loop (i - 1) (← f (a.uget (i - 1) lcProof) b) else pure b

/-- Folds a monadic function over the elements of `a`, from last to first. -/
@[implemented_by foldrMImpl, expose]
public def foldrM {β : Type v} {m : Type v → Type w} [Monad m] (f : UInt8 → β → m β) (init : β)
    (a : @& UInt8Array) : m β :=
  a.data.foldrM f init

@[inline, expose]
public def foldl {β : Type v} (f : β → UInt8 → β) (init : β) (a : @& UInt8Array) (start := 0)
    (stop := a.size) : β :=
  Id.run <| a.foldlM (pure <| f · ·) init start stop

@[inline, expose]
public def foldr {β : Type v} (f : UInt8 → β → β) (init : β) (a : @& UInt8Array) : β :=
  Id.run <| a.foldrM (pure <| f · ·) init

@[inline, expose]
public def forM {m : Type v → Type w} [Monad m] (f : UInt8 → m PUnit) (a : @& UInt8Array) :
    m PUnit :=
  a.foldlM (fun _ x => f x) ⟨⟩

@[specialize]
private unsafe def forInImpl {β : Type v} {m : Type v → Type w} [Monad m] (a : @& UInt8Array)
    (init : β) (f : UInt8 → β → m (ForInStep β)) : m β :=
  loop a.usize 0 init
where
  @[specialize] loop (stop i : USize) (b : β) : m β :=
    if i < stop then do
      match ← f (a.uget i lcProof) b with
      | .done b => pure b
      | .yield b => loop stop (i + 1) b
    else pure b

@[implemented_by forInImpl, expose]
public def forIn {β : Type v} {m : Type v → Type w} [Monad m] (a : @& UInt8Array) (init : β)
    (f : UInt8 → β → m (ForInStep β)) : m β :=
  ForIn.forIn a.data init f

public instance [Monad m] : ForIn m UInt8Array UInt8 where
  forIn a b f := UInt8Array.forIn a b f

public instance [Monad m] : ForM m UInt8Array UInt8 where
  forM a f := a.forM f

@[specialize]
private unsafe def anyImpl (a : @& UInt8Array) (p : UInt8 → Bool) : Bool :=
  loop a.usize 0
where
  @[specialize] loop (stop i : USize) : Bool :=
    if i < stop then p (a.uget i lcProof) || loop stop (i + 1) else false

/-- Whether some element of `a` satisfies `p`. -/
@[implemented_by anyImpl, expose]
public def any (a : @& UInt8Array) (p : UInt8 → Bool) : Bool :=
  a.data.any p

@[specialize]
private unsafe def allImpl (a : @& UInt8Array) (p : UInt8 → Bool) : Bool :=
  loop a.usize 0
where
  @[specialize] loop (stop i : USize) : Bool :=
    if i < stop then p (a.uget i lcProof) && loop stop (i + 1) else true

/-- Whether every element of `a` satisfies `p`. -/
@[implemented_by allImpl, expose]
public def all (a : @& UInt8Array) (p : UInt8 → Bool) : Bool :=
  a.data.all p

private unsafe def containsImpl (a : @& UInt8Array) (v : UInt8) : Bool :=
  anyImpl a (v == ·)

/-- Whether some element of `a` is `==` to `v`. -/
@[implemented_by containsImpl, expose]
public def contains (a : @& UInt8Array) (v : UInt8) : Bool :=
  a.data.contains v

/-- `x ∈ a` when `x` is an element of `a`. -/
public instance : Membership UInt8 UInt8Array where
  mem a x := x ∈ a.data

/-! ## Equality and hashing -/

private theorem data_injective : {a b : UInt8Array} → a.data = b.data → a = b
  | mk _, mk _, rfl => rfl

/-- Decides equality by comparing the two arrays' memory. -/
@[extern "lean_sarray_dec_eq", expose]
public def decEq (a b : @& UInt8Array) : Decidable (a = b) :=
  decidable_of_iff (a.data = b.data) ⟨fun h => by cases a; cases b; cases h; rfl, fun h => h ▸ rfl⟩

public instance : DecidableEq UInt8Array := decEq

private unsafe def hashImpl (a : @& UInt8Array) : UInt64 :=
  foldlMImpl (m := Id) (fun r x => mixHash r (Hashable.hash x)) 7 a

/-- The same hash as `a.data`. -/
@[implemented_by hashImpl]
public def hash (a : @& UInt8Array) : UInt64 :=
  Hashable.hash a.data

public instance : Hashable UInt8Array := ⟨hash⟩

public theorem hash_eq_hash_data (a : UInt8Array) : Hashable.hash a = Hashable.hash a.data := by
  rfl

/-! ## Conversion and printing -/

@[expose] public def toList (a : UInt8Array) : List UInt8 := a.data.toList

public instance : Repr UInt8Array where
  reprPrec a _ := "UInt8Array.mk " ++ repr a.data

public instance : ToString UInt8Array where
  toString a := "UInt8Array.mk " ++ toString a.data

/-! ## Slices -/

/-- Internal representation of `UInt8Array.Slice`. -/
public protected structure SliceData where
  /-- The underlying array. -/
  array : UInt8Array
  /-- The starting index of the slice (inclusive). -/
  start : Nat
  /-- The ending index of the slice (exclusive). -/
  stop : Nat
  /-- The starting index is no later than the ending index. -/
  start_le_stop : start ≤ stop
  /-- The ending index is no later than the end of the array. -/
  stop_le_array_size : stop ≤ array.size

/--
A region of a `UInt8Array`: the elements from index `start` up to, but not including, `stop`.
Taking a slice doesn't copy the array. Slices are written with core's slice notation, such as
`a[i...j]`, `a[i...*]` or `a[*...j]`.
-/
public protected abbrev Slice := Std.Slice UInt8Array.SliceData

public instance : Std.Slice.Self (Std.Slice UInt8Array.SliceData) UInt8Array.Slice where

namespace Slice

@[always_inline, inline, expose, inherit_doc SliceData.array]
public def array (s : UInt8Array.Slice) : UInt8Array := s.internalRepresentation.array

@[always_inline, inline, expose, inherit_doc SliceData.start]
public def start (s : UInt8Array.Slice) : Nat := s.internalRepresentation.start

@[always_inline, inline, expose, inherit_doc SliceData.stop]
public def stop (s : UInt8Array.Slice) : Nat := s.internalRepresentation.stop

@[inherit_doc SliceData.start_le_stop]
public theorem start_le_stop (s : UInt8Array.Slice) : s.start ≤ s.stop :=
  s.internalRepresentation.start_le_stop

@[inherit_doc SliceData.stop_le_array_size]
public theorem stop_le_array_size (s : UInt8Array.Slice) : s.stop ≤ s.array.size :=
  s.internalRepresentation.stop_le_array_size

public instance : Std.Slice.SliceSize UInt8Array.SliceData where
  size s := s.internalRepresentation.stop - s.internalRepresentation.start

public theorem size_eq (s : UInt8Array.Slice) : s.size = s.stop - s.start := rfl

/-- The element at index `i` of the slice, counted from the start of the slice. -/
@[inline, expose]
public def get (s : UInt8Array.Slice) (i : Nat) (h : i < s.size := by get_elem_tactic) :
    UInt8 :=
  s.array[s.start + i]'(by have := s.stop_le_array_size; rw [size_eq] at h; lia)

public instance : GetElem UInt8Array.Slice Nat UInt8 fun s i => i < s.size where
  getElem s i h := s.get i h

/-- The element at index `i` of the slice, or `v₀` if `i` is out of bounds. -/
@[inline]
public def getD (s : UInt8Array.Slice) (i : Nat) (v₀ : UInt8) : UInt8 :=
  if h : i < s.size then s[i] else v₀

/-- The element at index `i` of the slice, or `default` if `i` is out of bounds. -/
public abbrev get! (s : UInt8Array.Slice) (i : Nat) : UInt8 :=
  getD s i default

/-- Removes the first element of the slice, if any. -/
@[expose]
public def popFront (s : UInt8Array.Slice) : UInt8Array.Slice :=
  if h : s.start < s.stop then
    ⟨{ s.internalRepresentation with start := s.start + 1, start_le_stop := h }⟩
  else
    s

/-- The empty slice, backed by an empty array. -/
@[expose]
public protected def empty : UInt8Array.Slice :=
  ⟨{ array := UInt8Array.empty, start := 0, stop := 0, start_le_stop := Nat.le_refl 0,
     stop_le_array_size := Nat.le_refl 0 }⟩

public instance : EmptyCollection UInt8Array.Slice := ⟨Slice.empty⟩

public instance : Inhabited UInt8Array.Slice := ⟨Slice.empty⟩

/-- The elements of the slice, copied into a new array with a single `memcpy`. -/
@[expose]
public def copy (s : UInt8Array.Slice) : UInt8Array :=
  s.array.extract s.start s.stop

public theorem getElem_eq (s : UInt8Array.Slice) (i : Nat) (h : i < s.size) :
    s[i] = s.array[s.start + i]'(by have := s.stop_le_array_size; rw [size_eq] at h; lia) := rfl

public instance : Repr UInt8Array.Slice where
  reprPrec s _ := repr s.copy ++ ".toSlice"

public instance : ToString UInt8Array.Slice where
  toString s := toString s.copy

end Slice

/--
The slice of `a` from index `start` up to, but not including, `stop`. If `start` or `stop` are not
valid bounds, they are clamped to the size of `a`, and `start` is clamped to `stop`.
-/
@[expose]
public def toSlice (a : UInt8Array) (start : Nat := 0) (stop : Nat := a.size) :
    UInt8Array.Slice :=
  if h₂ : stop ≤ a.size then
    if h₁ : start ≤ stop then
      ⟨{ array := a, start, stop, start_le_stop := h₁, stop_le_array_size := h₂ }⟩
    else
      ⟨{ array := a, start := stop, stop, start_le_stop := Nat.le_refl _,
         stop_le_array_size := h₂ }⟩
  else
    if h₁ : start ≤ a.size then
      ⟨{ array := a, start, stop := a.size, start_le_stop := h₁,
         stop_le_array_size := Nat.le_refl _ }⟩
    else
      ⟨{ array := a, start := a.size, stop := a.size, start_le_stop := Nat.le_refl _,
         stop_le_array_size := Nat.le_refl _ }⟩

/-- Arrays coerce to slices, which is free. Slices don't coerce back, since that copies. -/
public instance : Coe UInt8Array UInt8Array.Slice := ⟨(·.toSlice)⟩

public instance : Std.Rcc.Sliceable UInt8Array Nat UInt8Array.Slice where
  mkSlice a range := a.toSlice range.lower (range.upper + 1)

public instance : Std.Rco.Sliceable UInt8Array Nat UInt8Array.Slice where
  mkSlice a range := a.toSlice range.lower range.upper

public instance : Std.Rci.Sliceable UInt8Array Nat UInt8Array.Slice where
  mkSlice a range := a.toSlice range.lower

public instance : Std.Roc.Sliceable UInt8Array Nat UInt8Array.Slice where
  mkSlice a range := a.toSlice (range.lower + 1) (range.upper + 1)

public instance : Std.Roo.Sliceable UInt8Array Nat UInt8Array.Slice where
  mkSlice a range := a.toSlice (range.lower + 1) range.upper

public instance : Std.Roi.Sliceable UInt8Array Nat UInt8Array.Slice where
  mkSlice a range := a.toSlice (range.lower + 1)

public instance : Std.Ric.Sliceable UInt8Array Nat UInt8Array.Slice where
  mkSlice a range := a.toSlice 0 (range.upper + 1)

public instance : Std.Rio.Sliceable UInt8Array Nat UInt8Array.Slice where
  mkSlice a range := a.toSlice 0 range.upper

public instance : Std.Rii.Sliceable UInt8Array Nat UInt8Array.Slice where
  mkSlice a _ := a.toSlice

namespace Slice

/-- The slice of `s` from index `start` up to, but not including, `stop`, clamped like `toSlice`. -/
@[expose]
public def slice (s : UInt8Array.Slice) (start : Nat := 0) (stop : Nat := s.size) :
    UInt8Array.Slice :=
  s.array.toSlice (s.start + min start s.size) (s.start + min stop s.size)

end Slice

public instance : Std.Rcc.Sliceable UInt8Array.Slice Nat UInt8Array.Slice where
  mkSlice s range := s.slice range.lower (range.upper + 1)

public instance : Std.Rco.Sliceable UInt8Array.Slice Nat UInt8Array.Slice where
  mkSlice s range := s.slice range.lower range.upper

public instance : Std.Rci.Sliceable UInt8Array.Slice Nat UInt8Array.Slice where
  mkSlice s range := s.slice range.lower

public instance : Std.Roc.Sliceable UInt8Array.Slice Nat UInt8Array.Slice where
  mkSlice s range := s.slice (range.lower + 1) (range.upper + 1)

public instance : Std.Roo.Sliceable UInt8Array.Slice Nat UInt8Array.Slice where
  mkSlice s range := s.slice (range.lower + 1) range.upper

public instance : Std.Roi.Sliceable UInt8Array.Slice Nat UInt8Array.Slice where
  mkSlice s range := s.slice (range.lower + 1)

public instance : Std.Ric.Sliceable UInt8Array.Slice Nat UInt8Array.Slice where
  mkSlice s range := s.slice 0 (range.upper + 1)

public instance : Std.Rio.Sliceable UInt8Array.Slice Nat UInt8Array.Slice where
  mkSlice s range := s.slice 0 range.upper

public instance : Std.Rii.Sliceable UInt8Array.Slice Nat UInt8Array.Slice where
  mkSlice s _ := s

/-- The iterator over the elements of a slice, used for `for` loops and the generic slice API. -/
public protected structure SliceIterator where
  /-- The rest of the slice. -/
  xs : UInt8Array.Slice

@[inline, expose]
public def SliceIterator.step :
    Std.IterM (α := UInt8Array.SliceIterator) Id UInt8 →
      Std.IterStep (Std.IterM (α := UInt8Array.SliceIterator) m UInt8) UInt8
  | ⟨⟨xs⟩⟩ =>
    if h : xs.start < xs.stop then
      have := xs.stop_le_array_size
      .yield ⟨⟨⟨xs.array, xs.start + 1, xs.stop, h, xs.stop_le_array_size⟩⟩⟩ xs.array[xs.start]
    else
      .done

public instance : Std.Iterator UInt8Array.SliceIterator Id UInt8 where
  IsPlausibleStep it step := step = SliceIterator.step it
  step it := pure <| .deflate ⟨SliceIterator.step it, rfl⟩

private def SliceIterator.finitenessRelation :
    Std.Iterators.FinitenessRelation UInt8Array.SliceIterator Id where
  Rel := InvImage WellFoundedRelation.rel
    (fun it => it.internalState.xs.stop - it.internalState.xs.start)
  wf := InvImage.wf _ WellFoundedRelation.wf
  subrelation {it it'} h := by
    rcases it with ⟨⟨⟨⟨array, start, stop, h₁, h₂⟩⟩⟩⟩
    obtain ⟨step, h, h'⟩ := h
    cases h'
    simp only [SliceIterator.step] at h
    split at h
    next hs =>
      simp only [Std.IterStep.successor, Option.some.injEq] at h
      subst h
      simp only [InvImage, WellFoundedRelation.rel, sizeOf_nat, Slice.start, Slice.stop] at hs ⊢
      lia
    next =>
      simp [Std.IterStep.successor] at h

public instance : Std.Iterators.Finite UInt8Array.SliceIterator Id :=
  .of_finitenessRelation SliceIterator.finitenessRelation

-- Each element goes through `lift`, like each step of the iterator in the default implementation,
-- so the two agree for every lawful `lift`, which is what core's consumers pass.
@[specialize]
private unsafe def SliceIterator.forInImpl {n : Type x → Type x'} [Monad n]
    (lift : (γ : Type) → (δ : Type x) → (γ → n δ) → Id γ → n δ) (γ : Type x)
    (Pl : UInt8 → γ → ForInStep γ → Prop)
    (it : Std.IterM (α := UInt8Array.SliceIterator) Id UInt8) (init : γ)
    (f : (b : UInt8) → it.IsPlausibleIndirectOutput b → (c : γ) → n (Subtype (Pl b c))) :
    n γ :=
  let xs := it.internalState.xs
  loop xs.array xs.stop.toUSize xs.start.toUSize init
where
  @[specialize] loop (a : UInt8Array) (stop i : USize) (c : γ) : n γ :=
    if i < stop then
      lift _ _ (fun x => do
        match ← f x lcProof c with
        | ⟨.yield c, _⟩ => loop a stop (i + 1) c
        | ⟨.done c, _⟩ => pure c) (pure (a.uget i lcProof))
    else pure c

/--
The loop behind `for` loops and the `Std.Iterators` consumers on slices. Logically it is
`Std.IteratorLoop.defaultImplementation`, which steps the iterator one element at a time; it is
implemented by a loop over the `USize` indices of the underlying array.
-/
@[implemented_by SliceIterator.forInImpl, expose]
public def SliceIterator.forIn {n : Type x → Type x'} [Monad n]
    (lift : (γ : Type) → (δ : Type x) → (γ → n δ) → Id γ → n δ) (γ : Type x)
    (Pl : UInt8 → γ → ForInStep γ → Prop)
    (it : Std.IterM (α := UInt8Array.SliceIterator) Id UInt8) (init : γ)
    (f : (b : UInt8) → it.IsPlausibleIndirectOutput b → (c : γ) → n (Subtype (Pl b c))) :
    n γ :=
  Std.IteratorLoop.defaultImplementation.forIn lift γ Pl it init f

public instance [Monad m] : Std.IteratorLoop UInt8Array.SliceIterator Id m where
  forIn := SliceIterator.forIn

public instance [Monad m] : Std.LawfulIteratorLoop UInt8Array.SliceIterator Id m where
  lawful _ _ _ _ _ _ _ _ := rfl

public instance :
    Std.ToIterator (Std.Slice UInt8Array.SliceData) Id UInt8Array.SliceIterator UInt8 :=
  Std.ToIterator.of UInt8Array.SliceIterator (⟨⟨·⟩⟩)

public instance [Monad m] : ForIn m UInt8Array.Slice UInt8 := inferInstance

public instance [Monad m] : ForM m UInt8Array.Slice UInt8 where
  forM s f := s.foldlM (fun _ x => f x) ⟨⟩

/-- An iterator over the elements of `a`, for use with the `Std.Iterators` API. -/
@[inline, expose]
public def iter (a : UInt8Array) : Std.Iter (α := UInt8Array.SliceIterator) UInt8 :=
  a.toSlice.iter

namespace Slice

@[specialize]
private unsafe def foldrMImpl {β : Type v} {m : Type v → Type w} [Monad m]
    (f : UInt8 → β → m β) (init : β) (s : UInt8Array.Slice) : m β :=
  loop s.array s.start.toUSize s.stop.toUSize init
where
  @[specialize] loop (a : UInt8Array) (start i : USize) (b : β) : m β :=
    if start < i then do loop a start (i - 1) (← f (a.uget (i - 1) lcProof) b) else pure b

/-- Folds a monadic function over the elements of `s`, from last to first. -/
@[implemented_by foldrMImpl, expose]
public def foldrM {β : Type v} {m : Type v → Type w} [Monad m] (f : UInt8 → β → m β) (init : β)
    (s : UInt8Array.Slice) : m β :=
  loop s.size (Nat.le_refl _) init
where
  @[specialize] loop : (i : Nat) → i ≤ s.size → β → m β
    | 0, _, b => pure b
    | i + 1, h, b => do loop i (Nat.le_of_succ_le h) (← f s[i] b)

/-- Folds a function over the elements of `s`, from last to first. -/
@[inline, expose]
public def foldr {β : Type v} (f : UInt8 → β → β) (init : β) (s : UInt8Array.Slice) : β :=
  Id.run <| s.foldrM (pure <| f · ·) init

/-- Runs a monadic action on each element of `s`, from last to first. -/
@[inline, expose]
public def forRevM {m : Type v → Type w} [Monad m] (f : UInt8 → m PUnit)
    (s : UInt8Array.Slice) : m PUnit :=
  s.foldrM (fun x _ => f x) ⟨⟩

@[specialize]
private unsafe def findSomeRevMImpl {β : Type v} {m : Type v → Type w} [Monad m]
    (s : UInt8Array.Slice) (f : UInt8 → m (Option β)) : m (Option β) :=
  loop s.array s.start.toUSize s.stop.toUSize
where
  @[specialize] loop (a : UInt8Array) (start i : USize) : m (Option β) :=
    if start < i then do
      match ← f (a.uget (i - 1) lcProof) with
      | some b => pure (some b)
      | none => loop a start (i - 1)
    else pure none

/-- The result of the last element of `s` for which `f` returns `some`, searching from the end. -/
@[implemented_by findSomeRevMImpl, expose]
public def findSomeRevM? {β : Type v} {m : Type v → Type w} [Monad m] (s : UInt8Array.Slice)
    (f : UInt8 → m (Option β)) : m (Option β) :=
  loop s.size (Nat.le_refl _)
where
  @[specialize] loop : (i : Nat) → i ≤ s.size → m (Option β)
    | 0, _ => pure none
    | i + 1, h => do
      match ← f s[i] with
      | some b => pure (some b)
      | none => loop i (Nat.le_of_succ_le h)

/-- The last element of `s` that satisfies the monadic predicate `p`. -/
@[inline, expose]
public def findRevM? {m : Type → Type w} [Monad m] (s : UInt8Array.Slice) (p : UInt8 → m Bool) :
    m (Option UInt8) :=
  s.findSomeRevM? fun x => return if (← p x) then some x else none

/-- The last element of `s` that satisfies `p`. -/
@[inline, expose]
public def findRev? (s : UInt8Array.Slice) (p : UInt8 → Bool) : Option UInt8 :=
  Id.run <| s.findRevM? (pure <| p ·)

/-- The first element of `s` that satisfies `p`. -/
@[inline, expose]
public def find? (s : UInt8Array.Slice) (p : UInt8 → Bool) : Option UInt8 :=
  s.iter.find? p

/-- Whether some element of `s` satisfies `p`. -/
@[inline, expose]
public def any (s : UInt8Array.Slice) (p : UInt8 → Bool) : Bool :=
  s.iter.any p

/-- Whether every element of `s` satisfies `p`. -/
@[inline, expose]
public def all (s : UInt8Array.Slice) (p : UInt8 → Bool) : Bool :=
  s.iter.all p

/-- Whether some element of `s` is `==` to `v`. -/
@[inline, expose]
public def contains (s : UInt8Array.Slice) (v : UInt8) : Bool :=
  s.any (v == ·)

/-- The number of elements of `s` that satisfy `p`. -/
@[inline, expose]
public def count (s : UInt8Array.Slice) (p : UInt8 → Bool) : Nat :=
  s.iter.fold (fun n x => if p x then n + 1 else n) 0

/-- `x ∈ s` when `x` is an element of `s`. -/
public instance : Membership UInt8 UInt8Array.Slice where
  mem s x := x ∈ s.copy

private unsafe def beqImpl (s t : UInt8Array.Slice) : Bool :=
  s.size == t.size && loop s.array t.array s.stop.toUSize s.start.toUSize t.start.toUSize
where
  loop (a b : UInt8Array) (stop i j : USize) : Bool :=
    if i < stop then a.uget i lcProof == b.uget j lcProof && loop a b stop (i + 1) (j + 1)
    else true

/--
Compares the elements of two slices with `==`: slices of different arrays, or at different offsets,
are equal when their elements are. Logically it compares the copies.
-/
-- There is no `DecidableEq` instance: structural equality of slices compares the underlying arrays
-- and the bounds, so it would disagree with `==`.
@[implemented_by beqImpl]
public def beq (s t : UInt8Array.Slice) : Bool :=
  s.copy == t.copy

public instance : BEq UInt8Array.Slice := ⟨beq⟩

end Slice

/--
Collects the values emitted by an iterator into a new array. Together with the `Std.Iterators`
combinators, this gives functions such as `map`, `filter`, `take` and `zipWith`, for example
`(a.iter.map (· + 1)).toUInt8Array`.
-/
@[inline, expose]
public def _root_.Std.Iter.toUInt8Array {α : Type} [Std.Iterator α Id UInt8]
    [Std.IteratorLoop α Id Id] (it : Std.Iter (α := α) UInt8) : UInt8Array :=
  it.fold (·.push ·) empty

/-- Like `Std.Iter.toUInt8Array`, but the new array starts with room for `capacity` elements. -/
@[inline, expose]
public def _root_.Std.Iter.toUInt8ArrayWithCapacity {α : Type} [Std.Iterator α Id UInt8]
    [Std.IteratorLoop α Id Id] (it : Std.Iter (α := α) UInt8) (capacity : Nat) : UInt8Array :=
  it.fold (·.push ·) (emptyWithCapacity capacity)

@[simp] public theorem _root_.Std.Iter.toUInt8ArrayWithCapacity_eq {α : Type}
    [Std.Iterator α Id UInt8] [Std.IteratorLoop α Id Id] (it : Std.Iter (α := α) UInt8)
    (capacity : Nat) : it.toUInt8ArrayWithCapacity capacity = it.toUInt8Array := rfl

@[simp] public theorem size_mk (a : Array UInt8) : (mk a).size = a.size := rfl

@[simp] public theorem data_mk (a : Array UInt8) : (mk a).data = a := rfl

@[simp] public theorem mk_data (a : UInt8Array) : mk a.data = a := by cases a; rfl

public theorem size_eq_data_size (a : UInt8Array) : a.size = a.data.size := by cases a; rfl

@[simp] public theorem size_data (a : UInt8Array) : a.data.size = a.size :=
  (size_eq_data_size a).symm

@[simp] public theorem size_uset (a : UInt8Array) (i : USize) (v : UInt8) (h) :
    (a.uset i v h).size = a.size := by
  cases a; exact Array.size_set ..

@[simp] public theorem size_set (a : UInt8Array) (i : Nat) (v : UInt8) (h) :
    (a.set i v h).size = a.size := by
  cases a; exact Array.size_set ..

@[simp] public theorem size_push (a : UInt8Array) (v : UInt8) :
    (a.push v).size = a.size + 1 := by
  cases a; simp [push, size]

@[simp] public theorem data_append (a b : UInt8Array) : (a ++ b).data = a.data ++ b.data := by
  cases a; cases b; rfl

@[simp] public theorem size_append (a b : UInt8Array) : (a ++ b).size = a.size + b.size := by
  simp [-size_data, size_eq_data_size]

@[ext] public theorem ext {a b : UInt8Array} (h : a.data = b.data) : a = b := data_injective h

@[simp] public theorem getElem_mk (a : Array UInt8) (i : Nat) (h : i < (mk a).size) :
    (mk a)[i] = a[i] := rfl

public theorem getElem_eq_getElem_data (a : UInt8Array) (i : Nat) (h : i < a.size) :
    a[i] = a.data[i]'(size_eq_data_size a ▸ h) := by
  cases a; rfl

@[simp] public theorem getElem_data (a : UInt8Array) (i : Nat) (h : i < a.data.size) :
    a.data[i] = a[i]'(by simpa using h) := by
  cases a; rfl

public theorem ext_getElem {a b : UInt8Array} (h₁ : a.size = b.size)
    (h₂ : ∀ (i : Nat) (hi₁ : i < a.size) (hi₂ : i < b.size), a[i] = b[i]) : a = b := by
  ext i hi₁ hi₂
  · simpa using h₁
  · simpa using h₂ i (by simpa using hi₁) (by simpa using hi₂)

@[simp] public theorem getElem_usize (a : UInt8Array) (i : USize) (h : i.toNat < a.size) :
    a[i] = a[i.toNat] := by
  cases a; rfl

@[simp] public theorem data_uset (a : UInt8Array) (i : USize) (v : UInt8) (h) :
    (a.uset i v h).data = a.data.set i.toNat v (size_eq_data_size a ▸ h) := by
  cases a; rfl

@[simp] public theorem data_set (a : UInt8Array) (i : Nat) (v : UInt8) (h) :
    (a.set i v h).data = a.data.set i v (size_eq_data_size a ▸ h) := by
  cases a; rfl

@[simp] public theorem data_push (a : UInt8Array) (v : UInt8) :
    (a.push v).data = a.data.push v := by
  cases a; rfl

@[simp] public theorem data_pop (a : UInt8Array) : a.pop.data = a.data.pop := by
  cases a; rfl

@[simp] public theorem data_extract (a : UInt8Array) (start stop : Nat) :
    (a.extract start stop).data = a.data.extract start stop := by
  cases a; rfl

@[simp] public theorem data_replicate (n : Nat) (v : UInt8) :
    (replicate n v).data = Array.replicate n v := rfl

@[simp] public theorem data_ofFn {n : Nat} (f : Fin n → UInt8) :
    (ofFn f).data = Array.ofFn f := rfl

@[simp] public theorem data_empty : (empty : UInt8Array).data = #[] := rfl

@[simp] public theorem size_pop (a : UInt8Array) : a.pop.size = a.size - 1 := by
  simp [-size_data, size_eq_data_size]

@[simp] public theorem size_extract (a : UInt8Array) (start stop : Nat) :
    (a.extract start stop).size = min stop a.size - start := by
  simp [-size_data, size_eq_data_size]

@[simp] public theorem size_replicate (n : Nat) (v : UInt8) : (replicate n v).size = n := by
  simp [-size_data, size_eq_data_size]

@[simp] public theorem size_ofFn {n : Nat} (f : Fin n → UInt8) : (ofFn f).size = n := by
  simp [-size_data, size_eq_data_size]

@[simp] public theorem size_empty : (empty : UInt8Array).size = 0 := rfl

@[simp] public theorem getElem_set (a : UInt8Array) (i : Nat) (v : UInt8) (h) (j : Nat) (hj) :
    (a.set i v h)[j]'hj = if i = j then v else a[j]'(by simpa using hj) := by
  simp [-getElem_data, getElem_eq_getElem_data, Array.getElem_set]

@[simp] public theorem getElem_push (a : UInt8Array) (v : UInt8) (i : Nat) (h) :
    (a.push v)[i]'h = if h' : i < a.size then a[i] else v := by
  simp [-getElem_data, getElem_eq_getElem_data, Array.getElem_push, -size_data, size_eq_data_size]

@[simp] public theorem getElem_pop (a : UInt8Array) (i : Nat) (h) :
    a.pop[i]'h = a[i]'(by simp at h; lia) := by
  simp [-getElem_data, getElem_eq_getElem_data]

@[simp] public theorem data_popWhile (p : UInt8 → Bool) (a : UInt8Array) :
    (a.popWhile p).data = a.data.popWhile p := by
  cases a; rfl

@[simp] public theorem getElem_append (a b : UInt8Array) (i : Nat) (h) :
    (a ++ b)[i]'h = if h' : i < a.size then a[i] else b[i - a.size]'(by simp at h; lia) := by
  simp [-getElem_data, getElem_eq_getElem_data, Array.getElem_append, -size_data, size_eq_data_size]

@[simp] public theorem getElem_extract (a : UInt8Array) (start stop i : Nat) (h) :
    (a.extract start stop)[i]'h = a[start + i]'(by simp at h; lia) := by
  simp [-getElem_data, getElem_eq_getElem_data]

@[simp] public theorem getElem_replicate (n : Nat) (v : UInt8) (i : Nat) (h) :
    (replicate n v)[i]'h = v := by
  simp [-getElem_data, getElem_eq_getElem_data]

@[simp] public theorem getElem_ofFn {n : Nat} (f : Fin n → UInt8) (i : Nat) (h) :
    (ofFn f)[i]'h = f ⟨i, by simpa using h⟩ := by
  simp [-getElem_data, getElem_eq_getElem_data]

public theorem foldl_eq_foldl_data {β : Type v} (f : β → UInt8 → β) (init : β)
    (a : UInt8Array) :
    a.foldl f init = a.data.foldl f init := by
  rfl

public theorem foldr_eq_foldr_data {β : Type v} (f : UInt8 → β → β) (init : β)
    (a : UInt8Array) :
    a.foldr f init = a.data.foldr f init := by
  rfl

@[simp] public theorem toList_data (a : UInt8Array) : a.data.toList = a.toList := rfl

@[simp] public theorem emptyc_eq_empty : (∅ : UInt8Array) = empty := rfl

@[simp] public theorem emptyWithCapacity_eq_empty (c : Nat) : emptyWithCapacity c = empty := rfl

public theorem size_eq_zero_iff {a : UInt8Array} : a.size = 0 ↔ a = empty := by
  simp [UInt8Array.ext_iff, ← Array.size_eq_zero_iff]

@[simp] public theorem data_set! (a : UInt8Array) (i : Nat) (v : UInt8) :
    (a.set! i v).data = a.data.set! i v := by
  cases a; rfl

@[simp] public theorem size_set! (a : UInt8Array) (i : Nat) (v : UInt8) :
    (a.set! i v).size = a.size := by
  simp [-size_data, size_eq_data_size]

public theorem getElem!_eq_getElem!_data (a : UInt8Array) (i : Nat) : a[i]! = a.data[i]! := by
  rcases a with ⟨a⟩
  by_cases h : i < a.size <;> simp [getElem!_def, getElem?_def, h] <;> rfl

@[simp] public theorem data_ofList (l : List UInt8) : (ofList l).data = l.toArray := rfl

@[simp] public theorem size_ofList (l : List UInt8) : (ofList l).size = l.length := rfl

@[simp] public theorem getElem_ofList (l : List UInt8) (i : Nat) (h) :
    (ofList l)[i]'h = l[i]'(by simpa using h) := rfl

@[simp] public theorem toList_ofList (l : List UInt8) : (ofList l).toList = l := rfl

@[simp] public theorem ofList_toList (a : UInt8Array) : ofList a.toList = a := by
  simp [UInt8Array.ext_iff, ← toList_data]

@[simp] public theorem markLinear_eq (a : UInt8Array) : a.markLinear = a := rfl

@[simp] public theorem propagateMark_eq (a b : UInt8Array) : a.propagateMark b = b := rfl

@[simp] public theorem append_empty (a : UInt8Array) : a ++ empty = a := by
  simp [UInt8Array.ext_iff]

@[simp] public theorem empty_append (a : UInt8Array) : empty ++ a = a := by
  simp [UInt8Array.ext_iff]

public theorem append_assoc (a b c : UInt8Array) : a ++ b ++ c = a ++ (b ++ c) := by
  simp [UInt8Array.ext_iff]

@[simp] public theorem append_eq_empty_iff {a b : UInt8Array} :
    a ++ b = empty ↔ a = empty ∧ b = empty := by
  simp only [UInt8Array.ext_iff, data_append, data_empty, Array.append_eq_empty_iff]

@[simp] public theorem append_right_inj (a : UInt8Array) {b c : UInt8Array} :
    a ++ b = a ++ c ↔ b = c := by
  simp only [UInt8Array.ext_iff, data_append, Array.append_right_inj]

@[simp] public theorem append_left_inj {a b : UInt8Array} (c : UInt8Array) :
    a ++ c = b ++ c ↔ a = b := by
  simp only [UInt8Array.ext_iff, data_append, Array.append_left_inj]

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
  simp [UInt8Array.ext_iff, -size_data, size_eq_data_size]

@[simp] public theorem data_copySlice (src : UInt8Array) (srcOff : Nat) (dest : UInt8Array)
    (destOff len : Nat) (exact : Bool) :
    (src.copySlice srcOff dest destOff len exact).data =
      dest.data.extract 0 destOff ++ src.data.extract srcOff (srcOff + len) ++
        dest.data.extract (destOff + min len (src.size - srcOff)) dest.size := by
  simp [copySlice]

public theorem copySlice_eq_append (src : UInt8Array) (srcOff : Nat) (dest : UInt8Array)
    (destOff len : Nat) (exact : Bool) :
    src.copySlice srcOff dest destOff len exact =
      dest.extract 0 destOff ++ src.extract srcOff (srcOff + len) ++
        dest.extract (destOff + min len (src.size - srcOff)) dest.size := by
  simp [UInt8Array.ext_iff]

@[simp] public theorem Slice.size_copy (s : UInt8Array.Slice) : s.copy.size = s.size := by
  have := s.stop_le_array_size
  simp only [Slice.copy, size_extract, Slice.size_eq]
  lia

/-! ### Lists -/

@[simp] public theorem toList_mk (a : Array UInt8) : (mk a).toList = a.toList := rfl

@[simp] public theorem length_toList (a : UInt8Array) : a.toList.length = a.size := by
  simp [← toList_data]

@[simp] public theorem getElem_toList (a : UInt8Array) (i : Nat) (h : i < a.toList.length) :
    a.toList[i] = a[i]'(by simpa using h) := by
  simp [← toList_data]

@[simp] public theorem getElem?_toList (a : UInt8Array) (i : Nat) : a.toList[i]? = a[i]? := by
  by_cases h : i < a.size <;> simp [h, ← toList_data]

@[simp] public theorem toList_inj {a b : UInt8Array} : a.toList = b.toList ↔ a = b :=
  ⟨fun h => by rw [← ofList_toList a, h, ofList_toList], fun h => h ▸ rfl⟩

@[simp] public theorem toList_empty : (empty : UInt8Array).toList = [] := rfl

@[simp] public theorem toList_push (a : UInt8Array) (v : UInt8) :
    (a.push v).toList = a.toList ++ [v] := by
  simp [← toList_data]

@[simp] public theorem toList_pop (a : UInt8Array) : a.pop.toList = a.toList.dropLast := by
  simp [← toList_data]

@[simp] public theorem toList_append (a b : UInt8Array) :
    (a ++ b).toList = a.toList ++ b.toList := by
  simp [← toList_data]

@[simp] public theorem toList_set (a : UInt8Array) (i : Nat) (v : UInt8) (h) :
    (a.set i v h).toList = a.toList.set i v := by
  simp [← toList_data]

@[simp] public theorem toList_set! (a : UInt8Array) (i : Nat) (v : UInt8) :
    (a.set! i v).toList = a.toList.set i v := by
  simp [← toList_data]

@[simp] public theorem toList_extract (a : UInt8Array) (start stop : Nat) :
    (a.extract start stop).toList = a.toList.extract start stop := by
  simp [← toList_data]

@[simp] public theorem toList_replicate (n : Nat) (v : UInt8) :
    (replicate n v).toList = List.replicate n v := by
  simp [← toList_data]

@[simp] public theorem toList_ofFn {n : Nat} (f : Fin n → UInt8) :
    (ofFn f).toList = List.ofFn f := by
  simp [← toList_data]

@[simp] public theorem toList_popWhile (p : UInt8 → Bool) (a : UInt8Array) :
    (a.popWhile p).toList = (a.toList.reverse.dropWhile p).reverse := by
  rw [← toList_data, data_popWhile, ← Array.toArray_toList (xs := a.data),
    List.popWhile_toArray]
  simp

/-! ### Machine-word indices -/

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

/-! ### Last element -/

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

@[simp] public theorem back?_push (a : UInt8Array) (v : UInt8) :
    (a.push v).back? = some v := by
  rw [← getLast?_toList, toList_push, List.getLast?_concat]

@[simp] public theorem back!_push (a : UInt8Array) (v : UInt8) : (a.push v).back! = v := by
  simp [back!_eq_getElem!]

@[simp] public theorem back_push (a : UInt8Array) (v : UInt8) (h) : (a.push v).back h = v := by
  simp [back_eq_getElem]

/-! ### More lists -/

@[simp] public theorem toList_uset (a : UInt8Array) (i : USize) (v : UInt8) (h) :
    (a.uset i v h).toList = a.toList.set i.toNat v := by
  simp [← toList_data]

@[simp] public theorem toList_copySlice (src : UInt8Array) (srcOff : Nat) (dest : UInt8Array)
    (destOff len : Nat) (exact : Bool) :
    (src.copySlice srcOff dest destOff len exact).toList =
      dest.toList.extract 0 destOff ++ src.toList.extract srcOff (srcOff + len) ++
        dest.toList.extract (destOff + min len (src.size - srcOff)) dest.size := by
  simp [copySlice_eq_append]

/-! ### Accessors -/

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

/-! ### Queries -/

@[simp] public theorem any_toList (a : UInt8Array) (p : UInt8 → Bool) :
    a.toList.any p = a.any p := by
  simp [any, ← toList_data]

@[simp] public theorem all_toList (a : UInt8Array) (p : UInt8 → Bool) :
    a.toList.all p = a.all p := by
  simp [all, ← toList_data]

@[simp] public theorem contains_toList (a : UInt8Array) (v : UInt8) :
    a.toList.contains v = a.contains v := by
  simp [contains, ← toList_data]

@[simp] public theorem foldl_toList {β : Type v} (f : β → UInt8 → β) (init : β)
    (a : UInt8Array) : a.toList.foldl f init = a.foldl f init := by
  simp [foldl_eq_foldl_data, ← toList_data]

@[simp] public theorem foldr_toList {β : Type v} (f : UInt8 → β → β) (init : β)
    (a : UInt8Array) : a.toList.foldr f init = a.foldr f init := by
  simp [foldr_eq_foldr_data, ← toList_data]

@[simp] public theorem forIn_toList {β : Type v} {m : Type v → Type w} [Monad m] [LawfulMonad m]
    (a : UInt8Array) (init : β) (f : UInt8 → β → m (ForInStep β)) :
    ForIn.forIn a.toList init f = ForIn.forIn a init f := by
  rw [← toList_data, Array.forIn_toList]
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
  fun_induction findFinIdx?.loop a p i <;> rw [findIdx?.loop] <;> simp_all <;> lia

@[simp] public theorem map_val_findFinIdx? (a : UInt8Array) (p : UInt8 → Bool) (start : Nat) :
    (a.findFinIdx? p start).map Fin.val = a.findIdx? p start := by
  simp [findFinIdx?, findIdx?, findFinIdx?_loop_eq]

/-! ### Slices -/

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

/-! ### Writes -/

@[simp] public theorem getElem_uset (a : UInt8Array) (i : USize) (v : UInt8) (h) (j : Nat)
    (hj) : (a.uset i v h)[j]'hj = if i.toNat = j then v else a[j]'(by simpa using hj) := by
  simp [-getElem_data, getElem_eq_getElem_data, Array.getElem_set]

@[simp] public theorem getElem_set! (a : UInt8Array) (i : Nat) (v : UInt8) (j : Nat) (hj) :
    (a.set! i v)[j]'hj = if i = j then v else a[j]'(by simpa using hj) := by
  simp only [getElem_eq_getElem_data, data_set!, Array.set!_eq_setIfInBounds]
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
  simp [-size_data, size_eq_data_size]
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

/-! ### Monadic folds -/

@[simp] public theorem foldlM_toList {β : Type v} {m : Type v → Type w} [Monad m]
    (f : β → UInt8 → m β) (init : β) (a : UInt8Array) :
    a.toList.foldlM f init = a.foldlM f init := by
  rw [← toList_data, Array.foldlM_toList, foldlM, size_eq_data_size]

@[simp] public theorem foldrM_toList {β : Type v} {m : Type v → Type w} [Monad m]
    (f : UInt8 → β → m β) (init : β) (a : UInt8Array) :
    a.toList.foldrM f init = a.foldrM f init := by
  rw [← toList_data, Array.foldrM_toList]
  rfl

@[simp] public theorem forM_eq_forM {m : Type v → Type w} [Monad m] (f : UInt8 → m PUnit)
    (a : UInt8Array) : a.forM f = ForM.forM a f := rfl

@[simp] public theorem forM_toList {m : Type v → Type w} [Monad m] (f : UInt8 → m PUnit)
    (a : UInt8Array) : ForM.forM a.toList f = ForM.forM a f := by
  rcases a with ⟨⟨l⟩⟩
  exact (List.forM_toArray l f).symm

/-! ### Membership -/

public theorem mem_def {x : UInt8} {a : UInt8Array} : x ∈ a ↔ x ∈ a.data := Iff.rfl

@[simp] public theorem mem_data {x : UInt8} {a : UInt8Array} : x ∈ a.data ↔ x ∈ a := Iff.rfl

@[simp] public theorem mem_mk {x : UInt8} {xs : Array UInt8} : x ∈ mk xs ↔ x ∈ xs := Iff.rfl

@[simp] public theorem mem_toList {x : UInt8} {a : UInt8Array} : x ∈ a.toList ↔ x ∈ a := by
  rw [← toList_data, Array.mem_toList_iff, mem_data]

public theorem mem_iff_getElem {x : UInt8} {a : UInt8Array} :
    x ∈ a ↔ ∃ (i : Nat) (h : i < a.size), a[i] = x := by
  rw [← mem_data, Array.mem_iff_getElem]
  simp

public theorem getElem_mem {a : UInt8Array} {i : Nat} (h : i < a.size) : a[i] ∈ a :=
  mem_iff_getElem.mpr ⟨i, h, rfl⟩

@[simp] public theorem not_mem_empty (x : UInt8) : ¬x ∈ (empty : UInt8Array) := by
  simp [← mem_data]

@[simp] public theorem mem_push {x v : UInt8} {a : UInt8Array} :
    x ∈ a.push v ↔ x ∈ a ∨ x = v := by
  simp [← mem_data]

@[simp] public theorem mem_append {x : UInt8} {a b : UInt8Array} :
    x ∈ a ++ b ↔ x ∈ a ∨ x ∈ b := by
  simp [← mem_data]

/-! ### Iterators -/

private theorem toList_foldl_push (a : UInt8Array) (l : List UInt8) :
    (l.foldl (·.push ·) a).toList = a.toList ++ l := by
  induction l generalizing a <;> simp_all

@[simp] public theorem _root_.Std.Iter.toList_toUInt8Array {α : Type} [Std.Iterator α Id UInt8]
    [Std.Iterators.Finite α Id] [Std.IteratorLoop α Id Id] [Std.LawfulIteratorLoop α Id Id]
    (it : Std.Iter (α := α) UInt8) : it.toUInt8Array.toList = it.toList := by
  rw [Std.Iter.toUInt8Array, ← Std.Iter.foldl_toList, toList_foldl_push, toList_empty,
    List.nil_append]

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

/-! ### Slices as copies -/

@[simp] public theorem Slice.size_empty : (Slice.empty : UInt8Array.Slice).size = 0 := rfl

@[simp] public theorem Slice.emptyc_eq_empty : (∅ : UInt8Array.Slice) = Slice.empty := rfl

@[simp] public theorem Slice.copy_empty : (Slice.empty : UInt8Array.Slice).copy = empty := by
  simp [Slice.copy, Slice.empty, Slice.array, Slice.start, Slice.stop]

@[simp] public theorem Slice.toList_eq_toList_copy (s : UInt8Array.Slice) :
    s.toList = s.copy.toList := by
  rw [Std.Slice.Internal.toList_eq_toList_iter, SliceIterator.toList_eq,
    Std.Slice.Internal.iter_eq_toIteratorIter, Std.ToIterator.iter_eq]
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
  | cons x l ih => by_cases hx : p x <;> simp [ih, hx] <;> lia

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
    by_cases hp : p s[i] <;> simp [ih, hp] <;> rfl

@[simp] public theorem Slice.findRev?_eq_find?_reverse_toList_copy (s : UInt8Array.Slice)
    (p : UInt8 → Bool) : s.findRev? p = s.copy.toList.reverse.find? p := by
  have := Slice.findSomeRevM?_loop_eq p s s.size (Nat.le_refl _)
  rw [List.take_of_length_le (by simp)] at this
  exact this

/-! ### Membership in slices -/

@[simp] public theorem Slice.mem_iff_mem_copy {x : UInt8} {s : UInt8Array.Slice} :
    x ∈ s ↔ x ∈ s.copy := Iff.rfl

public theorem Slice.mem_iff_getElem {x : UInt8} {s : UInt8Array.Slice} :
    x ∈ s ↔ ∃ (i : Nat) (h : i < s.size), s[i] = x := by
  rw [mem_iff_mem_copy, UInt8Array.mem_iff_getElem]
  simp

public theorem Slice.getElem_mem {s : UInt8Array.Slice} {i : Nat} (h : i < s.size) : s[i] ∈ s :=
  mem_iff_getElem.mpr ⟨i, h, rfl⟩

/-! ### Slice equality -/

@[simp] public theorem Slice.beq_eq_beq_copy (s t : UInt8Array.Slice) :
    (s == t) = (s.copy == t.copy) := by
  rfl

/-! ## In-place folds -/

@[specialize]
private unsafe def foldInPlaceImpl {β : Type v} (a : UInt8Array) (start len : USize) (init : β)
    (f : (k : USize) → k.toNat < len.toNat → UInt8 → β → UInt8 × β)
    (_ : start.toNat + len.toNat ≤ a.size) : UInt8Array × β :=
  loop (ensureExclusiveUnsafe a) 0 init
where
  @[specialize] loop (a : UInt8Array) (k : USize) (b : β) : UInt8Array × β :=
    if k < len then
      let p := f k lcProof (a.uget (start + k) lcProof) b
      loop (setUnsafe a (start + k) p.1) (k + 1) p.2
    else
      (a, b)

/-- The loop of `foldInPlace`, over `Nat` indices. -/
@[expose]
public def foldInPlace.loop {β : Type v} (len' : USize)
    (f : (k : USize) → k.toNat < len'.toNat → UInt8 → β → UInt8 × β)
    (start len : Nat) (a : UInt8Array) (h : start + len ≤ a.size) (hlen : len ≤ len'.toNat)
    (k : Nat) (b : β) : UInt8Array × β :=
  if hk : k < len then
    let p := f k.toUSize (by
      have := len'.toNat_lt_size
      rw [USize.toNat_ofNat_of_lt' (by lia)]
      lia) (a[start + k]'(by lia)) b
    foldInPlace.loop len' f start len (a.set (start + k) p.1 (by lia)) (by simpa using h) hlen
      (k + 1) p.2
  else
    (a, b)
termination_by len - k

/--
Replaces each element of `a` from index `start` for `len` elements while threading an
accumulator, in place when `a` is not shared: for each `k < len`, the element `x` at `start + k`
becomes the first component of `f k hk x b`, whose second component is the next accumulator.
Returns the new array and the last accumulator. The proof `hk : k.toNat < len.toNat` lets `f`
read other arrays with `uget`.

The point is the implementation: the result is that of a loop of `set`s, but `a` is made
exclusive once, before the loop, which then stores without checks, where each `uset` checks at
every write. `f` only sees the elements, never the array, which is what makes skipping the
checks safe.
-/
@[implemented_by foldInPlaceImpl, expose]
public def foldInPlace {β : Type v} (a : UInt8Array) (start len : USize) (init : β)
    (f : (k : USize) → k.toNat < len.toNat → UInt8 → β → UInt8 × β)
    (h : start.toNat + len.toNat ≤ a.size) : UInt8Array × β :=
  foldInPlace.loop len f start.toNat len.toNat a h (Nat.le_refl _) 0 init

public theorem size_foldInPlace_loop {β : Type v} (len' : USize)
    (f : (k : USize) → k.toNat < len'.toNat → UInt8 → β → UInt8 × β) (start len : Nat)
    (a : UInt8Array) (h : start + len ≤ a.size) (hlen : len ≤ len'.toNat) (k : Nat) (b : β) :
    (foldInPlace.loop len' f start len a h hlen k b).1.size = a.size := by
  induction a, h, k, b using foldInPlace.loop.induct len' f start len hlen with
  | case1 a h k b hk p ih =>
    rw [foldInPlace.loop]
    simp only [hk, ↓reduceDIte]
    rw [ih]
    simp
  | case2 a h k b hk =>
    rw [foldInPlace.loop]
    simp [hk]

@[simp] public theorem size_foldInPlace {β : Type v} (a : UInt8Array) (start len : USize)
    (init : β) (f : (k : USize) → k.toNat < len.toNat → UInt8 → β → UInt8 × β)
    (h : start.toNat + len.toNat ≤ a.size) :
    (a.foldInPlace start len init f h).1.size = a.size :=
  size_foldInPlace_loop len f _ _ a h _ 0 init

@[specialize]
private unsafe def foldInPlaceThenImpl {β : Type v} {γ : Type w} (a : UInt8Array)
    (start len : USize) (init : β)
    (f : (k : USize) → k.toNat < len.toNat → UInt8 → β → UInt8 × β)
    (g : UInt8Array → β → γ) (_ : start.toNat + len.toNat ≤ a.size) : γ :=
  loop (ensureExclusiveUnsafe a) 0 init
where
  @[specialize] loop (a : UInt8Array) (k : USize) (b : β) : γ :=
    if k < len then
      let p := f k lcProof (a.uget (start + k) lcProof) b
      loop (setUnsafe a (start + k) p.1) (k + 1) p.2
    else
      g a b

/--
`foldInPlace` followed by `g` on the new array and the last accumulator, which the loop calls
itself where `foldInPlace` returns them as a pair. The pair is a heap object, allocated once per
call, which shows when the fold runs over short ranges many times; when `g` consumes the
accumulator, for example by writing it into the array, no pair is allocated at all.
`foldInPlace` is the case `g := Prod.mk`.
-/
@[implemented_by foldInPlaceThenImpl, expose]
public def foldInPlaceThen {β : Type v} {γ : Type w} (a : UInt8Array) (start len : USize)
    (init : β) (f : (k : USize) → k.toNat < len.toNat → UInt8 → β → UInt8 × β)
    (g : UInt8Array → β → γ) (h : start.toNat + len.toNat ≤ a.size) : γ :=
  g (a.foldInPlace start len init f h).1 (a.foldInPlace start len init f h).2

@[simp] public theorem foldInPlaceThen_eq {β : Type v} {γ : Type w} (a : UInt8Array)
    (start len : USize) (init : β)
    (f : (k : USize) → k.toNat < len.toNat → UInt8 → β → UInt8 × β)
    (g : UInt8Array → β → γ) (h : start.toNat + len.toNat ≤ a.size) :
    a.foldInPlaceThen start len init f g h =
      g (a.foldInPlace start len init f h).1 (a.foldInPlace start len init f h).2 :=
  rfl

/-! ## Writing through slices -/

namespace Slice

/--
Replaces the element at index `i` of the slice, counted from the start of the slice, in the
underlying array. The array is updated in place when neither it nor the slice is shared, so a slice
taken from an array that is no longer used writes into that array. `s.array` gives back the whole
array afterwards.
-/
@[inline, expose]
public def set (s : UInt8Array.Slice) (i : Nat) (v : UInt8)
    (h : i < s.size := by get_elem_tactic) : UInt8Array.Slice :=
  ⟨{ s.internalRepresentation with
      array := s.array.set (s.start + i) v
        (by have := s.stop_le_array_size; rw [size_eq] at h; lia)
      stop_le_array_size := by rw [size_set]; exact s.stop_le_array_size }⟩

@[simp] public theorem array_set (s : UInt8Array.Slice) (i : Nat) (v : UInt8) (h) :
    (s.set i v h).array =
      s.array.set (s.start + i) v (by have := s.stop_le_array_size; rw [size_eq] at h; lia) :=
  rfl

@[simp] public theorem start_set (s : UInt8Array.Slice) (i : Nat) (v : UInt8) (h) :
    (s.set i v h).start = s.start := rfl

@[simp] public theorem stop_set (s : UInt8Array.Slice) (i : Nat) (v : UInt8) (h) :
    (s.set i v h).stop = s.stop := rfl

@[simp] public theorem size_set (s : UInt8Array.Slice) (i : Nat) (v : UInt8) (h) :
    (s.set i v h).size = s.size := rfl

@[simp] public theorem getElem_set (s : UInt8Array.Slice) (i : Nat) (v : UInt8) (h) (j : Nat)
    (hj) :
    (s.set i v h)[j]'hj = if i = j then v else s[j]'(by rw [size_set] at hj; exact hj) := by
  simp only [getElem_eq, array_set, UInt8Array.getElem_set, start_set]
  congr 1
  simp

@[simp] public theorem copy_set (s : UInt8Array.Slice) (i : Nat) (v : UInt8) (h) :
    (s.set i v h).copy = s.copy.set i v (by simpa using h) := by
  apply ext_getElem
  · simp
  · intro j _ _
    simp only [getElem_copy, getElem_set, UInt8Array.getElem_set]

/--
Replaces the element at index `i` of the slice in the underlying array, like `set`. If `i` is out of
bounds, the slice is returned unmodified.
-/
@[inline, expose]
public def set! (s : UInt8Array.Slice) (i : Nat) (v : UInt8) : UInt8Array.Slice :=
  if h : i < s.size then s.set i v h else s

public theorem set!_eq (s : UInt8Array.Slice) (i : Nat) (v : UInt8) :
    s.set! i v = if h : i < s.size then s.set i v h else s := rfl

@[simp] public theorem set!_eq_set (s : UInt8Array.Slice) (i : Nat) (v : UInt8)
    (h : i < s.size) : s.set! i v = s.set i v h := by
  simp [set!, h]

/--
Applies `f` to the element at index `i` of the slice, in place like `set`. If `i` is out of bounds,
the slice is returned unmodified.
-/
@[inline, expose]
public def modify (s : UInt8Array.Slice) (i : Nat) (f : UInt8 → UInt8) : UInt8Array.Slice :=
  if h : i < s.size then s.set i (f s[i]) h else s

public theorem modify_eq (s : UInt8Array.Slice) (i : Nat) (f : UInt8 → UInt8) :
    s.modify i f = if h : i < s.size then s.set i (f s[i]) h else s := rfl

@[simp] public theorem start_modify (s : UInt8Array.Slice) (i : Nat) (f : UInt8 → UInt8) :
    (s.modify i f).start = s.start := by
  unfold modify; split <;> rfl

@[simp] public theorem stop_modify (s : UInt8Array.Slice) (i : Nat) (f : UInt8 → UInt8) :
    (s.modify i f).stop = s.stop := by
  unfold modify; split <;> rfl

@[simp] public theorem size_modify (s : UInt8Array.Slice) (i : Nat) (f : UInt8 → UInt8) :
    (s.modify i f).size = s.size := by
  unfold modify; split <;> rfl

@[simp] public theorem getElem_modify (s : UInt8Array.Slice) (i : Nat) (f : UInt8 → UInt8)
    (j : Nat) (hj) :
    (s.modify i f)[j]'hj =
      have hj' : j < s.size := by rw [size_modify] at hj; exact hj
      if i = j then f s[j] else s[j] := by
  have := size_modify s i f
  by_cases h : i < s.size
  · have e : s.modify i f = s.set i (f s[i]) h := by simp [modify_eq, h]
    rw [getElem_congr_coll e, getElem_set]
    split
    · subst_vars; rfl
    · rfl
  · have e : s.modify i f = s := by simp [modify_eq, h]
    rw [getElem_congr_coll e]
    split
    · lia
    · rfl

/-- Swaps the elements at indices `i` and `j` of the slice, in place like `set`. -/
@[inline, expose]
public def swap (s : UInt8Array.Slice) (i j : Nat) (hi : i < s.size := by get_elem_tactic)
    (hj : j < s.size := by get_elem_tactic) : UInt8Array.Slice :=
  -- Both reads come before the first write, so that `s` is no longer used when it is written.
  let x := s[i]
  let y := s[j]
  (s.set i y hi).set j x (by simpa using hj)

public theorem swap_eq (s : UInt8Array.Slice) (i j : Nat) (hi hj) :
    s.swap i j hi hj = (s.set i s[j] hi).set j s[i] (by simpa using hj) := rfl

@[simp] public theorem start_swap (s : UInt8Array.Slice) (i j : Nat) (hi hj) :
    (s.swap i j hi hj).start = s.start := rfl

@[simp] public theorem stop_swap (s : UInt8Array.Slice) (i j : Nat) (hi hj) :
    (s.swap i j hi hj).stop = s.stop := rfl

@[simp] public theorem size_swap (s : UInt8Array.Slice) (i j : Nat) (hi hj) :
    (s.swap i j hi hj).size = s.size := rfl

@[simp] public theorem getElem_swap (s : UInt8Array.Slice) (i j : Nat) (hi hj) (k : Nat) (hk) :
    (s.swap i j hi hj)[k]'hk =
      if j = k then s[i] else if i = k then s[j] else s[k]'(by rw [size_swap] at hk; exact hk) := by
  rw [getElem_congr_coll (swap_eq ..), getElem_set, getElem_set]

/-- The loop of `reverse`: swaps the elements at `i` and `j`, then moves both towards the middle. -/
@[expose]
public def reverse.loop (s : UInt8Array.Slice) (i j : Nat) (hj : j < s.size) :
    UInt8Array.Slice :=
  if h : i < j then reverse.loop (s.swap i j (by lia)) (i + 1) (j - 1) (by simp; lia) else s
termination_by j - i

private unsafe def reverseImpl (s : UInt8Array.Slice) : UInt8Array.Slice :=
  match s with
  | ⟨⟨a, start, stop, h, _⟩⟩ =>
    if start < stop then
      ⟨⟨loop (ensureExclusiveUnsafe a) start.toUSize (stop.toUSize - 1), start, stop, h, lcProof⟩⟩
    else
      s
where
  loop (a : UInt8Array) (i j : USize) : UInt8Array :=
    if i < j then
      let x := a.uget i lcProof
      let y := a.uget j lcProof
      loop (setUnsafe (setUnsafe a i y) j x) (i + 1) (j - 1)
    else
      a

/--
Reverses the order of the elements of the slice, in place like `set`. The array is made exclusive
once, before the loop, which then stores without checks.
-/
@[implemented_by reverseImpl, expose]
public def reverse (s : UInt8Array.Slice) : UInt8Array.Slice :=
  if h : 0 < s.size then reverse.loop s 0 (s.size - 1) (by lia) else s

private theorem reverse_loop_props (s : UInt8Array.Slice) (i j : Nat) (hj : j < s.size) :
    (reverse.loop s i j hj).start = s.start ∧ (reverse.loop s i j hj).stop = s.stop := by
  fun_induction reverse.loop s i j hj with
  | case1 s i j hj h ih => simpa using ih
  | case2 => exact ⟨rfl, rfl⟩

@[simp] public theorem start_reverse (s : UInt8Array.Slice) : s.reverse.start = s.start := by
  rw [reverse]; split
  · exact (reverse_loop_props ..).1
  · rfl

@[simp] public theorem stop_reverse (s : UInt8Array.Slice) : s.reverse.stop = s.stop := by
  rw [reverse]; split
  · exact (reverse_loop_props ..).2
  · rfl

@[simp] public theorem size_reverse (s : UInt8Array.Slice) : s.reverse.size = s.size := by
  rw [size_eq, size_eq, start_reverse, stop_reverse]

private theorem size_reverse_loop (s : UInt8Array.Slice) (i j : Nat) (hj : j < s.size) :
    (reverse.loop s i j hj).size = s.size := by
  rw [size_eq, size_eq, (reverse_loop_props ..).1, (reverse_loop_props ..).2]

private theorem getElem_reverse_loop (s : UInt8Array.Slice) (i j : Nat) (hj : j < s.size)
    (hij : i ≤ j + 1) (k : Nat) (hk : k < s.size) :
    (reverse.loop s i j hj)[k]'(by rw [size_reverse_loop]; exact hk) =
      if h : i ≤ k ∧ k ≤ j then s[i + j - k]'(by lia) else s[k] := by
  fun_induction reverse.loop s i j hj with
  | case1 s i j hj h ih =>
    have e : reverse.loop s i j hj =
        reverse.loop (s.swap i j (by lia)) (i + 1) (j - 1) (by simp; lia) := by
      rw [reverse.loop]; simp [h]
    rw [getElem_congr_coll e, ih (by lia) (by simpa using hk)]
    simp only [getElem_swap]
    repeat' split
    all_goals first | lia | rfl | (congr 1; lia)
  | case2 s i j hj h =>
    have e : reverse.loop s i j hj = s := by rw [reverse.loop]; simp [h]
    rw [getElem_congr_coll e]
    split
    · congr 1; lia
    · rfl

@[simp] public theorem getElem_reverse (s : UInt8Array.Slice) (i : Nat) (h) :
    s.reverse[i]'h = s[s.size - 1 - i]'(by simp at h; lia) := by
  have h' : i < s.size := by simpa using h
  have hs : 0 < s.size := by lia
  simp only [reverse, hs, ↓reduceDIte]
  rw [getElem_reverse_loop _ _ _ _ (by lia) _ h']
  simp only [Nat.zero_le, true_and, Nat.zero_add]
  split <;> (try congr 1) <;> lia

@[simp] public theorem toList_copy_reverse (s : UInt8Array.Slice) :
    s.reverse.copy.toList = s.copy.toList.reverse := by
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    simp only [getElem_toList, getElem_copy, getElem_reverse, List.getElem_reverse]
    congr 1
    simp

/-- The loop of `foldlInPlace`, over `Nat` indices. -/
@[expose]
public def foldlInPlace.loop {β : Type v} (n : Nat)
    (f : (k : USize) → k.toNat < n → UInt8 → β → UInt8 × β)
    (s : UInt8Array.Slice) (hs : s.size = n) (k : Nat) (b : β) : UInt8Array.Slice × β :=
  if hk : k < n then
    have hk' : k.toUSize.toNat < n := by
      rw [Nat.toUSize_eq, USize.toNat_ofNat']
      exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) hk
    let p := f k.toUSize hk' (s[k]'(by lia)) b
    foldlInPlace.loop n f (s.set k p.1 (by lia)) (by simpa using hs) (k + 1) p.2
  else
    (s, b)
termination_by n - k

@[specialize]
private unsafe def foldlInPlaceImpl {β : Type v} (s : UInt8Array.Slice) (init : β)
    (f : (k : USize) → k.toNat < s.size → UInt8 → β → UInt8 × β) : UInt8Array.Slice × β :=
  match s with
  | ⟨⟨a, start, stop, h, _⟩⟩ =>
    UInt8Array.foldInPlaceThenImpl a start.toUSize (stop - start).toUSize init
      (fun k _ => f k lcProof)
      (fun a b => (⟨⟨a, start, stop, h, lcProof⟩⟩, b)) lcProof

/--
Replaces each element of the slice while threading an accumulator, in place like `set`: for each
`k < s.size`, from `0` up, the element `x` at index `k` of the slice becomes the first component of
`f k hk x b`, whose second component is the next accumulator. Returns the new slice and the last
accumulator.

This is `UInt8Array.foldInPlace` on the slice's range: the array is made exclusive once, before
the loop, which then stores without checks.
-/
@[implemented_by foldlInPlaceImpl, expose]
public def foldlInPlace {β : Type v} (s : UInt8Array.Slice) (init : β)
    (f : (k : USize) → k.toNat < s.size → UInt8 → β → UInt8 × β) : UInt8Array.Slice × β :=
  foldlInPlace.loop s.size f s rfl 0 init

private theorem foldlInPlace_loop_props {β : Type v} (n : Nat)
    (f : (k : USize) → k.toNat < n → UInt8 → β → UInt8 × β)
    (s : UInt8Array.Slice) (hs : s.size = n) (k : Nat) (b : β) :
    (foldlInPlace.loop n f s hs k b).1.start = s.start ∧
      (foldlInPlace.loop n f s hs k b).1.stop = s.stop := by
  fun_induction foldlInPlace.loop n f s hs k b with
  | case1 s hs k b hk hk' p ih => simpa using ih
  | case2 => exact ⟨rfl, rfl⟩

@[simp] public theorem start_foldlInPlace {β : Type v} (s : UInt8Array.Slice) (init : β)
    (f : (k : USize) → k.toNat < s.size → UInt8 → β → UInt8 × β) :
    (s.foldlInPlace init f).1.start = s.start :=
  (foldlInPlace_loop_props ..).1

@[simp] public theorem stop_foldlInPlace {β : Type v} (s : UInt8Array.Slice) (init : β)
    (f : (k : USize) → k.toNat < s.size → UInt8 → β → UInt8 × β) :
    (s.foldlInPlace init f).1.stop = s.stop :=
  (foldlInPlace_loop_props ..).2

@[simp] public theorem size_foldlInPlace {β : Type v} (s : UInt8Array.Slice) (init : β)
    (f : (k : USize) → k.toNat < s.size → UInt8 → β → UInt8 × β) :
    (s.foldlInPlace init f).1.size = s.size := by
  rw [size_eq, size_eq, start_foldlInPlace, stop_foldlInPlace]

/-- The loop of `foldrInPlace`, over `Nat` indices, from `k - 1` down to `0`. -/
@[expose]
public def foldrInPlace.loop {β : Type v} (n : Nat)
    (f : (k : USize) → k.toNat < n → UInt8 → β → UInt8 × β)
    (s : UInt8Array.Slice) (hs : s.size = n) : (k : Nat) → k ≤ n → β → UInt8Array.Slice × β
  | 0, _, b => (s, b)
  | k + 1, hk, b =>
    have hk' : k.toUSize.toNat < n := by
      rw [Nat.toUSize_eq, USize.toNat_ofNat']
      exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) hk
    let p := f k.toUSize hk' (s[k]'(by lia)) b
    foldrInPlace.loop n f (s.set k p.1 (by lia)) (by simpa using hs) k (by lia) p.2

@[specialize]
private unsafe def foldrInPlaceImpl.loop {β : Type v} {γ : Type w} (base : USize)
    (f : (k : USize) → UInt8 → β → UInt8 × β) (g : UInt8Array → β → γ) (a : UInt8Array)
    (k : USize) (b : β) : γ :=
  if 0 < k then
    let k := k - 1
    let p := f k (a.uget (base + k) lcProof) b
    foldrInPlaceImpl.loop base f g (setUnsafe a (base + k) p.1) k p.2
  else
    g a b

@[specialize]
private unsafe def foldrInPlaceImpl {β : Type v} (s : UInt8Array.Slice) (init : β)
    (f : (k : USize) → k.toNat < s.size → UInt8 → β → UInt8 × β) : UInt8Array.Slice × β :=
  match s with
  | ⟨⟨a, start, stop, h, _⟩⟩ =>
    foldrInPlaceImpl.loop start.toUSize (fun k => f k lcProof)
      (fun a b => (⟨⟨a, start, stop, h, lcProof⟩⟩, b))
      (ensureExclusiveUnsafe a) (stop - start).toUSize init

/--
Replaces each element of the slice while threading an accumulator, like `foldlInPlace` but from
the last element to the first: for each `k < s.size`, from `s.size - 1` down to `0`, the element
`x` at index `k` of the slice becomes the first component of `f k hk x b`, whose second component
is the next accumulator. Returns the new slice and the last accumulator.

The array is made exclusive once, before the loop, which then stores without checks.
-/
@[implemented_by foldrInPlaceImpl, expose]
public def foldrInPlace {β : Type v} (s : UInt8Array.Slice) (init : β)
    (f : (k : USize) → k.toNat < s.size → UInt8 → β → UInt8 × β) : UInt8Array.Slice × β :=
  foldrInPlace.loop s.size f s rfl s.size (Nat.le_refl _) init

private theorem foldrInPlace_loop_props {β : Type v} (n : Nat)
    (f : (k : USize) → k.toNat < n → UInt8 → β → UInt8 × β)
    (s : UInt8Array.Slice) (hs : s.size = n) (k : Nat) (hk : k ≤ n) (b : β) :
    (foldrInPlace.loop n f s hs k hk b).1.start = s.start ∧
      (foldrInPlace.loop n f s hs k hk b).1.stop = s.stop := by
  induction k generalizing s b with
  | zero => exact ⟨rfl, rfl⟩
  | succ k ih =>
    rw [foldrInPlace.loop]
    obtain ⟨h₁, h₂⟩ := ih ..
    exact ⟨h₁, h₂⟩

@[simp] public theorem start_foldrInPlace {β : Type v} (s : UInt8Array.Slice) (init : β)
    (f : (k : USize) → k.toNat < s.size → UInt8 → β → UInt8 × β) :
    (s.foldrInPlace init f).1.start = s.start :=
  (foldrInPlace_loop_props ..).1

@[simp] public theorem stop_foldrInPlace {β : Type v} (s : UInt8Array.Slice) (init : β)
    (f : (k : USize) → k.toNat < s.size → UInt8 → β → UInt8 × β) :
    (s.foldrInPlace init f).1.stop = s.stop :=
  (foldrInPlace_loop_props ..).2

@[simp] public theorem size_foldrInPlace {β : Type v} (s : UInt8Array.Slice) (init : β)
    (f : (k : USize) → k.toNat < s.size → UInt8 → β → UInt8 × β) :
    (s.foldrInPlace init f).1.size = s.size := by
  rw [size_eq, size_eq, start_foldrInPlace, stop_foldrInPlace]

@[specialize]
private unsafe def foldlInPlaceThenImpl {β : Type v} {γ : Type w} (s : UInt8Array.Slice)
    (init : β) (f : (k : USize) → k.toNat < s.size → UInt8 → β → UInt8 × β)
    (g : UInt8Array.Slice → β → γ) : γ :=
  match s with
  | ⟨⟨a, start, stop, h, _⟩⟩ =>
    UInt8Array.foldInPlaceThenImpl a start.toUSize (stop - start).toUSize init
      (fun k _ => f k lcProof)
      (fun a b => g ⟨⟨a, start, stop, h, lcProof⟩⟩ b) lcProof

/--
`foldlInPlace` followed by `g` on the new slice and the last accumulator, which the loop calls
itself where `foldlInPlace` returns them as a pair, like `UInt8Array.foldInPlaceThen`. When `g`
consumes the accumulator, for example by writing it into the slice, no pair is allocated.
`foldlInPlace` is the case `g := Prod.mk`.
-/
@[implemented_by foldlInPlaceThenImpl, expose]
public def foldlInPlaceThen {β : Type v} {γ : Type w} (s : UInt8Array.Slice) (init : β)
    (f : (k : USize) → k.toNat < s.size → UInt8 → β → UInt8 × β)
    (g : UInt8Array.Slice → β → γ) : γ :=
  g (s.foldlInPlace init f).1 (s.foldlInPlace init f).2

@[simp] public theorem foldlInPlaceThen_eq {β : Type v} {γ : Type w} (s : UInt8Array.Slice)
    (init : β) (f : (k : USize) → k.toNat < s.size → UInt8 → β → UInt8 × β)
    (g : UInt8Array.Slice → β → γ) :
    s.foldlInPlaceThen init f g = g (s.foldlInPlace init f).1 (s.foldlInPlace init f).2 :=
  rfl

@[specialize]
private unsafe def foldrInPlaceThenImpl {β : Type v} {γ : Type w} (s : UInt8Array.Slice)
    (init : β) (f : (k : USize) → k.toNat < s.size → UInt8 → β → UInt8 × β)
    (g : UInt8Array.Slice → β → γ) : γ :=
  match s with
  | ⟨⟨a, start, stop, h, _⟩⟩ =>
    foldrInPlaceImpl.loop start.toUSize (fun k => f k lcProof)
      (fun a b => g ⟨⟨a, start, stop, h, lcProof⟩⟩ b)
      (ensureExclusiveUnsafe a) (stop - start).toUSize init

/--
`foldrInPlace` followed by `g` on the new slice and the last accumulator, which the loop calls
itself where `foldrInPlace` returns them as a pair. When `g` consumes the accumulator, no pair is
allocated. `foldrInPlace` is the case `g := Prod.mk`.
-/
@[implemented_by foldrInPlaceThenImpl, expose]
public def foldrInPlaceThen {β : Type v} {γ : Type w} (s : UInt8Array.Slice) (init : β)
    (f : (k : USize) → k.toNat < s.size → UInt8 → β → UInt8 × β)
    (g : UInt8Array.Slice → β → γ) : γ :=
  g (s.foldrInPlace init f).1 (s.foldrInPlace init f).2

@[simp] public theorem foldrInPlaceThen_eq {β : Type v} {γ : Type w} (s : UInt8Array.Slice)
    (init : β) (f : (k : USize) → k.toNat < s.size → UInt8 → β → UInt8 × β)
    (g : UInt8Array.Slice → β → γ) :
    s.foldrInPlaceThen init f g = g (s.foldrInPlace init f).1 (s.foldrInPlace init f).2 :=
  rfl

end Slice

/-! ### Decidable membership and slice hashing -/

public theorem contains_iff_mem {a : UInt8Array} {x : UInt8} :
    a.contains x = true ↔ x ∈ a := by
  simp only [contains, Array.contains_iff_mem, mem_data]

private def decMemImpl (x : UInt8) (a : UInt8Array) : Decidable (x ∈ a) :=
  decidable_of_iff _ contains_iff_mem

/--
Decides membership with `contains`. Logically it decides membership in `a.toList`, so that `decide`
can evaluate it.
-/
@[implemented_by decMemImpl, expose]
public def decMem (x : UInt8) (a : UInt8Array) : Decidable (x ∈ a) :=
  decidable_of_iff _ mem_toList

public instance (x : UInt8) (a : UInt8Array) : Decidable (x ∈ a) := decMem x a

@[simp] public theorem contains_eq_mem {a : UInt8Array} {x : UInt8} :
    a.contains x = decide (x ∈ a) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, contains_iff_mem]

public theorem Slice.contains_iff_mem {s : UInt8Array.Slice} {x : UInt8} :
    s.contains x = true ↔ x ∈ s := by
  simp

private def Slice.decMemImpl (x : UInt8) (s : UInt8Array.Slice) : Decidable (x ∈ s) :=
  decidable_of_iff _ Slice.contains_iff_mem

/--
Decides membership with `contains`. Logically it decides membership in `s.copy.toList`, so that
`decide` can evaluate it.
-/
@[implemented_by Slice.decMemImpl, expose]
public def Slice.decMem (x : UInt8) (s : UInt8Array.Slice) : Decidable (x ∈ s) :=
  decidable_of_iff (x ∈ s.copy.toList) (by simp)

public instance (x : UInt8) (s : UInt8Array.Slice) : Decidable (x ∈ s) := Slice.decMem x s

private def Slice.hashImpl (s : UInt8Array.Slice) : UInt64 :=
  s.foldl (fun r x => mixHash r (Hashable.hash x)) 7

/-- The same hash as `s.copy`, so slices with the same elements have the same hash. -/
@[implemented_by Slice.hashImpl]
public def Slice.hash (s : UInt8Array.Slice) : UInt64 :=
  Hashable.hash s.copy

public instance : Hashable UInt8Array.Slice := ⟨Slice.hash⟩

public theorem Slice.hash_eq_hash_copy (s : UInt8Array.Slice) :
    Hashable.hash s = Hashable.hash s.copy := by
  rfl

public theorem Slice.beq_iff_copy_eq {s t : UInt8Array.Slice} :
    (s == t) = true ↔ s.copy = t.copy := by
  simp

public instance : EquivBEq UInt8Array.Slice where
  rfl := by simp
  symm h := by simp_all
  trans h₁ h₂ := by simp_all

public instance : LawfulHashable UInt8Array.Slice where
  hash_eq s t h := by
    rw [Slice.hash_eq_hash_copy, Slice.hash_eq_hash_copy, Slice.beq_iff_copy_eq.mp h]

/-! ### End of the part left out of the float types -/

end UInt8Array

end ScalarArray

/-- The array with the elements of `l`. -/
@[inline, expose]
public def List.toUInt8Array (l : List UInt8) : ScalarArray.UInt8Array :=
  ScalarArray.UInt8Array.ofList l
