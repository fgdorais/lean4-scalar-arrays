/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public meta import Lean.Elab.Term
public meta import Lean.Elab.Tactic

/-!
# Notation for in-place programs

Experimental: the root module `ScalarArray` doesn't import this one.

`inplace a do …` writes an in-place program (`XArray.InPlace`) on the array `a` in a small
imperative language, and runs it, which returns the program's result and the new array, or hands
them to a continuation `then k`. It works for all 13 array types:

```
inplace a do
  for j in 0...len with (c := 0) (b := 0) do
    let u ← a[xs + j]
    let v ← a[ys + j]
    let (s, c') := addc u v c
    let (d, b') := subb u v b
    a[xs + j] := s
    a[ts + j] := d
    c := c'
    b := b'
  return (c, b)
```

## Statements

* `let x ← a[i]` reads the element at the `USize` index `i`. In the terms of a statement, `a[i]`
  also reads the current element, before the statement runs: `a[i] := a[i] + 1`. So a read can't
  be under a binder, or in a branch of a term (`if`, `match`, or the right side of `&&`, `||`,
  `∧` and `∨`), which would run later or not at all: read it first with `let x ← a[i]`, or branch
  with an `if` statement.
* `a[i] := e` writes `e` at `i`.
* `let x ← m` runs an in-place program `m : XArray.InPlace n α`, for the program's size `n`, and
  binds its result, so that programs compose.
* `let p := e` binds a pure value, where `p` can be a pattern such as `(s, c)`, and
  `let x : t := e` one of type `t`.
* `let mut x := e` or `let mut x : t := e` declares a mutable variable, and `x := e` assigns it.
* `have h : t := p` adds a fact to the context, for the bounds of later indices.
* `if c then … else …` and `if h : c then … else …` run one of two blocks, which may read, write,
  loop and assign mutable variables. The `else` block is optional, and `unless c do …` is
  `if ¬c then …`.
* `for j in lo...hi do …` loops over `lo ≤ j < hi` upward, and `for j in reverse lo...hi do …`
  over the same range downward, from `hi - 1` to `lo`. The bounds are `USize`s; `lo...<hi` and
  `*...hi` (from `0`) work too, and `lo.toNat ≤ j.toNat` and `j.toNat < hi.toNat` are in context
  in the body. An optional `with (x := init) …` clause names the loop's variables, as
  `(x : t := init)` with their types: up to four, which the loop keeps as separate unboxed
  arguments. They are mutable in the body, and they hold their last values after the loop. Loops
  nest, and a nested loop allocates nothing either.
* `return e`, last, gives the program's result, and so may `return` in both branches of the
  program's last `if`. Without it, the result is `()`.

A loop body can assign only its own variables: to update a variable across a loop, carry it, as
`with (c := c)`.

## Results

`inplace a do …` returns the pair of the program's result and the new array. With `then k` after
the statements, it is `k x a' h` instead, for the result `x`, the new array `a'` and
`h : a'.size = a.size`:

```
inplace a do
  for j in 0...len with (c := 0) (b := 0) do
    …
  return (c, b)
then fun (c, b) a' h => g c b a' h
```

The program calls `k` where it ends, inside its last loop if it ends with one, so the result goes
into no pair, and scalars such as the carries above reach `k` unboxed. `h` lets `k` run another
program on `a'` with the bounds proved for `a`.

## Compilation

The program expands to a tail program (`XArray.InPlace.Tail`) on arrays of size `n`, run with
`a.runInPlaceThenOf n h`, where `n` and `a.usize` are bound to variables before the program runs,
and the program uses them in place of `a.size` and `a.usize`. So nothing in the compiled program
refers to `a`, which the compiler would otherwise keep alive past the point where the program makes
the array exclusive, and the array would be copied. The program ends with `Tail.done x k`, where `k`
is the `then` continuation or makes the pair. Its statements expand to the tail programs
`readThen`, `writeThen`, `ite`, `dite` and the loops `Tail.forIn`, `Tail.forIn2`, … and
`Tail.forInRev`, …, in continuation-passing style: a loop body ends by calling `next` on the loop's
variables, which runs the next step, and the loop ends by calling the rest of the program, so the
variables are arguments of both and stay unboxed. A nested loop ends by calling the outer loop's
`next`, so the two compile to mutually recursive loops with no allocation, and the program compiles
to the same loops as a hand-written one. The rest of the program after an `if` becomes a local function of
the mutable variables, which the compiler turns into a join point: an `if` in a loop allocates
nothing.

## Bounds

The bound of each index is proved by the tactic `inplace_bound`, from the hypotheses in context:

* for an index `off + j` in a loop over `j < len`, from a window hypothesis
  `off.toNat + len.toNat ≤ a.size`;
* otherwise by `lia`;
* otherwise, for indices with `USize` arithmetic such as `j - 17` or `2 * j + 1`, by `lia` after
  unfolding `+`, `-`, `*` and literals of `USize`, with the bound `x.toNat < USize.size` of each
  `USize` in the goal and the wrap-around facts of each `x % USize.size`. The modulus stays
  symbolic, so the proof holds on both platform widths.

It looks inside conjunctions. A loop body has both bounds of its index, `lo.toNat ≤ j.toNat` and
`j.toNat < hi.toNat`, in context, and the program has `a.usize.toNat ≤ a.size`, so `a.usize`
works as a loop bound with no other hypothesis. A bound that needs more is given by a `have`
before the index, or by a hypothesis around the program, and a bound that `inplace_bound` can't
prove is reported with its goal. For example, in this left shift of 64-bit limbs by
1111 bits:

```
if h : 18 ≤ a.size then
  (inplace a do
    for j in reverse 18...a.usize do
      a[j] := (a[j - 17] <<< 23) ||| (a[j - 18] >>> 41)
    a[17] := a[0] <<< 23
    for j in 0...17 do
      a[j] := 0).2
else UInt64Array.mk (Array.replicate a.size 0)
```

## Limits

* `a` is a local variable: the program's array. `let x ← b[i]` and `b[i] := e` on another array
  `b` are errors, while `b[i]` in a term is ordinary indexing of `b`, with its own bound.
* Inside the program, `a` is the array before the program runs, so it is an error outside of the
  reads `a[i]` and its size `a.size` or `a.usize`: `a[i]!`, `a[i]'h` or `a.toArray` would read old
  elements, and keep the old array alive, which copies it. A `have` and the proofs in `by` blocks
  may use `a`, and so may `then k`, which runs after the program, but `k` keeps the old array alive
  if it uses more than its size.
* Reads in terms are written `a[i]`, not `(← a[i])`.
* A loop has at most four variables, and its range is `lo...hi`, `lo...<hi`, `*...hi` or `*...<hi`.
* `have` takes a name: `have h : t := p`.
-/

namespace ScalarArray.InPlaceSyntax

/-- The index `off + j` of a window of `len` elements at `off` is in bounds, for `j < len`. -/
public theorem toNat_add_lt_of_window {n : Nat} {off len j : USize}
    (hw : off.toNat + len.toNat ≤ n) (hj : j.toNat < len.toNat) : (off + j).toNat < n := by
  rw [USize.toNat_add]
  exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (by lia)

/-- `x % m = x - m` for `m ≤ x < 2 * m`: the wrap-around of a `USize` subtraction or addition. -/
public theorem mod_eq_sub_of_le_of_lt {x m : Nat} (h₁ : m ≤ x) (h₂ : x < 2 * m) :
    x % m = x - m := by
  rw [Nat.mod_eq_sub_mod h₁, Nat.mod_eq_of_lt (by lia)]

/-- The platform word has at least 32 bits. -/
public theorem two_pow_32_le_size : 2 ^ 32 ≤ 2 ^ System.Platform.numBits := by
  rcases System.Platform.numBits_eq with h | h <;> rw [h] <;> decide

end ScalarArray.InPlaceSyntax

public meta section

open Lean Meta in
/--
Adds the conjuncts of the conjunctions in the context of `g` to its context, recursively. It adds
them as new hypotheses, rather than with `cases`, which would revert and reintroduce the
hypotheses after them, and fails on the `let` variables of an `inplace` program.
-/
def splitAnds (g : MVarId) : MetaM MVarId := do
  let mut g := g
  let mut todo : Array FVarId := #[]
  for d in ← g.withContext getLCtx do
    if !d.isImplementationDetail then todo := todo.push d.fvarId
  while !todo.isEmpty do
    let h := todo.back!
    todo := todo.pop
    let (g', xs) ← g.withContext do
      let t ← whnfR (← instantiateMVars (← h.getType))
      if !t.isAppOfArity ``And 2 then return (g, #[])
      let mut g := g
      let mut xs := #[]
      for (i, ty) in [(0, t.appFn!.appArg!), (1, t.appArg!)] do
        let (x, g') ← (← g.assert `hand ty (mkProj ``And i (.fvar h))).intro1P
        g := g'
        xs := xs.push x
      return (g, xs)
    g := g'
    todo := todo ++ xs
  return g

/-- Splits the conjunctions in context, recursively. -/
syntax (name := inplaceSplit) "inplace_split" : tactic

open Lean Elab Tactic in
/-- Elaborates `inplace_split`. -/
@[tactic inplaceSplit] def evalInplaceSplit : Tactic := fun _ =>
  liftMetaTactic fun g => return [← splitAnds g]

open Lean Meta in
/-- Adds `x.toNat < USize.size` to the context of `g` for each `x.toNat` in its goal or context. -/
def addUSizeBounds (g : MVarId) : MetaM MVarId := g.withContext do
  let atoms ← IO.mkRef (#[] : Array Expr)
  let mut types := #[← instantiateMVars (← g.getType)]
  for d in ← getLCtx do
    if !d.isImplementationDetail then types := types.push (← instantiateMVars d.type)
  for t in types do
    t.forEachWhere (fun e => e.isAppOfArity ``USize.toNat 1 && !e.hasLooseBVars) fun e =>
      atoms.modify fun xs => if xs.contains e.appArg! then xs else xs.push e.appArg!
  let mut g := g
  for x in ← atoms.get do
    let h ← mkAppM ``USize.toNat_lt_size #[x]
    let (_, g') ← (← g.assert `hsize (← inferType h) h).intro1P
    g := g'
  return g

/-- Adds `x.toNat < USize.size` to the context for each `x.toNat` in the goal or context. -/
syntax (name := inplaceUSizeBounds) "inplace_usize_bounds" : tactic

open Lean Elab Tactic in
/-- Elaborates `inplace_usize_bounds`. -/
@[tactic inplaceUSizeBounds] def evalInplaceUSizeBounds : Tactic := fun _ =>
  liftMetaTactic fun g => return [← addUSizeBounds g]

open Lean Meta in
/--
Adds, for each `x % m` on `Nat` in the goal or context of `g`, the facts `x % m ≤ x`,
`x < m → x % m = x` and `m ≤ x → x < 2 * m → x % m = x - m`, which let `lia` reason about
the wrap-around of `USize` arithmetic without dividing by the modulus.
-/
def addModFacts (g : MVarId) : MetaM MVarId := g.withContext do
  let mods ← IO.mkRef (#[] : Array (Expr × Expr))
  let mut types := #[← instantiateMVars (← g.getType)]
  for d in ← getLCtx do
    if !d.isImplementationDetail then types := types.push (← instantiateMVars d.type)
  let nat := mkConst ``Nat
  for t in types do
    t.forEachWhere (fun e => e.isAppOfArity ``HMod.hMod 6 && e.getArg! 0 == nat &&
        !e.hasLooseBVars) fun e =>
      mods.modify fun xs =>
        let p := (e.getArg! 4, e.getArg! 5)
        if xs.contains p then xs else xs.push p
  let mut g := g
  for (x, m) in ← mods.get do
    for h in [← mkAppM ``Nat.mod_le #[x, m], ← mkAppOptM ``Nat.mod_eq_of_lt #[x, m],
        ← mkAppOptM ``ScalarArray.InPlaceSyntax.mod_eq_sub_of_le_of_lt #[x, m]] do
      let (_, g') ← (← g.assert `hmod (← inferType h) h).intro1P
      g := g'
  return g

/-- Adds the facts of `addModFacts` for each `x % m` on `Nat` in the goal or context. -/
syntax (name := inplaceModFacts) "inplace_mod_facts" : tactic

open Lean Elab Tactic in
/-- Elaborates `inplace_mod_facts`. -/
@[tactic inplaceModFacts] def evalInplaceModFacts : Tactic := fun _ =>
  liftMetaTactic fun g => return [← addModFacts g]

/--
Proves the bound `i.toNat < n` of an index in an `inplace` program: for `i = off + j`, from a
window hypothesis `off.toNat + len.toNat ≤ n` and the loop bound `j.toNat < len.toNat`, or else by
`lia` from the hypotheses in context, or else by `lia` after unfolding the `USize` arithmetic of
the index and of the hypotheses (`+`, `-`, `*` and literals), with the bound of each `USize` and
the wrap-around facts of each `x % USize.size` (see `inplace_mod_facts`). Conjunctions in context
are split first.
-/
syntax (name := inplaceBound) "inplace_bound" : tactic

/-- The proof search of `inplace_bound`, which fails with the errors of its last attempt. -/
syntax (name := inplaceBoundCore) "inplace_bound_core" : tactic

macro_rules
  | `(tactic| inplace_bound_core) => `(tactic| (
      inplace_split
      first
        | (refine ScalarArray.InPlaceSyntax.toNat_add_lt_of_window (len := ?len) ?hw ?hj
           case hj => assumption
           case hw => assumption)
        | assumption
        | lia
        | (inplace_usize_bounds
           have := ScalarArray.InPlaceSyntax.two_pow_32_le_size
           simp only [USize.toNat_add, USize.toNat_sub, USize.toNat_mul, USize.reduceToNat,
             USize.size] at *
           inplace_mod_facts
           lia)))

open Lean Elab Tactic Meta in
/-- Elaborates `inplace_bound`: runs its proof search, and reports a failure with the bound. -/
@[tactic inplaceBound] def evalInplaceBound : Tactic := fun _ => do
  let g ← getMainGoal
  try evalTactic (← `(tactic| inplace_bound_core))
  catch _ =>
    let t ← instantiateMVars (← g.getType)
    throwError m!"inplace: cannot prove the bound of this index from the hypotheses in context:"
      ++ indentExpr t ++ m!"\nAdd the missing fact with a `have` before the statement, or as a \
        hypothesis around the program."

/-- A statement of an `inplace` program. -/
declare_syntax_cat inplaceStmt

/-- A sequence of statements of an `inplace` program. -/
syntax inplaceSeq := sepByIndentSemicolon(inplaceStmt)

/-- `let x ← a[i]` reads the element of `a` at `i`. -/
syntax "let " ident " ← " ident "[" term "]" : inplaceStmt
/-- `a[i] := e` writes `e` at `i`. -/
syntax ident "[" term "]" " := " term : inplaceStmt
/--
`let x ← m` runs the in-place program `m` (an `XArray.InPlace n α`, for the program's size `n`)
and binds its result to `x`.
-/
syntax (priority := low) "let " ident " ← " term : inplaceStmt
/-- `let mut x := e` declares the mutable variable `x`, and `let mut x : t := e` gives its type. -/
syntax "let " "mut " ident (" : " term)? " := " term : inplaceStmt
/-- `let x : t := e` binds the value of the pure term `e` of type `t` to `x`. -/
syntax "let " ident " : " term " := " term : inplaceStmt
/-- `let p := e` binds the value of the pure term `e` to the pattern `p`. -/
syntax "let " term " := " term : inplaceStmt
/-- `have h : t := p` adds the fact `h` to the context, for the bounds of later indices. -/
syntax "have " ident " : " term " := " term : inplaceStmt
/-- `x := e` assigns the mutable variable `x`. -/
syntax ident " := " term : inplaceStmt
/-- `if c then … else …` runs one of two blocks. -/
syntax "if " (atomic(ident " : "))? term " then" inplaceSeq (" else" inplaceSeq)? : inplaceStmt
/-- `unless c do …` runs the block if `c` doesn't hold. -/
syntax "unless " termBeforeDo " do" inplaceSeq : inplaceStmt
/-- A loop over `j` in `lo...hi` or `reverse lo...hi`, with the variables of its `with` clause. -/
syntax "for " ident " in " (&"reverse ")? termBeforeDo
  (" with" (ppSpace "(" ident (" : " term)? " := " term ")")+)? " do" inplaceSeq : inplaceStmt
/-- `return e` gives the program's result. -/
syntax "return " term : inplaceStmt

/--
`inplace a do …` is the in-place program on `a` that the statements describe, run on `a`: it
returns the program's result and the new array, or, with `then k`, `k` on them and the new array's
size. See the module documentation of `ScalarArray.InPlaceSyntax`.
-/
syntax (name := inplaceTerm) "inplace " ident " do" inplaceSeq (ppDedent(ppLine) "then " term)? :
  term

open Lean

/--
The program's array `arr`, and the variables bound to its size `arr.size` and `arr.usize` before
the program runs, which the program uses in their place, with the proof `hsize : arr.size = size`.
-/
private structure Arr where
  /-- The program's array. -/
  arr : Ident
  /-- The variable bound to `arr.size`. -/
  size : Ident
  /-- The variable bound to `arr.usize`. -/
  usize : Ident
  /-- The proof of `arr.size = size`. -/
  hsize : Ident

/-- Checks that a read or a write is on the program's array. -/
private def checkArray (arr a : Ident) : MacroM Unit :=
  unless arr.getId == a.getId do
    Macro.throwErrorAt a
      s!"an `inplace` program on `{arr.getId}` reads and writes only `{arr.getId}`"

/--
Replaces `a.size` and `a.usize` in the terms of `stx` by the variables bound to them before the
program, for the program's array `a`, so that the program doesn't keep `a` alive, and, if `strict`,
rejects every other use of `a` outside of a read `a[i]`: inside the program, `a` is the array before
the program runs.
-/
private partial def replaceArray (p : Arr) (strict : Bool) (stx : Syntax) : MacroM Syntax := do
  let a := p.arr.getId
  if let `($b:ident[$i]) := stx then
    if b.getId == a then
      return ← `($b:ident[$(⟨← replaceArray p strict i⟩)])
  match stx with
  | .ident _ _ id _ =>
    if id == a ++ `size then return p.size
    if id == a ++ `usize then return p.usize
    if strict && (id == a || id.getRoot == a && a.isAtomic) then
      Macro.throwErrorAt stx s!"inside `inplace {a} do`, `{a}` is the array before the program \
        runs: read its current elements with `{a}[i]`, at a `USize` index `i`, and its size with \
        `{a}.size` or `{a}.usize`"
    return stx
  | .node info kind args =>
    -- Nested blocks are statements of their own, and proofs run nothing.
    if kind == ``inplaceSeq || kind == ``Lean.Parser.Term.byTactic then return stx
    return .node info kind (← args.mapM (replaceArray p strict))
  | _ => return stx

/-- The operators whose right operand runs only depending on the left one. -/
private def lazyOps : List SyntaxNodeKind :=
  [`«term_&&_», `«term_||_», `«term_∧_», `«term_∨_»]

/-- The terms that bind variables, or choose what runs, in all their parts. -/
private def lazyTerms : List SyntaxNodeKind :=
  [``Lean.Parser.Term.fun, ``Lean.Parser.Term.matchAlts, ``Lean.Parser.Term.let,
    ``Lean.Parser.Term.have]

/--
Replaces the reads `a[i]` of the program's array `a` in the terms of `stx` by fresh variables, from
the inside out and left to right, and returns them with their indices, in the order to read them.
The reads run before the statement, so a read under a binder or in a branch of the statement, where
`lazy` holds, is an error: lifted out, its index could lose its variables, or its bound the branch's
condition.
-/
private partial def liftReads (arr : Ident) (lazy : Bool) (stx : Syntax) :
    StateT (Array (Ident × Term)) MacroM Syntax := do
  if let `($a:ident[$i]) := stx then
    if a.getId == arr.getId then
      if lazy then
        Macro.throwErrorAt stx s!"`inplace` reads `{arr.getId}[i]` before the statement runs, so \
          it can't read under a binder or in a branch of a term: read the element first, with \
          `let x ← {arr.getId}[i]`, or branch with an `if` statement"
      let i ← liftReads arr lazy i
      let x ← withFreshMacroScope `(x)
      modify (·.push (⟨x⟩, ⟨i⟩))
      return x
  match stx with
  | .node info kind args =>
    -- The reads of a nested block belong to its own statements, and proofs read nothing.
    if kind == ``inplaceSeq || kind == ``Lean.Parser.Term.byTactic then return stx
    let lazyFrom :=
      if lazyTerms.contains kind then 0
      else if lazyOps.contains kind then 2
      else if kind == ``termIfThenElse || kind == ``termDepIfThenElse then
        (args.findIdx? (·.isToken "then")).getD args.size
      else args.size
    return .node info kind (← args.mapIdxM fun k arg => liftReads arr (lazy || lazyFrom ≤ k) arg)
  | _ => return stx

/-- The proof of the bound of an index, `i.toNat < size`, from `i.toNat < arr.size`. -/
private def bound (p : Arr) : MacroM Term :=
  `(Nat.lt_of_lt_of_eq (by inplace_bound) $p.hsize)

/-- `k` after the reads `reads`. -/
private def withReads (p : Arr) (reads : Array (Ident × Term)) (k : Term) : MacroM Term :=
  reads.foldrM (init := k) fun (x, i) k => do `(.readThen $i $(← bound p) fun $x => $k)

/--
The terms of the statement `s` with `a.size` and `a.usize` replaced and other uses of `a` rejected,
for the program's array `a`. The array of a read or a write statement, and `have`, whose proof and
statement are about the array before the program, are left alone.
-/
private def replaceStmt (p : Arr) (s : TSyntax `inplaceStmt) : MacroM (TSyntax `inplaceStmt) := do
  match s with
  | `(inplaceStmt| let $x:ident ← $b:ident[$i]) =>
    let i : Term := ⟨← replaceArray p true i⟩
    `(inplaceStmt| let $x:ident ← $b:ident[$i])
  | `(inplaceStmt| $b:ident[$i] := $v) =>
    let i : Term := ⟨← replaceArray p true i⟩
    let v : Term := ⟨← replaceArray p true v⟩
    `(inplaceStmt| $b:ident[$i] := $v)
  | `(inplaceStmt| have $_:ident : $_ := $_) => return s
  | _ => return ⟨← replaceArray p true s⟩

/-- Runs `f` on the statement `s` with its nested reads lifted, and puts the reads before it. -/
private def lifting (p : Arr) (s : TSyntax `inplaceStmt)
    (f : TSyntax `inplaceStmt → MacroM Term) : MacroM Term := do
  -- A `have` is about the array before the program, and reads nothing.
  if let `(inplaceStmt| have $_:ident : $_ := $_) := s then return ← f s
  let (s, reads) ← (liftReads p.arr false (← replaceStmt p s)).run #[]
  withReads p reads (← f ⟨s⟩)

mutual

/--
The program of the statements `stmts` on the array `p.arr`, ending with `ret`, where `mvars` are the
mutable variables in scope and `top` says whether the statements end the whole program, where a
`return e` can end them with `ending e`.
-/
private partial def expandSeq (p : Arr) (ending : Term → MacroM Term) (mvars : Array Ident)
    (ret : Term) (top : Bool) : List (TSyntax `inplaceStmt) → MacroM Term
  | [] => pure ret
  | s :: rest => withRef s do
    if let `(inplaceStmt| return $_) := s then
      unless rest.isEmpty && top do
        Macro.throwError "`return` must be the last statement of the program, or of a branch of \
          the program's last `if`"
      return ← lifting p s fun s => do
        let `(inplaceStmt| return $e) := s | Macro.throwUnsupported
        ending e
    lifting p s fun s => expandStmt p ending mvars ret top s rest

/-- The program of the statement `s` followed by `rest`. -/
private partial def expandStmt (p : Arr) (ending : Term → MacroM Term) (mvars : Array Ident)
    (ret : Term) (top : Bool) (s : TSyntax `inplaceStmt) (rest : List (TSyntax `inplaceStmt)) :
    MacroM Term := do
  let arr := p.arr
  let k (mvars : Array Ident) := expandSeq p ending mvars ret top rest
  match s with
  | `(inplaceStmt| let $x:ident ← $a:ident[$i]) =>
    checkArray arr a
    `(.readThen $i $(← bound p) fun $x => $(← k mvars))
  | `(inplaceStmt| $a:ident[$i] := $v) =>
    checkArray arr a
    `(.writeThen $i $(← bound p) $v $(← k mvars))
  | `(inplaceStmt| let mut $x:ident $[: $ty]? := $e) =>
    match ty with
    | some ty => `(let $x:ident : $ty := $e; $(← k (mvars.push x)))
    | none => `(let $x:ident := $e; $(← k (mvars.push x)))
  | `(inplaceStmt| let $x:ident : $ty := $e) =>
    `(let $x:ident : $ty := $e; $(← k mvars))
  | `(inplaceStmt| let $x:ident ← $m) =>
    if let `($b:ident[$_]) := m then checkArray arr b
    `(.bind $m fun $x => $(← k mvars))
  | `(inplaceStmt| let $p := $e) =>
    `(match $e:term with | $p:term => $(← k mvars))
  | `(inplaceStmt| have $h:ident : $t := $p) =>
    `(have $h:ident : $t := $p; $(← k mvars))
  | `(inplaceStmt| $x:ident := $e) =>
    unless mvars.any (·.getId == x.getId) do
      Macro.throwErrorAt x s!"`{x.getId}` is not a mutable variable here: declare it with \
        `let mut`, or carry it into the loop with `with ({x.getId} := {x.getId})`"
    `(let $x:ident := $e; $(← k mvars))
  | `(inplaceStmt| if $[$h :]? $c then $t;* $[else $e;*]?) =>
    expandIf p ending mvars (k mvars) top rest.isEmpty h c t.getElems.toList
      (e.map (·.getElems.toList))
  | `(inplaceStmt| unless $c do $t;*) =>
    expandIf p ending mvars (k mvars) top rest.isEmpty none (← `(¬$c)) t.getElems.toList none
  | `(inplaceStmt| for $j in $[reverse%$rev]? $range $[with $[($xs $[: $ts]? := $is)]*]? do $b;*) =>
    let (lo, hi) ← match range with
      | `($lo...$hi) | `($lo...<$hi) => pure (lo, hi)
      | `(*...$hi) | `(*...<$hi) => pure (← `((0 : USize)), hi)
      | _ => Macro.throwErrorAt range "expected a range `lo...hi` or `*...hi`"
    let xs : Array Ident := xs.getD #[]
    let inits ← (is.getD #[]).zip (ts.getD #[]) |>.mapM fun
      | (init, some ty) => `(($init : $ty))
      | (init, none) => pure init
    if xs.size > 4 then Macro.throwError "a loop has at most four variables"
    -- The body ends by calling `next` on the loop's variables, which runs the next step, and the
    -- loop ends by calling the rest of the program itself: the variables are arguments of both,
    -- so they stay unboxed, and a nested loop ends by calling the outer `next`.
    let next ← withFreshMacroScope `(next)
    let args : Array Term := xs.map fun x => x
    let call ← if xs.isEmpty then `($next ()) else `($next $args*)
    let b ← expandSeq p ending xs call false b.getElems.toList
    let rest ← k (mvars ++ xs)
    let body ← if xs.isEmpty then `(fun $j hlo hj $next _ => $b) else
      `(fun $j hlo hj $next $xs* => $b)
    let rest ← if xs.isEmpty then `(fun _ => $rest) else `(fun $xs* => $rest)
    match rev.isSome, inits.size with
    | false, 0 => `(.forIn $lo $hi () $body $rest)
    | false, 1 => `(.forIn $lo $hi $inits* $body $rest)
    | false, 2 => `(.forIn2 $lo $hi $inits* $body $rest)
    | false, 3 => `(.forIn3 $lo $hi $inits* $body $rest)
    | false, _ => `(.forIn4 $lo $hi $inits* $body $rest)
    | true, 0 => `(.forInRev $lo $hi () $body $rest)
    | true, 1 => `(.forInRev $lo $hi $inits* $body $rest)
    | true, 2 => `(.forInRev2 $lo $hi $inits* $body $rest)
    | true, 3 => `(.forInRev3 $lo $hi $inits* $body $rest)
    | true, _ => `(.forInRev4 $lo $hi $inits* $body $rest)
  | _ => Macro.throwUnsupported

/--
The program of `if h : c then t else e` followed by the rest `rest` of the program, where `last`
says whether the `if` is the last statement, so that the branches of the program's last `if` can
end it with `return`.
-/
private partial def expandIf (p : Arr) (ending : Term → MacroM Term) (mvars : Array Ident)
    (rest : MacroM Term) (top last : Bool) (h : Option Ident) (c : Term)
    (t : List (TSyntax `inplaceStmt)) (e : Option (List (TSyntax `inplaceStmt))) :
    MacroM Term := do
  if top && last then
    -- The rest of the program is its end, which the branches can share without a function, and
    -- must, when they both `return`, since the function's type would then be unknown.
    let rest ← rest
    let t ← expandSeq p ending mvars rest true t
    let e ← match e with
      | some e => expandSeq p ending mvars rest true e
      | none => pure rest
    return ← match h with
      | some h => `(.dite $c (fun $h => $t) (fun $h => $e))
      | none => `(.ite $c $t $e)
  -- The rest of the program, as a function of the mutable variables.
  let kont ← withFreshMacroScope `(kont)
  let call ← if mvars.isEmpty then `($kont ()) else `($kont $mvars*)
  let t ← expandSeq p ending mvars call false t
  let e ← match e with
    | some e => expandSeq p ending mvars call false e
    | none => pure call
  let branch ← match h with
    | some h => `(.dite $c (fun $h => $t) (fun $h => $e))
    | none => `(.ite $c $t $e)
  let rest ← rest
  let fn ← if mvars.isEmpty then `(fun (_ : Unit) => $rest) else `(fun $mvars* => $rest)
  `((fun $kont => $branch) $fn)

end

end

macro_rules
  | `(inplace $a:ident do $stmts;* $[then $k]?) => do
    -- The program's size `n` is a variable bound before it runs, and so are `a.size` and
    -- `a.usize` in it: then nothing in the program refers to `a`, which the compiler would
    -- otherwise keep alive past `ensureExclusive`, and copy.
    let p : Arr :=
      { arr := a, size := Lean.mkIdent (← Lean.Macro.addMacroScope `n),
        usize := Lean.mkIdent (← Lean.Macro.addMacroScope `usize),
        hsize := Lean.mkIdent (← Lean.Macro.addMacroScope `hsize) }
    let size := p.size
    -- The program is a tail program, which ends by handing its result and the new array to `k`,
    -- or by returning them as a pair.
    let ending (e : Lean.Term) : Lean.MacroM Lean.Term := match k with
      | some k => do
        let k : Lean.Term := ⟨← replaceArray p false k⟩
        `(.done $e fun x a' h =>
          ($k : _ → (a'' : type_of% $a) → a''.size = ($a).size → _) x a'
            (h.trans (Eq.symm $p.hsize)))
      | none => `(.done $e fun x a' _ => (x, a'))
    let prog ← expandSeq p ending #[] (← ending (← `(()))) true stmts.getElems.toList
    -- They are bound by a function application, not by `let`, which fails to elaborate when the
    -- program has metavariables left for later, such as the types of loop variables.
    `((fun ($size : Nat) ($p.hsize : ($a).size = $size) ($p.usize : USize)
          (_ : ($p.usize).toNat ≤ ($a).size) => ($a).runInPlaceThenOf $size $p.hsize $prog)
        ($a).size rfl ($a).usize ($a).toNat_usize_le)
