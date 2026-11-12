/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public meta import Lean.Elab.Term
public meta import Lean.Elab.Tactic
import ScalarArray.Internal

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
* `let mut x := e` or `let mut x : t := e` declares a mutable variable, and `x := e` assigns it,
  or `(x, y) := e` for a pattern of mutable variables. As in `do` notation, a `let` can't shadow
  a mutable variable.
* `have h : t := p` adds a fact to the context, for the bounds of later indices.
* `if c then … else …` and `if h : c then … else …` run one of two blocks, which may read, write,
  loop and assign mutable variables. The `else` block is optional, and `unless c do …` is
  `if ¬c then …`.
* `match e with | p => … | q => …` runs the block of the first pattern that `e` matches, and
  `match e, f with | p, q => …` matches several terms.
* `for j in lo...hi do …` loops over `lo ≤ j < hi` upward, and `for j in reverse lo...hi do …`
  over the same range downward, from `hi - 1` to `lo`. The bounds are `USize`s, and the ranges are
  those of core: `lo...hi` and `lo...<hi`, `lo...=hi` (up to `hi`), `lo<...hi` and `lo<...=hi`
  (from `lo + 1`), and `*...hi` and `*...=hi` (from `0`). `lo.toNat ≤ j.toNat` and
  `j.toNat < hi.toNat` are in context in the body, or `j.toNat ≤ hi.toNat` and
  `lo.toNat < j.toNat` for the other ranges, which need `hi.toNat + 1 < USize.size` and
  `lo.toNat + 1 < USize.size`, proved like the bounds of indices. `for j in lo...hi by s do …` runs
  over `lo`, `lo + s`, … below `hi`, for `s > 0`, and `reverse` runs over the same indices
  downward.
* An optional `with (x := init) …` clause names the loop's variables, as `(x : t := init)` with
  their types: up to four, which the loop keeps as separate unboxed arguments. They are mutable in
  the body, and they hold their last values after the loop. Loops nest, and a nested loop
  allocates nothing either.
* `while c do …` and `while h : c do …` loop while `c` holds, with a `with` clause like `for`. The
  condition runs, with its reads, before each step. A `while` loop stops after `USize.size - 1`
  steps at the most.
* `break` leaves the innermost loop, and its variables keep their current values after it.
  `continue` goes on with the loop's next step.
* `return e` ends the program with the result `e`, anywhere, even in a loop. Without it, the result
  is `()`. Nothing in a block can follow a `return`, a `break` or a `continue`.

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
is the `then` continuation or makes the pair. Its statements expand to the tail programs `readThen`,
`writeThen`, `ite`, `dite` and the loops `Tail.forIn`, `Tail.forIn2`, … and `Tail.forInRev`, …, in
continuation-passing style: a loop body ends by calling `next` on the loop's variables, which runs
the next step, and the loop ends by calling the rest of the program, so the variables are arguments
of both and stay unboxed. `continue` calls `next`, and `break` calls the rest of the program, which
a loop that `break`s binds to a local function. A nested loop ends by calling the outer loop's
`next`, so the two compile to mutually recursive loops with no allocation, and the program compiles
to the same loops as a hand-written one. The rest of the program after an `if` becomes a local
function of the mutable variables, which the compiler turns into a join point: an `if` in a loop
allocates nothing.

## Bounds

The bound of each index is proved by the tactic `inplace_bound`, from the hypotheses in context:

* for an index `off + j` in a loop over `j < len`, from a window hypothesis
  `off.toNat + len.toNat ≤ a.size`;
* otherwise by `lia`;
* otherwise, for indices with `USize` arithmetic such as `j - 17` or `2 * j + 1`, by `grind`, which
  splits on the platform width `System.Platform.numBits` (see the `grind_pattern` in
  `ScalarArray.Internal`), so the proof holds on both widths.

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
* A loop has at most four variables.
* A block has at least one statement.
* A program makes the array exclusive before it runs, even when it only reads, so a shared array
  is copied. For a computation that only reads, use plain reads `a[i]`, `foldl` or the folds of
  slices, which don't copy.
* `have` takes a name: `have h : t := p`.
-/

namespace ScalarArray.InPlaceSyntax

/-- The index `off + j` of a window of `len` elements at `off` is in bounds, for `j < len`. -/
public theorem toNat_add_lt_of_window {n : Nat} {off len j : USize}
    (hw : off.toNat + len.toNat ≤ n) (hj : j.toNat < len.toNat) : (off + j).toNat < n := by
  grind

/--
The number of steps of the range `lo...hi` by `s`, for `s > 0`: of the indices `lo + s * k` below
`hi`.
-/
@[inline, expose]
public def stepCount (lo hi s : USize) : USize :=
  if lo < hi then (hi - lo - 1) / s + 1 else 0

private theorem step_toNat {lo hi s k : USize} (hk : k.toNat < (stepCount lo hi s).toNat) :
    (lo + s * k).toNat = lo.toNat + s.toNat * k.toNat ∧
      lo.toNat + s.toNat * k.toNat < hi.toNat := by
  unfold stepCount at hk
  split at hk
  · rename_i h
    have hlt : lo.toNat < hi.toNat := h
    have hd : (hi - lo - 1).toNat = hi.toNat - lo.toNat - 1 := by grind
    have hq : ((hi - lo - 1) / s).toNat = (hi.toNat - lo.toNat - 1) / s.toNat := by
      rw [USize.toNat_div, hd]
    have := Nat.div_le_self (hi.toNat - lo.toNat - 1) s.toNat
    have hq1 : ((hi - lo - 1) / s + 1).toNat = (hi.toNat - lo.toNat - 1) / s.toNat + 1 := by
      grind
    rw [hq1] at hk
    have hk' : k.toNat ≤ (hi.toNat - lo.toNat - 1) / s.toNat := by lia
    have hsk : s.toNat * k.toNat ≤ hi.toNat - lo.toNat - 1 :=
      Nat.le_trans (Nat.mul_le_mul_left _ hk') (Nat.mul_div_le _ _)
    refine ⟨?_, by lia⟩
    grind
  · simp at hk

/--
`f k`. The notation `inplace` writes a loop that may `break` as `withExit (fun brk => loop) k`, with
the rest `k` of the program after the loop, which `break` calls: elaborated as the arguments of
`withExit`, the loop comes first and fixes the type of `k`.
-/
@[inline, expose]
public def withExit {α : Sort u} {β : Sort v} (f : α → β) (k : α) : β := f k

/-- The index `lo + s * k` of the step `k` of `lo...hi` by `s` is at least `lo`. -/
public theorem step_le {lo hi s k : USize} (hk : k.toNat < (stepCount lo hi s).toNat) :
    lo.toNat ≤ (lo + s * k).toNat := by
  rw [(step_toNat hk).1]; lia

/-- The index `lo + s * k` of the step `k` of `lo...hi` by `s` is below `hi`. -/
public theorem step_lt {lo hi s k : USize} (hk : k.toNat < (stepCount lo hi s).toNat) :
    (lo + s * k).toNat < hi.toNat := by
  rw [(step_toNat hk).1]; exact (step_toNat hk).2

/--
The index of a loop over `lo...hi + 1`, which is `lo...=hi`, is at most `hi`. The proof doesn't need
`hi + 1` not to wrap around, but the loop does, so the notation passes that fact here too.
-/
public theorem le_of_lt_succ {hi j : USize} (_h : hi.toNat + 1 < USize.size)
    (hj : j.toNat < (hi + 1).toNat) : j.toNat ≤ hi.toNat := by
  grind

/-- The index of a loop over `lo + 1...hi`, which is `lo<...hi`, is above `lo`. -/
public theorem lt_of_succ_le {lo j : USize} (h : lo.toNat + 1 < USize.size)
    (hj : (lo + 1).toNat ≤ j.toNat) : lo.toNat < j.toNat := by
  grind

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

/--
Proves the bound `i.toNat < n` of an index in an `inplace` program: for `i = off + j`, from a
window hypothesis `off.toNat + len.toNat ≤ n` and the loop bound `j.toNat < len.toNat`, or else by
`lia` from the hypotheses in context, or else by `grind`, for `USize` arithmetic that may wrap
around. Conjunctions in context are split first.
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
        | grind))

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
syntax inplaceSeq := sepBy1IndentSemicolon(inplaceStmt)

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
/-- `(x, y) := e` assigns the mutable variables of the pattern `(x, y)`. -/
syntax (priority := low) term:max " := " term : inplaceStmt
/-- `if c then … else …` runs one of two blocks. -/
syntax "if " (atomic(ident " : "))? term " then" inplaceSeq (" else" inplaceSeq)? : inplaceStmt
/-- `unless c do …` runs the block if `c` doesn't hold. -/
syntax "unless " termBeforeDo " do" inplaceSeq : inplaceStmt
/-- The variables of a loop, `with (x := init) (y : t := init) …`. -/
syntax inplaceLoopVars := " with" (ppSpace "(" ident (" : " term)? " := " term ")")+
/--
A loop over `j` in a range such as `lo...hi` or `reverse lo...hi`, by steps of `s` with `by s`, with
the variables of its `with` clause.
-/
syntax (name := inplaceFor) "for " ident " in " (&"reverse ")? termBeforeDo (" by " termBeforeDo)?
  (inplaceLoopVars)? " do" inplaceSeq : inplaceStmt
/-- A loop that runs while `c` holds, with the variables of its `with` clause. -/
syntax (name := inplaceWhile) "while " (atomic(ident " : "))? termBeforeDo (inplaceLoopVars)?
  " do" inplaceSeq : inplaceStmt
/-- `break` leaves the innermost loop, with the current values of its variables. -/
syntax (name := inplaceBreak) "break" : inplaceStmt
/-- `continue` goes on with the next step of the innermost loop. -/
syntax (name := inplaceContinue) "continue" : inplaceStmt
/-- An alternative `| p => …` of a `match` statement. -/
syntax inplaceMatchAlt := ppDedent(ppLine) "| " sepBy1(term, ", ") " => " inplaceSeq
/-- `match e with | p => … | q => …` runs the block of the first pattern that `e` matches. -/
syntax (name := inplaceMatch) "match " sepBy1(term, ", ") " with" (inplaceMatchAlt)+ : inplaceStmt
/-- `return e` ends the program with the result `e`. -/
syntax "return " term : inplaceStmt

/--
`inplace a do …` is the in-place program on `a` that the statements describe, run on `a`: it
returns the program's result and the new array, or, with `then k`, `k` on them and the new array's
size. See the module documentation of `ScalarArray.InPlaceSyntax`.
-/
syntax (name := inplaceTerm) "inplace " termBeforeDo " do" inplaceSeq
  (ppDedent(ppLine) "then " term)? : term

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

/-- The variables of the pattern `stx`: its identifiers with atomic names. -/
private partial def patternVars (stx : Syntax) : Array Ident :=
  match stx with
  | .ident _ _ id _ => if id.isAtomic && !id.isAnonymous then #[⟨stx⟩] else #[]
  | .node _ _ args => args.flatMap patternVars
  | _ => #[]

/-- Checks that the variables bound by a `let` don't shadow the mutable variables `mvars`. -/
private def checkNoShadow (mvars : Array Ident) (xs : Array Ident) : MacroM Unit :=
  for x in xs do
    if mvars.any (·.getId == x.getId) then
      Macro.throwErrorAt x s!"mutable variable `{x.getId}` cannot be shadowed: assign it with \
        `{x.getId} := e`, or in a pattern, as in `({x.getId}, y) := e`"

/-- A fresh identifier named `n`. -/
private def fresh (n : Name) : MacroM Ident :=
  withFreshMacroScope do return mkIdent (← Macro.addMacroScope n)

/-- `f xs`, or `f ()` without variables. -/
private def call (f : Ident) (xs : Array Ident) : MacroM Term :=
  if xs.isEmpty then `($f ()) else `($f $xs*)

/-- The loop body `fun j hlo hj next xs => body`, or `fun j hlo hj next _ => body`. -/
private def lam (j hlo hj next : Ident) (xs : Array Ident) (body : Term) : MacroM Term :=
  if xs.isEmpty then `(fun $j $hlo $hj $next _ => $body) else
    `(fun $j $hlo $hj $next $xs* => $body)

/-- The variables of a `with` clause and their initial values, with their types. -/
private def loopVars (vars : Option (TSyntax ``inplaceLoopVars)) :
    MacroM (Array Ident × Array Term) := do
  let some vars := vars | return (#[], #[])
  let `(inplaceLoopVars| with $[($xs $[: $ts]? := $is)]*) := vars | Macro.throwUnsupported
  let inits ← (is.zip ts).mapM fun
    | (init, some ty) => `(($init : $ty))
    | (init, none) => pure init
  return (xs, inits)

/-- The loop function, `.forIn`, `.forIn2`, … or `.forInRev`, …, for `n` variables. -/
private def loopFn (rev : Bool) (n : Nat) : MacroM Term :=
  match rev, n with
  | false, 0 | false, 1 => `(.forIn) | false, 2 => `(.forIn2) | false, 3 => `(.forIn3)
  | false, _ => `(.forIn4)
  | true, 0 | true, 1 => `(.forInRev) | true, 2 => `(.forInRev2) | true, 3 => `(.forInRev3)
  | true, _ => `(.forInRev4)

/-- The innermost loop of a statement: the calls that `continue` and `break` make. -/
private structure InplaceLoop where
  /-- The call of the loop's next step on its variables, which `continue` makes. -/
  next : Term
  /-- The call of the rest of the program after the loop on its variables, which `break` makes. -/
  brk : Term

/--
Whether the statement `stx`, or a statement nested in it outside of nested loops, is a `break`:
then its loop binds the rest of the program, which `break` calls.
-/
private partial def hasBreak (stx : Syntax) : Bool :=
  if stx.getKind == ``inplaceBreak then true
  else if stx.getKind == ``inplaceFor || stx.getKind == ``inplaceWhile then false
  else stx.getArgs.any hasBreak

/--
Whether the statements `stmts` never reach their end: they end with `return`, `break` or
`continue`, or with an `if` or a `match` whose blocks all never reach their ends.
-/
private partial def ends (stmts : List (TSyntax `inplaceStmt)) : Bool :=
  match stmts.getLast? with
  | none => false
  | some s => match s with
    | `(inplaceStmt| return $_) | `(inplaceStmt| break) | `(inplaceStmt| continue) => true
    | `(inplaceStmt| if $[$_ :]? $_ then $t;* else $e;*) =>
      ends t.getElems.toList && ends e.getElems.toList
    | `(inplaceStmt| match $_,* with $alts:inplaceMatchAlt*) =>
      alts.all fun
        | `(inplaceMatchAlt| | $_,* => $b;*) => ends b.getElems.toList
        | _ => false
    | _ => false

/--
The bounds `lo` and `hi` of a loop over `lo...<hi` for the range `range`, with the facts to prove
before the loop, and a function of the loop's index `j` and of the proofs `hlo` and `hj` of
`lo.toNat ≤ j.toNat` and `j.toNat < hi.toNat` that adds the bounds of `j` in the range's own terms
to a body. `lo...=hi` and `lo<...hi` loop over `lo...<hi + 1` and `lo + 1...<hi`, so they need
`hi + 1` and `lo + 1` not to wrap around.
-/
private def rangeBounds (range : Term) :
    MacroM (Term × Term × Array (Ident × Term) × (Term → Term → Term → Term → MacroM Term)) := do
  let zero ← `((0 : USize))
  let hh ← fresh `hh
  let hl ← fresh `hl
  -- The facts about `j` of the range's upper and lower bounds, after the loop's own.
  let upper (hi : Term) (j hj b : Term) : MacroM Term :=
    `(have _ : USize.toNat $j ≤ USize.toNat $hi :=
        ScalarArray.InPlaceSyntax.le_of_lt_succ $hh $hj; $b)
  let lower (lo : Term) (j hlo b : Term) : MacroM Term :=
    `(have _ : USize.toNat $lo < USize.toNat $j :=
        ScalarArray.InPlaceSyntax.lt_of_succ_le $hl $hlo; $b)
  let factHi (hi : Term) : MacroM (Ident × Term) :=
    return (hh, ← `(USize.toNat $hi + 1 < USize.size))
  let factLo (lo : Term) : MacroM (Ident × Term) :=
    return (hl, ← `(USize.toNat $lo + 1 < USize.size))
  match range with
  | `($lo...$hi) | `($lo...<$hi) => pure (lo, hi, #[], fun _ _ _ b => pure b)
  | `(*...$hi) | `(*...<$hi) => pure (zero, hi, #[], fun _ _ _ b => pure b)
  | `($lo...=$hi) => pure (lo, ← `($hi + 1), #[← factHi hi], fun j _ hj b => upper hi j hj b)
  | `(*...=$hi) => pure (zero, ← `($hi + 1), #[← factHi hi], fun j _ hj b => upper hi j hj b)
  | `($lo<...$hi) | `($lo<...<$hi) =>
    pure (← `($lo + 1), hi, #[← factLo lo], fun j hlo _ b => lower lo j hlo b)
  | `($lo<...=$hi) =>
    pure (← `($lo + 1), ← `($hi + 1), #[← factLo lo, ← factHi hi], fun j hlo hj b => do
      upper hi j hj (← lower lo j hlo b))
  | _ => Macro.throwErrorAt range "expected a range such as `lo...hi`, `lo...=hi`, `lo<...hi` or \
      `*...hi`"

mutual

/--
The program of the statements `stmts` on the array `p.arr`, ending with `ret`, where `mvars` are the
mutable variables in scope, `loop` is the innermost loop, and `return e` ends the whole program
with `ending e`.
-/
private partial def expandSeq (p : Arr) (ending : Term → MacroM Term) (mvars : Array Ident)
    (loop : Option InplaceLoop) (ret : Term) : List (TSyntax `inplaceStmt) → MacroM Term
  | [] => pure ret
  | s :: rest => withRef s do
    let isEnd := match s with
      | `(inplaceStmt| return $_) | `(inplaceStmt| break) | `(inplaceStmt| continue) => true
      | _ => false
    if isEnd then
      if let some s' := rest.head? then
        Macro.throwErrorAt s' "this statement is unreachable: it follows a `return`, `break` or \
          `continue`"
    match s with
    | `(inplaceStmt| return $_) =>
      lifting p s fun s => do
        let `(inplaceStmt| return $e) := s | Macro.throwUnsupported
        ending e
    | `(inplaceStmt| break) =>
      let some l := loop | Macro.throwError "`break` is only allowed in a loop"
      pure l.brk
    | `(inplaceStmt| continue) =>
      let some l := loop | Macro.throwError "`continue` is only allowed in a loop"
      pure l.next
    -- The condition of a `while` runs at each step, so its reads are lifted inside the loop.
    | `(inplaceStmt| while $[$_ :]? $_ $[$_:inplaceLoopVars]? do $_;*) =>
      expandStmt p ending mvars loop ret ⟨← replaceArray p true s⟩ rest
    | _ => lifting p s fun s => expandStmt p ending mvars loop ret s rest

/-- The program of the statement `s` followed by `rest`. -/
private partial def expandStmt (p : Arr) (ending : Term → MacroM Term) (mvars : Array Ident)
    (loop : Option InplaceLoop) (ret : Term) (s : TSyntax `inplaceStmt)
    (rest : List (TSyntax `inplaceStmt)) : MacroM Term := do
  let arr := p.arr
  let k (mvars : Array Ident) := expandSeq p ending mvars loop ret rest
  match s with
  | `(inplaceStmt| let $x:ident ← $a:ident[$i]) =>
    checkArray arr a
    checkNoShadow mvars #[x]
    `(.readThen $i $(← bound p) fun $x => $(← k mvars))
  | `(inplaceStmt| $a:ident[$i] := $v) =>
    checkArray arr a
    `(.writeThen $i $(← bound p) $v $(← k mvars))
  | `(inplaceStmt| let mut $x:ident $[: $ty]? := $e) =>
    match ty with
    | some ty => `(let $x:ident : $ty := $e; $(← k (mvars.push x)))
    | none => `(let $x:ident := $e; $(← k (mvars.push x)))
  | `(inplaceStmt| let $x:ident : $ty := $e) =>
    checkNoShadow mvars #[x]
    `(let $x:ident : $ty := $e; $(← k mvars))
  | `(inplaceStmt| let $x:ident ← $m) =>
    if let `($b:ident[$_]) := m then checkArray arr b
    checkNoShadow mvars #[x]
    `(.bind $m fun $x => $(← k mvars))
  | `(inplaceStmt| let $p := $e) =>
    checkNoShadow mvars (patternVars p)
    `(match $e:term with | $p:term => $(← k mvars))
  | `(inplaceStmt| have $h:ident : $t := $p) =>
    `(have $h:ident : $t := $p; $(← k mvars))
  | `(inplaceStmt| $x:ident := $e) =>
    unless mvars.any (·.getId == x.getId) do
      Macro.throwErrorAt x s!"`{x.getId}` is not a mutable variable here: declare it with \
        `let mut`, or carry it into the loop with `with ({x.getId} := {x.getId})`"
    `(let $x:ident := $e; $(← k mvars))
  | `(inplaceStmt| $q:term := $e) =>
    for x in patternVars q do
      unless mvars.any (·.getId == x.getId) do
        Macro.throwErrorAt x s!"`{x.getId}` is not a mutable variable here: declare it with \
          `let mut`, or carry it into the loop with `with ({x.getId} := {x.getId})`"
    `(match $e:term with | $q:term => $(← k mvars))
  | `(inplaceStmt| if $[$h :]? $c then $t;* $[else $e;*]?) =>
    expandBranches p ending mvars loop (k mvars) rest
      [t.getElems.toList, (e.map (·.getElems.toList)).getD []] fun bs => match h with
        | some h => `(.dite $c (fun $h => $(bs[0]!)) (fun $h => $(bs[1]!)))
        | none => `(.ite $c $(bs[0]!) $(bs[1]!))
  | `(inplaceStmt| unless $c do $t;*) =>
    expandBranches p ending mvars loop (k mvars) rest [t.getElems.toList, []] fun bs =>
      `(.ite $c $(bs[1]!) $(bs[0]!))
  | `(inplaceStmt| match $ds,* with $alts:inplaceMatchAlt*) =>
    let alts ← alts.mapM fun
      | `(inplaceMatchAlt| | $ps,* => $b;*) => pure (ps, b.getElems.toList)
      | _ => Macro.throwUnsupported
    for (ps, _) in alts do
      checkNoShadow mvars (ps.getElems.flatMap fun p => patternVars p)
    expandBranches p ending mvars loop (k mvars) rest (alts.toList.map (·.2)) fun bs => do
      -- Several discriminants are matched as one tuple.
      let tuple (xs : Array Term) : MacroM Term :=
        if h : xs.size = 1 then pure xs[0] else `(($(xs[0]!), $(xs.extract 1),*))
      let d ← tuple ds.getElems
      let ps ← alts.mapM fun (ps, _) => tuple ps.getElems
      `(match $d:term with $[| $ps => $bs]*)
  | `(inplaceStmt| for $j in $[reverse%$rev]? $range $[by $step]? $[$vars:inplaceLoopVars]?
      do $b;*) =>
    let (lo, hi, facts, more) ← rangeBounds range
    let (xs, inits) ← loopVars vars
    let b := b.getElems.toList
    let (lo', hi') ← match step with
      | none => pure (lo, hi)
      | some step => pure (← `((0 : USize)), ← `(ScalarArray.InPlaceSyntax.stepCount $lo $hi $step))
    let mkBody (next : Ident) (_ : Term) (body : Term) : MacroM Term := do
      let hlo ← fresh `hlo
      let hj ← fresh `hj
      let body ← more j hlo hj body
      match step with
      | none => lam j hlo hj next xs body
      | some step =>
        -- The loop runs over the steps `k`, for the indices `j = lo + step * k`.
        let kk ← fresh `k
        let hk ← fresh `hk
        let body ← `((fun ($j : USize) ($hlo : USize.toNat $lo ≤ USize.toNat $j)
            ($hj : USize.toNat $j < USize.toNat $hi) => $body) ($lo + $step * $kk)
          (ScalarArray.InPlaceSyntax.step_le $hk) (ScalarArray.InPlaceSyntax.step_lt $hk))
        lam kk (← fresh `_hk0) hk next xs body
    let f ← loopFn rev.isSome xs.size
    let brk := hasBreak (mkNullNode (b.toArray.map (·.raw)))
    let prog ← expandLoop p ending (k (mvars ++ xs)) xs b brk
      mkBody fun body k =>
        if xs.isEmpty then `($f $lo' $hi' () $body $k) else `($f $lo' $hi' $inits* $body $k)
    let prog ← match step with
      | none => pure prog
      | some step => `(have _ : 0 < USize.toNat $step := (by inplace_bound); $prog)
    facts.foldrM (init := prog) fun (h, t) prog => `(have $h : $t := (by inplace_bound); $prog)
  | `(inplaceStmt| while $[$h :]? $c $[$vars:inplaceLoopVars]? do $b;*) =>
    let (xs, inits) ← loopVars vars
    let b := b.getElems.toList
    -- A `while` loop is a loop over at most `USize.size - 1` steps that the body leaves when `c`
    -- fails: it runs the condition, with its reads, at each step.
    let (c, reads) ← (liftReads p.arr false c).run #[]
    let c : Term := ⟨c⟩
    let f ← loopFn false xs.size
    expandLoop p ending (k (mvars ++ xs)) xs b true
      (fun next brk body => do
        let step ← match h with
          | some h => `(.dite $c (fun $h => $body) (fun _ => $brk))
          | none => `(.ite $c $body $brk)
        let step ← withReads p reads step
        lam (← fresh `_i) (← fresh `_hlo)
          (← fresh `_hj) next xs step)
      fun body k =>
        if xs.isEmpty then `($f 0 ((0 : USize) - 1) () $body $k) else
          `($f 0 ((0 : USize) - 1) $inits* $body $k)
  | _ => Macro.throwUnsupported

/--
The program of a loop over the variables `xs` with the body `b`, followed by `rest`:
`mkBody next brk body` is the loop's body for the program `body` of a step, where `brk` is the call
that leaves the loop, and `mkLoop body k` is the loop with the body `body` and the rest `k`. When
`brk` holds, the body may leave the loop, and the rest is bound to a local function, which `break`
calls.
-/
private partial def expandLoop (p : Arr) (ending : Term → MacroM Term) (rest : MacroM Term)
    (xs : Array Ident) (b : List (TSyntax `inplaceStmt)) (brk : Bool)
    (mkBody : Ident → Term → Term → MacroM Term) (mkLoop : Term → Term → MacroM Term) :
    MacroM Term := do
  if xs.size > 4 then Macro.throwError "a loop has at most four variables"
  -- The body ends by calling `next` on the loop's variables, which runs the next step, and the
  -- loop ends by calling the rest of the program itself: the variables are arguments of both,
  -- so they stay unboxed, and a nested loop ends by calling the outer `next`.
  let next ← fresh `next
  let brkFn ← fresh `brk
  let callNext ← call next xs
  let callBrk ← call brkFn xs
  let body ← expandSeq p ending xs (some { next := callNext, brk := callBrk }) callNext b
  let body ← mkBody next callBrk body
  let rest ← rest
  let restFn ← if xs.isEmpty then `(fun _ => $rest) else `(fun $xs* => $rest)
  -- `withExit` elaborates the loop before the rest, so that the loop fixes the type of the rest.
  if brk then `(ScalarArray.InPlaceSyntax.withExit (fun $brkFn => $(← mkLoop body brkFn)) $restFn)
  else mkLoop body restFn

/--
The program of a statement with the blocks `bs`, such as an `if` or a `match`, followed by the rest
`rest` of the program: `mk` makes the statement from the programs of the blocks. The rest becomes a
local function of the mutable variables, which the blocks call, unless the statement is the last
of its block: then the blocks end as the block does.
-/
private partial def expandBranches (p : Arr) (ending : Term → MacroM Term) (mvars : Array Ident)
    (loop : Option InplaceLoop) (rest : MacroM Term) (restStmts : List (TSyntax `inplaceStmt))
    (bs : List (List (TSyntax `inplaceStmt))) (mk : Array Term → MacroM Term) : MacroM Term := do
  if restStmts.isEmpty then
    let rest ← rest
    return ← mk (← bs.toArray.mapM fun b => expandSeq p ending mvars loop rest b)
  if bs.all ends then
    Macro.throwErrorAt restStmts.head! "this statement is unreachable: every block of the \
      statement before it ends with `return`, `break` or `continue`"
  -- The rest of the program, as a function of the mutable variables.
  let kont ← fresh `kont
  let callK ← call kont mvars
  let branch ← mk (← bs.toArray.mapM fun b => expandSeq p ending mvars loop callK b)
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
    let prog ← expandSeq p ending #[] none (← ending (← `(()))) stmts.getElems.toList
    -- They are bound by a function application, not by `let`, which fails to elaborate when the
    -- program has metavariables left for later, such as the types of loop variables.
    `((fun ($size : Nat) ($p.hsize : ($a).size = $size) ($p.usize : USize)
          (_ : ($p.usize).toNat ≤ ($a).size) => ($a).runInPlaceThenOf $size $p.hsize $prog)
        ($a).size rfl ($a).usize ($a).toNat_usize_le)
  | `(inplace $e do $_;* $[then $_]?) =>
    Lean.Macro.throwErrorAt e "`inplace` needs the array as a local variable: bind it first, as \
      in `let a := e; inplace a do …`"
