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
imperative language, and runs it with `a.runInPlace`, which returns the program's result and the
new array. It works for all 13 array types:

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
  also reads the current element, before the statement runs: `a[i] := a[i] + 1`. (Outside the
  program, `a` is the array before it.)
* `a[i] := e` writes `e` at `i`.
* `let p := e` binds a pure value, where `p` can be a pattern such as `(s, c)`.
* `let mut x := e` declares a mutable variable, and `x := e` assigns it.
* `have h : t := p` adds a fact to the context, for the bounds of later indices.
* `if c then … else …` and `if h : c then … else …` run one of two blocks, which may read, write,
  loop and assign mutable variables. The `else` block is optional.
* `for j in lo...hi do …` loops over `lo ≤ j < hi` upward, and `for j in reverse 0...hi do …` over
  `j < hi` downward, from `hi - 1`. The bounds are `USize`s; `lo...<hi` and `*...hi` (from `0`)
  work too, and `j.toNat < hi.toNat` is in context in the body. An optional `with (x := init) …`
  clause names the loop's variables: up to two, which the loop keeps as separate unboxed
  arguments. They are mutable in the body, and they hold their last values after the loop. Loops
  nest.
* `return e`, last, gives the program's result. Without it, the result is `()`.

A loop body can assign only its own variables: to update a variable across a loop, carry it, as
`with (c := c)`.

## Compilation

The program expands to `readThen`, `write`, `bind`, `InPlace.ite`, `InPlace.dite` and the
`forUp`, `forUp2`, `forDown` and `forDown2` loops, so it compiles to the same loop as a hand-written
program, with the loop variables unboxed. The rest of the program after an `if` becomes a local
function of the mutable variables, which the compiler turns into a join point: an `if` in a loop
allocates nothing.

## Bounds

The bound of each index is proved by the tactic `inplace_bound`: for an index `off + j` in a loop
over `j < len`, from a hypothesis `off.toNat + len.toNat ≤ a.size` in context, or else by `lia`
from the hypotheses in context. It looks inside conjunctions.
-/

namespace ScalarArray.InPlaceSyntax

/-- The index `off + j` of a window of `len` elements at `off` is in bounds, for `j < len`. -/
public theorem toNat_add_lt_of_window {n : Nat} {off len j : USize}
    (hw : off.toNat + len.toNat ≤ n) (hj : j.toNat < len.toNat) : (off + j).toNat < n := by
  rw [USize.toNat_add]
  exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (by lia)

end ScalarArray.InPlaceSyntax

public meta section

open Lean Meta in
/-- Splits the conjunctions in the context of `g`, recursively. -/
partial def splitAnds (g : MVarId) : MetaM MVarId := g.withContext do
  for d in ← getLCtx do
    if !d.isImplementationDetail && (← instantiateMVars d.type).isAppOfArity ``And 2 then
      let #[s] ← g.cases d.fvarId | return g
      return ← splitAnds s.mvarId
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
`lia` from the hypotheses in context. Conjunctions in context are split first.
-/
syntax (name := inplaceBound) "inplace_bound" : tactic

macro_rules
  | `(tactic| inplace_bound) => `(tactic| (
      inplace_split
      first
        | (refine ScalarArray.InPlaceSyntax.toNat_add_lt_of_window (len := ?len) ?hw ?hj
           case hj => assumption
           case hw => assumption)
        | assumption
        | lia))

/-- A statement of an `inplace` program. -/
declare_syntax_cat inplaceStmt

/-- A sequence of statements of an `inplace` program. -/
syntax inplaceSeq := sepByIndentSemicolon(inplaceStmt)

/-- `let x ← a[i]` reads the element of `a` at `i`. -/
syntax "let " ident " ← " ident "[" term "]" : inplaceStmt
/-- `a[i] := e` writes `e` at `i`. -/
syntax ident "[" term "]" " := " term : inplaceStmt
/-- `let mut x := e` declares the mutable variable `x`. -/
syntax "let " "mut " ident " := " term : inplaceStmt
/-- `let p := e` binds the value of the pure term `e` to the pattern `p`. -/
syntax "let " term " := " term : inplaceStmt
/-- `have h : t := p` adds the fact `h` to the context, for the bounds of later indices. -/
syntax "have " ident " : " term " := " term : inplaceStmt
/-- `x := e` assigns the mutable variable `x`. -/
syntax ident " := " term : inplaceStmt
/-- `if c then … else …` runs one of two blocks. -/
syntax "if " (atomic(ident " : "))? term " then" inplaceSeq (" else" inplaceSeq)? : inplaceStmt
/-- A loop over `j` in `lo...hi` or `reverse 0...hi`, with the variables of its `with` clause. -/
syntax "for " ident " in " (&"reverse ")? termBeforeDo
  (" with" (ppSpace "(" ident " := " term ")")+)? " do" inplaceSeq : inplaceStmt
/-- `return e` gives the program's result. -/
syntax "return " term : inplaceStmt

/--
`inplace a do …` is the in-place program on `a` that the statements describe, run with
`a.runInPlace`. See the module documentation of `ScalarArray.InPlaceSyntax`.
-/
syntax (name := inplaceTerm) "inplace " ident " do" inplaceSeq : term

open Lean

/-- Checks that a read or a write is on the program's array. -/
private def checkArray (arr a : Ident) : MacroM Unit :=
  unless arr.getId == a.getId do
    Macro.throwErrorAt a
      s!"an `inplace` program on `{arr.getId}` reads and writes only `{arr.getId}`"

/--
Replaces the reads `a[i]` of the program's array `a` in the terms of `stx` by fresh variables, from
the inside out and left to right, and returns them with their indices, in the order to read them.
-/
private partial def liftReads (arr : Ident) (stx : Syntax) :
    StateT (Array (Ident × Term)) MacroM Syntax := do
  if let `($a:ident[$i]) := stx then
    if a.getId == arr.getId then
      let i ← liftReads arr i
      let x ← withFreshMacroScope `(x)
      modify (·.push (⟨x⟩, ⟨i⟩))
      return x
  match stx with
  | .node info kind args =>
    -- The reads of a nested block belong to its own statements, and proofs read nothing.
    if kind == ``inplaceSeq || kind == ``Lean.Parser.Term.byTactic then return stx
    return .node info kind (← args.mapM (liftReads arr))
  | _ => return stx

/-- `k` after the reads `reads`. -/
private def withReads (reads : Array (Ident × Term)) (k : Term) : MacroM Term :=
  reads.foldrM (init := k) fun (x, i) k => `(.readThen $i (by inplace_bound) fun $x => $k)

/-- Runs `f` on the statement `s` with its nested reads lifted, and puts the reads before it. -/
private def lifting (arr : Ident) (s : TSyntax `inplaceStmt)
    (f : TSyntax `inplaceStmt → MacroM Term) : MacroM Term := do
  let (s, reads) ← (liftReads arr s).run #[]
  withReads reads (← f ⟨s⟩)

/-- The tuple of the variables `xs`, or `()`. -/
private def tuple (xs : Array Ident) : MacroM Term :=
  match xs with
  | #[] => `(())
  | #[x] => pure x
  | _ => `(($(xs[0]!), $(xs[1:].toArray),*))

/-- The pattern that binds the variables `xs` from their tuple. -/
private def tuplePat (xs : Array Ident) : MacroM Term :=
  match xs with
  | #[] => `(_)
  | _ => tuple xs

mutual

/--
The program of the statements `stmts` on the array `arr`, ending with `ret`, where `mvars` are the
mutable variables in scope and `top` says whether the statements end the whole program, where a
`return` can end them.
-/
private partial def expandSeq (arr : Ident) (mvars : Array Ident) (ret : Term) (top : Bool) :
    List (TSyntax `inplaceStmt) → MacroM Term
  | [] => pure ret
  | s :: rest => withRef s do
    if let `(inplaceStmt| return $_) := s then
      unless rest.isEmpty && top do
        Macro.throwError "`return` must be the last statement of the program"
      return ← lifting arr s fun s => do
        let `(inplaceStmt| return $e) := s | Macro.throwUnsupported
        `(.pure $e)
    lifting arr s fun s => expandStmt arr mvars ret top s rest

/-- The program of the statement `s` followed by `rest`. -/
private partial def expandStmt (arr : Ident) (mvars : Array Ident) (ret : Term) (top : Bool)
    (s : TSyntax `inplaceStmt) (rest : List (TSyntax `inplaceStmt)) : MacroM Term := do
  let k (mvars : Array Ident) := expandSeq arr mvars ret top rest
  match s with
  | `(inplaceStmt| let $x:ident ← $a:ident[$i]) =>
    checkArray arr a
    `(.readThen $i (by inplace_bound) fun $x => $(← k mvars))
  | `(inplaceStmt| $a:ident[$i] := $v) =>
    checkArray arr a
    `(.bind (.write $i (by inplace_bound) $v) fun _ => $(← k mvars))
  | `(inplaceStmt| let mut $x:ident := $e) =>
    `(let $x:ident := $e; $(← k (mvars.push x)))
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
    -- The rest of the program, as a function of the mutable variables.
    let kont ← withFreshMacroScope `(kont)
    let call ← if mvars.isEmpty then `($kont ()) else `($kont $mvars*)
    let t ← expandSeq arr mvars call false t.getElems.toList
    let e ← match e with
      | some e => expandSeq arr mvars call false e.getElems.toList
      | none => pure call
    let branch ← match h with
      | some h => `(.dite $c (fun $h => $t) (fun $h => $e))
      | none => `(.ite $c $t $e)
    let rest ← k mvars
    let fn ← if mvars.isEmpty then `(fun (_ : Unit) => $rest) else `(fun $mvars* => $rest)
    `((fun $kont => $branch) $fn)
  | `(inplaceStmt| for $j in $[reverse%$rev]? $range $[with $[($xs := $inits)]*]? do $body;*) =>
    let (lo, len) ← match range with
      | `($lo...$hi) | `($lo...<$hi) => pure (some lo, hi)
      | `(*...$hi) | `(*...<$hi) => pure (none, hi)
      | _ => Macro.throwErrorAt range "expected a range `lo...hi` or `*...hi`"
    let xs := xs.getD #[]
    let inits := inits.getD #[]
    let b ← expandSeq arr xs (← `(.pure $(← tuple xs))) false body.getElems.toList
    -- The upward loop: `plain` from `0`, or `fromLo` from `lo`.
    let up (plain : Term) (fromLo : Term → Term → MacroM Term) : MacroM Term :=
      match lo with
      | some lo => fromLo len lo
      | none => pure plain
    let loop ← if rev.isSome then
        if let some lo := lo then
          unless lo.raw.isOfKind numLitKind && lo.raw.isNatLit? == some 0 do
            Macro.throwErrorAt lo "a `reverse` loop runs down to `0`: write `reverse 0...hi`"
        match xs, inits with
        | #[], #[] => `(.forDown $len () fun $j hj _ => $b)
        | #[x], #[init] => `(.forDown $len $init fun $j hj $x => $b)
        | #[x, y], #[initx, inity] => `(.forDown2 $len $initx $inity fun $j hj $x $y => $b)
        | _, _ => Macro.throwError "a loop has at most two variables"
      else
        match xs, inits with
        | #[], #[] => do
          up (← `(.forUp $len () fun $j hj _ => $b))
            fun len lo => `(.forUpFrom $len $lo () fun $j hj _ => $b)
        | #[x], #[init] => do
          up (← `(.forUp $len $init fun $j hj $x => $b))
            fun len lo => `(.forUpFrom $len $lo $init fun $j hj $x => $b)
        | #[x, y], #[initx, inity] => do
          up (← `(.forUp2 $len $initx $inity fun $j hj $x $y => $b))
            fun len lo => `(.forUp2From $len $lo $initx $inity fun $j hj $x $y => $b)
        | _, _ => Macro.throwError "a loop has at most two variables"
    `(.bind $loop fun p => match p with | $(← tuplePat xs) => $(← k (mvars ++ xs)))
  | _ => Macro.throwUnsupported

end

end

macro_rules
  | `(inplace $a:ident do $stmts;*) => do
    let prog ← expandSeq a #[] (← `(.pure ())) true stmts.getElems.toList
    `(($a).runInPlace $prog)
