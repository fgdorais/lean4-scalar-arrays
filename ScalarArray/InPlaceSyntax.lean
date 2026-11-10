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
imperative language, and runs it with `a.runInPlace`. It works for all 13 array types:

```
inplace a do
  for j < len with (c := 0) (b := 0) do
    let u ← a[xs + j]
    let v ← a[ys + j]
    let (s, c) := addc u v c
    let (d, b) := subb u v b
    a[xs + j] := s
    a[ts + j] := d
  return (c, b)
```

The statements are

* `let x ← a[i]` reads the element at the `USize` index `i`,
* `a[i] := e` writes `e` at `i`,
* `let p := e` binds a pure value, where `p` can be a pattern such as `(s, c)`,
* `for j < len do …` and `for j < len, downward do …` loop over `j < len`, up from `0` or down
  from `len - 1`, carrying the variables named in an optional `with (x := init) …` clause: up to two,
  which the loop keeps as separate unboxed arguments. The body rebinds them with `let`, and they
  hold their last values after the loop.
* `return e`, last, gives the program's result. Without it, the result is `()`.

The program runs as `forUp`, `forUp2`, `forDown` and `forDown2` loops over `read` and `write`, so
it compiles to the same loop as a hand-written program. The bound of each index is proved by the
tactic `inplace_bound`, from a hypothesis in context such as `hx : xs.toNat + len.toNat ≤ a.size`
for an index `xs + j` in a loop over `j < len`, or else by `lia`. The hypotheses must be separate:
`inplace_bound` doesn't look inside a conjunction.
-/

namespace ScalarArray.InPlaceSyntax

/-- The index `off + j` of a window of `len` elements at `off` is in bounds, for `j < len`. -/
public theorem toNat_add_lt_of_window {n : Nat} {off len j : USize}
    (hw : off.toNat + len.toNat ≤ n) (hj : j.toNat < len.toNat) : (off + j).toNat < n := by
  rw [USize.toNat_add]
  exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (by lia)

end ScalarArray.InPlaceSyntax

/--
Proves the bound `i.toNat < n` of an index in an `inplace` program: for `i = off + j` from a
window hypothesis `off.toNat + len.toNat ≤ n` and the loop bound `j.toNat < len.toNat`, or else by
`lia` from the hypotheses in context.
-/
syntax (name := inplaceBound) "inplace_bound" : tactic

macro_rules
  | `(tactic| inplace_bound) => `(tactic| first
      | exact ScalarArray.InPlaceSyntax.toNat_add_lt_of_window (by assumption) (by assumption)
      | assumption
      | lia)

public meta section

/-- A statement of an `inplace` program. -/
declare_syntax_cat inplaceStmt

/-- A sequence of statements of an `inplace` program. -/
syntax inplaceSeq := sepByIndentSemicolon(inplaceStmt)

/-- `let x ← a[i]` reads the element of `a` at `i`. -/
syntax "let " ident " ← " ident "[" term "]" : inplaceStmt
/-- `a[i] := e` writes `e` at `i`. -/
syntax ident "[" term "]" " := " term : inplaceStmt
/-- `let p := e` binds the value of the pure term `e` to the pattern `p`. -/
syntax "let " term " := " term : inplaceStmt
/-- A loop over `j < len`, carrying the variables of its `with` clause. -/
syntax "for " ident " < " term (", " &"downward")? (" with" (ppSpace "(" ident " := " term ")")+)?
  " do" inplaceSeq : inplaceStmt
/-- `return e` gives the program's result. -/
syntax "return " term : inplaceStmt

/--
`inplace a do …` is the in-place program on `a` that the statements describe, run with
`a.runInPlace`. See the module documentation.
-/
syntax (name := inplaceTerm) "inplace " ident " do" inplaceSeq : term

open Lean in
/-- The program of the statements `stmts` on the array `arr`, ending with `ret`. -/
private partial def expandStmts (arr : Ident) (ret : Term) :
    List (TSyntax `inplaceStmt) → MacroM Term
  | [] => pure ret
  | s :: rest => withRef s do
    if rest.isEmpty then
      if let `(inplaceStmt| return $e) := s then
        return ← `(.pure $e)
    let k ← expandStmts arr ret rest
    match s with
    | `(inplaceStmt| let $x:ident ← $a:ident[$i]) =>
      checkArray arr a
      `(.readThen $i (by inplace_bound) fun $x => $k)
    | `(inplaceStmt| $a:ident[$i] := $v) =>
      checkArray arr a
      `(.bind (.write $i (by inplace_bound) $v) fun _ => $k)
    | `(inplaceStmt| let $p := $e) =>
      `(match $e:term with | $p:term => $k)
    | `(inplaceStmt| for $j < $len $[, downward%$down]? $[with $[($xs := $inits)]*]? do $body;*) =>
      let xs := xs.getD #[]
      let inits := inits.getD #[]
      let down := down.isSome
      match xs, inits with
      | #[], #[] =>
        let b ← expandStmts arr (← `(.pure ())) body.getElems.toList
        let loop ← if down then `(.forDown $len () fun $j hj _ => $b)
          else `(.forUp $len () fun $j hj _ => $b)
        `(.bind $loop fun _ => $k)
      | #[x], #[init] =>
        let b ← expandStmts arr (← `(.pure $x)) body.getElems.toList
        let loop ← if down then `(.forDown $len $init fun $j hj $x => $b)
          else `(.forUp $len $init fun $j hj $x => $b)
        `(.bind $loop fun $x => $k)
      | #[x, y], #[initx, inity] =>
        let b ← expandStmts arr (← `(.pure ($x, $y))) body.getElems.toList
        let loop ← if down then `(.forDown2 $len $initx $inity fun $j hj $x $y => $b)
          else `(.forUp2 $len $initx $inity fun $j hj $x $y => $b)
        `(.bind $loop fun p => match p with | ($x, $y) => $k)
      | _, _ => Macro.throwError "a loop carries at most two variables"
    | `(inplaceStmt| return $_) =>
      Macro.throwError "`return` must be the last statement"
    | _ => Macro.throwUnsupported
where
  /-- Checks that a read or a write is on the program's array. -/
  checkArray (arr a : Ident) : MacroM Unit :=
    unless arr.getId == a.getId do
      Macro.throwErrorAt a
        s!"an `inplace` program on `{arr.getId}` reads and writes only `{arr.getId}`"

end

macro_rules
  | `(inplace $a:ident do $stmts;*) => do
    let prog ← expandStmts a (← `(.pure ())) stmts.getElems.toList
    `(($a).runInPlace $prog)
