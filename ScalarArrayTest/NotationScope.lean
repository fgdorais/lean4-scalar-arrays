/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import ScalarArray.Notation
meta import Lean.Elab.Command

/-!
Tests that `ScalarArray.Notation` adds nothing outside of `inplace … do` blocks but the keyword
`inplace`: the statements, and the terms that the notation expands to, are parsed only inside a
block, and the names of its tactics aren't keywords.
-/

open Lean Parser Elab Command in
/--
The tokens that the module `m` adds to those of Lean and of the other imported modules, and the
parsers that it adds to the categories other than its own `inplaceStmt` and `inplaceInternal`.
-/
private meta def printAdded (m : Name) : CommandElabM Unit := do
  let env ← getEnv
  let some idx := env.getModuleIdx? m | throwError "{m} isn't imported"
  let entries (i : ModuleIdx) : Array ParserExtension.OLeanEntry :=
    (parserExtension.ext.getModuleEntries env i).filterMap fun
      | .global e => some e
      | .scoped .. => none
  let mut known : Std.HashSet Token := {}
  for t in (← builtinTokenTable.get).findPrefix "" do known := known.insert t
  for i in [0:env.allImportedModuleNames.size] do
    if i != idx.toNat then
      for e in entries i do
        if let .token t := e then known := known.insert t
  let mut tokens : Array Token := #[]
  let mut parsers : Array String := #[]
  for e in entries idx do
    match e with
    | .token t => if !known.contains t && !tokens.contains t then tokens := tokens.push t
    | .parser cat k _ =>
      unless cat == `inplaceStmt || cat == `inplaceInternal do parsers := parsers.push s!"{cat}: {k}"
    | _ => pure ()
  logInfo m!"tokens: {tokens.qsort (· < ·)}\nparsers: {parsers.qsort (· < ·)}"

/--
info: tokens: [`(inplaceInternal|, `(inplaceStmt|, inplace]
parsers: [tactic: inplaceBound, term: inplaceInternal.quot, term: inplaceStmt.quot, term: inplaceTerm]
-/
#guard_msgs in
run_cmd printAdded `ScalarArray.Notation

-- The names of the tactics and of the terms of the expansion are free for other uses.
private def inplace_bound : Nat := 1
private def inplace_index : Nat := 2
private def inplace_elem : Nat := 3
private def inplace_choose : Nat := 4
-- `reverse`, which starts a reverse loop, isn't a keyword either.
private def reverse : Nat := inplace_bound + inplace_index + inplace_elem + inplace_choose

#guard reverse == 10

