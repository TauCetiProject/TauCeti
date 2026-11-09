/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Diagram.Parse.Basic
public meta import TauCeti.KnotTheory.Grid.Diagram.Parse.Basic
import Lean

/-!
# Grid link diagram syntax

The `link%` syntax parses a multiline box-drawing literal into a grid diagram. Invalid input is
reported as an elaboration error.

## Main definitions

* `link%`: parse a quoted multiline diagram literal into a `GridDiagram n`.
-/

public section

open Lean

namespace TauCeti

namespace GridDiagram

private meta def blankLine (line : String) : Bool := line.trimAscii.isEmpty

private meta def leadingWhitespaceCount (line : String) : Nat :=
  line.toList.takeWhile Char.isWhitespace |>.length

private meta def minimumIndent : List String → Nat
  | [] => 0
  | line :: rows =>
    rows.foldl (fun n row ↦ min n (leadingWhitespaceCount row)) (leadingWhitespaceCount line)

private meta def normalizeDiagramText (s : String) : Option String := do
  let first :: rest := s.splitOn "\n" | none
  guard (blankLine first)
  let rows := rest.dropWhile blankLine |>.reverse.dropWhile blankLine |>.reverse
  let indent := minimumIndent rows
  return String.intercalate "\n" <| rows.map fun line ↦
    (String.ofList (line.toList.drop indent)).trimAsciiEnd.toString

private meta def permutationFunctionTerm {n : ℕ} (values : List ℕ) :
    MacroM (TSyntax `term) := do
  let valuesStx := quote values
  `(fun c : Fin $(quote n) ↦
    ⟨$valuesStx[c.val]'(Nat.lt_of_lt_of_eq c.isLt (by decide)) % $(quote n),
      Nat.mod_lt _ (Nat.zero_lt_of_lt c.isLt)⟩)

private meta def permutationTerm {n : ℕ} (σ : Equiv.Perm (Fin n)) : MacroM (TSyntax `term) := do
  let values := (List.ofFn σ).map Fin.val
  let inverseValues := (List.ofFn σ.symm).map Fin.val
  let f ← permutationFunctionTerm (n := n) values
  let g ← permutationFunctionTerm (n := n) inverseValues
  `(Equiv.mk $f $g (by decide) (by decide))

private meta def diagramTerm {n : ℕ} (G : GridDiagram n) : MacroM (TSyntax `term) := do
  let O ← permutationTerm G.O.toPerm
  let X ← permutationTerm G.X.toPerm
  `(TauCeti.GridDiagram.mk (TauCeti.GridState.mk $O) (TauCeti.GridState.mk $X) (by decide))

macro (name := linkSyntax) "link% " s:str : term => do
  let some text := normalizeDiagramText s.getString |
    Macro.throwErrorAt s "expected a multiline grid diagram"
  let some ⟨n, G⟩ := parseLink text | Macro.throwErrorAt s "invalid grid diagram"
  diagramTerm (n := n) G

end GridDiagram

end TauCeti
