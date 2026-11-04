/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fin.VecNotation
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Tactic.FinCases
public import TauCeti.GroupTheory.Presentation.NormalGeneration

/-!
# A normal-generation certificate in the symmetric group on three letters

A five-register program recovers both adjacent transpositions from the first one. It exercises
conjugation, multiplication, inversion and register sharing. The accepted check proves normal
generation in the actual permutation group. A different output assignment is rejected.
-/

public section

namespace TauCeti.Examples.NormalGeneration

open Equiv

/-- The adjacent transpositions on three letters. -/
def generators (i : Fin 2) : Perm (Fin 3) := swap i.castSucc i.succ

/-- Start from the first adjacent transposition `a`. Conjugation by `ba` gives `b`;
then `a⁻¹ * (a * b)` recovers `b` again using shared registers. -/
def program : NormalClosureProgram (Fin 2) 5 :=
  .snoc (.snoc (.snoc (.snoc (.snoc .nil .seed)
    (.conj (.mul (.gen 1) (.gen 0)) 0)) (.mul 0 1)) (.inv 0)) (.mul 3 2)

/-- The five computed register values, with the ambient multiplication convention. -/
theorem eval_program :
    program.eval generators (swap 0 1) =
      ![swap 0 1, swap 1 2, swap 0 1 * swap 1 2, swap 0 1, swap 1 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [program, NormalClosureProgram.eval_snoc, Fin.snoc, generators,
      Perm.mul_apply, swap_apply_def]

/-- The selected registers recover the two generators. -/
theorem check_program : program.check generators (swap 0 1) ![0, 4] = true := by
  rw [NormalClosureProgram.check_eq_true, eval_program]
  decide

/-- Reusing the seed as both outputs does not recover the second generator. -/
theorem check_wrong_output : program.check generators (swap 0 1) ![0, 0] = false := by
  rw [Bool.eq_false_iff, ne_eq, NormalClosureProgram.check_eq_true, eval_program]
  decide

/-- The certificate proves that a transposition normally generates the symmetric group
on three letters, using the actual adjacent-transposition generation theorem. -/
theorem normalClosure_swap :
    Subgroup.normalClosure ({swap 0 1} : Set (Perm (Fin 3))) = ⊤ := by
  apply program.normalClosure_eq_top_of_check generators (swap 0 1) ![0, 4] _ check_program
  exact Subgroup.closure_eq_top_of_mclosure_eq_top (Perm.mclosure_swap_castSucc_succ 2)

end TauCeti.Examples.NormalGeneration
