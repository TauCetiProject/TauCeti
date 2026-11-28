/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PermutationTriple.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Free-group representations of permutation triples

The first two permutations of a triple specify an action of the free group on two generators
on its sheets. The correspondence combines `TauCeti.PermutationTriple.equivPair` with
`FreeGroup.lift`. The image of each representation is the monodromy group of its triple.
Evaluating the same word on two sets of sheets describes the monodromy on their disjoint union.
-/

public section

namespace TauCeti.PermutationTriple

open Equiv

/-- Permutation triples of degree `n` correspond to permutation representations of the free
group on two generators, with the generators acting by `σ0` and `σ1` in that order. -/
def equivFreeGroupHom (n : ℕ) :
    PermutationTriple n ≃ (FreeGroup (Fin 2) →* Perm (Fin n)) :=
  (equivPair n).trans ((finTwoArrowEquiv _).symm.trans FreeGroup.lift)

variable {n : ℕ} (t : PermutationTriple n)

theorem equivFreeGroupHom_apply :
    equivFreeGroupHom n t = FreeGroup.lift ![t.σ0, t.σ1] := (rfl)

/-- The inverse representation correspondence recovers the triple from the generator images. -/
@[simp] theorem equivFreeGroupHom_symm_apply (ρ : FreeGroup (Fin 2) →* Perm (Fin n)) :
    (equivFreeGroupHom n).symm ρ = ofTwo (ρ (FreeGroup.of 0)) (ρ (FreeGroup.of 1)) := (rfl)

@[simp] theorem equivFreeGroupHom_of_zero :
    equivFreeGroupHom n t (FreeGroup.of 0) = t.σ0 := by
  simp [equivFreeGroupHom_apply]

@[simp] theorem equivFreeGroupHom_of_one :
    equivFreeGroupHom n t (FreeGroup.of 1) = t.σ1 := by
  simp [equivFreeGroupHom_apply]

/-- The image of the free group acting on the sheets is the monodromy group. -/
@[simp] theorem range_equivFreeGroupHom : (equivFreeGroupHom n t).range = t.monodromyGroup := by
  rw [equivFreeGroupHom_apply, FreeGroup.range_lift_eq_closure, Matrix.range_cons_cons_empty,
    closure_pair_eq_monodromyGroup]

end TauCeti.PermutationTriple
