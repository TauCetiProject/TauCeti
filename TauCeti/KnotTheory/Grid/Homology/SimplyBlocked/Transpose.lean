/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Homology.SimplyBlocked.Basic
public import TauCeti.KnotTheory.Grid.SimplyBlocked.Transpose

/-!
# Diagonal reflection on simply blocked grid homology

For a knot grid, reflection induces a specified semilinear equivalence on `G-hat`. The blocked
`O`-marking moves from column `i` to column `G.O i`, and the remaining variables are renamed
by the same permutation. The equivalence is characterized on cycle classes, not just by the
existence of an abstract isomorphism. Its inverse is likewise characterized on cycle classes.

Together with the pentagon equivalence for column commutations, this reflection allows one to
compare simply blocked homologies across row commutations.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Chapters 3 and 4.6.
-/

public section

open CategoryTheory

namespace TauCeti.GridDiagram.IsKnot

variable {n : ℕ} {G : GridDiagram n} (hG : G.IsKnot)
  (R : Type*) [CommRing R] [CharP R 2] (i : Fin n)

/-- Reflection identifies the cycle modules, transporting the blocked marking along `G.O`. -/
noncomputable def simplyBlockedTransposeCyclesEquiv :
    hG.simplyBlockedCycles R i ≃ₛₗ[
      ((simplyBlockedRenameEquiv R G.O.toPerm i).toRingEquiv :
        MvPolynomial {c : Fin n // c ≠ i} R →+* MvPolynomial {c : Fin n // c ≠ G.O i} R)]
      (G.isKnot_transpose.mpr hG).simplyBlockedCycles R (G.O i) :=
  oneVariableSpecializationCyclesEquivOfIntertwining R i (G.O i)
    ((simplyBlockedRenameEquiv R G.O.toPerm i).toRingEquiv : _ →+* _)
    (G.simplyBlockedTransposeEquiv R i)
    (G.simplyBlockedDifferential_transpose_simplyBlockedTransposeEquiv R i)

/-- On underlying explicit chains, the cycle equivalence is reflection with variable renaming. -/
@[simp]
theorem simplyBlockedChainEquiv_simplyBlockedTransposeCyclesEquiv
    (z : hG.simplyBlockedCycles R i) :
    G.transpose.simplyBlockedChainEquiv R (G.O i) (hG.simplyBlockedTransposeCyclesEquiv R i z) =
      G.simplyBlockedTransposeEquiv R i (G.simplyBlockedChainEquiv R i z) := by
  exact simplyBlockedChainEquiv_oneVariableSpecializationCyclesEquivOfIntertwining
    R i (G.O i) _ _ _ z

/-- On underlying explicit chains, the inverse cycle equivalence is inverse reflection. -/
@[simp]
theorem simplyBlockedChainEquiv_simplyBlockedTransposeCyclesEquiv_symm
    (z : (G.isKnot_transpose.mpr hG).simplyBlockedCycles R (G.O i)) :
    G.simplyBlockedChainEquiv R i ((hG.simplyBlockedTransposeCyclesEquiv R i).symm z) =
      (G.simplyBlockedTransposeEquiv R i).symm
        (G.transpose.simplyBlockedChainEquiv R (G.O i) z) := by
  exact simplyBlockedChainEquiv_oneVariableSpecializationCyclesEquivOfIntertwining_symm
    R i (G.O i) _ _ _ z

/-- Diagonal reflection on simply blocked knot grid homology, semilinear along the renaming
of the surviving variables and with the blocked column transported to `G.O i`. -/
noncomputable def simplyBlockedHomologyTransposeEquiv :
    hG.simplyBlockedHomology R i ≃ₛₗ[
      ((simplyBlockedRenameEquiv R G.O.toPerm i).toRingEquiv :
        MvPolynomial {c : Fin n // c ≠ i} R →+* MvPolynomial {c : Fin n // c ≠ G.O i} R)]
      (G.isKnot_transpose.mpr hG).simplyBlockedHomology R (G.O i) :=
  oneVariableSpecializationHomologyEquivOfIntertwining R i (G.O i)
    ((simplyBlockedRenameEquiv R G.O.toPerm i).toRingEquiv : _ →+* _)
    (G.simplyBlockedTransposeEquiv R i)
    (G.simplyBlockedDifferential_transpose_simplyBlockedTransposeEquiv R i)

/-- Reflection sends the homology class of a cycle to the class of its reflected cycle. -/
@[simp]
theorem simplyBlockedHomologyTransposeEquiv_oneVariableSpecializationHomologyClass
    (z : hG.simplyBlockedCycles R i) :
    hG.simplyBlockedHomologyTransposeEquiv R i (G.oneVariableSpecializationHomologyClass R i z) =
      G.transpose.oneVariableSpecializationHomologyClass R (G.O i)
        (hG.simplyBlockedTransposeCyclesEquiv R i z) := by
  exact oneVariableSpecializationHomologyEquivOfIntertwining_oneVariableSpecializationHomologyClass
    R i (G.O i) _ _ _ z

/-- The inverse reflection sends a cycle class back by the inverse cycle equivalence. -/
@[simp]
theorem simplyBlockedHomologyTransposeEquiv_symm_oneVariableSpecializationHomologyClass
    (z : (G.isKnot_transpose.mpr hG).simplyBlockedCycles R (G.O i)) :
    (hG.simplyBlockedHomologyTransposeEquiv R i).symm
        (G.transpose.oneVariableSpecializationHomologyClass R (G.O i) z) =
      G.oneVariableSpecializationHomologyClass R i
        ((hG.simplyBlockedTransposeCyclesEquiv R i).symm z) := by
  exact
    oneVariableSpecializationHomologyEquivOfIntertwining_symm_oneVariableSpecializationHomologyClass
      R i (G.O i) _ _ _ z

end TauCeti.GridDiagram.IsKnot
