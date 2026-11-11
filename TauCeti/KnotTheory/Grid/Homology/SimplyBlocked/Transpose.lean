/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Equiv.Basic
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
The descent uses Mathlib's `LinearEquiv.ofSubmodules` and `Submodule.Quotient.equiv`, as in
the unblocked reflection `GridDiagram.unblockedHomologyTransposeEquiv`.
-/

public section

open CategoryTheory

namespace TauCeti.GridDiagram.IsKnot

variable {n : ℕ} {G : GridDiagram n} (hG : G.IsKnot)
  (R : Type*) [CommRing R] [CharP R 2] (i : Fin n)

/-- Reflection between the categorical chain carriers. -/
private noncomputable def simplyBlockedTransposeChainEquiv :
    (G.simplyBlockedComplex R i).X () ≃ₛₗ[
      ((simplyBlockedRenameEquiv R G.O.toPerm i).toRingEquiv :
        MvPolynomial {c : Fin n // c ≠ i} R →+* MvPolynomial {c : Fin n // c ≠ G.O i} R)]
      (G.transpose.simplyBlockedComplex R (G.O i)).X () :=
  (G.simplyBlockedChainEquiv R i).trans <|
    (G.simplyBlockedTransposeEquiv R i).trans
      (G.transpose.simplyBlockedChainEquiv R (G.O i)).symm

private theorem simplyBlockedTransposeChainEquiv_d
    (z : (G.simplyBlockedComplex R i).X ()) :
    (G.transpose.simplyBlockedComplex R (G.O i)).d () ()
        (simplyBlockedTransposeChainEquiv R i z) =
      simplyBlockedTransposeChainEquiv R i ((G.simplyBlockedComplex R i).d () () z) := by
  apply (G.transpose.simplyBlockedChainEquiv R (G.O i)).injective
  simp only [simplyBlockedTransposeChainEquiv, LinearEquiv.trans_apply,
    simplyBlockedChainEquiv_d, LinearEquiv.apply_symm_apply,
    simplyBlockedDifferential_transpose_simplyBlockedTransposeEquiv]

/-- Reflection identifies the cycle modules, transporting the blocked marking along `G.O`. -/
noncomputable def simplyBlockedTransposeCyclesEquiv :
    hG.simplyBlockedCycles R i ≃ₛₗ[
      ((simplyBlockedRenameEquiv R G.O.toPerm i).toRingEquiv :
        MvPolynomial {c : Fin n // c ≠ i} R →+* MvPolynomial {c : Fin n // c ≠ G.O i} R)]
      (G.isKnot_transpose.mpr hG).simplyBlockedCycles R (G.O i) :=
  (simplyBlockedTransposeChainEquiv R i).ofSubmodules _ _
    ((simplyBlockedTransposeChainEquiv R i).map_ker_of_intertwine _ _
      (simplyBlockedTransposeChainEquiv_d R i))

/-- On underlying explicit chains, the cycle equivalence is reflection with variable renaming. -/
@[simp]
theorem simplyBlockedChainEquiv_simplyBlockedTransposeCyclesEquiv
    (z : hG.simplyBlockedCycles R i) :
    G.transpose.simplyBlockedChainEquiv R (G.O i) (hG.simplyBlockedTransposeCyclesEquiv R i z) =
      G.simplyBlockedTransposeEquiv R i (G.simplyBlockedChainEquiv R i z) := by
  simp only [simplyBlockedTransposeCyclesEquiv, LinearEquiv.ofSubmodules_apply,
    simplyBlockedTransposeChainEquiv, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]

/-- On underlying explicit chains, the inverse cycle equivalence is inverse reflection. -/
@[simp]
theorem simplyBlockedChainEquiv_simplyBlockedTransposeCyclesEquiv_symm
    (z : (G.isKnot_transpose.mpr hG).simplyBlockedCycles R (G.O i)) :
    G.simplyBlockedChainEquiv R i ((hG.simplyBlockedTransposeCyclesEquiv R i).symm z) =
      (G.simplyBlockedTransposeEquiv R i).symm
        (G.transpose.simplyBlockedChainEquiv R (G.O i) z) := by
  apply (G.simplyBlockedTransposeEquiv R i).injective
  rw [← simplyBlockedChainEquiv_simplyBlockedTransposeCyclesEquiv,
    LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

private theorem map_boundaries_simplyBlockedTransposeCyclesEquiv :
    (hG.simplyBlockedBoundaries R i).map
        (hG.simplyBlockedTransposeCyclesEquiv R i).toLinearMap =
      (G.isKnot_transpose.mpr hG).simplyBlockedBoundaries R (G.O i) := by
  -- The boundary map is the differential with codomain restricted to cycles, and
  -- `ofSubmodules` restricts the chain equivalence. After `Subtype.ext`, both underlying
  -- chain maps are therefore definitionally the ones in `simplyBlockedTransposeChainEquiv_d`.
  -- We work in cycles here, rather than the ambient ranges of `map_range_of_intertwine`.
  ext z
  constructor
  · rintro ⟨w, ⟨c, rfl⟩, rfl⟩
    refine ⟨simplyBlockedTransposeChainEquiv R i c, Subtype.ext ?_⟩
    exact simplyBlockedTransposeChainEquiv_d R i c
  · rintro ⟨c, rfl⟩
    refine ⟨hG.simplyBlockedBoundaryMap R i
      ((simplyBlockedTransposeChainEquiv R i).symm c), ⟨_, rfl⟩, Subtype.ext ?_⟩
    exact (simplyBlockedTransposeChainEquiv_d R i _).symm.trans
      (congrArg ((G.transpose.simplyBlockedComplex R (G.O i)).d () ())
        ((simplyBlockedTransposeChainEquiv R i).apply_symm_apply c))

/-- Diagonal reflection on simply blocked knot grid homology, semilinear along the renaming
of the surviving variables and with the blocked column transported to `G.O i`. -/
noncomputable def simplyBlockedHomologyTransposeEquiv :
    hG.simplyBlockedHomology R i ≃ₛₗ[
      ((simplyBlockedRenameEquiv R G.O.toPerm i).toRingEquiv :
        MvPolynomial {c : Fin n // c ≠ i} R →+* MvPolynomial {c : Fin n // c ≠ G.O i} R)]
      (G.isKnot_transpose.mpr hG).simplyBlockedHomology R (G.O i) :=
  (hG.simplyBlockedHomologyIsoQuotient R i).toLinearEquiv.trans <|
    (Submodule.Quotient.equiv _ _ (hG.simplyBlockedTransposeCyclesEquiv R i)
      (hG.map_boundaries_simplyBlockedTransposeCyclesEquiv R i)).trans
        ((G.isKnot_transpose.mpr hG).simplyBlockedHomologyIsoQuotient R (G.O i)).toLinearEquiv.symm

/-- Reflection sends the homology class of a cycle to the class of its reflected cycle. -/
@[simp]
theorem simplyBlockedHomologyTransposeEquiv_oneVariableSpecializationHomologyClass
    (z : hG.simplyBlockedCycles R i) :
    hG.simplyBlockedHomologyTransposeEquiv R i (G.oneVariableSpecializationHomologyClass R i z) =
      G.transpose.oneVariableSpecializationHomologyClass R (G.O i)
        (hG.simplyBlockedTransposeCyclesEquiv R i z) := by
  simp only [simplyBlockedHomologyTransposeEquiv, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_eq]
  rw [Iso.toLinearEquiv_apply, Iso.toLinearEquiv_apply,
    simplyBlockedHomologyIsoQuotient_hom_class, simplyBlockedHomologyIsoQuotient_hom_class,
    Submodule.Quotient.equiv_apply, Submodule.mapQ_apply, LinearEquiv.coe_coe]

/-- The inverse reflection sends a cycle class back by the inverse cycle equivalence. -/
@[simp]
theorem simplyBlockedHomologyTransposeEquiv_symm_oneVariableSpecializationHomologyClass
    (z : (G.isKnot_transpose.mpr hG).simplyBlockedCycles R (G.O i)) :
    (hG.simplyBlockedHomologyTransposeEquiv R i).symm
        (G.transpose.oneVariableSpecializationHomologyClass R (G.O i) z) =
      G.oneVariableSpecializationHomologyClass R i
        ((hG.simplyBlockedTransposeCyclesEquiv R i).symm z) := by
  rw [LinearEquiv.symm_apply_eq,
    simplyBlockedHomologyTransposeEquiv_oneVariableSpecializationHomologyClass,
    LinearEquiv.apply_symm_apply]

end TauCeti.GridDiagram.IsKnot
