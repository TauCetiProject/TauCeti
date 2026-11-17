/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Homology.SimplyBlocked.Intertwining
public import TauCeti.KnotTheory.Grid.SimplyBlocked.Transpose

/-!
# Diagonal reflection on simply blocked grid homology

For a knot grid, reflection induces a specified semilinear equivalence on `G-hat`. The blocked
`O`-marking moves from column `i` to column `G.O i`, and the remaining variables are renamed
by the same permutation. The equivalence is characterized on cycle classes, not just by the
existence of an abstract isomorphism. Its inverse is likewise characterized on cycle classes.

Reflection preserves and reflects the `(O-Maslov, Alexander)` bigrading of `G-hat`, restricts to
coefficient-linear equivalences on every homogeneous piece, and preserves the bigraded Poincaré
series and Alexander-graded Euler characteristic. Together with the pentagon equivalence for column
commutations, this reflection allows one to compare bigraded simply blocked homologies across row
commutations.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Chapters 3 and 4.6.
The descent and grading preservation use
`TauCeti.GridDiagram.IsKnot.simplyBlockedHomologyEquivOfIntertwining`, parallel to the unblocked
reflection `GridDiagram.unblockedHomologyTransposeEquiv`.
-/

public section

open CategoryTheory

namespace TauCeti.GridDiagram.IsKnot

variable {n : ℕ} {G : GridDiagram n} (hG : G.IsKnot)

local notation "hGₜ" => G.isKnot_transpose.mpr hG
local notation "Base(" R ", " n ", " i ")" =>
  ModuleCat.restrictScalars (MvPolynomial.C : R →+* MvPolynomial {c : Fin n // c ≠ i} R)

private theorem simplyBlockedTransposeEquiv_mem_bigradedChainHatPiece {R : Type*}
    [CommSemiring R] {i : Fin n} (g : ℤ × ℤ) (c : GridChainHat R n i)
    (hc : c ∈ hG.toOddComponentGridDiagram.bigradedChainHatPiece R i g) :
    G.simplyBlockedTransposeEquiv R i c ∈
      (hGₜ).toOddComponentGridDiagram.bigradedChainHatPiece R (G.O i) g := by
  have h :=
    hG.toOddComponentGridDiagram.simplyBlockedTransposeEquiv_mem_bigradedChainHatPiece_iff.mpr hc
  rwa [hG.val_toOddComponentGridDiagram, hG.transpose_toOddComponentGridDiagram] at h

section Ring

variable (R : Type*) [CommRing R] [CharP R 2] (i : Fin n)

/-- Reflection identifies the cycle modules, transporting the blocked marking along `G.O`. -/
noncomputable def simplyBlockedTransposeCyclesEquiv :
    hG.simplyBlockedCycles R i ≃ₛₗ[
      ((simplyBlockedRenameEquiv R G.O.toPerm i).toRingEquiv :
        MvPolynomial {c : Fin n // c ≠ i} R →+* MvPolynomial {c : Fin n // c ≠ G.O i} R)]
      (G.isKnot_transpose.mpr hG).simplyBlockedCycles R (G.O i) :=
  hG.simplyBlockedCyclesEquivOfIntertwining R hGₜ (G.simplyBlockedTransposeEquiv R i)
    (G.simplyBlockedDifferential_transpose_simplyBlockedTransposeEquiv R i)

/-- On underlying explicit chains, the cycle equivalence is reflection with variable renaming. -/
@[simp]
theorem simplyBlockedChainEquiv_simplyBlockedTransposeCyclesEquiv
    (z : hG.simplyBlockedCycles R i) :
    G.transpose.simplyBlockedChainEquiv R (G.O i) (hG.simplyBlockedTransposeCyclesEquiv R i z) =
      G.simplyBlockedTransposeEquiv R i (G.simplyBlockedChainEquiv R i z) :=
  hG.simplyBlockedChainEquiv_simplyBlockedCyclesEquivOfIntertwining R hGₜ _
    (G.simplyBlockedDifferential_transpose_simplyBlockedTransposeEquiv R i) z

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

/-- Diagonal reflection on simply blocked knot grid homology, semilinear along the renaming
of the surviving variables and with the blocked column transported to `G.O i`. -/
noncomputable def simplyBlockedHomologyTransposeEquiv :
    hG.simplyBlockedHomology R i ≃ₛₗ[
      ((simplyBlockedRenameEquiv R G.O.toPerm i).toRingEquiv :
        MvPolynomial {c : Fin n // c ≠ i} R →+* MvPolynomial {c : Fin n // c ≠ G.O i} R)]
      (G.isKnot_transpose.mpr hG).simplyBlockedHomology R (G.O i) :=
  hG.simplyBlockedHomologyEquivOfIntertwining R hGₜ (G.simplyBlockedTransposeEquiv R i)
    (G.simplyBlockedDifferential_transpose_simplyBlockedTransposeEquiv R i)

/-- Reflection sends the homology class of a cycle to the class of its reflected cycle. -/
@[simp]
theorem simplyBlockedHomologyTransposeEquiv_oneVariableSpecializationHomologyClass
    (z : hG.simplyBlockedCycles R i) :
    hG.simplyBlockedHomologyTransposeEquiv R i (G.oneVariableSpecializationHomologyClass R i z) =
      G.transpose.oneVariableSpecializationHomologyClass R (G.O i)
        (hG.simplyBlockedTransposeCyclesEquiv R i z) :=
  hG.simplyBlockedHomologyEquivOfIntertwining_oneVariableSpecializationHomologyClass R hGₜ _ _ z

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

/-- Diagonal reflection preserves and reflects both homology degrees of `G-hat`. -/
@[simp]
theorem simplyBlockedHomologyTransposeEquiv_mem_bigradedHatHomologyPiece_iff
    {g : ℤ × ℤ} {y : (Base(R, n, i)).obj (hG.simplyBlockedHomology R i)} :
    hG.simplyBlockedHomologyTransposeEquiv R i y ∈
        (hGₜ).toOddComponentGridDiagram.bigradedHatHomologyPiece R (G.O i) g ↔
      y ∈ hG.toOddComponentGridDiagram.bigradedHatHomologyPiece R i g :=
  hG.simplyBlockedHomologyEquivOfIntertwining_mem_bigradedHatHomologyPiece_iff R hGₜ _
    (G.simplyBlockedDifferential_transpose_simplyBlockedTransposeEquiv R i)
    (simplyBlockedRenameEquiv R G.O.toPerm i).commutes
    (simplyBlockedTransposeEquiv_mem_bigradedChainHatPiece hG)

/-- Diagonal reflection restricted to a homogeneous piece of `G-hat`. -/
noncomputable def simplyBlockedHomologyTransposePieceEquiv (g : ℤ × ℤ) :
    hG.toOddComponentGridDiagram.bigradedHatHomologyPiece R i g ≃ₗ[R]
      (hGₜ).toOddComponentGridDiagram.bigradedHatHomologyPiece R (G.O i) g :=
  hG.simplyBlockedHomologyPieceEquivOfIntertwining R hGₜ _
    (G.simplyBlockedDifferential_transpose_simplyBlockedTransposeEquiv R i)
    (simplyBlockedRenameEquiv R G.O.toPerm i).commutes
    (simplyBlockedTransposeEquiv_mem_bigradedChainHatPiece hG) g

/-- On underlying classes, the homogeneous-piece reflection is
`simplyBlockedHomologyTransposeEquiv`. -/
@[simp]
theorem coe_simplyBlockedHomologyTransposePieceEquiv (g : ℤ × ℤ)
    (y : hG.toOddComponentGridDiagram.bigradedHatHomologyPiece R i g) :
    (hG.simplyBlockedHomologyTransposePieceEquiv R i g y :
      (Base(R, n, G.O i)).obj ((hGₜ).simplyBlockedHomology R (G.O i))) =
      hG.simplyBlockedHomologyTransposeEquiv R i
        (y : (Base(R, n, i)).obj (hG.simplyBlockedHomology R i)) :=
  hG.coe_simplyBlockedHomologyPieceEquivOfIntertwining R hGₜ _
    (G.simplyBlockedDifferential_transpose_simplyBlockedTransposeEquiv R i)
    (simplyBlockedRenameEquiv R G.O.toPerm i).commutes
    (simplyBlockedTransposeEquiv_mem_bigradedChainHatPiece hG) g y

end Ring

section Field

variable (K : Type*) [Field K] [CharP K 2] (i : Fin n)

/-- The bigraded Poincaré series of `G-hat` is invariant under diagonal reflection, transporting
the blocked column from `i` to `G.O i`. -/
theorem bigradedSimplyBlockedHomologyPoincareSeries_transpose :
    (hGₜ).bigradedSimplyBlockedHomologyPoincareSeries K (G.O i) =
      hG.bigradedSimplyBlockedHomologyPoincareSeries K i :=
  hG.bigradedSimplyBlockedHomologyPoincareSeries_eq_of_intertwining K hGₜ _
    (G.simplyBlockedDifferential_transpose_simplyBlockedTransposeEquiv K i)
    (simplyBlockedRenameEquiv K G.O.toPerm i).commutes
    (simplyBlockedTransposeEquiv_mem_bigradedChainHatPiece hG)

/-- The Alexander-graded Euler characteristic of `G-hat` is invariant under diagonal reflection. -/
theorem gradedSimplyBlockedHomologyEulerChar_transpose :
    (hGₜ).gradedSimplyBlockedHomologyEulerChar K (G.O i) =
      hG.gradedSimplyBlockedHomologyEulerChar K i :=
  hG.gradedSimplyBlockedHomologyEulerChar_eq_of_intertwining K hGₜ _
    (G.simplyBlockedDifferential_transpose_simplyBlockedTransposeEquiv K i)
    (simplyBlockedRenameEquiv K G.O.toPerm i).commutes
    (simplyBlockedTransposeEquiv_mem_bigradedChainHatPiece hG)

end Field

end TauCeti.GridDiagram.IsKnot
