/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Homology.SimplyBlocked.Transpose
public import TauCeti.KnotTheory.Grid.Homology.Series.SimplyBlocked

/-!
# Diagonal reflection preserves the bigrading of simply blocked homology

The specified reflection equivalence on `G-hat` preserves and reflects each integral
`(O-Maslov, Alexander)` degree. The blocked marking moves from column `i` to column `G.O i`;
the surviving polynomial variables are renamed along the same permutation. Restriction to
coefficient scalars gives a linear equivalence on each homogeneous homology piece, and hence
equality of the bigraded Poincaré series and Alexander-graded Euler characteristics.

Reflection exchanges rows and columns, so this supplies the grading comparison needed to
transfer column-commutation invariance to row commutations. No field hypothesis is needed
for the equivalences; dimensions and series are considered over fields of characteristic two.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Sections 4.3, 4.6 and 5.1.
The underlying map is `GridDiagram.IsKnot.simplyBlockedHomologyTransposeEquiv`.
-/

public section

noncomputable section

namespace TauCeti.GridDiagram.IsKnot

variable {n : ℕ} {G : GridDiagram n} (hG : G.IsKnot)
  (R : Type*) [CommRing R] [CharP R 2] (i : Fin n)

local notation "hG'" => G.isKnot_transpose.mpr hG
local notation "H" => hG.toOddComponentGridDiagram
local notation "H'" => GridDiagram.IsKnot.toOddComponentGridDiagram
  (G.isKnot_transpose.mpr hG)
local notation "Base" => ModuleCat.restrictScalars (MvPolynomial.C :
  R →+* MvPolynomial {c : Fin n // c ≠ i} R)
local notation "Base'" => ModuleCat.restrictScalars (MvPolynomial.C :
  R →+* MvPolynomial {c : Fin n // c ≠ G.O i} R)

/-- The coefficient action on source homology is the action selected by
`ModuleCat.restrictScalars` along the inclusion of constant polynomials. -/
local instance transposeSourceCoefficientModule : Module R (hG.simplyBlockedHomology R i) :=
  Module.compHom _ (MvPolynomial.C : R →+* MvPolynomial {c : Fin n // c ≠ i} R)
/-- The coefficient action on reflected homology is restriction along constant polynomials. -/
local instance transposeTargetCoefficientModule :
    Module R ((hG').simplyBlockedHomology R (G.O i)) :=
  Module.compHom _ (MvPolynomial.C : R →+* MvPolynomial {c : Fin n // c ≠ G.O i} R)

/-- Diagonal reflection on homology, linear over the coefficient ring. The underlying
semilinear equivalence renames the surviving polynomial variables along `G.O`. -/
noncomputable def simplyBlockedHomologyTransposeCoefficientEquiv :
    (Base).obj (hG.simplyBlockedHomology R i) ≃ₗ[R]
      (Base').obj ((hG').simplyBlockedHomology R (G.O i)) :=
  (hG.simplyBlockedHomologyTransposeEquiv R i).toAddEquiv.toLinearEquiv fun r y => by
    have hr : (simplyBlockedRenameEquiv R G.O.toPerm i).toRingEquiv (MvPolynomial.C r) =
        (MvPolynomial.C r : MvPolynomial {c : Fin n // c ≠ G.O i} R) :=
      (simplyBlockedRenameEquiv R G.O.toPerm i).commutes r
    have he := (hG.simplyBlockedHomologyTransposeEquiv R i).map_smulₛₗ
      (MvPolynomial.C r) y
    simp only [RingEquiv.coe_toRingHom, hr] at he
    exact he

/-- Restricting scalars does not change the specified reflection on homology classes. -/
@[simp]
theorem simplyBlockedHomologyTransposeCoefficientEquiv_apply
    (y : (Base).obj (hG.simplyBlockedHomology R i)) :
    hG.simplyBlockedHomologyTransposeCoefficientEquiv R i y =
      hG.simplyBlockedHomologyTransposeEquiv R i y :=
  (rfl)

/-- The inverse coefficient-linear equivalence is the inverse specified reflection. -/
@[simp]
theorem simplyBlockedHomologyTransposeCoefficientEquiv_symm_apply
    (y : (Base').obj ((hG').simplyBlockedHomology R (G.O i))) :
    (hG.simplyBlockedHomologyTransposeCoefficientEquiv R i).symm y =
      (hG.simplyBlockedHomologyTransposeEquiv R i).symm y :=
  (rfl)

/-- Reflection sends a homogeneous homology class to one of the same bidegree. -/
theorem simplyBlockedHomologyTransposeEquiv_mem_bigradedHatHomologyPiece
    {g : ℤ × ℤ} {y : (Base).obj (hG.simplyBlockedHomology R i)}
    (hy : y ∈ (H).bigradedHatHomologyPiece R i g) :
    hG.simplyBlockedHomologyTransposeEquiv R i y ∈
      (H').bigradedHatHomologyPiece R (G.O i) g := by
  obtain ⟨z, hz, rfl⟩ := ((H).mem_bigradedHatHomologyPiece_iff R i).mp hy
  rw [simplyBlockedHomologyTransposeEquiv_oneVariableSpecializationHomologyClass]
  apply (H').oneVariableSpecializationHomologyClass_mem_bigradedHatHomologyPiece
  rw [simplyBlockedChainEquiv_simplyBlockedTransposeCyclesEquiv]
  exact (H).simplyBlockedTransposeEquiv_mem_bigradedChainHatPiece R i hz

private theorem simplyBlockedHomologyTransposeCoefficientEquiv_homogeneous :
    LinearMap.IsHomogeneous
      (hG.simplyBlockedHomologyTransposeCoefficientEquiv R i).toLinearMap
      ((H).bigradedHatHomologyGrading R i).piece
      ((H').bigradedHatHomologyGrading R (G.O i)).piece 0 := by
  rw [LinearMap.isHomogeneous_def]
  intro g y hy
  simp only [OddComponentGridDiagram.bigradedHatHomologyGrading_piece] at hy ⊢
  rw [add_zero, LinearEquiv.coe_coe,
    simplyBlockedHomologyTransposeCoefficientEquiv_apply]
  exact hG.simplyBlockedHomologyTransposeEquiv_mem_bigradedHatHomologyPiece R i hy

/-- The specified reflection equivalence preserves and reflects both homology degrees. -/
@[simp]
theorem simplyBlockedHomologyTransposeEquiv_mem_bigradedHatHomologyPiece_iff
    {g : ℤ × ℤ} {y : (Base).obj (hG.simplyBlockedHomology R i)} :
    hG.simplyBlockedHomologyTransposeEquiv R i y ∈
        (H').bigradedHatHomologyPiece R (G.O i) g ↔
      y ∈ (H).bigradedHatHomologyPiece R i g := by
  constructor
  · intro hy
    have hinv := (hG.simplyBlockedHomologyTransposeCoefficientEquiv_homogeneous
      R i).linearEquiv_symm
    rw [← OddComponentGridDiagram.bigradedHatHomologyGrading_piece] at hy
    have hm := hinv.map_mem hy
    rw [add_zero, OddComponentGridDiagram.bigradedHatHomologyGrading_piece,
      LinearEquiv.coe_coe, ← simplyBlockedHomologyTransposeCoefficientEquiv_apply,
      LinearEquiv.symm_apply_apply] at hm
    exact hm
  · exact hG.simplyBlockedHomologyTransposeEquiv_mem_bigradedHatHomologyPiece R i

/-- Diagonal reflection restricted to a Maslov--Alexander homogeneous homology piece. -/
noncomputable def simplyBlockedHomologyTransposePieceEquiv (g : ℤ × ℤ) :
    (H).bigradedHatHomologyPiece R i g ≃ₗ[R] (H').bigradedHatHomologyPiece R (G.O i) g :=
  (hG.simplyBlockedHomologyTransposeCoefficientEquiv R i).ofSubmodules _ _ (by
    ext y
    rw [Submodule.mem_map_equiv,
      ← hG.simplyBlockedHomologyTransposeEquiv_mem_bigradedHatHomologyPiece_iff R i,
      ← simplyBlockedHomologyTransposeCoefficientEquiv_apply,
      LinearEquiv.apply_symm_apply]
    rfl)

/-- On underlying classes, the homogeneous-piece equivalence is the specified reflection. -/
@[simp]
theorem coe_simplyBlockedHomologyTransposePieceEquiv (g : ℤ × ℤ)
    (y : (H).bigradedHatHomologyPiece R i g) :
    (hG.simplyBlockedHomologyTransposePieceEquiv R i g y :
      (Base').obj ((hG').simplyBlockedHomology R (G.O i))) =
      hG.simplyBlockedHomologyTransposeEquiv R i
        (y : (Base).obj (hG.simplyBlockedHomology R i)) := by
  rw [simplyBlockedHomologyTransposePieceEquiv, LinearEquiv.ofSubmodules_apply,
    simplyBlockedHomologyTransposeCoefficientEquiv_apply]

/-- On underlying classes, inverse reflection on a homogeneous piece is the inverse
of the original homology reflection. -/
@[simp]
theorem coe_simplyBlockedHomologyTransposePieceEquiv_symm (g : ℤ × ℤ)
    (y : (H').bigradedHatHomologyPiece R (G.O i) g) :
    ((hG.simplyBlockedHomologyTransposePieceEquiv R i g).symm y :
      (Base).obj (hG.simplyBlockedHomology R i)) =
      (hG.simplyBlockedHomologyTransposeEquiv R i).symm
        (y : (Base').obj ((hG').simplyBlockedHomology R (G.O i))) := by
  rw [simplyBlockedHomologyTransposePieceEquiv, LinearEquiv.ofSubmodules_symm_apply,
    simplyBlockedHomologyTransposeCoefficientEquiv_symm_apply]

section Field

variable (K : Type*) [Field K] [CharP K 2]

/-- Diagonal reflection preserves the bigraded Poincaré series of simply blocked homology,
transporting the blocked marking to column `G.O i`. -/
theorem bigradedSimplyBlockedHomologyPoincareSeries_transpose :
    (hG').bigradedSimplyBlockedHomologyPoincareSeries K (G.O i) =
      hG.bigradedSimplyBlockedHomologyPoincareSeries K i := by
  ext g
  simp only [coeff_bigradedSimplyBlockedHomologyPoincareSeries]
  exact (hG.simplyBlockedHomologyTransposePieceEquiv K i g).finrank_eq.symm

/-- Diagonal reflection preserves the Alexander-graded Euler characteristic of simply
blocked knot-grid homology. -/
theorem gradedSimplyBlockedHomologyEulerChar_transpose :
    (hG').gradedSimplyBlockedHomologyEulerChar K (G.O i) =
      hG.gradedSimplyBlockedHomologyEulerChar K i := by
  rw [gradedSimplyBlockedHomologyEulerChar_eq_euler,
    gradedSimplyBlockedHomologyEulerChar_eq_euler,
    hG.bigradedSimplyBlockedHomologyPoincareSeries_transpose i K]

end Field

end TauCeti.GridDiagram.IsKnot
