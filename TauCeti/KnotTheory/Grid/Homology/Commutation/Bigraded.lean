/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Grading.SimplyBlocked
public import TauCeti.KnotTheory.Grid.Homology.Commutation.SimplyBlocked
public import TauCeti.KnotTheory.Grid.Homology.Series.SimplyBlocked

/-!
# Bigraded commutation invariance of simply blocked grid homology

The specified pentagon comparison on simply blocked knot-grid homology preserves and
reflects the integral `(O-Maslov, Alexander)` bigrading. Restricting it gives a coefficient-linear
equivalence on each homogeneous piece. Consequently both the bigraded Poincaré series and
the Alexander-graded Euler characteristic are unchanged by column commutation.

The total comparison is semilinear over the surviving polynomial variables, which are renamed
by the column transposition. Its coefficient-linear presentation below uses the actual
`ModuleCat.restrictScalars` homology carriers, so it is compatible with their internal gradings.
The inverse preserves degrees because an equivalence preserving the pieces of two internal
gradings also preserves their unique homogeneous decompositions.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Sections 4.6 and 5.1;
Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*, Section 3.1
(arXiv:math/0610559).
-/

public section

noncomputable section

namespace TauCeti.GridDiagram.IsKnot

variable {n : ℕ} {G : GridDiagram n} (hG : G.IsKnot)
  (R : Type*) [CommRing R] [CharP R 2] (C : ColumnCommutationData G) (i : Fin n)

local notation "σ" => Equiv.swap C.column (finRotate n C.column)
local notation "hG'" => C.isColumnCommutation.isKnot_iff.mpr hG
local notation "H" => hG.toOddComponentGridDiagram
local notation "H'" => GridDiagram.IsKnot.toOddComponentGridDiagram
  (C.isColumnCommutation.isKnot_iff.mpr hG)
local notation "Base" => ModuleCat.restrictScalars (MvPolynomial.C :
  R →+* MvPolynomial {c : Fin n // c ≠ i} R)
local notation "Base'" => ModuleCat.restrictScalars (MvPolynomial.C :
  R →+* MvPolynomial {c : Fin n // c ≠ σ i} R)

/-- The coefficient action on source homology is the action selected by
`ModuleCat.restrictScalars` along the inclusion of constant polynomials. -/
local instance : Module R (hG.simplyBlockedHomology R i) :=
  Module.compHom _ (MvPolynomial.C : R →+* MvPolynomial {c : Fin n // c ≠ i} R)
/-- The coefficient action on commuted homology is the same restricted-scalar action,
with the blocked column transported by the transposition. -/
local instance : Module R ((hG').simplyBlockedHomology R (σ i)) :=
  Module.compHom _ (MvPolynomial.C : R →+* MvPolynomial {c : Fin n // c ≠ σ i} R)

/-- The specified commutation equivalence, restricted to coefficient scalars rather than
surviving polynomial scalars. -/
noncomputable def simplyBlockedHomologyCommutationCoefficientEquiv :
    (Base).obj (hG.simplyBlockedHomology R i) ≃ₗ[R]
      (Base').obj ((hG').simplyBlockedHomology R (σ i)) :=
  (hG.simplyBlockedHomologyCommutationEquiv R C i).toAddEquiv.toLinearEquiv fun r y => by
    have hr : (simplyBlockedRenameEquiv R σ i).toRingEquiv (MvPolynomial.C r) =
        (MvPolynomial.C r : MvPolynomial {c : Fin n // c ≠ σ i} R) :=
      (simplyBlockedRenameEquiv R σ i).commutes r
    have he := (hG.simplyBlockedHomologyCommutationEquiv R C i).map_smulₛₗ
      (MvPolynomial.C r) y
    simp only [RingEquiv.coe_toRingHom, hr] at he
    exact he

/-- Restriction of coefficient scalars does not change the specified pentagon comparison. -/
@[simp]
theorem simplyBlockedHomologyCommutationCoefficientEquiv_apply
    (y : (Base).obj (hG.simplyBlockedHomology R i)) :
    hG.simplyBlockedHomologyCommutationCoefficientEquiv R C i y =
      hG.simplyBlockedHomologyCommutationMap R C i y :=
  congrFun (hG.coe_simplyBlockedHomologyCommutationEquiv R C i) y

/-- The pentagon comparison sends a homogeneous class to one of the same bidegree. -/
theorem simplyBlockedHomologyCommutationMap_mem_bigradedHatHomologyPiece
    {g : ℤ × ℤ} {y : (Base).obj (hG.simplyBlockedHomology R i)}
    (hy : y ∈ (H).bigradedHatHomologyPiece R i g) :
    hG.simplyBlockedHomologyCommutationMap R C i y ∈
      (H').bigradedHatHomologyPiece R (σ i) g := by
  obtain ⟨z, hz, rfl⟩ := ((H).mem_bigradedHatHomologyPiece_iff R i).mp hy
  rw [simplyBlockedHomologyCommutationMap_oneVariableSpecializationHomologyClass]
  apply (H').oneVariableSpecializationHomologyClass_mem_bigradedHatHomologyPiece
  rw [simplyBlockedChainEquiv_simplyBlockedCommutationCyclesMap]
  exact (H).simplyBlockedCommutationMap_mem_bigradedChainHatPiece R C i hz

private theorem simplyBlockedHomologyCommutationCoefficientEquiv_homogeneous :
    LinearMap.IsHomogeneous
      (hG.simplyBlockedHomologyCommutationCoefficientEquiv R C i).toLinearMap
      ((H).bigradedHatHomologyGrading R i).piece
      ((H').bigradedHatHomologyGrading R (σ i)).piece 0 := by
  rw [LinearMap.isHomogeneous_def]
  intro g y hy
  simp only [OddComponentGridDiagram.bigradedHatHomologyGrading_piece] at hy ⊢
  rw [add_zero, LinearEquiv.coe_coe,
    simplyBlockedHomologyCommutationCoefficientEquiv_apply]
  exact hG.simplyBlockedHomologyCommutationMap_mem_bigradedHatHomologyPiece R C i hy

/-- The specified commutation map preserves and reflects both homology degrees. -/
@[simp]
theorem simplyBlockedHomologyCommutationMap_mem_bigradedHatHomologyPiece_iff
    {g : ℤ × ℤ} {y : (Base).obj (hG.simplyBlockedHomology R i)} :
    hG.simplyBlockedHomologyCommutationMap R C i y ∈
        (H').bigradedHatHomologyPiece R (σ i) g ↔
      y ∈ (H).bigradedHatHomologyPiece R i g := by
  constructor
  · intro hy
    have hinv := (hG.simplyBlockedHomologyCommutationCoefficientEquiv_homogeneous
      R C i).linearEquiv_symm
    rw [← OddComponentGridDiagram.bigradedHatHomologyGrading_piece] at hy
    have hm := hinv.map_mem hy
    rw [add_zero, OddComponentGridDiagram.bigradedHatHomologyGrading_piece,
      LinearEquiv.coe_coe, ← simplyBlockedHomologyCommutationCoefficientEquiv_apply,
      LinearEquiv.symm_apply_apply] at hm
    exact hm
  · exact hG.simplyBlockedHomologyCommutationMap_mem_bigradedHatHomologyPiece R C i

/-- Commutation induces a coefficient-linear equivalence on every homogeneous homology piece.
It is the restriction of the specified pentagon comparison, not an arbitrarily chosen
isomorphism between modules of the same dimension. -/
noncomputable def simplyBlockedHomologyCommutationPieceEquiv (g : ℤ × ℤ) :
    (H).bigradedHatHomologyPiece R i g ≃ₗ[R] (H').bigradedHatHomologyPiece R (σ i) g :=
  (hG.simplyBlockedHomologyCommutationCoefficientEquiv R C i).ofSubmodules _ _ (by
    ext y
    rw [Submodule.mem_map_equiv,
      ← hG.simplyBlockedHomologyCommutationMap_mem_bigradedHatHomologyPiece_iff R C i,
      ← simplyBlockedHomologyCommutationCoefficientEquiv_apply,
      LinearEquiv.apply_symm_apply]
    rfl)

/-- On underlying classes, the equivalence of homogeneous pieces is the pentagon map. -/
@[simp]
theorem coe_simplyBlockedHomologyCommutationPieceEquiv (g : ℤ × ℤ)
    (y : (H).bigradedHatHomologyPiece R i g) :
    (hG.simplyBlockedHomologyCommutationPieceEquiv R C i g y :
      (Base').obj ((hG').simplyBlockedHomology R (σ i))) =
      hG.simplyBlockedHomologyCommutationMap R C i
        (y : (Base).obj (hG.simplyBlockedHomology R i)) := by
  rw [simplyBlockedHomologyCommutationPieceEquiv, LinearEquiv.ofSubmodules_apply,
    simplyBlockedHomologyCommutationCoefficientEquiv_apply]

section Field

variable (K : Type*) [Field K] [CharP K 2]

/-- The bigraded Poincaré series of simply blocked knot-grid homology is invariant under
column commutation, transporting the blocked marking by the column transposition. -/
theorem bigradedSimplyBlockedHomologyPoincareSeries_swapColumns :
    (hG').bigradedSimplyBlockedHomologyPoincareSeries K (σ i) =
      hG.bigradedSimplyBlockedHomologyPoincareSeries K i := by
  ext g
  simp only [coeff_bigradedSimplyBlockedHomologyPoincareSeries]
  exact (hG.simplyBlockedHomologyCommutationPieceEquiv K C i g).finrank_eq.symm

/-- The Alexander-graded Euler characteristic of simply blocked knot-grid homology is
invariant under column commutation. -/
theorem gradedSimplyBlockedHomologyEulerChar_swapColumns :
    (hG').gradedSimplyBlockedHomologyEulerChar K (σ i) =
      hG.gradedSimplyBlockedHomologyEulerChar K i := by
  rw [gradedSimplyBlockedHomologyEulerChar_eq_euler,
    gradedSimplyBlockedHomologyEulerChar_eq_euler,
    hG.bigradedSimplyBlockedHomologyPoincareSeries_swapColumns C i K]

end Field

end TauCeti.GridDiagram.IsKnot
