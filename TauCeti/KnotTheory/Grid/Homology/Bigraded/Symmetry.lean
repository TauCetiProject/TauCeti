/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Homology.Bigraded.Knot
public import TauCeti.KnotTheory.Grid.Homology.HalfTurn
public import TauCeti.KnotTheory.Grid.Homology.Transpose

/-!
# Diagonal reflection and half-turn on bigraded unblocked grid homology

The diagonal reflection `G ↦ G.transpose` and the half-turn `G ↦ G.rotate` induce semilinear
equivalences `GridDiagram.unblockedHomologyTransposeEquiv` and
`GridDiagram.unblockedHomologyRotateEquiv` on `GH⁻` (`Homology/Transpose.lean` and
`Homology/HalfTurn.lean`). On chains with an odd number of link components, both involutions
identify each `(O-Maslov, Alexander)` piece
(`OddComponentGridDiagram.transposeRenameEquiv_mem_bigradedChainMinusPiece_iff` and
`OddComponentGridDiagram.halfTurnRenameEquiv_mem_bigradedChainMinusPiece_iff`), so on homology they
identify every bidegree piece and restrict to ground-ring linear equivalences
`bigradedUnblockedHomologyTransposeEquiv` and `bigradedUnblockedHomologyRotateEquiv`.

For a knot grid, specializing all grid variables to `U` makes both symmetries `K[U]`-linear, giving
Maslov--Alexander bigraded `K[U]`-isomorphisms `bigradedUnblockedHomologyIsomorphic_transpose` and
`bigradedUnblockedHomologyIsomorphic_rotate`.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Chapters 3, 4.6 and 5.
The homogeneous piece equivalences parallel
`TauCeti.KnotTheory.Grid.Homology.Bigraded.CyclicPermutation`
(`OddComponentGridDiagram.bigradedUnblockedHomologyRelabelColumnsFinRotateEquiv`).
-/

public section

open MvPolynomial

namespace TauCeti

namespace OddComponentGridDiagram

variable {n : ℕ} (G : OddComponentGridDiagram n) (R : Type*) [CommRing R] [CharP R 2]

/-- The diagonal-reflection equivalence on `GH⁻` identifies every Maslov--Alexander piece. -/
@[simp]
theorem unblockedHomologyTransposeEquiv_mem_bigradedPiece_iff
    {g : ℤ × ℤ} {y : G.1.unblockedHomology R} :
    G.1.unblockedHomologyTransposeEquiv R y ∈
        G.transpose.bigradedUnblockedHomologyPiece R g ↔
      y ∈ G.bigradedUnblockedHomologyPiece R g :=
  G.unblockedHomologyEquiv_mem_bigradedPiece_iff R G.transpose
    (G.1.transposeRenameEquiv R)
    (G.1.unblockedDifferential_transpose_transposeRenameEquiv R)
    (G.1.unblockedHomologyTransposeEquiv R)
    (G.1.unblockedHomologyTransposeEquiv_unblockedHomologyClass R)
    (fun _ _ ↦ G.transposeRenameEquiv_mem_bigradedChainMinusPiece_iff R)

/-- The half-turn equivalence on `GH⁻` identifies every Maslov--Alexander piece. -/
@[simp]
theorem unblockedHomologyRotateEquiv_mem_bigradedPiece_iff
    {g : ℤ × ℤ} {y : G.1.unblockedHomology R} :
    G.1.unblockedHomologyRotateEquiv R y ∈
        G.rotate.bigradedUnblockedHomologyPiece R g ↔
      y ∈ G.bigradedUnblockedHomologyPiece R g :=
  G.unblockedHomologyEquiv_mem_bigradedPiece_iff R G.rotate
    (GridChain.halfTurnRenameEquiv R)
    (G.1.unblockedDifferential_rotate_halfTurnRenameEquiv R)
    (G.1.unblockedHomologyRotateEquiv R)
    (G.1.unblockedHomologyRotateEquiv_unblockedHomologyClass R)
    (fun _ _ ↦ G.halfTurnRenameEquiv_mem_bigradedChainMinusPiece_iff R)

private theorem isHomogeneous_unblockedHomologyTransposeEquiv :
    LinearMap.IsHomogeneous
      ((G.1.unblockedHomologyTransposeEquiv R).restrictScalarsOfCommutes R
        fun _ ↦ by rw [RingHom.coe_coe, AlgEquiv.coe_toRingEquiv, AlgEquiv.commutes]).toLinearMap
      (G.bigradedUnblockedHomologyGrading R).piece
      (G.transpose.bigradedUnblockedHomologyGrading R).piece 0 := by
  refine LinearMap.isHomogeneous_def.mpr fun g y hy ↦ ?_
  rw [bigradedUnblockedHomologyGrading_piece] at hy
  simpa only [add_zero, bigradedUnblockedHomologyGrading_piece, LinearEquiv.coe_coe,
    LinearEquiv.restrictScalarsOfCommutes_apply] using
    (G.unblockedHomologyTransposeEquiv_mem_bigradedPiece_iff R).mpr hy

/-- Diagonal reflection gives a ground-ring linear equivalence in each bidegree of `GH⁻`. -/
noncomputable def bigradedUnblockedHomologyTransposeEquiv (g : ℤ × ℤ) :
    G.bigradedUnblockedHomologyPiece R g ≃ₗ[R]
      G.transpose.bigradedUnblockedHomologyPiece R g :=
  ((LinearEquiv.ofEq _ _ (G.bigradedUnblockedHomologyGrading_piece R g).symm).trans
    ((G.isHomogeneous_unblockedHomologyTransposeEquiv R).pieceLinearEquiv g)).trans
    (LinearEquiv.ofEq _ _ (G.transpose.bigradedUnblockedHomologyGrading_piece R g))

/-- On underlying classes the transpose piece equivalence is `unblockedHomologyTransposeEquiv`. -/
@[simp]
theorem coe_bigradedUnblockedHomologyTransposeEquiv (g : ℤ × ℤ)
    (y : G.bigradedUnblockedHomologyPiece R g) :
    (G.bigradedUnblockedHomologyTransposeEquiv R g y : G.1.transpose.unblockedHomology R) =
      G.1.unblockedHomologyTransposeEquiv R y := by
  simp only [bigradedUnblockedHomologyTransposeEquiv, LinearEquiv.trans_apply,
    LinearEquiv.coe_ofEq_apply, LinearMap.IsHomogeneous.coe_pieceLinearEquiv_apply]
  rw [LinearEquiv.restrictScalarsOfCommutes_apply]

/-- The inverse transpose piece equivalence acts as `(unblockedHomologyTransposeEquiv R).symm`. -/
@[simp]
theorem coe_bigradedUnblockedHomologyTransposeEquiv_symm (g : ℤ × ℤ)
    (y : G.transpose.bigradedUnblockedHomologyPiece R g) :
    ((G.bigradedUnblockedHomologyTransposeEquiv R g).symm y : G.1.unblockedHomology R) =
      (G.1.unblockedHomologyTransposeEquiv R).symm y := by
  simp only [bigradedUnblockedHomologyTransposeEquiv, LinearEquiv.symm_trans_apply,
    LinearEquiv.ofEq_symm, LinearEquiv.coe_ofEq_apply,
    LinearMap.IsHomogeneous.coe_pieceLinearEquiv_symm_apply]
  rw [LinearEquiv.restrictScalarsOfCommutes_symm_apply]

private theorem isHomogeneous_unblockedHomologyRotateEquiv :
    LinearMap.IsHomogeneous
      ((G.1.unblockedHomologyRotateEquiv R).restrictScalarsOfCommutes R
        fun _ ↦ by rw [RingHom.coe_coe, AlgEquiv.coe_toRingEquiv, AlgEquiv.commutes]).toLinearMap
      (G.bigradedUnblockedHomologyGrading R).piece
      (G.rotate.bigradedUnblockedHomologyGrading R).piece 0 := by
  refine LinearMap.isHomogeneous_def.mpr fun g y hy ↦ ?_
  rw [bigradedUnblockedHomologyGrading_piece] at hy
  simpa only [add_zero, bigradedUnblockedHomologyGrading_piece, LinearEquiv.coe_coe,
    LinearEquiv.restrictScalarsOfCommutes_apply] using
    (G.unblockedHomologyRotateEquiv_mem_bigradedPiece_iff R).mpr hy

/-- The half-turn gives a ground-ring linear equivalence in each bidegree of `GH⁻`. -/
noncomputable def bigradedUnblockedHomologyRotateEquiv (g : ℤ × ℤ) :
    G.bigradedUnblockedHomologyPiece R g ≃ₗ[R]
      G.rotate.bigradedUnblockedHomologyPiece R g :=
  ((LinearEquiv.ofEq _ _ (G.bigradedUnblockedHomologyGrading_piece R g).symm).trans
    ((G.isHomogeneous_unblockedHomologyRotateEquiv R).pieceLinearEquiv g)).trans
    (LinearEquiv.ofEq _ _ (G.rotate.bigradedUnblockedHomologyGrading_piece R g))

/-- On underlying classes the half-turn piece equivalence is `unblockedHomologyRotateEquiv`. -/
@[simp]
theorem coe_bigradedUnblockedHomologyRotateEquiv (g : ℤ × ℤ)
    (y : G.bigradedUnblockedHomologyPiece R g) :
    (G.bigradedUnblockedHomologyRotateEquiv R g y : G.1.rotate.unblockedHomology R) =
      G.1.unblockedHomologyRotateEquiv R y := by
  simp only [bigradedUnblockedHomologyRotateEquiv, LinearEquiv.trans_apply,
    LinearEquiv.coe_ofEq_apply, LinearMap.IsHomogeneous.coe_pieceLinearEquiv_apply]
  rw [LinearEquiv.restrictScalarsOfCommutes_apply]

/-- The inverse half-turn piece equivalence acts as `(unblockedHomologyRotateEquiv R).symm`. -/
@[simp]
theorem coe_bigradedUnblockedHomologyRotateEquiv_symm (g : ℤ × ℤ)
    (y : G.rotate.bigradedUnblockedHomologyPiece R g) :
    ((G.bigradedUnblockedHomologyRotateEquiv R g).symm y : G.1.unblockedHomology R) =
      (G.1.unblockedHomologyRotateEquiv R).symm y := by
  simp only [bigradedUnblockedHomologyRotateEquiv, LinearEquiv.symm_trans_apply,
    LinearEquiv.ofEq_symm, LinearEquiv.coe_ofEq_apply,
    LinearMap.IsHomogeneous.coe_pieceLinearEquiv_symm_apply]
  rw [LinearEquiv.restrictScalarsOfCommutes_symm_apply]

end OddComponentGridDiagram

namespace GridDiagram.IsKnot

variable {n : ℕ} {G : GridDiagram n} (hG : G.IsKnot) (K : Type*) [CommRing K] [CharP K 2]

/-- The diagonal reflection of a knot grid preserves `GH⁻` as a Maslov--Alexander bigraded
`K[U]`-module. -/
theorem bigradedUnblockedHomologyIsomorphic_transpose :
    hG.BigradedUnblockedHomologyIsomorphic (G.isKnot_transpose.mpr hG) K := by
  refine .of_semilinearMap (fun p ↦ ?_)
    (G.unblockedHomologyTransposeEquiv K).toLinearMap
    (G.unblockedHomologyTransposeEquiv K).bijective fun g y hy ↦ ?_
  · simp [aeval_rename, Function.comp_def]
  · rw [bigradedUnblockedHomologyGrading_piece] at hy ⊢
    exact (hG.toOddComponentGridDiagram.unblockedHomologyTransposeEquiv_mem_bigradedPiece_iff K).mpr
      hy

/-- The half-turn of a knot grid preserves `GH⁻` as a Maslov--Alexander bigraded `K[U]`-module. -/
theorem bigradedUnblockedHomologyIsomorphic_rotate :
    hG.BigradedUnblockedHomologyIsomorphic (G.isKnot_rotate.mpr hG) K := by
  refine .of_semilinearMap (fun p ↦ ?_)
    (G.unblockedHomologyRotateEquiv K).toLinearMap
    (G.unblockedHomologyRotateEquiv K).bijective fun g y hy ↦ ?_
  · simp [aeval_rename, Function.comp_def]
  · rw [bigradedUnblockedHomologyGrading_piece] at hy ⊢
    exact (hG.toOddComponentGridDiagram.unblockedHomologyRotateEquiv_mem_bigradedPiece_iff K).mpr hy

end GridDiagram.IsKnot

end TauCeti
