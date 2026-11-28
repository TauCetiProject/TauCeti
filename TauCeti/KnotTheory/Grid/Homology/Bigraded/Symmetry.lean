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
Maslov--Alexander bigraded `K[U]`-isomorphisms `bigradedUnblockedHomologyIsomorphic_transpose`
(`Homology/Transpose.lean`) and `bigradedUnblockedHomologyIsomorphic_rotate`
(`Homology/HalfTurn.lean`).

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
    {g : ℤ × ℤ} {y : G.val.unblockedHomology R} :
    G.val.unblockedHomologyTransposeEquiv R y ∈
        G.transpose.bigradedUnblockedHomologyPiece R g ↔
      y ∈ G.bigradedUnblockedHomologyPiece R g :=
  G.unblockedHomologyEquiv_mem_bigradedPiece_iff R G.transpose
    (G.val.transposeRenameEquiv R)
    (G.val.unblockedDifferential_transpose_transposeRenameEquiv R)
    (G.val.unblockedHomologyTransposeEquiv R)
    (G.val.unblockedHomologyTransposeEquiv_unblockedHomologyClass R)
    (fun _ _ ↦ G.transposeRenameEquiv_mem_bigradedChainMinusPiece_iff R)

/-- The half-turn equivalence on `GH⁻` identifies every Maslov--Alexander piece. -/
@[simp]
theorem unblockedHomologyRotateEquiv_mem_bigradedPiece_iff
    {g : ℤ × ℤ} {y : G.val.unblockedHomology R} :
    G.val.unblockedHomologyRotateEquiv R y ∈
        G.rotate.bigradedUnblockedHomologyPiece R g ↔
      y ∈ G.bigradedUnblockedHomologyPiece R g :=
  G.unblockedHomologyEquiv_mem_bigradedPiece_iff R G.rotate
    (GridChain.halfTurnRenameEquiv R)
    (G.val.unblockedDifferential_rotate_halfTurnRenameEquiv R)
    (G.val.unblockedHomologyRotateEquiv R)
    (G.val.unblockedHomologyRotateEquiv_unblockedHomologyClass R)
    (fun _ _ ↦ G.halfTurnRenameEquiv_mem_bigradedChainMinusPiece_iff R)

/-- Diagonal reflection gives a ground-ring linear equivalence in each bidegree of `GH⁻`. -/
noncomputable def bigradedUnblockedHomologyTransposeEquiv (g : ℤ × ℤ) :
    G.bigradedUnblockedHomologyPiece R g ≃ₗ[R]
      G.transpose.bigradedUnblockedHomologyPiece R g :=
  G.bigradedUnblockedHomologyPieceEquivOfSemilinear R G.transpose
    (fun _ ↦ by rw [RingHom.coe_coe, AlgEquiv.coe_toRingEquiv, AlgEquiv.commutes])
    (G.val.unblockedHomologyTransposeEquiv R)
    (fun _ _ hy ↦ (G.unblockedHomologyTransposeEquiv_mem_bigradedPiece_iff R).mpr hy) g

/-- On underlying classes the transpose piece equivalence is `unblockedHomologyTransposeEquiv`. -/
@[simp]
theorem coe_bigradedUnblockedHomologyTransposeEquiv (g : ℤ × ℤ)
    (y : G.bigradedUnblockedHomologyPiece R g) :
    (G.bigradedUnblockedHomologyTransposeEquiv R g y : G.val.transpose.unblockedHomology R) =
      G.val.unblockedHomologyTransposeEquiv R y := by
  rw [bigradedUnblockedHomologyTransposeEquiv]
  exact G.coe_bigradedUnblockedHomologyPieceEquivOfSemilinear R G.transpose _ _ _ g y

/-- The inverse transpose piece equivalence acts as `(unblockedHomologyTransposeEquiv R).symm`. -/
@[simp]
theorem coe_bigradedUnblockedHomologyTransposeEquiv_symm (g : ℤ × ℤ)
    (y : G.transpose.bigradedUnblockedHomologyPiece R g) :
    ((G.bigradedUnblockedHomologyTransposeEquiv R g).symm y : G.val.unblockedHomology R) =
      (G.val.unblockedHomologyTransposeEquiv R).symm y := by
  rw [bigradedUnblockedHomologyTransposeEquiv]
  exact G.coe_bigradedUnblockedHomologyPieceEquivOfSemilinear_symm R G.transpose _ _ _ g y

/-- The half-turn gives a ground-ring linear equivalence in each bidegree of `GH⁻`. -/
noncomputable def bigradedUnblockedHomologyRotateEquiv (g : ℤ × ℤ) :
    G.bigradedUnblockedHomologyPiece R g ≃ₗ[R]
      G.rotate.bigradedUnblockedHomologyPiece R g :=
  G.bigradedUnblockedHomologyPieceEquivOfSemilinear R G.rotate
    (fun _ ↦ by rw [RingHom.coe_coe, AlgEquiv.coe_toRingEquiv, AlgEquiv.commutes])
    (G.val.unblockedHomologyRotateEquiv R)
    (fun _ _ hy ↦ (G.unblockedHomologyRotateEquiv_mem_bigradedPiece_iff R).mpr hy) g

/-- On underlying classes the half-turn piece equivalence is `unblockedHomologyRotateEquiv`. -/
@[simp]
theorem coe_bigradedUnblockedHomologyRotateEquiv (g : ℤ × ℤ)
    (y : G.bigradedUnblockedHomologyPiece R g) :
    (G.bigradedUnblockedHomologyRotateEquiv R g y : G.val.rotate.unblockedHomology R) =
      G.val.unblockedHomologyRotateEquiv R y := by
  rw [bigradedUnblockedHomologyRotateEquiv]
  exact G.coe_bigradedUnblockedHomologyPieceEquivOfSemilinear R G.rotate _ _ _ g y

/-- The inverse half-turn piece equivalence acts as `(unblockedHomologyRotateEquiv R).symm`. -/
@[simp]
theorem coe_bigradedUnblockedHomologyRotateEquiv_symm (g : ℤ × ℤ)
    (y : G.rotate.bigradedUnblockedHomologyPiece R g) :
    ((G.bigradedUnblockedHomologyRotateEquiv R g).symm y : G.val.unblockedHomology R) =
      (G.val.unblockedHomologyRotateEquiv R).symm y := by
  rw [bigradedUnblockedHomologyRotateEquiv]
  exact G.coe_bigradedUnblockedHomologyPieceEquivOfSemilinear_symm R G.rotate _ _ _ g y

end OddComponentGridDiagram

end TauCeti
