/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Homology.Bigraded.Symmetry
public import TauCeti.KnotTheory.Grid.Homology.Commutation.Invariance

/-!
# Commutation invariance of bigraded unblocked grid homology

For validated column-commutation data `C` on a grid diagram `G`, the pentagon-counting homology map
`GridDiagram.unblockedHomologyCommutationMap` upgrades to the semilinear equivalence
`GridDiagram.unblockedHomologyCommutationEquiv`
(`TauCeti.KnotTheory.Grid.Homology.Commutation.Invariance`). When `G` has an odd number of link
components, this equivalence preserves and reflects every `(O-Maslov, Alexander)` homogeneous piece
(`unblockedHomologyCommutationMap_mem_bigradedPiece_iff`), inducing ground-ring linear equivalences
`bigradedUnblockedHomologyCommutationEquiv` in each bidegree.

For a knot grid, specializing all grid variables to `U` makes the commutation map of any column turn
`C` homogeneous of bidegree `G.commutationBidegree C` over `K[U]`
(`isHomogeneous_unblockedHomologyCommutationLinearMap_bigraded`). Since `commutationBidegree`
vanishes for a column commutation, `GH⁻` is invariant as a Maslov--Alexander bigraded
`K[U]`-module under column commutations (`bigradedUnblockedHomologyIsomorphic_swapColumns`,
`bigradedUnblockedHomologyIsomorphic_of_isColumnCommutation`) and, by diagonal reflection, under
all elementary row or column commutations (`bigradedUnblockedHomologyIsomorphic_of_isCommutation`).

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 5.1, and
Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*, Section 3.1.
The knot homogeneity and commutation invariance theorems adapt their Alexander-graded counterparts
`GridDiagram.IsKnot.isHomogeneous_unblockedHomologyCommutationLinearMap`
(`TauCeti.KnotTheory.Grid.Homology.Commutation.Basic`) and
`GridDiagram.IsKnot.unblockedHomologyIsomorphic_of_isCommutation`
(`TauCeti.KnotTheory.Grid.Homology.Commutation.Invariance`).
-/

public section

open MvPolynomial

namespace TauCeti

namespace OddComponentGridDiagram

variable {n : ℕ} (G : OddComponentGridDiagram n) (R : Type*) [CommRing R] [CharP R 2]
  (C : GridDiagram.ColumnCommutationData G.1)

private theorem isHomogeneous_unblockedHomologyCommutationEquiv :
    LinearMap.IsHomogeneous
      ((G.1.unblockedHomologyCommutationEquiv C R).restrictScalarsOfCommutes R
        fun _ ↦ by rw [RingHom.coe_coe, AlgEquiv.coe_toRingEquiv, AlgEquiv.commutes]).toLinearMap
      (G.bigradedUnblockedHomologyGrading R).piece
      ((G.swapColumns C).bigradedUnblockedHomologyGrading R).piece 0 := by
  refine LinearMap.isHomogeneous_def.mpr fun p z hz ↦ ?_
  rw [bigradedUnblockedHomologyGrading_piece] at hz
  simpa only [add_zero, bigradedUnblockedHomologyGrading_piece, LinearEquiv.coe_coe,
    LinearEquiv.restrictScalarsOfCommutes_apply,
    GridDiagram.unblockedHomologyCommutationEquiv_apply] using
    G.unblockedHomologyCommutationMap_mem_bigradedUnblockedHomologyPiece R C hz

/-- The commutation map on `GH⁻` preserves and reflects every Maslov--Alexander piece. -/
@[simp]
theorem unblockedHomologyCommutationMap_mem_bigradedPiece_iff
    {g : ℤ × ℤ} {y : G.1.unblockedHomology R} :
    G.1.unblockedHomologyCommutationMap R C y ∈
        (G.swapColumns C).bigradedUnblockedHomologyPiece R g ↔
      y ∈ G.bigradedUnblockedHomologyPiece R g := by
  simpa only [bigradedUnblockedHomologyGrading_piece,
    LinearEquiv.restrictScalarsOfCommutes_apply,
    GridDiagram.unblockedHomologyCommutationEquiv_apply] using
    (G.isHomogeneous_unblockedHomologyCommutationEquiv R C).linearEquiv_mem_piece_iff
      (p := g) (x := y)

/-- A validated column commutation gives a ground-ring linear equivalence in each Maslov--Alexander
bidegree of `GH⁻`. -/
noncomputable def bigradedUnblockedHomologyCommutationEquiv (g : ℤ × ℤ) :
    G.bigradedUnblockedHomologyPiece R g ≃ₗ[R]
      (G.swapColumns C).bigradedUnblockedHomologyPiece R g :=
  ((LinearEquiv.ofEq _ _ (G.bigradedUnblockedHomologyGrading_piece R g).symm).trans
    ((G.isHomogeneous_unblockedHomologyCommutationEquiv R C).pieceLinearEquiv g)).trans
    (LinearEquiv.ofEq _ _ ((G.swapColumns C).bigradedUnblockedHomologyGrading_piece R g))

/-- On underlying classes the piece equivalence acts by `unblockedHomologyCommutationMap`. -/
@[simp]
theorem coe_bigradedUnblockedHomologyCommutationEquiv (g : ℤ × ℤ)
    (y : G.bigradedUnblockedHomologyPiece R g) :
    (G.bigradedUnblockedHomologyCommutationEquiv R C g y :
        (G.1.swapColumns C.column (finRotate n C.column)).unblockedHomology R) =
      G.1.unblockedHomologyCommutationMap R C y := by
  simp only [bigradedUnblockedHomologyCommutationEquiv, LinearEquiv.trans_apply,
    LinearEquiv.coe_ofEq_apply, LinearMap.IsHomogeneous.coe_pieceLinearEquiv_apply]
  rw [LinearEquiv.restrictScalarsOfCommutes_apply,
    GridDiagram.unblockedHomologyCommutationEquiv_apply]

/-- The inverse piece equivalence acts by `(unblockedHomologyCommutationEquiv C R).symm`. -/
@[simp]
theorem coe_bigradedUnblockedHomologyCommutationEquiv_symm (g : ℤ × ℤ)
    (y : (G.swapColumns C).bigradedUnblockedHomologyPiece R g) :
    ((G.bigradedUnblockedHomologyCommutationEquiv R C g).symm y : G.1.unblockedHomology R) =
      (G.1.unblockedHomologyCommutationEquiv C R).symm y := by
  simp only [bigradedUnblockedHomologyCommutationEquiv, LinearEquiv.symm_trans_apply,
    LinearEquiv.ofEq_symm, LinearEquiv.coe_ofEq_apply,
    LinearMap.IsHomogeneous.coe_pieceLinearEquiv_symm_apply]
  rw [LinearEquiv.restrictScalarsOfCommutes_symm_apply]

end OddComponentGridDiagram

namespace GridDiagram.IsKnot

variable {n : ℕ} {G : GridDiagram n} (hG : G.IsKnot) (K : Type*) [CommRing K] [CharP K 2]

/-- The degree-`g` piece of a swapped knot grid's bigrading agrees with the piece on
`hG.toOddComponentGridDiagram.swapColumns C`. -/
theorem bigradedUnblockedHomologyGrading_swapColumns_piece (C : ColumnTurn n) (g : ℤ × ℤ) :
    ((hG.swapColumns C.column (finRotate n C.column)).bigradedUnblockedHomologyGrading K).piece g =
      (hG.toOddComponentGridDiagram.swapColumns C).bigradedUnblockedHomologyPiece K g :=
  (hG.swapColumns C.column (finRotate n C.column)).bigradedUnblockedHomologyGrading_piece_eq_mk
    K _ g

open OddComponentGridDiagram in
/-- For a knot grid, the `K[U]`-linear commutation map of any column turn `C` is homogeneous for the
Maslov--Alexander bigradings, of bidegree `G.commutationBidegree C`. -/
theorem isHomogeneous_unblockedHomologyCommutationLinearMap_bigraded (C : ColumnTurn n) :
    letI := hG.unblockedHomologyModule K
    letI := (hG.swapColumns C.column (finRotate n C.column)).unblockedHomologyModule K
    LinearMap.IsHomogeneous (hG.unblockedHomologyCommutationLinearMap K C)
      (hG.bigradedUnblockedHomologyGrading K).piece
      ((hG.swapColumns C.column (finRotate n C.column)).bigradedUnblockedHomologyGrading K).piece
      (G.commutationBidegree C) := by
  let _ := hG.unblockedHomologyModule K
  let _ := (hG.swapColumns C.column (finRotate n C.column)).unblockedHomologyModule K
  refine LinearMap.isHomogeneous_def.mpr fun g y hy ↦ ?_
  rw [hG.bigradedUnblockedHomologyGrading_piece] at hy
  rw [hG.bigradedUnblockedHomologyGrading_swapColumns_piece,
    unblockedHomologyCommutationLinearMap_apply]
  exact unblockedHomologyCommutationMap_mem_bigradedUnblockedHomologyPiece_add _ K C hy

/-- **`GH⁻` is invariant under column commutation as a Maslov--Alexander bigraded
`K[U]`-module.** -/
theorem bigradedUnblockedHomologyIsomorphic_swapColumns (C : ColumnCommutationData G) :
    hG.BigradedUnblockedHomologyIsomorphic
      (hG.swapColumns C.column (finRotate n C.column)) K := by
  refine .of_semilinearMap (fun p ↦ ?_) (G.unblockedHomologyCommutationMap K C)
    (G.unblockedHomologyCommutationMap_bijective C K) fun g y hy ↦ ?_
  · simp [aeval_rename, Function.comp_def]
  · let _ := hG.unblockedHomologyModule K
    let _ := (hG.swapColumns C.column (finRotate n C.column)).unblockedHomologyModule K
    simpa using (hG.isHomogeneous_unblockedHomologyCommutationLinearMap_bigraded K C).map_mem hy

/-- **`GH⁻` is invariant under elementary column commutations as a bigraded `K[U]`-module.** -/
theorem bigradedUnblockedHomologyIsomorphic_of_isColumnCommutation {G' : GridDiagram n}
    (hG' : G'.IsKnot) (h : IsColumnCommutation G G') :
    hG.BigradedUnblockedHomologyIsomorphic hG' K := by
  obtain ⟨C, rfl⟩ := isColumnCommutation_iff_exists_columnCommutationData.mp h
  exact hG.bigradedUnblockedHomologyIsomorphic_swapColumns K C

/-- **`GH⁻` is invariant under elementary row or column commutations as a bigraded
`K[U]`-module.** -/
theorem bigradedUnblockedHomologyIsomorphic_of_isCommutation {G' : GridDiagram n}
    (hG' : G'.IsKnot) (h : IsCommutation G G') :
    hG.BigradedUnblockedHomologyIsomorphic hG' K := by
  rcases (isCommutation_iff G G').mp h with h | h
  · exact (hG.bigradedUnblockedHomologyIsomorphic_transpose K).trans
      ((bigradedUnblockedHomologyIsomorphic_of_isColumnCommutation _ K _
        ((isColumnCommutation_transpose G G').mpr h)).trans
        (hG'.bigradedUnblockedHomologyIsomorphic_transpose K).symm)
  · exact hG.bigradedUnblockedHomologyIsomorphic_of_isColumnCommutation K hG' h

end GridDiagram.IsKnot

end TauCeti
