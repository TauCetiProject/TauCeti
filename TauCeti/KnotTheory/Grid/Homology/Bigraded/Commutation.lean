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
`GridDiagram.unblockedHomologyCommutationMap` is bijective
(`GridDiagram.unblockedHomologyCommutationMap_bijective`), hence upgrades to a semilinear
equivalence `GridDiagram.unblockedHomologyCommutationEquiv` along the transposition of the two
swapped column variables.

When `G` has an odd number of link components, this equivalence preserves and reflects every
`(O-Maslov, Alexander)` homogeneous piece (`unblockedHomologyCommutationMap_mem_bigradedPiece_iff`),
inducing ground-ring linear equivalences `bigradedUnblockedHomologyCommutationEquiv` in each
bidegree.

For a knot grid, specializing all grid variables to `U` makes the commutation map of any column turn
`C` homogeneous of bidegree `G.commutationBidegree C` over `K[U]`
(`isHomogeneous_unblockedHomologyCommutationLinearMap_bigraded`). Since `commutationBidegree`
vanishes for a column commutation, `GH⁻` is invariant as a Maslov--Alexander bigraded `K[U]`-module
under column commutations (`bigradedUnblockedHomologyIsomorphic_swapColumns`,
`bigradedUnblockedHomologyIsomorphic_of_isColumnCommutation`) and, by diagonal reflection, under
all elementary row or column commutations (`bigradedUnblockedHomologyIsomorphic_of_isCommutation`).

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 5.1, and
Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*, Section 3.1.
-/

public section

open MvPolynomial

namespace TauCeti

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n) (C : ColumnCommutationData G) (R : Type*)
  [CommRing R] [CharP R 2]

/-- The pentagon-counting map of a validated column commutation as a semilinear equivalence on
`GH⁻`, along the transposition of the two swapped column variables. -/
noncomputable def unblockedHomologyCommutationEquiv :
    G.unblockedHomology R ≃ₛₗ[((renameEquiv R
      (Equiv.swap C.column (finRotate n C.column))).toRingEquiv :
      MvPolynomial (Fin n) R →+* MvPolynomial (Fin n) R)]
      (G.swapColumns C.column (finRotate n C.column)).unblockedHomology R :=
  LinearEquiv.ofBijective (G.unblockedHomologyCommutationMap R C)
    (G.unblockedHomologyCommutationMap_bijective C R)

/-- `unblockedHomologyCommutationEquiv` acts by `unblockedHomologyCommutationMap`. -/
@[simp]
theorem unblockedHomologyCommutationEquiv_apply (y : G.unblockedHomology R) :
    G.unblockedHomologyCommutationEquiv C R y = G.unblockedHomologyCommutationMap R C y :=
  LinearEquiv.ofBijective_apply _ y

end GridDiagram

namespace OddComponentGridDiagram

variable {n : ℕ} (G : OddComponentGridDiagram n) (R : Type*) [CommRing R] [CharP R 2]
  (C : GridDiagram.ColumnCommutationData G.1)

/-- The commutation map on `GH⁻` preserves and reflects every Maslov--Alexander piece. -/
@[simp]
theorem unblockedHomologyCommutationMap_mem_bigradedPiece_iff
    {g : ℤ × ℤ} {y : G.1.unblockedHomology R} :
    G.1.unblockedHomologyCommutationMap R C y ∈
        (G.swapColumns C).bigradedUnblockedHomologyPiece R g ↔
      y ∈ G.bigradedUnblockedHomologyPiece R g := by
  let eR : G.1.unblockedHomology R ≃ₗ[R] (G.swapColumns C).1.unblockedHomology R :=
    { toEquiv := (G.1.unblockedHomologyCommutationEquiv C R).toEquiv
      map_add' := fun x z ↦ (G.1.unblockedHomologyCommutationEquiv C R).map_add x z
      map_smul' := map_smul_of_renameEquiv (Equiv.swap C.column (finRotate n C.column))
        (G.1.unblockedHomologyCommutationEquiv C R) }
  have heR_apply (z : G.1.unblockedHomology R) :
      eR z = G.1.unblockedHomologyCommutationMap R C z :=
    G.1.unblockedHomologyCommutationEquiv_apply C R z
  have he : LinearMap.IsHomogeneous eR.toLinearMap
      (G.bigradedUnblockedHomologyGrading R).piece
      ((G.swapColumns C).bigradedUnblockedHomologyGrading R).piece 0 := by
    refine LinearMap.isHomogeneous_def.mpr fun p z hz ↦ ?_
    rw [bigradedUnblockedHomologyGrading_piece] at hz
    simpa only [add_zero, bigradedUnblockedHomologyGrading_piece, LinearEquiv.coe_coe,
      heR_apply] using G.unblockedHomologyCommutationMap_mem_bigradedUnblockedHomologyPiece R C hz
  constructor
  · intro hy
    rw [← bigradedUnblockedHomologyGrading_piece, ← heR_apply] at hy
    have h := he.linearEquiv_symm.map_mem hy
    simpa only [add_zero, bigradedUnblockedHomologyGrading_piece, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply] using h
  · exact G.unblockedHomologyCommutationMap_mem_bigradedUnblockedHomologyPiece R C

/-- A validated column commutation gives a ground-ring linear equivalence in each Maslov--Alexander
bidegree of `GH⁻`. -/
noncomputable def bigradedUnblockedHomologyCommutationEquiv (g : ℤ × ℤ) :
    G.bigradedUnblockedHomologyPiece R g ≃ₗ[R]
      (G.swapColumns C).bigradedUnblockedHomologyPiece R g where
  toEquiv := (G.1.unblockedHomologyCommutationEquiv C R).toEquiv.subtypeEquiv
    fun _ ↦ (G.unblockedHomologyCommutationMap_mem_bigradedPiece_iff R C).symm
  map_add' x y := Subtype.ext ((G.1.unblockedHomologyCommutationEquiv C R).map_add x y)
  map_smul' r y := Subtype.ext
    (map_smul_of_renameEquiv (Equiv.swap C.column (finRotate n C.column))
      (G.1.unblockedHomologyCommutationEquiv C R) r y)

/-- On underlying classes the piece equivalence acts by `unblockedHomologyCommutationMap`. -/
@[simp]
theorem coe_bigradedUnblockedHomologyCommutationEquiv (g : ℤ × ℤ)
    (y : G.bigradedUnblockedHomologyPiece R g) :
    (G.bigradedUnblockedHomologyCommutationEquiv R C g y :
        (G.1.swapColumns C.column (finRotate n C.column)).unblockedHomology R) =
      G.1.unblockedHomologyCommutationMap R C y :=
  G.1.unblockedHomologyCommutationEquiv_apply C R y

/-- The inverse piece equivalence acts by `(unblockedHomologyCommutationEquiv C R).symm`. -/
@[simp]
theorem coe_bigradedUnblockedHomologyCommutationEquiv_symm (g : ℤ × ℤ)
    (y : (G.swapColumns C).bigradedUnblockedHomologyPiece R g) :
    ((G.bigradedUnblockedHomologyCommutationEquiv R C g).symm y : G.1.unblockedHomology R) =
      (G.1.unblockedHomologyCommutationEquiv C R).symm y :=
  (rfl)

end OddComponentGridDiagram

namespace GridDiagram.IsKnot

variable {n : ℕ} {G : GridDiagram n} (hG : G.IsKnot) (K : Type*) [CommRing K] [CharP K 2]

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
  rw [bigradedUnblockedHomologyGrading_piece] at hy ⊢
  rw [unblockedHomologyCommutationLinearMap_apply]
  change G.unblockedHomologyCommutationMap K C y ∈
    (hG.toOddComponentGridDiagram.swapColumns C).bigradedUnblockedHomologyPiece K
      (g + G.commutationBidegree C)
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
