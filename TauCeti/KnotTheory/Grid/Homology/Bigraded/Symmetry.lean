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
identify each `(O-Maslov, Alexander)` piece, so on homology they identify every bidegree piece and
restrict to ground-ring linear equivalences `bigradedUnblockedHomologyTransposeEquiv` and
`bigradedUnblockedHomologyRotateEquiv`.

For a knot grid, specializing all grid variables to `U` makes both symmetries `K[U]`-linear, giving
Maslov--Alexander bigraded `K[U]`-isomorphisms `bigradedUnblockedHomologyIsomorphic_transpose` and
`bigradedUnblockedHomologyIsomorphic_rotate`.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Chapters 3, 4.6 and 5.
-/

public section

open MvPolynomial

namespace TauCeti

namespace OddComponentGridDiagram

section Chains

variable {n : ℕ} (G : OddComponentGridDiagram n) (R : Type*) [CommSemiring R]

/-- The diagonal reflection identifies each Maslov--Alexander piece of `GC⁻`. -/
theorem transposeRenameEquiv_mem_bigradedChainMinusPiece_iff
    {g : ℤ × ℤ} {c : GridChainMinus R n} :
    G.1.transposeRenameEquiv R c ∈ G.transpose.bigradedChainMinusPiece R g ↔
      c ∈ G.bigradedChainMinusPiece R g := by
  refine ⟨fun hc ↦ ?_, G.transposeRenameEquiv_mem_bigradedChainMinusPiece R⟩
  have h := G.transpose.transposeRenameEquiv_mem_bigradedChainMinusPiece R hc
  rwa [G.val_transpose, G.1.transposeRenameEquiv_transpose_transposeRenameEquiv,
    G.transpose_transpose] at h

/-- The half-turn identifies each Maslov--Alexander piece of `GC⁻`. -/
theorem halfTurnRenameEquiv_mem_bigradedChainMinusPiece_iff
    {g : ℤ × ℤ} {c : GridChainMinus R n} :
    GridChain.halfTurnRenameEquiv R c ∈ G.rotate.bigradedChainMinusPiece R g ↔
      c ∈ G.bigradedChainMinusPiece R g := by
  refine ⟨fun hc ↦ ?_, G.halfTurnRenameEquiv_mem_bigradedChainMinusPiece R⟩
  have h := G.rotate.halfTurnRenameEquiv_mem_bigradedChainMinusPiece R hc
  rwa [GridChain.halfTurnRenameEquiv_halfTurnRenameEquiv, G.rotate_rotate] at h

end Chains

/-- A semilinear equivalence along a variable permutation `renameEquiv R σ` is linear over the
ground semiring `R`. -/
theorem map_smul_of_renameEquiv {ι κ M N : Type*} {R : Type*} [CommSemiring R]
    [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) M]
    [Module R N] [Module (MvPolynomial κ R) N] [IsScalarTower R (MvPolynomial κ R) N]
    (σ : ι ≃ κ)
    (e : M ≃ₛₗ[((renameEquiv R σ).toRingEquiv : MvPolynomial ι R →+* MvPolynomial κ R)] N)
    (r : R) (y : M) :
    e (r • y) = r • e y := by
  have hr : ((renameEquiv R σ).toRingEquiv : MvPolynomial ι R →+* MvPolynomial κ R)
      (algebraMap R (MvPolynomial ι R) r) = algebraMap R (MvPolynomial κ R) r :=
    (renameEquiv R σ).commutes r
  have h := e.map_smulₛₗ (algebraMap R (MvPolynomial ι R) r) y
  rwa [hr, algebraMap_smul, algebraMap_smul] at h

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

/-- Diagonal reflection gives a ground-ring linear equivalence in each bidegree of `GH⁻`. -/
noncomputable def bigradedUnblockedHomologyTransposeEquiv (g : ℤ × ℤ) :
    G.bigradedUnblockedHomologyPiece R g ≃ₗ[R]
      G.transpose.bigradedUnblockedHomologyPiece R g where
  toEquiv := (G.1.unblockedHomologyTransposeEquiv R).toEquiv.subtypeEquiv
    fun _ ↦ (G.unblockedHomologyTransposeEquiv_mem_bigradedPiece_iff R).symm
  map_add' x y := Subtype.ext ((G.1.unblockedHomologyTransposeEquiv R).map_add x y)
  map_smul' r y := Subtype.ext
    (map_smul_of_renameEquiv G.1.O.toPerm (G.1.unblockedHomologyTransposeEquiv R) r y)

/-- On underlying classes the transpose piece equivalence is `unblockedHomologyTransposeEquiv`. -/
@[simp]
theorem coe_bigradedUnblockedHomologyTransposeEquiv (g : ℤ × ℤ)
    (y : G.bigradedUnblockedHomologyPiece R g) :
    (G.bigradedUnblockedHomologyTransposeEquiv R g y : G.1.transpose.unblockedHomology R) =
      G.1.unblockedHomologyTransposeEquiv R y :=
  (rfl)

/-- The inverse transpose piece equivalence acts as `(unblockedHomologyTransposeEquiv R).symm`. -/
@[simp]
theorem coe_bigradedUnblockedHomologyTransposeEquiv_symm (g : ℤ × ℤ)
    (y : G.transpose.bigradedUnblockedHomologyPiece R g) :
    ((G.bigradedUnblockedHomologyTransposeEquiv R g).symm y : G.1.unblockedHomology R) =
      (G.1.unblockedHomologyTransposeEquiv R).symm y :=
  (rfl)

/-- The half-turn gives a ground-ring linear equivalence in each bidegree of `GH⁻`. -/
noncomputable def bigradedUnblockedHomologyRotateEquiv (g : ℤ × ℤ) :
    G.bigradedUnblockedHomologyPiece R g ≃ₗ[R]
      G.rotate.bigradedUnblockedHomologyPiece R g where
  toEquiv := (G.1.unblockedHomologyRotateEquiv R).toEquiv.subtypeEquiv
    fun _ ↦ (G.unblockedHomologyRotateEquiv_mem_bigradedPiece_iff R).symm
  map_add' x y := Subtype.ext ((G.1.unblockedHomologyRotateEquiv R).map_add x y)
  map_smul' r y := Subtype.ext
    (map_smul_of_renameEquiv (Fin.revPerm (n := n)) (G.1.unblockedHomologyRotateEquiv R) r y)

/-- On underlying classes the half-turn piece equivalence is `unblockedHomologyRotateEquiv`. -/
@[simp]
theorem coe_bigradedUnblockedHomologyRotateEquiv (g : ℤ × ℤ)
    (y : G.bigradedUnblockedHomologyPiece R g) :
    (G.bigradedUnblockedHomologyRotateEquiv R g y : G.1.rotate.unblockedHomology R) =
      G.1.unblockedHomologyRotateEquiv R y :=
  (rfl)

/-- The inverse half-turn piece equivalence acts as `(unblockedHomologyRotateEquiv R).symm`. -/
@[simp]
theorem coe_bigradedUnblockedHomologyRotateEquiv_symm (g : ℤ × ℤ)
    (y : G.rotate.bigradedUnblockedHomologyPiece R g) :
    ((G.bigradedUnblockedHomologyRotateEquiv R g).symm y : G.1.unblockedHomology R) =
      (G.1.unblockedHomologyRotateEquiv R).symm y :=
  (rfl)

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
