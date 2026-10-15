/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Grading.Unblocked.Chain
public import TauCeti.KnotTheory.Grid.Homology.Unblocked
public import TauCeti.Algebra.Module.GradedModule.Homology

/-!
# The bigrading of unblocked grid homology

The homogeneous cycles and their classes give an internal direct sum decomposition of `GH⁻`
by `(O-Maslov, Alexander)` degree. The differential has degree `(-1, 0)`, and each variable
has degree `(-2, -1)`. Homogeneous projection preserves both cycles and boundaries, so a class
has a homogeneous representative precisely when it belongs to the corresponding piece.

The cycle pieces are defined over commutative semirings, and their internal direct sum
decomposition is available over commutative rings, using the chain decomposition
`isInternal_bigradedChainMinusPiece`, whose internality criterion requires a ring.
The homology grading and its consequences
require a commutative ring of characteristic two (`[CommRing R] [CharP R 2]`).

These pieces are modules over the ground ring, not over the polynomial coefficient ring.
As for the chain bigrading, an odd number of link components ensures integral Alexander degrees.
The decomposition allows degree-preserving homology comparisons to be restricted to each
bidegree without choosing cycle representatives.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Sections 4.3 and 4.6.
-/

public section

open MvPolynomial

namespace TauCeti.OddComponentGridDiagram

variable {n : ℕ} (G : OddComponentGridDiagram n) (R : Type*)

section Cycles

variable [CommSemiring R]

/-- The cycles of `GC⁻` homogeneous of bidegree `g`. -/
noncomputable def bigradedUnblockedCyclesPiece (g : ℤ × ℤ) :
    Submodule R (LinearMap.ker (G.1.unblockedDifferential R)) :=
  (G.bigradedChainMinusPiece R g).comap
    ((LinearMap.ker (G.1.unblockedDifferential R)).subtype.restrictScalars R)

/-- Homogeneity of a cycle is homogeneity of its underlying chain. -/
@[simp]
theorem mem_bigradedUnblockedCyclesPiece {g : ℤ × ℤ}
    {z : LinearMap.ker (G.1.unblockedDifferential R)} :
    z ∈ G.bigradedUnblockedCyclesPiece R g ↔
      (z : GridChainMinus R n) ∈ G.bigradedChainMinusPiece R g := Iff.rfl

end Cycles

variable [CommRing R]

/-- The homogeneous cycle modules form an internal direct sum. -/
theorem isInternal_bigradedUnblockedCyclesPiece :
    DirectSum.IsInternal (G.bigradedUnblockedCyclesPiece R) := by
  have hpieces : ((G.bigradedChainMinusGrading R).ker
    (G.isHomogeneous_unblockedDifferential_bigradedChainMinusGrading R)).piece =
      G.bigradedUnblockedCyclesPiece R := by
    funext g
    ext z
    exact (G.bigradedChainMinusGrading R).mem_ker_piece
      (G.isHomogeneous_unblockedDifferential_bigradedChainMinusGrading R)
  rw [← hpieces]
  exact ((G.bigradedChainMinusGrading R).ker
    (G.isHomogeneous_unblockedDifferential_bigradedChainMinusGrading R)).isInternal

variable [CharP R 2]

/-- The internal `(O-Maslov, Alexander)` grading of unblocked grid homology. -/
noncomputable def bigradedUnblockedHomologyGrading :
    InternalGrading R (G.1.unblockedHomology R) (ℤ × ℤ) :=
  ((G.bigradedChainMinusGrading R).homology
    (G.isHomogeneous_unblockedDifferential_bigradedChainMinusGrading R)
    (G.1.unblockedDifferential_comp_self_eq_zero R)).map
      ((G.1.unblockedHomologyIso R).symm.toLinearEquiv.restrictScalars R)

/-- The bidegree-`g` piece of `GH⁻`: classes of cycles homogeneous of bidegree `g`. -/
noncomputable def bigradedUnblockedHomologyPiece (g : ℤ × ℤ) :
    Submodule R (G.1.unblockedHomology R) :=
  (G.bigradedUnblockedHomologyGrading R).piece g

/-- The pieces of the bundled homology grading are the homogeneous homology pieces. -/
@[simp]
theorem bigradedUnblockedHomologyGrading_piece (g : ℤ × ℤ) :
    (G.bigradedUnblockedHomologyGrading R).piece g = G.bigradedUnblockedHomologyPiece R g := by
  rw [bigradedUnblockedHomologyPiece]

/-- A class has bidegree `g` exactly when it has a cycle representative of that bidegree. -/
theorem mem_bigradedUnblockedHomologyPiece_iff {g : ℤ × ℤ} {y : G.1.unblockedHomology R} :
    y ∈ G.bigradedUnblockedHomologyPiece R g ↔
      ∃ z : LinearMap.ker (G.1.unblockedDifferential R),
        (z : GridChainMinus R n) ∈ G.bigradedChainMinusPiece R g ∧
          G.1.unblockedHomologyClass R z = y := by
  rw [bigradedUnblockedHomologyPiece, bigradedUnblockedHomologyGrading,
    InternalGrading.mem_map_piece_iff, InternalGrading.mem_homology_piece_iff]
  constructor
  · rintro ⟨z, hz, hzy⟩
    refine ⟨z, hz, ?_⟩
    apply (ModuleCat.mono_iff_injective (G.1.unblockedHomologyIso R).hom).mp inferInstance
    rw [GridDiagram.unblockedHomologyIso_hom_unblockedHomologyClass]
    exact hzy
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, hz, (G.1.unblockedHomologyIso_hom_unblockedHomologyClass R z).symm⟩

/-- The class of a homogeneous cycle lies in the homology piece of the same bidegree. -/
theorem unblockedHomologyClass_mem_bigradedUnblockedHomologyPiece {g : ℤ × ℤ}
    {z : LinearMap.ker (G.1.unblockedDifferential R)}
    (hz : (z : GridChainMinus R n) ∈ G.bigradedChainMinusPiece R g) :
    G.1.unblockedHomologyClass R z ∈ G.bigradedUnblockedHomologyPiece R g :=
  (G.mem_bigradedUnblockedHomologyPiece_iff R).mpr ⟨z, hz, rfl⟩

/-- The bigraded homology pieces span `GH⁻`. -/
theorem iSup_bigradedUnblockedHomologyPiece_eq_top :
    ⨆ g, G.bigradedUnblockedHomologyPiece R g = ⊤ :=
  (G.bigradedUnblockedHomologyGrading R).isInternal.submodule_iSup_eq_top

/-- The bigraded homology pieces are independent: a homogeneous boundary can be detected in
its own bidegree. -/
theorem iSupIndep_bigradedUnblockedHomologyPiece :
    iSupIndep (G.bigradedUnblockedHomologyPiece R) :=
  (G.bigradedUnblockedHomologyGrading R).isInternal.submodule_iSupIndep

/-- `GH⁻` is the internal direct sum of its `(O-Maslov, Alexander)` pieces. -/
theorem isInternal_bigradedUnblockedHomologyPiece :
    DirectSum.IsInternal (G.bigradedUnblockedHomologyPiece R) :=
  (G.bigradedUnblockedHomologyGrading R).isInternal

/-- Multiplication by a monomial of total degree `d.degree` lowers homology bidegree by
`(2 * d.degree, d.degree)`. -/
theorem monomial_smul_mem_bigradedUnblockedHomologyPiece (d : Fin n →₀ ℕ) (a : R)
    {g : ℤ × ℤ} {y : G.1.unblockedHomology R}
    (hy : y ∈ G.bigradedUnblockedHomologyPiece R g) :
    (monomial d a : MvPolynomial (Fin n) R) • y ∈
      G.bigradedUnblockedHomologyPiece R (g - (2 * (d.degree : ℤ), (d.degree : ℤ))) := by
  rw [bigradedUnblockedHomologyPiece, bigradedUnblockedHomologyGrading,
    InternalGrading.mem_map_piece_iff] at hy ⊢
  -- Use the polynomial-linear quotient isomorphism to transport the monomial action.
  suffices h : (G.1.unblockedHomologyIso R).hom ((monomial d a) • y) ∈
      ((G.bigradedChainMinusGrading R).homology
        (G.isHomogeneous_unblockedDifferential_bigradedChainMinusGrading R)
        (G.1.unblockedDifferential_comp_self_eq_zero R)).piece
          (g - (2 * (d.degree : ℤ), (d.degree : ℤ))) by exact h
  rw [map_smul, sub_eq_add_neg]
  refine (G.bigradedChainMinusGrading R).smul_mem_homology_piece
    (G.isHomogeneous_unblockedDifferential_bigradedChainMinusGrading R)
    (G.1.unblockedDifferential_comp_self_eq_zero R) (fun p c hc ↦ ?_) hy
  simp only [bigradedChainMinusGrading] at hc ⊢
  simpa only [sub_eq_add_neg] using G.monomial_smul_mem_bigradedChainMinusPiece d a hc

/-- Multiplication by a grid variable lowers homology bidegree by `(2, 1)`. -/
theorem X_smul_mem_bigradedUnblockedHomologyPiece (i : Fin n) {g : ℤ × ℤ}
    {y : G.1.unblockedHomology R} (hy : y ∈ G.bigradedUnblockedHomologyPiece R g) :
    (X i : MvPolynomial (Fin n) R) • y ∈ G.bigradedUnblockedHomologyPiece R (g - (2, 1)) := by
  have h := G.monomial_smul_mem_bigradedUnblockedHomologyPiece R (Finsupp.single i 1) (1 : R) hy
  rwa [Finsupp.degree_single, Nat.cast_one, mul_one, ← X] at h

end TauCeti.OddComponentGridDiagram
