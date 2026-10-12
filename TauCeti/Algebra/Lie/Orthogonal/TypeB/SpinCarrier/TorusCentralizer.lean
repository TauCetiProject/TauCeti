/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeB.SpinCarrier.Basic
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Basic
import TauCeti.LinearAlgebra.Matrix.Diagonal

/-!
# The centralizer of the type-B spin weight torus

Over an infinite field, a point of the integral type-`Bₙ₊₁` spin carrier centralizes its
weight torus exactly when its spin matrix is diagonal. The spin weights are distinct, so
characters separate every pair of exterior-basis vectors, including in characteristic two.
The centralizer is therefore the intersection of the carrier with the ambient diagonal torus.

This is the matrix reduction needed to identify the carrier's torus centralizer. It does not
identify the diagonal carrier points with the weight-torus image, prove maximality of that
image, or identify the carrier with an independently pinned simply connected group scheme.

## References

* J. E. Humphreys, *Linear Algebraic Groups*, §§16 and 26.
* The character-separation argument follows
  `TauCeti.Algebra.Lie.F4.ShortRoot.PrimeField.TorusCentralizer`. Unlike that representation,
  the spin representation has no repeated weights.
-/

public section

open Matrix

namespace TauCeti.TypeBSpinCarrier

universe u

variable (n : ℕ) {A : Type u} [CommRing A] [IsLeftCancelMulZero A]

/-- If the spin weights define distinct characters on torus points, a carrier point
centralizes the weight torus exactly when its spin matrix is diagonal. -/
theorem mem_centralizer_range_weightTorusPoints_iff_isDiag_of_weightChar_basisWeight_injective
    (hchar : Function.Injective fun i : Fin (dimension n) ↦ weightChar A (basisWeight n i))
    (g : points n A) :
    g ∈ Subgroup.centralizer (Set.range (weightTorusPoints n A)) ↔
      ((g : GL (Fin (dimension n)) A) :
        Matrix (Fin (dimension n)) (Fin (dimension n)) A).IsDiag := by
  constructor
  · intro hg i j hij
    obtain ⟨s, hs⟩ := DFunLike.ne_iff.mp (hchar.ne hij)
    simp only [weightChar_apply] at hs
    have hcomm := Subgroup.mem_centralizer_iff.mp hg (weightTorusPoints n A s) ⟨s, rfl⟩
    have hmatrix := congrArg (fun x : points n A ↦
      ((x : GL (Fin (dimension n)) A) : Matrix (Fin (dimension n)) (Fin (dimension n)) A)) hcomm
    simp only [Subgroup.coe_mul, Units.val_mul, coe_weightTorusPoints,
      UniversalEnvelopingAlgebra.kostantTorusMatrix_apply, diagGL_coe] at hmatrix
    exact apply_eq_zero_of_commute_diagonal hmatrix (fun h ↦ hs (Units.ext h))
  · intro hg
    rw [Subgroup.mem_centralizer_iff]
    rintro d ⟨s, rfl⟩
    apply (points n A).subtype_injective
    apply Units.ext
    simp only [Subgroup.subtype_apply, Subgroup.coe_mul, Units.val_mul, coe_weightTorusPoints,
      UniversalEnvelopingAlgebra.kostantTorusMatrix_apply, diagGL_coe]
    rw [← hg.diagonal_diag]
    exact (Matrix.commute_diagonal _ _).eq

/-- If the spin weights define distinct characters on torus points, the weight-torus
centralizer is the inverse image of the ambient diagonal torus under the carrier inclusion. -/
theorem
    centralizer_range_weightTorusPoints_eq_comap_diagonalTorus_of_weightChar_basisWeight_injective
    (hchar : Function.Injective fun i : Fin (dimension n) ↦ weightChar A (basisWeight n i)) :
    Subgroup.centralizer (Set.range (weightTorusPoints n A)) =
      (diagonalTorus A (dimension n)).comap (points n A).subtype := by
  ext g
  simp only [mem_centralizer_range_weightTorusPoints_iff_isDiag_of_weightChar_basisWeight_injective
    n hchar, Subgroup.mem_comap, Subgroup.subtype_apply, mem_diagonalTorus_iff]

variable {k : Type u} [Field k] [Infinite k]

/-- Over an infinite field in any characteristic, the spin weight-torus centralizer consists
exactly of the carrier points whose spin matrices are diagonal. -/
@[simp]
theorem mem_centralizer_range_weightTorusPoints_iff_isDiag (g : points n k) :
    g ∈ Subgroup.centralizer (Set.range (weightTorusPoints n k)) ↔
      ((g : GL (Fin (dimension n)) k) :
        Matrix (Fin (dimension n)) (Fin (dimension n)) k).IsDiag := by
  apply mem_centralizer_range_weightTorusPoints_iff_isDiag_of_weightChar_basisWeight_injective
  intro i j h
  exact (Fintype.equivFin (Finset (Fin (n + 1)))).symm.injective
    (DynkinType.typeBSpinWeight_injective (weightChar_injective h))

/-- The centralizer of the spin weight torus over an infinite field is the inverse image of
the ambient diagonal torus under the carrier's matrix inclusion. This is not an assertion
that the weight torus is its own centralizer. -/
theorem centralizer_range_weightTorusPoints_eq_comap_diagonalTorus :
    Subgroup.centralizer (Set.range (weightTorusPoints n k)) =
      (diagonalTorus k (dimension n)).comap (points n k).subtype := by
  apply
    centralizer_range_weightTorusPoints_eq_comap_diagonalTorus_of_weightChar_basisWeight_injective
  intro i j h
  exact (Fintype.equivFin (Finset (Fin (n + 1)))).symm.injective
    (DynkinType.typeBSpinWeight_injective (weightChar_injective h))

end TauCeti.TypeBSpinCarrier
