/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module
public import TauCeti.NumberTheory.IntegralLattice.Binary.NormForm
public import TauCeti.LinearAlgebra.IntegralLattice.Index
public import TauCeti.LinearAlgebra.IntegralLattice.Examples
public import TauCeti.LinearAlgebra.IntegralLattice.Unit
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Binary lattice examples

The standard square lattice has norm `x² + y²`. Its sublattices spanned by
`(2, 0), (0, 1)` and by `(1, 1), (1, -1)` share the same ambient rational form and
both have index two. Their norm forms are `4x² + y²` and `2x² + 2y²`, with contents
one and two. Thus the sublattice index alone does not determine binary content.

The existing hyperbolic plane has norm `2xy`, content two, primitive norm form `xy`,
and primitive discriminant one. The calculations use actual embedded lattice carriers
and their integral bases.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, §1.
-/

public section

open Module Matrix
namespace TauCeti.IntegralLattice

private noncomputable def integralMatrixBasis (P : Matrix (Fin 2) (Fin 2) ℤ)
    (hP : IsUnit (P.map (Int.castRingHom ℚ)).det) : Basis (Fin 2) ℚ (Fin 2 → ℚ) :=
  (Pi.basisFun ℚ (Fin 2)).map
    (Matrix.toLinearEquiv (Pi.basisFun ℚ (Fin 2)) (P.map (Int.castRingHom ℚ)) hP)

private theorem integralMatrixBasis_apply (P : Matrix (Fin 2) (Fin 2) ℤ)
    (hP : IsUnit (P.map (Int.castRingHom ℚ)).det) (i j : Fin 2) :
    integralMatrixBasis P hP i j = (P j i : ℚ) := by
  fin_cases i <;> fin_cases j <;>
    simp [integralMatrixBasis, Matrix.toLinearEquiv_apply, Matrix.toLin_apply,
      Fin.sum_univ_two, Pi.basisFun_apply, Pi.basisFun_repr, Matrix.mulVec, dotProduct]

private theorem integralMatrixBasis_integral (P : Matrix (Fin 2) (Fin 2) ℤ)
    (hP : IsUnit (P.map (Int.castRingHom ℚ)).det) (i j : Fin 2) :
    (unitLattice (Fin 2)).form (integralMatrixBasis P hP i) (integralMatrixBasis P hP j) ∈
      (1 : Submodule ℤ ℚ) := by
  rw [unitLattice_form_apply, Fin.sum_univ_two]
  simp only [integralMatrixBasis_apply]
  exact Submodule.mem_one.mpr ⟨P 0 i * P 0 j + P 1 i * P 1 j, by simp⟩

private theorem coordinateMatrix_det_unit :
    IsUnit ((!![2, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℚ)).det := by
  norm_num [Matrix.det_fin_two]

private theorem diagonalMatrix_det_unit :
    IsUnit ((!![1, 1; 1, -1] : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℚ)).det := by
  norm_num [Matrix.det_fin_two]

/-- The sublattice spanned by `(2, 0)` and `(0, 1)`, with the standard square form. -/
noncomputable def coordinateIndexTwoSublattice : IntegralLattice (Fin 2 → ℚ) :=
  ofBasis (integralMatrixBasis !![2, 0; 0, 1] coordinateMatrix_det_unit)
    (unitLattice (Fin 2)).form (unitLattice (Fin 2)).isSymm
    (integralMatrixBasis_integral !![2, 0; 0, 1] coordinateMatrix_det_unit)

/-- The sublattice spanned by `(1, 1)` and `(1, -1)`, with the standard square form. -/
noncomputable def diagonalIndexTwoSublattice : IntegralLattice (Fin 2 → ℚ) :=
  ofBasis (integralMatrixBasis !![1, 1; 1, -1] diagonalMatrix_det_unit)
    (unitLattice (Fin 2)).form (unitLattice (Fin 2)).isSymm
    (integralMatrixBasis_integral !![1, 1; 1, -1] diagonalMatrix_det_unit)

/-- The integral carrier basis induced by `(2, 0), (0, 1)`. -/
noncomputable def coordinateIndexTwoSublattice.basis :
    Basis (Fin 2) ℤ coordinateIndexTwoSublattice :=
  ofBasis.basis _ _ _ _

/-- The integral carrier basis induced by `(1, 1), (1, -1)`. -/
noncomputable def diagonalIndexTwoSublattice.basis : Basis (Fin 2) ℤ diagonalIndexTwoSublattice :=
  ofBasis.basis _ _ _ _

private theorem normForm_of_integralMatrixBasis (P : Matrix (Fin 2) (Fin 2) ℤ)
    (hP : IsUnit (P.map (Int.castRingHom ℚ)).det) :
    let L := ofBasis (integralMatrixBasis P hP)
      (unitLattice (Fin 2)).form (unitLattice (Fin 2)).isSymm
      (integralMatrixBasis_integral P hP)
    L.binaryNormForm (ofBasis.basis _ _ _ _) =
      ⟨P 0 0 ^ 2 + P 1 0 ^ 2, 2 * (P 0 0 * P 0 1 + P 1 0 * P 1 1),
        P 0 1 ^ 2 + P 1 1 ^ 2⟩ := by
  dsimp only
  ext
  all_goals apply Int.cast_injective (α := ℚ)
  all_goals simp [binaryNormForm_a, binaryNormForm_b, binaryNormForm_c, gramMatrix_apply,
    integralForm_cast,
    ofBasis.coe_basis, integralMatrixBasis_apply, pow_two, Fin.sum_univ_two]

/-- Restriction to the coordinate sublattice gives `4x² + y²`. -/
@[simp] theorem coordinateIndexTwoSublattice_normForm :
    coordinateIndexTwoSublattice.binaryNormForm coordinateIndexTwoSublattice.basis = ⟨4, 0, 1⟩ := by
  simpa [coordinateIndexTwoSublattice, coordinateIndexTwoSublattice.basis] using
    normForm_of_integralMatrixBasis !![2, 0; 0, 1] coordinateMatrix_det_unit

/-- Restriction to the diagonal sublattice gives `2x² + 2y²`. -/
@[simp] theorem diagonalIndexTwoSublattice_normForm :
    diagonalIndexTwoSublattice.binaryNormForm diagonalIndexTwoSublattice.basis = ⟨2, 0, 2⟩ := by
  simpa [diagonalIndexTwoSublattice, diagonalIndexTwoSublattice.basis] using
    normForm_of_integralMatrixBasis !![1, 1; 1, -1] diagonalMatrix_det_unit

private theorem integralMatrixBasis_carrier_le (P : Matrix (Fin 2) (Fin 2) ℤ)
    (hP : IsUnit (P.map (Int.castRingHom ℚ)).det) :
    (ofBasis (integralMatrixBasis P hP) (unitLattice (Fin 2)).form (unitLattice (Fin 2)).isSymm
      (integralMatrixBasis_integral P hP)).carrier ≤ (unitLattice (Fin 2)).carrier := by
  rw [ofBasis_carrier, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact (mem_unitLattice_carrier_iff (Fin 2) _).mpr
    (fun j ↦ ⟨P j i, (integralMatrixBasis_apply P hP i j).symm⟩)

/-- The coordinate sublattice keeps the original ambient rational form. -/
@[simp] theorem coordinateIndexTwoSublattice_form :
    coordinateIndexTwoSublattice.form = (unitLattice (Fin 2)).form := by
  simp [coordinateIndexTwoSublattice]

/-- The diagonal sublattice keeps the original ambient rational form. -/
@[simp] theorem diagonalIndexTwoSublattice_form :
    diagonalIndexTwoSublattice.form = (unitLattice (Fin 2)).form := by
  simp [diagonalIndexTwoSublattice]

/-- The coordinate sublattice lies inside the standard square lattice. -/
theorem coordinateIndexTwoSublattice_carrier_le :
    coordinateIndexTwoSublattice.carrier ≤ (unitLattice (Fin 2)).carrier :=
  integralMatrixBasis_carrier_le _ _

/-- The diagonal sublattice lies inside the standard square lattice. -/
theorem diagonalIndexTwoSublattice_carrier_le :
    diagonalIndexTwoSublattice.carrier ≤ (unitLattice (Fin 2)).carrier :=
  integralMatrixBasis_carrier_le _ _

/-- The coordinate sublattice has determinant four. -/
@[simp] theorem coordinateIndexTwoSublattice_determinant :
    coordinateIndexTwoSublattice.determinant = 4 := by
  have h := coordinateIndexTwoSublattice.discrim_binaryNormForm
    coordinateIndexTwoSublattice.basis
  rw [coordinateIndexTwoSublattice_normForm] at h
  norm_num [BinaryQuadraticForm.discrim_def, discrim] at h
  omega

/-- The diagonal sublattice has determinant four. -/
@[simp] theorem diagonalIndexTwoSublattice_determinant :
    diagonalIndexTwoSublattice.determinant = 4 := by
  have h := diagonalIndexTwoSublattice.discrim_binaryNormForm
    diagonalIndexTwoSublattice.basis
  rw [diagonalIndexTwoSublattice_normForm] at h
  norm_num [BinaryQuadraticForm.discrim_def, discrim] at h
  omega

/-- The coordinate sublattice has index two in the standard square lattice. -/
@[simp] theorem coordinateIndexTwoSublattice_relIndex :
    coordinateIndexTwoSublattice.carrier.toAddSubgroup.relIndex
      (unitLattice (Fin 2)).carrier.toAddSubgroup = 2 := by
  have h := coordinateIndexTwoSublattice.determinant_eq_mul_relIndex_sq (unitLattice (Fin 2))
    coordinateIndexTwoSublattice_form coordinateIndexTwoSublattice_carrier_le
  simp only [coordinateIndexTwoSublattice_determinant, unitLattice_determinant, one_mul] at h
  have hnonneg := Int.natCast_nonneg
    (coordinateIndexTwoSublattice.carrier.toAddSubgroup.relIndex
      (unitLattice (Fin 2)).carrier.toAddSubgroup)
  have he : (coordinateIndexTwoSublattice.carrier.toAddSubgroup.relIndex
      (unitLattice (Fin 2)).carrier.toAddSubgroup : ℤ) = 2 := by nlinarith
  exact_mod_cast he

/-- The diagonal sublattice has index two in the standard square lattice. -/
@[simp] theorem diagonalIndexTwoSublattice_relIndex :
    diagonalIndexTwoSublattice.carrier.toAddSubgroup.relIndex
      (unitLattice (Fin 2)).carrier.toAddSubgroup = 2 := by
  have h := diagonalIndexTwoSublattice.determinant_eq_mul_relIndex_sq (unitLattice (Fin 2))
    diagonalIndexTwoSublattice_form diagonalIndexTwoSublattice_carrier_le
  simp only [diagonalIndexTwoSublattice_determinant, unitLattice_determinant, one_mul] at h
  have hnonneg := Int.natCast_nonneg
    (diagonalIndexTwoSublattice.carrier.toAddSubgroup.relIndex
      (unitLattice (Fin 2)).carrier.toAddSubgroup)
  have he : (diagonalIndexTwoSublattice.carrier.toAddSubgroup.relIndex
      (unitLattice (Fin 2)).carrier.toAddSubgroup : ℤ) = 2 := by nlinarith
  exact_mod_cast he

/-- The coordinate restriction remains primitive, despite having index two. -/
@[simp] theorem coordinateIndexTwoSublattice_binaryContent :
    coordinateIndexTwoSublattice.binaryContent (by simp) = 1 := by
  rw [binaryContent_eq_content_binaryNormForm _ coordinateIndexTwoSublattice.basis,
    coordinateIndexTwoSublattice_normForm]
  norm_num [BinaryQuadraticForm.content_def]

/-- The diagonal restriction has binary content two. -/
@[simp] theorem diagonalIndexTwoSublattice_binaryContent :
    diagonalIndexTwoSublattice.binaryContent (by simp) = 2 := by
  rw [binaryContent_eq_content_binaryNormForm _ diagonalIndexTwoSublattice.basis,
    diagonalIndexTwoSublattice_normForm]
  norm_num [BinaryQuadraticForm.content_def]

/-- Two sublattices of the same lattice, of the same index and with the same ambient form, have
different binary contents. -/
theorem indexTwoSublattices_binaryContent_ne :
    coordinateIndexTwoSublattice.binaryContent (by simp) ≠
      diagonalIndexTwoSublattice.binaryContent (by simp) := by
  simp

/-- The integral norm form of the hyperbolic plane is `2xy`. -/
@[simp] theorem hyperbolicPlane_binaryNormForm :
    hyperbolicPlane.binaryNormForm hyperbolicPlaneBasis = ⟨0, 2, 0⟩ := by
  ext <;> simp only [binaryNormForm_a, binaryNormForm_b, binaryNormForm_c,
    gramMatrix_hyperbolicPlaneBasis] <;> norm_num

/-- The hyperbolic plane has binary content two. -/
@[simp] theorem hyperbolicPlane_binaryContent : hyperbolicPlane.binaryContent (by simp) = 2 := by
  rw [binaryContent_eq_content_binaryNormForm _ hyperbolicPlaneBasis,
    hyperbolicPlane_binaryNormForm]
  norm_num [BinaryQuadraticForm.content_def]

/-- The primitive norm form of the hyperbolic plane is `xy`. -/
theorem hyperbolicPlane_binaryNormForm_primPart :
    (hyperbolicPlane.binaryNormForm hyperbolicPlaneBasis).primPart = ⟨0, 1, 0⟩ := by
  rw [hyperbolicPlane_binaryNormForm]
  ext <;> norm_num [BinaryQuadraticForm.primPart_a, BinaryQuadraticForm.primPart_b,
    BinaryQuadraticForm.primPart_c, BinaryQuadraticForm.content_def]

/-- The hyperbolic plane has primitive discriminant one. -/
@[simp] theorem hyperbolicPlane_binaryDiscriminant :
    hyperbolicPlane.binaryDiscriminant (by simp) = 1 := by
  rw [binaryDiscriminant_eq_discrim_primPart _ hyperbolicPlaneBasis,
    hyperbolicPlane_binaryNormForm_primPart]
  norm_num [BinaryQuadraticForm.discrim_def, discrim]

/-- The coordinate sublattice basis vectors are the columns `(2, 0), (0, 1)`. -/
@[simp] theorem coordinateIndexTwoSublattice_coe_basis (i j : Fin 2) :
    (coordinateIndexTwoSublattice.basis i : Fin 2 → ℚ) j =
      ((!![2, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) j i : ℚ) := by
  exact (congrFun (ofBasis.coe_basis
    (integralMatrixBasis !![2, 0; 0, 1] coordinateMatrix_det_unit) (unitLattice (Fin 2)).form
    (unitLattice (Fin 2)).isSymm (integralMatrixBasis_integral _ _) i) j).trans
    (integralMatrixBasis_apply _ _ i j)

/-- The diagonal sublattice basis vectors are the columns `(1, 1), (1, -1)`. -/
@[simp] theorem diagonalIndexTwoSublattice_coe_basis (i j : Fin 2) :
    (diagonalIndexTwoSublattice.basis i : Fin 2 → ℚ) j =
      ((!![1, 1; 1, -1] : Matrix (Fin 2) (Fin 2) ℤ) j i : ℚ) := by
  exact (congrFun (ofBasis.coe_basis
    (integralMatrixBasis !![1, 1; 1, -1] diagonalMatrix_det_unit) (unitLattice (Fin 2)).form
    (unitLattice (Fin 2)).isSymm (integralMatrixBasis_integral _ _) i) j).trans
    (integralMatrixBasis_apply _ _ i j)

/-- The original square lattice has binary content one. -/
@[simp] theorem unitLattice_binaryContent : (unitLattice (Fin 2)).binaryContent (by simp) = 1 := by
  have hf : (unitLattice (Fin 2)).binaryNormForm (unitLatticeBasis (Fin 2)) = ⟨1, 0, 1⟩ := by
    ext <;> simp only [binaryNormForm_a, binaryNormForm_b, binaryNormForm_c,
      gramMatrix_unitLatticeBasis] <;> norm_num
  rw [binaryContent_eq_content_binaryNormForm _ (unitLatticeBasis (Fin 2)), hf]
  norm_num [BinaryQuadraticForm.content_def]

end TauCeti.IntegralLattice
