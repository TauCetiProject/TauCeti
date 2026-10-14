/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module
public import TauCeti.NumberTheory.IntegralLattice.Binary.NormForm
public import TauCeti.LinearAlgebra.IntegralLattice.Index
public import TauCeti.LinearAlgebra.IntegralLattice.Restriction
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

private theorem integralMatrixBasis_carrier_le (P : Matrix (Fin 2) (Fin 2) ℤ)
    (hP : IsUnit (P.map (Int.castRingHom ℚ)).det) :
    Submodule.span ℤ (Set.range (integralMatrixBasis P hP)) ≤
      (unitLattice (Fin 2)).carrier := by
  rw [Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact (mem_unitLattice_carrier_iff (Fin 2) _).mpr
    (fun j ↦ ⟨P j i, (integralMatrixBasis_apply P hP i j).symm⟩)

private noncomputable def integralMatrixSublattice (P : Matrix (Fin 2) (Fin 2) ℤ)
    (hP : IsUnit (P.map (Int.castRingHom ℚ)).det) : IntegralLattice (Fin 2 → ℚ) := by
  letI := isLattice_span_basis (integralMatrixBasis P hP)
  exact (unitLattice (Fin 2)).restrictFull
    (Submodule.span ℤ (Set.range (integralMatrixBasis P hP)))
    (integralMatrixBasis_carrier_le P hP)

private theorem integralMatrixSublattice_carrier (P : Matrix (Fin 2) (Fin 2) ℤ)
    (hP : IsUnit (P.map (Int.castRingHom ℚ)).det) :
    (integralMatrixSublattice P hP).carrier =
      Submodule.span ℤ (Set.range (integralMatrixBasis P hP)) := by
  simp [integralMatrixSublattice]

private theorem integralMatrixSublattice_form (P : Matrix (Fin 2) (Fin 2) ℤ)
    (hP : IsUnit (P.map (Int.castRingHom ℚ)).det) :
    (integralMatrixSublattice P hP).form = (unitLattice (Fin 2)).form := by
  simp [integralMatrixSublattice]

private theorem integralMatrixSublattice_carrier_le (P : Matrix (Fin 2) (Fin 2) ℤ)
    (hP : IsUnit (P.map (Int.castRingHom ℚ)).det) :
    (integralMatrixSublattice P hP).carrier ≤ (unitLattice (Fin 2)).carrier := by
  rw [integralMatrixSublattice_carrier]
  exact integralMatrixBasis_carrier_le P hP

private noncomputable def integralMatrixSublatticeBasis (P : Matrix (Fin 2) (Fin 2) ℤ)
    (hP : IsUnit (P.map (Int.castRingHom ℚ)).det) :
    Basis (Fin 2) ℤ (integralMatrixSublattice P hP) :=
  ((integralMatrixBasis P hP).restrictScalars ℤ).map
    (LinearEquiv.ofEq _ _ (integralMatrixSublattice_carrier P hP).symm)

private theorem integralMatrixSublatticeBasis_apply (P : Matrix (Fin 2) (Fin 2) ℤ)
    (hP : IsUnit (P.map (Int.castRingHom ℚ)).det) (i j : Fin 2) :
    (integralMatrixSublatticeBasis P hP i : Fin 2 → ℚ) j = (P j i : ℚ) := by
  simp only [integralMatrixSublatticeBasis, Basis.map_apply, LinearEquiv.coe_ofEq_apply]
  exact (congrFun ((integralMatrixBasis P hP).restrictScalars_apply ℤ i) j).trans
    (integralMatrixBasis_apply P hP i j)

private theorem binaryNormForm_integralMatrixSublattice (P : Matrix (Fin 2) (Fin 2) ℤ)
    (hP : IsUnit (P.map (Int.castRingHom ℚ)).det) :
    (integralMatrixSublattice P hP).binaryNormForm (integralMatrixSublatticeBasis P hP) =
      ⟨P 0 0 ^ 2 + P 1 0 ^ 2, 2 * (P 0 0 * P 0 1 + P 1 0 * P 1 1),
        P 0 1 ^ 2 + P 1 1 ^ 2⟩ := by
  ext
  all_goals apply Int.cast_injective (α := ℚ)
  all_goals simp [binaryNormForm_a, binaryNormForm_b, binaryNormForm_c, gramMatrix_apply,
    integralForm_cast, integralMatrixSublattice_form, unitLattice_form_apply,
    integralMatrixSublatticeBasis_apply, pow_two, Fin.sum_univ_two]

private theorem mem_integralMatrixSublattice_iff (P : Matrix (Fin 2) (Fin 2) ℤ)
    (hP : IsUnit (P.map (Int.castRingHom ℚ)).det) (x : Fin 2 → ℚ) :
    x ∈ (integralMatrixSublattice P hP).carrier ↔
      ∃ m n : ℤ, ∀ j, x j = (P j 0 : ℚ) * m + (P j 1 : ℚ) * n := by
  constructor
  · intro hx
    let z : integralMatrixSublattice P hP := ⟨x, hx⟩
    refine ⟨(integralMatrixSublatticeBasis P hP).repr z 0,
      (integralMatrixSublatticeBasis P hP).repr z 1, fun j ↦ ?_⟩
    have h := congrArg (fun v : integralMatrixSublattice P hP ↦ (v : Fin 2 → ℚ) j)
      ((integralMatrixSublatticeBasis P hP).sum_repr z)
    simp only [Fin.sum_univ_two] at h
    simpa [integralMatrixSublatticeBasis_apply, Algebra.smul_def, mul_comm, z] using h.symm
  · rintro ⟨m, n, h⟩
    rw [integralMatrixSublattice_carrier]
    have hx : x = m • integralMatrixBasis P hP 0 + n • integralMatrixBasis P hP 1 := by
      funext j
      simpa [integralMatrixBasis_apply, Algebra.smul_def, mul_comm] using h j
    rw [hx]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self 0)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self 1)))

private theorem integralMatrixSublattice_relIndex (P : Matrix (Fin 2) (Fin 2) ℤ)
    (hP : IsUnit (P.map (Int.castRingHom ℚ)).det) :
    (integralMatrixSublattice P hP).carrier.toAddSubgroup.relIndex
      (unitLattice (Fin 2)).carrier.toAddSubgroup = P.det.natAbs := by
  have hmat : (Pi.basisFun ℚ (Fin 2)).toMatrix (integralMatrixBasis P hP) =
      P.map (Int.castRingHom ℚ) := by
    ext i j
    simp [Basis.toMatrix_apply, integralMatrixBasis_apply, Pi.basisFun_repr]
  have h := AddSubgroup.relIndex_eq_abs_det
    (integralMatrixSublattice P hP).carrier.toAddSubgroup
    (unitLattice (Fin 2)).carrier.toAddSubgroup
    (integralMatrixSublattice_carrier_le P hP) (integralMatrixBasis P hP)
    (Pi.basisFun ℚ (Fin 2))
    (by rw [integralMatrixSublattice_carrier, Submodule.span_int_eq_addSubgroupClosure])
    (by rw [unitLattice_carrier_eq_span_basisFun, Submodule.span_int_eq_addSubgroupClosure])
  have hdet : (P.map (Int.castRingHom ℚ)).det = (P.det : ℚ) := (Int.cast_det P).symm
  rw [Basis.det_apply, hmat, hdet] at h
  have hidx : ((integralMatrixSublattice P hP).carrier.toAddSubgroup.relIndex
      (unitLattice (Fin 2)).carrier.toAddSubgroup : ℚ) = (P.det.natAbs : ℚ) := by
    simpa only [Nat.cast_natAbs, Int.cast_abs] using h
  exact_mod_cast hidx

private theorem integralMatrixSublattice_determinant (P : Matrix (Fin 2) (Fin 2) ℤ)
    (hP : IsUnit (P.map (Int.castRingHom ℚ)).det) :
    (integralMatrixSublattice P hP).determinant = P.det ^ 2 := by
  simpa only [unitLattice_determinant, one_mul, integralMatrixSublattice_relIndex,
    Int.natCast_natAbs, sq_abs] using
    (integralMatrixSublattice P hP).determinant_eq_mul_relIndex_sq (unitLattice (Fin 2))
      (integralMatrixSublattice_form P hP) (integralMatrixSublattice_carrier_le P hP)

private theorem coordinateMatrix_det_unit :
    IsUnit ((!![2, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℚ)).det := by
  norm_num [Matrix.det_fin_two]

private theorem diagonalMatrix_det_unit :
    IsUnit ((!![1, 1; 1, -1] : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℚ)).det := by
  norm_num [Matrix.det_fin_two]

/-- The sublattice spanned by `(2, 0)` and `(0, 1)`, with the standard square form. -/
noncomputable def coordinateIndexTwoSublattice : IntegralLattice (Fin 2 → ℚ) :=
  integralMatrixSublattice !![2, 0; 0, 1] coordinateMatrix_det_unit

/-- The sublattice spanned by `(1, 1)` and `(1, -1)`, with the standard square form. -/
noncomputable def diagonalIndexTwoSublattice : IntegralLattice (Fin 2 → ℚ) :=
  integralMatrixSublattice !![1, 1; 1, -1] diagonalMatrix_det_unit

/-- The integral carrier basis induced by `(2, 0), (0, 1)`. -/
noncomputable def coordinateIndexTwoSublatticeBasis :
    Basis (Fin 2) ℤ coordinateIndexTwoSublattice :=
  integralMatrixSublatticeBasis _ _

/-- The integral carrier basis induced by `(1, 1), (1, -1)`. -/
noncomputable def diagonalIndexTwoSublatticeBasis : Basis (Fin 2) ℤ diagonalIndexTwoSublattice :=
  integralMatrixSublatticeBasis _ _

/-- The coordinate sublattice basis vectors are the columns `(2, 0), (0, 1)`. -/
@[simp] theorem coe_coordinateIndexTwoSublatticeBasis_apply (i j : Fin 2) :
    (coordinateIndexTwoSublatticeBasis i : Fin 2 → ℚ) j =
      ((!![2, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) j i : ℚ) :=
  integralMatrixSublatticeBasis_apply _ _ i j

/-- The diagonal sublattice basis vectors are the columns `(1, 1), (1, -1)`. -/
@[simp] theorem coe_diagonalIndexTwoSublatticeBasis_apply (i j : Fin 2) :
    (diagonalIndexTwoSublatticeBasis i : Fin 2 → ℚ) j =
      ((!![1, 1; 1, -1] : Matrix (Fin 2) (Fin 2) ℤ) j i : ℚ) :=
  integralMatrixSublatticeBasis_apply _ _ i j

/-- Restriction to the coordinate sublattice gives `4x² + y²`. -/
@[simp] theorem coordinateIndexTwoSublattice_binaryNormForm :
    coordinateIndexTwoSublattice.binaryNormForm coordinateIndexTwoSublatticeBasis = ⟨4, 0, 1⟩ :=
  (binaryNormForm_integralMatrixSublattice _ _).trans (by ext <;> norm_num)

/-- Restriction to the diagonal sublattice gives `2x² + 2y²`. -/
@[simp] theorem diagonalIndexTwoSublattice_binaryNormForm :
    diagonalIndexTwoSublattice.binaryNormForm diagonalIndexTwoSublatticeBasis = ⟨2, 0, 2⟩ :=
  (binaryNormForm_integralMatrixSublattice _ _).trans (by ext <;> norm_num)

/-- Coordinate-sublattice membership means an even integer first coordinate and an integer second
coordinate. -/
@[simp] theorem mem_coordinateIndexTwoSublattice_carrier_iff (x : Fin 2 → ℚ) :
    x ∈ coordinateIndexTwoSublattice.carrier ↔
      (∃ m : ℤ, ((2 * m : ℤ) : ℚ) = x 0) ∧ ∃ n : ℤ, (n : ℚ) = x 1 := by
  rw [coordinateIndexTwoSublattice, mem_integralMatrixSublattice_iff]
  constructor
  · rintro ⟨m, n, h⟩
    exact ⟨⟨m, by simpa using (h 0).symm⟩, ⟨n, by simpa using (h 1).symm⟩⟩
  · rintro ⟨⟨m, hm⟩, ⟨n, hn⟩⟩
    refine ⟨m, n, fun j ↦ ?_⟩
    fin_cases j <;> simp [← hm, ← hn]

/-- Diagonal-sublattice membership means integer coordinates with even sum. -/
@[simp] theorem mem_diagonalIndexTwoSublattice_carrier_iff (x : Fin 2 → ℚ) :
    x ∈ diagonalIndexTwoSublattice.carrier ↔
      ∃ m n : ℤ, (m : ℚ) = x 0 ∧ (n : ℚ) = x 1 ∧ Even (m + n) := by
  rw [diagonalIndexTwoSublattice, mem_integralMatrixSublattice_iff]
  constructor
  · rintro ⟨m, n, h⟩
    refine ⟨m + n, m - n, ?_, ?_, ⟨m, by ring⟩⟩
    · simpa using (h 0).symm
    · simpa [sub_eq_add_neg] using (h 1).symm
  · rintro ⟨m, n, hm, hn, ⟨k, hk⟩⟩
    have hkQ : (m : ℚ) + (n : ℚ) = (k : ℚ) + (k : ℚ) := by exact_mod_cast hk
    refine ⟨k, m - k, fun j ↦ ?_⟩
    fin_cases j
    · simp [← hm]
    · simp [← hn]
      linarith

/-- The coordinate sublattice keeps the original ambient rational form. -/
@[simp] theorem coordinateIndexTwoSublattice_form :
    coordinateIndexTwoSublattice.form = (unitLattice (Fin 2)).form := by
  exact integralMatrixSublattice_form _ _

/-- The diagonal sublattice keeps the original ambient rational form. -/
@[simp] theorem diagonalIndexTwoSublattice_form :
    diagonalIndexTwoSublattice.form = (unitLattice (Fin 2)).form := by
  exact integralMatrixSublattice_form _ _

/-- The coordinate sublattice lies inside the standard square lattice. -/
theorem coordinateIndexTwoSublattice_carrier_le :
    coordinateIndexTwoSublattice.carrier ≤ (unitLattice (Fin 2)).carrier :=
  integralMatrixSublattice_carrier_le _ _

/-- The diagonal sublattice lies inside the standard square lattice. -/
theorem diagonalIndexTwoSublattice_carrier_le :
    diagonalIndexTwoSublattice.carrier ≤ (unitLattice (Fin 2)).carrier :=
  integralMatrixSublattice_carrier_le _ _

/-- The coordinate sublattice has determinant four. -/
@[simp] theorem coordinateIndexTwoSublattice_determinant :
    coordinateIndexTwoSublattice.determinant = 4 :=
  (integralMatrixSublattice_determinant _ _).trans (by norm_num [Matrix.det_fin_two])

/-- The diagonal sublattice has determinant four. -/
@[simp] theorem diagonalIndexTwoSublattice_determinant :
    diagonalIndexTwoSublattice.determinant = 4 :=
  (integralMatrixSublattice_determinant _ _).trans (by norm_num [Matrix.det_fin_two])

/-- The coordinate sublattice has index two in the standard square lattice. -/
@[simp] theorem coordinateIndexTwoSublattice_relIndex :
    coordinateIndexTwoSublattice.carrier.toAddSubgroup.relIndex
      (unitLattice (Fin 2)).carrier.toAddSubgroup = 2 :=
  (integralMatrixSublattice_relIndex _ _).trans (by norm_num [Matrix.det_fin_two])

/-- The diagonal sublattice has index two in the standard square lattice. -/
@[simp] theorem diagonalIndexTwoSublattice_relIndex :
    diagonalIndexTwoSublattice.carrier.toAddSubgroup.relIndex
      (unitLattice (Fin 2)).carrier.toAddSubgroup = 2 :=
  (integralMatrixSublattice_relIndex _ _).trans (by norm_num [Matrix.det_fin_two])

/-- The coordinate restriction remains primitive, despite having index two. -/
@[simp] theorem coordinateIndexTwoSublattice_binaryContent :
    coordinateIndexTwoSublattice.binaryContent (by simp) = 1 := by
  rw [binaryContent_eq_content_binaryNormForm _ coordinateIndexTwoSublatticeBasis,
    coordinateIndexTwoSublattice_binaryNormForm]
  norm_num [BinaryQuadraticForm.content_def]

/-- The diagonal restriction has binary content two. -/
@[simp] theorem diagonalIndexTwoSublattice_binaryContent :
    diagonalIndexTwoSublattice.binaryContent (by simp) = 2 := by
  rw [binaryContent_eq_content_binaryNormForm _ diagonalIndexTwoSublatticeBasis,
    diagonalIndexTwoSublattice_binaryNormForm]
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

/-- The standard unit lattice has binary norm form `x² + y²`. -/
@[simp] theorem unitLattice_binaryNormForm :
    (unitLattice (Fin 2)).binaryNormForm (unitLatticeBasis (Fin 2)) = ⟨1, 0, 1⟩ := by
  ext <;> simp only [binaryNormForm_a, binaryNormForm_b, binaryNormForm_c,
    gramMatrix_unitLatticeBasis] <;> norm_num

/-- The original square lattice has binary content one. -/
@[simp] theorem unitLattice_binaryContent : (unitLattice (Fin 2)).binaryContent (by simp) = 1 := by
  rw [binaryContent_eq_content_binaryNormForm _ (unitLatticeBasis (Fin 2)),
    unitLattice_binaryNormForm]
  norm_num [BinaryQuadraticForm.content_def]

end TauCeti.IntegralLattice
