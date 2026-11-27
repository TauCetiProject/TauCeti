/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.CStarMatrix.Basic
public import TauCeti.Analysis.CStarAlgebra.Cuntz.Subequivalence

/-!
# Cuntz subequivalence in `M₂(ℂ)`: `1 ⋠ diag(1, 0)`

In `M₂(ℂ)` the identity is not Cuntz subequivalent to the rank-one projection `diag(1, 0)`
(`TauCeti.CuntzMatrixCheck.not_cuntzLE_one_diagOneZero`). Every `x⋆ diag(1, 0) x` has
determinant `0`, and the determinant is continuous, so no norm limit of such elements is
invertible. Contrast with `ℂ`, where every nonzero positive scalar is subequivalent to every other
(`TauCeti.cuntzLE_complex_iff`).

## References

* Rørdam, Part I of Rørdam–Størmer, *Classification of Nuclear C*-Algebras. Entropy in Operator
  Algebras*, Encyclopaedia of Mathematical Sciences 126, Springer, 2002, §4.1.
-/
public section

open Filter Topology
open scoped CStarAlgebra ComplexOrder

namespace TauCeti.CuntzMatrixCheck

/-- The rank-one projection `diag(1, 0) = e₁₁` in `M₂(ℂ)`, as a positive element. -/
noncomputable def diagOneZero : {a : CStarMatrix (Fin 2) (Fin 2) ℂ // 0 ≤ a} :=
  ⟨CStarMatrix.matrixUnit 0 0, (CStarMatrix.isStarProjection_matrixUnit 0).nonneg⟩

/-- **`1 ⋠ diag(1, 0)` in `M₂(ℂ)`.** The identity is not Cuntz subequivalent to the rank-one
projection `diag(1, 0)`: no sequence `xₙ⋆ diag(1, 0) xₙ` converges to `1`. -/
theorem not_cuntzLE_one_diagOneZero : ¬ CuntzLE 1 diagOneZero := by
  rw [cuntzLE_iff_exists_tendsto]
  rintro ⟨x, hx⟩
  -- Every `xₙ⋆ diag(1, 0) xₙ` has determinant `0`, the determinant is continuous, and `det 1 = 1`.
  let det : CStarMatrix (Fin 2) (Fin 2) ℂ → ℂ := fun M ↦ (CStarMatrix.ofMatrix.symm M).det
  -- `ofMatrix.symm` is the identity on the underlying matrices, as is `ofMatrixL.symm`.
  have hdet : Continuous det := CStarMatrix.ofMatrixL.symm.continuous.matrix_det
  have h0 (n : ℕ) : det (star (x n) * (diagOneZero : CStarMatrix (Fin 2) (Fin 2) ℂ) * x n) = 0 := by
    simp only [det, diagOneZero, CStarMatrix.ofMatrix_symm_mul, CStarMatrix.ofMatrix_symm_star,
      CStarMatrix.ofMatrix_symm_matrixUnit, Matrix.det_mul]
    simp [Matrix.det_fin_two]
  have hlim := (hdet.tendsto _).comp hx
  simp only [Function.comp_def, h0, Nonneg.coe_one] at hlim
  have : det 1 = 0 := tendsto_nhds_unique hlim tendsto_const_nhds
  simp [det, CStarMatrix.ofMatrix_symm_one] at this

end TauCeti.CuntzMatrixCheck
