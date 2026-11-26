/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import TauCeti.Analysis.CStarAlgebra.Cuntz.Subequivalence

/-!
# Check: `1 ⋠ diag(1, 0)` in `M₂(ℂ)`

A Check of CStarClassification CL4.1: in `M₂(ℂ)` the identity is not Cuntz subequivalent to the
rank-one projection `diag(1, 0)` (`TauCeti.CuntzMatrixCheck.not_cuntzLE_one_diag`). Every
`x⋆ diag(1, 0) x` has determinant `0`, and the determinant is continuous, so no norm limit of such
elements is invertible. The scalar Checks are `TauCeti.cuntzLE_complex_iff`.
-/

public section

open Filter Topology
open scoped CStarAlgebra ComplexOrder

namespace TauCeti.CuntzMatrixCheck

/-- The rank-one projection `diag(1, 0) = e₁₁⋆ e₁₁` in `M₂(ℂ)`, as a positive element. -/
noncomputable def diagOneZero : {a : CStarMatrix (Fin 2) (Fin 2) ℂ // 0 ≤ a} :=
  ⟨star (CStarMatrix.ofMatrix (Matrix.single 0 0 1)) * CStarMatrix.ofMatrix (Matrix.single 0 0 1),
    star_mul_self_nonneg _⟩

/-- The identity of `M₂(ℂ)`, as a positive element. -/
noncomputable def oneMatrix : {a : CStarMatrix (Fin 2) (Fin 2) ℂ // 0 ≤ a} :=
  ⟨1, zero_le_one⟩

/-- **`1 ⋠ diag(1, 0)` in `M₂(ℂ)`.** Every `x⋆ diag(1, 0) x` has determinant `0`, and the
determinant is continuous, while `det 1 = 1`. -/
theorem not_cuntzLE_one_diag : ¬ CuntzLE oneMatrix diagOneZero := by
  rw [cuntzLE_iff_exists_tendsto]
  rintro ⟨x, hx⟩
  let det : CStarMatrix (Fin 2) (Fin 2) ℂ → ℂ := fun M ↦ (CStarMatrix.ofMatrix.symm M).det
  have hdet : Continuous det :=
    (continuous_id.matrix_det).comp CStarMatrix.ofMatrixL.symm.continuous
  have h0 (n : ℕ) : det (star (x n) * (diagOneZero : CStarMatrix (Fin 2) (Fin 2) ℂ) * x n) = 0 := by
    change (CStarMatrix.ofMatrix.symm (star (x n)) * (CStarMatrix.ofMatrix.symm
      (star (CStarMatrix.ofMatrix (Matrix.single (0 : Fin 2) (0 : Fin 2) (1 : ℂ)))) *
      Matrix.single 0 0 1) * CStarMatrix.ofMatrix.symm (x n)).det = 0
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_mul]
    simp [Matrix.det_fin_two]
  have hlim := (hdet.tendsto _).comp hx
  simp only [Function.comp_def, h0, oneMatrix] at hlim
  have : det 1 = 0 := tendsto_nhds_unique hlim tendsto_const_nhds
  change Matrix.det (1 : Matrix (Fin 2) (Fin 2) ℂ) = 0 at this
  simp at this

end TauCeti.CuntzMatrixCheck
