/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import TauCeti.Analysis.CStarAlgebra.Cuntz.Subequivalence

/-!
# Cuntz subequivalence in `M₂(ℂ)`: `1 ⋠ diag(1, 0)`

In `M₂(ℂ)` the identity is not Cuntz subequivalent to the rank-one projection `diag(1, 0)`
(`TauCeti.CuntzMatrixCheck.not_cuntzLE_one_diag`). Every `x⋆ diag(1, 0) x` has determinant `0`,
and the determinant is continuous, so no norm limit of such elements is invertible. Contrast with
`ℂ`, where every nonzero positive scalar is subequivalent to every other
(`TauCeti.cuntzLE_complex_iff`).

## References

* Rørdam, Part I of Rørdam–Størmer, *Classification of Nuclear C*-Algebras. Entropy in Operator
  Algebras*, Encyclopaedia of Mathematical Sciences 126, Springer, 2002, §4.1.
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

/-- **`1 ⋠ diag(1, 0)` in `M₂(ℂ)`.** The identity is not Cuntz subequivalent to the rank-one
projection `diag(1, 0)`: no sequence `xₙ⋆ diag(1, 0) xₙ` converges to `1`. -/
theorem not_cuntzLE_one_diag : ¬ CuntzLE oneMatrix diagOneZero := by
  rw [cuntzLE_iff_exists_tendsto]
  rintro ⟨x, hx⟩
  -- Every `xₙ⋆ diag(1, 0) xₙ` has determinant `0`, the determinant is continuous, and `det 1 = 1`.
  let det : CStarMatrix (Fin 2) (Fin 2) ℂ → ℂ := fun M ↦
    (CStarMatrix.ofMatrixStarAlgEquiv.symm M).det
  have hdet : Continuous det :=
    (continuous_id.matrix_det).comp CStarMatrix.ofMatrixL.symm.continuous
  have h0 (n : ℕ) : det (star (x n) * (diagOneZero : CStarMatrix (Fin 2) (Fin 2) ℂ) * x n) = 0 := by
    simp only [det, diagOneZero, CStarMatrix.ofMatrix_eq_ofMatrixStarAlgEquiv, map_mul,
      map_star, StarAlgEquiv.symm_apply_apply, Matrix.det_mul]
    simp [Matrix.det_fin_two]
  have hlim := (hdet.tendsto _).comp hx
  simp only [Function.comp_def, h0, oneMatrix] at hlim
  have : det 1 = 0 := tendsto_nhds_unique hlim tendsto_const_nhds
  simp [det] at this

end TauCeti.CuntzMatrixCheck
