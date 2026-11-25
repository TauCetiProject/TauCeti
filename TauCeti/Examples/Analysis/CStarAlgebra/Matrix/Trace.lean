/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.CStarMatrix.Basic
public import TauCeti.Analysis.CStarAlgebra.Matrix.EuclideanCLM
public import TauCeti.Analysis.CStarAlgebra.Matrix.Trace

/-!
# Matrix-unit checks for the normalized trace and 2-norm

Checks on the matrix units `eᵢⱼ` of `M_k = CStarMatrix (Fin k) (Fin k) ℂ` for the normalized trace
`tr_k = k⁻¹ Tr` and the normalized 2-norm `‖x‖₂ = tr_k(x⋆x)^{1/2}`
(`CStarMatrix.normalizedTrace`, `CStarMatrix.normalizedTwoNorm`). Matrix indices start at `0`, so
the matrix unit written `e₁₁` in the literature is `matrixUnit 0 0` here.

* `e₁₁ ∈ M_k`: `‖e₁₁‖₂ = k^{-1/2}`, `‖e₁₁‖ = 1` and `tr_k(e₁₁) = 1/k ≤ ‖e₁₁‖₂`, while the
  unnormalized Frobenius norm of `1` is `k^{1/2} > 1 = ‖1‖` for `k ≥ 2`.
* `x = e₁₂`, `y = e₂₁` in `M_2`: `‖xy‖₂ = ‖x‖‖y‖₂ = 2^{-1/2}`, so `‖xy‖₂ ≤ ‖x‖‖y‖₂` is attained,
  while `‖x‖₂‖y‖₂ = 1/2`.
* The operator of `e₁₁ ∈ M_2` on `ℂ²` is an orthogonal projection, and the normalized trace of the
  operator agrees with `tr_2` on `e₁₁` (both `1/2`) and on `e₁₂` (both `0`).
* `k = 0`: `tr_0(1) = 0`, so `tr_0` is not a state.
* `tr_2(e₁₁⋆e₁₁) = 1/2` while the Frobenius inner product `⟪e₁₁, e₁₁⟫_F` is `1`; the trace-duality
  matrix of `tr_2` is `(1/2)·1`, and that of the state `x ↦ x₁₁` is `e₁₁`.
* `c = diag(1, 0) = e₁₁`, `x = e₁₂` in `M_2`: `cxc = 0` and
  `‖x - cxc‖₂ = 2^{-1/2} ≤ 2 · 2^{-1/2} = 2‖x‖‖c - 1‖₂`.
-/

public section

noncomputable section

open Matrix CStarMatrix
open scoped InnerProductSpace CStarAlgebra ComplexOrder Matrix.Norms.Frobenius

namespace TauCeti.MatrixTraceExample

variable {k : ℕ}

/-! ### `e₁₁ ∈ M_k` -/

/-- `tr_k(e₁₁) = 1/k`. -/
example (i : Fin k) : normalizedTrace (matrixUnit i i) = (k : ℂ)⁻¹ := by
  simp

/-- `‖e₁₁‖ = 1`. -/
example (i : Fin k) : ‖matrixUnit i i‖ = 1 :=
  norm_matrixUnit i i

/-- `tr_k(e₁₁) = 1/k ≤ k^{-1/2} = ‖e₁₁‖₂`. -/
example (i : Fin k) : (k : ℝ)⁻¹ ≤ normalizedTwoNorm (matrixUnit i i) := by
  have hk : (1 : ℝ) ≤ k := by exact_mod_cast i.pos
  rw [normalizedTwoNorm_matrixUnit, Fintype.card_fin]
  refine inv_anti₀ (by positivity) ?_
  calc √(k : ℝ) ≤ √(k : ℝ) * √(k : ℝ) :=
        le_mul_of_one_le_right (by positivity) (Real.one_le_sqrt.mpr hk)
    _ = k := Real.mul_self_sqrt (by positivity)

/-- The unnormalized trace would give `‖1‖₂ = k^{1/2}`, the Frobenius norm of `1`, which exceeds
`‖1‖ = 1` for `k ≥ 2`: only the normalized 2-norm is bounded by the operator norm. -/
example (hk : 2 ≤ k) :
    ‖ofMatrix.symm (1 : CStarMatrix (Fin k) (Fin k) ℂ)‖ = √k ∧
      ‖(1 : CStarMatrix (Fin k) (Fin k) ℂ)‖ = 1 ∧ 1 < √(k : ℝ) := by
  have : NeZero k := ⟨by omega⟩
  have hk : (1 : ℝ) < k := by exact_mod_cast hk
  refine ⟨?_, CStarRing.norm_one, Real.lt_sqrt zero_le_one |>.mpr (by norm_num; exact_mod_cast hk)⟩
  have h := normalizedTwoNorm_eq_inv_sqrt_mul_frobenius_norm (1 : CStarMatrix (Fin k) (Fin k) ℂ)
  rw [normalizedTwoNorm_one, Fintype.card_fin] at h
  field_simp at h
  linarith

/-! ### `e₁₂` and `e₂₁` in `M_2` -/

/-- `‖e₁₂e₂₁‖₂ = ‖e₁₂‖‖e₂₁‖₂ = 2^{-1/2}`: the bound `‖xy‖₂ ≤ ‖x‖‖y‖₂` is attained. -/
example : normalizedTwoNorm (matrixUnit (0 : Fin 2) 1 * matrixUnit 1 0) = (√2)⁻¹ ∧
    ‖matrixUnit (0 : Fin 2) 1‖ * normalizedTwoNorm (matrixUnit (1 : Fin 2) 0) = (√2)⁻¹ := by
  simp [norm_matrixUnit]

/-- `‖e₁₂‖₂‖e₂₁‖₂ = 1/2 < 2^{-1/2} = ‖e₁₂e₂₁‖₂`: the product of the 2-norms is not an upper
bound. -/
example : normalizedTwoNorm (matrixUnit (0 : Fin 2) 1) *
      normalizedTwoNorm (matrixUnit (1 : Fin 2) 0) = 1 / 2 ∧
    1 / 2 < normalizedTwoNorm (matrixUnit (0 : Fin 2) 1 * matrixUnit 1 0) := by
  have h2 : √(2 : ℝ) * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have h2' : √(2 : ℝ) < 2 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  simp only [matrixUnit_mul_matrixUnit, normalizedTwoNorm_matrixUnit, Fintype.card_fin]
  push_cast
  refine ⟨by rw [← mul_inv, h2]; norm_num, ?_⟩
  rw [one_div]
  exact inv_strictAnti₀ (by positivity) h2'

/-! ### The normalized trace of the operator -/

/-- The operator of `e₁₁ ∈ M_2` on `ℂ²` is an orthogonal projection. -/
example : IsStarProjection (toEuclideanCLM (matrixUnit (0 : Fin 2) 0)) :=
  ⟨(isStarProjection_matrixUnit 0).isIdempotentElem.map CStarMatrix.toEuclideanCLM,
    (isStarProjection_matrixUnit 0).isSelfAdjoint.map CStarMatrix.toEuclideanCLM⟩

/-- The normalized trace of the operator of `x ∈ M_2` on `ℂ²` is `tr_2(x)` for `x = e₁₁`, where
both are `1/2`, and for `x = e₁₂`, where both are `0`. -/
example : (2 : ℂ)⁻¹ * LinearMap.trace ℂ _ (toEuclideanCLM (matrixUnit (0 : Fin 2) 0)).toLinearMap =
      normalizedTrace (matrixUnit (0 : Fin 2) 0) ∧
    normalizedTrace (matrixUnit (0 : Fin 2) 0) = 1 / 2 ∧
    (2 : ℂ)⁻¹ * LinearMap.trace ℂ _ (toEuclideanCLM (matrixUnit (0 : Fin 2) 1)).toLinearMap =
      normalizedTrace (matrixUnit (0 : Fin 2) 1) ∧
    normalizedTrace (matrixUnit (0 : Fin 2) 1) = 0 := by
  simp [Matrix.trace_single_eq_of_ne]

/-! ### `k = 0` -/

/-- On `M_0` the normalized trace vanishes, so `tr_0(1) = 0 ≠ 1` and `tr_0` is not a state. -/
example : normalizedTrace (1 : CStarMatrix (Fin 0) (Fin 0) ℂ) = 0 :=
  normalizedTrace_of_isEmpty 1

/-! ### Normalization against the Frobenius inner product -/

/-- `tr_2(e₁₁⋆e₁₁) = 1/2`, while `⟪e₁₁, e₁₁⟫_F = 1`: the factor `k⁻¹`. -/
example : normalizedTrace (star (matrixUnit (0 : Fin 2) 0) * matrixUnit 0 0) = 1 / 2 ∧
    ⟪ofMatrix.symm (matrixUnit (0 : Fin 2) 0), ofMatrix.symm (matrixUnit (0 : Fin 2) 0)⟫_ℂ = 1 := by
  have h := normalizedTrace_star_mul_eq_inv_mul_frobenius_inner (matrixUnit (0 : Fin 2) 0)
    (matrixUnit (0 : Fin 2) 0)
  simp only [star_matrixUnit, matrixUnit_mul_matrixUnit, normalizedTrace_matrixUnit,
    Fintype.card_fin] at h ⊢
  refine ⟨by norm_num, ?_⟩
  simpa using h.symm

/-- The trace-duality matrix of `tr_2` is `(1/2)·1`: `tr_2(x) = Tr((1/2)·1 · x)`. -/
example (x : CStarMatrix (Fin 2) (Fin 2) ℂ) :
    normalizedTrace x = Matrix.trace (((1 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) *
      ofMatrix.symm x) := by
  simp [normalizedTrace_def]

/-- The trace-duality matrix of the non-tracial state `x ↦ x₁₁` is `e₁₁`. -/
example (x : CStarMatrix (Fin 2) (Fin 2) ℂ) :
    x 0 0 = Matrix.trace (ofMatrix.symm (matrixUnit 0 0) * ofMatrix.symm x) := by
  simp [Matrix.trace_single_mul]

/-! ### The `cxc` bound at `c = diag(1, 0)`, `x = e₁₂` -/

/-- For `c = e₁₁` and `x = e₁₂` in `M_2`, `cxc = 0`, `‖x - cxc‖₂ = 2^{-1/2}`, and
`2‖x‖‖c - 1‖₂ = 2 · 2^{-1/2}`. -/
example : matrixUnit (0 : Fin 2) 0 * matrixUnit 0 1 * matrixUnit 0 0 = 0 ∧
    normalizedTwoNorm
        (matrixUnit (0 : Fin 2) 1 - matrixUnit 0 0 * matrixUnit 0 1 * matrixUnit 0 0) = (√2)⁻¹ ∧
    2 * ‖matrixUnit (0 : Fin 2) 1‖ * normalizedTwoNorm (matrixUnit (0 : Fin 2) 0 - 1) =
      2 * (√2)⁻¹ := by
  have hc : matrixUnit (0 : Fin 2) 0 - 1 = -matrixUnit 1 1 := by
    ext a b
    fin_cases a <;> fin_cases b <;> simp
  exact ⟨by simp, by simp, by simp [hc, norm_matrixUnit]⟩

end TauCeti.MatrixTraceExample
