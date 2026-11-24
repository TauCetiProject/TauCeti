/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.CStarMatrix
public import TauCeti.Analysis.CStarAlgebra.Matrix.EuclideanCLM
public import TauCeti.Analysis.CStarAlgebra.Matrix.Trace

/-!
# Matrix-unit checks for the normalized trace and 2-norm

Checks on the matrix units `eᵢⱼ` of `M_k = CStarMatrix (Fin k) (Fin k) ℂ` for the normalized trace
`tr_k = k⁻¹ Tr` and the normalized 2-norm `‖x‖₂ = tr_k(x⋆x)^{1/2}`
(`CStarMatrix.normalizedTrace`, `CStarMatrix.normalizedTwoNorm`). Matrix indices start at `0`, so
the matrix unit written `e₁₁` in the literature is `unit 0 0` here.

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

/-- The matrix unit `eᵢⱼ` of `M_k`. -/
def unit (i j : Fin k) : CStarMatrix (Fin k) (Fin k) ℂ :=
  ofMatrix (Matrix.single i j 1)

/-- The entries of `eᵢⱼ`. -/
theorem unit_apply (i j a b : Fin k) : unit i j a b = if i = a ∧ j = b then 1 else 0 := by
  simp [unit, Matrix.single_apply]

/-- `eᵢⱼ⋆ = eⱼᵢ`. -/
theorem star_unit (i j : Fin k) : star (unit i j) = unit j i := by
  apply ofMatrix.symm.injective
  simp [unit, ofMatrix_symm_star]

/-- `eᵢⱼ eⱼₗ = eᵢₗ`. -/
theorem unit_mul_unit (i j l : Fin k) : unit i j * unit j l = unit i l := by
  apply ofMatrix.symm.injective
  simp [unit, ofMatrix_symm_mul]

/-- `eᵢⱼ eⱼ'ₗ = 0` for `j ≠ j'`. -/
theorem unit_mul_unit_of_ne (i j j' l : Fin k) (h : j ≠ j') : unit i j * unit j' l = 0 := by
  apply ofMatrix.symm.injective
  simp [unit, ofMatrix_symm_mul, h, ofMatrix_symm_zero]

/-- `tr_k(eᵢⱼ)` is `1/k` on the diagonal and `0` off it. -/
theorem normalizedTrace_unit (i j : Fin k) :
    normalizedTrace (unit i j) = if i = j then (k : ℂ)⁻¹ else 0 := by
  rw [normalizedTrace_def, unit, Equiv.symm_apply_apply, Fintype.card_fin]
  split_ifs with h
  · subst h; simp [Matrix.trace_single_eq_same]
  · simp [Matrix.trace_single_eq_of_ne _ _ _ h]

/-- **`‖eᵢⱼ‖₂ = k^{-1/2}`.** -/
theorem normalizedTwoNorm_unit (i j : Fin k) : normalizedTwoNorm (unit i j) = (√k)⁻¹ := by
  rw [normalizedTwoNorm_def, star_unit, unit_mul_unit, normalizedTrace_unit, ite_eq_left rfl,
    ← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.ofReal_re, Real.sqrt_inv]

/-- **`‖eᵢⱼ‖ = 1`.** -/
theorem norm_unit (i j : Fin k) : ‖unit i j‖ = 1 := by
  refine le_antisymm ?_ ?_
  · have hp : IsStarProjection (unit j j) :=
      ⟨by rw [IsIdempotentElem, unit_mul_unit], by rw [IsSelfAdjoint, star_unit]⟩
    have h := hp.norm_le
    have hn : ‖star (unit i j) * unit i j‖ = ‖unit i j‖ * ‖unit i j‖ :=
      CStarRing.norm_star_mul_self
    rw [← unit_mul_unit j i j, ← star_unit, hn] at h
    nlinarith [norm_nonneg (unit i j)]
  · simpa [unit_apply] using norm_entry_le_norm (M := unit i j) (i := i) (j := j)

/-! ### `e₁₁ ∈ M_k` -/

/-- `tr_k(e₁₁) = 1/k`. -/
example (i : Fin k) : normalizedTrace (unit i i) = (k : ℂ)⁻¹ := by
  simp [normalizedTrace_unit]

/-- `tr_k(e₁₁) = 1/k ≤ k^{-1/2} = ‖e₁₁‖₂`. -/
example (i : Fin k) : (k : ℝ)⁻¹ ≤ normalizedTwoNorm (unit i i) := by
  have hk : (1 : ℝ) ≤ k := by
    have := i.pos
    exact_mod_cast this
  rw [normalizedTwoNorm_unit]
  refine inv_anti₀ (by positivity) ?_
  calc √(k : ℝ) ≤ √(k : ℝ) * √(k : ℝ) := le_mul_of_one_le_right (by positivity) (by
        rw [Real.one_le_sqrt]; exact hk)
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
example : normalizedTwoNorm (unit (0 : Fin 2) 1 * unit 1 0) = (√2)⁻¹ ∧
    ‖unit (0 : Fin 2) 1‖ * normalizedTwoNorm (unit (1 : Fin 2) 0) = (√2)⁻¹ := by
  rw [unit_mul_unit, normalizedTwoNorm_unit, norm_unit, normalizedTwoNorm_unit, one_mul]
  norm_num

/-- `‖e₁₂‖₂‖e₂₁‖₂ = 1/2 < 2^{-1/2} = ‖e₁₂e₂₁‖₂`: the product of the 2-norms is not an upper
bound. -/
example : normalizedTwoNorm (unit (0 : Fin 2) 1) * normalizedTwoNorm (unit (1 : Fin 2) 0) = 1 / 2 ∧
    1 / 2 < normalizedTwoNorm (unit (0 : Fin 2) 1 * unit 1 0) := by
  rw [unit_mul_unit, normalizedTwoNorm_unit, normalizedTwoNorm_unit, normalizedTwoNorm_unit]
  have h2 : √(2 : ℝ) * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have h2' : √(2 : ℝ) < 2 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hpos : (0 : ℝ) < √2 := by positivity
  refine ⟨?_, ?_⟩
  · push_cast
    rw [← mul_inv, h2]
    norm_num
  · push_cast
    rw [one_div]
    exact inv_strictAnti₀ hpos h2'

/-! ### The normalized trace of the operator -/

/-- The operator of `e₁₁ ∈ M_2` on `ℂ²` is an orthogonal projection. -/
example : IsStarProjection (toEuclideanCLM (unit (0 : Fin 2) 0)) :=
  ⟨by rw [IsIdempotentElem, ← map_mul, unit_mul_unit], by rw [IsSelfAdjoint, ← map_star, star_unit]⟩

/-- The normalized trace of the operator of `x ∈ M_2` on `ℂ²` is `tr_2(x)` for `x = e₁₁`, where
both are `1/2`, and for `x = e₁₂`, where both are `0`. -/
example : (2 : ℂ)⁻¹ * LinearMap.trace ℂ _ (toEuclideanCLM (unit (0 : Fin 2) 0)).toLinearMap =
      normalizedTrace (unit (0 : Fin 2) 0) ∧
    normalizedTrace (unit (0 : Fin 2) 0) = 1 / 2 ∧
    (2 : ℂ)⁻¹ * LinearMap.trace ℂ _ (toEuclideanCLM (unit (0 : Fin 2) 1)).toLinearMap =
      normalizedTrace (unit (0 : Fin 2) 1) ∧
    normalizedTrace (unit (0 : Fin 2) 1) = 0 := by
  have htr (x : CStarMatrix (Fin 2) (Fin 2) ℂ) :
      LinearMap.trace ℂ _ (toEuclideanCLM x).toLinearMap = Matrix.trace (ofMatrix.symm x) := by
    rw [LinearMap.trace_eq_matrix_trace ℂ (EuclideanSpace.basisFun (Fin 2) ℂ).toBasis,
      toEuclideanCLM_apply, Matrix.coe_toEuclideanCLM_eq_toEuclideanLin,
      Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearMap.toMatrix_toLin]
  simp only [htr, normalizedTrace_def, Fintype.card_fin]
  norm_num
  simp [unit, Matrix.trace_single_eq_of_ne]

/-! ### `k = 0` -/

/-- On `M_0` the normalized trace vanishes, so `tr_0(1) = 0 ≠ 1` and `tr_0` is not a state. -/
example : normalizedTrace (1 : CStarMatrix (Fin 0) (Fin 0) ℂ) = 0 :=
  normalizedTrace_of_isEmpty 1

/-! ### Normalization against the Frobenius inner product -/

/-- `tr_2(e₁₁⋆e₁₁) = 1/2`, while `⟪e₁₁, e₁₁⟫_F = 1`: the factor `k⁻¹`. -/
example : normalizedTrace (star (unit (0 : Fin 2) 0) * unit 0 0) = 1 / 2 ∧
    ⟪ofMatrix.symm (unit (0 : Fin 2) 0), ofMatrix.symm (unit (0 : Fin 2) 0)⟫_ℂ = 1 := by
  have h := normalizedTrace_star_mul_eq_inv_mul_frobenius_inner (unit (0 : Fin 2) 0)
    (unit (0 : Fin 2) 0)
  rw [star_unit, unit_mul_unit, normalizedTrace_unit, Fintype.card_fin] at h
  refine ⟨by rw [star_unit, unit_mul_unit, normalizedTrace_unit]; norm_num, ?_⟩
  simp only [ite_true, Nat.cast_ofNat] at h
  exact (mul_left_cancel₀ (a := (2 : ℂ)⁻¹) (by norm_num) (h.symm.trans (mul_one _).symm))

/-- The trace-duality matrix of `tr_2` is `(1/2)·1`: `tr_2(x) = Tr((1/2)·1 · x)`. -/
example (x : CStarMatrix (Fin 2) (Fin 2) ℂ) :
    normalizedTrace x = Matrix.trace (((1 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) *
      ofMatrix.symm x) := by
  simp [normalizedTrace_def]

/-- The trace-duality matrix of the non-tracial state `x ↦ x₁₁` is `e₁₁`. -/
example (x : CStarMatrix (Fin 2) (Fin 2) ℂ) :
    x 0 0 = Matrix.trace (ofMatrix.symm (unit 0 0) * ofMatrix.symm x) := by
  simp [unit, Matrix.trace_single_mul]

/-! ### The `cxc` bound at `c = diag(1, 0)`, `x = e₁₂` -/

/-- For `c = e₁₁` and `x = e₁₂` in `M_2`, `cxc = 0`, `‖x - cxc‖₂ = 2^{-1/2}`, and
`2‖x‖‖c - 1‖₂ = 2 · 2^{-1/2}`. -/
example : unit (0 : Fin 2) 0 * unit 0 1 * unit 0 0 = 0 ∧
    normalizedTwoNorm (unit (0 : Fin 2) 1 - unit 0 0 * unit 0 1 * unit 0 0) = (√2)⁻¹ ∧
    2 * ‖unit (0 : Fin 2) 1‖ * normalizedTwoNorm (unit (0 : Fin 2) 0 - 1) = 2 * (√2)⁻¹ := by
  have hcxc : unit (0 : Fin 2) 0 * unit 0 1 * unit 0 0 = 0 := by
    rw [unit_mul_unit, unit_mul_unit_of_ne _ _ _ _ (by decide)]
  have hc : unit (0 : Fin 2) 0 - 1 = -unit 1 1 := by
    apply ofMatrix.symm.injective
    ext a b
    fin_cases a <;> fin_cases b <;> simp [unit]
  refine ⟨hcxc, ?_, ?_⟩
  · rw [hcxc, sub_zero, normalizedTwoNorm_unit]
    norm_num
  · rw [hc, normalizedTwoNorm_neg, normalizedTwoNorm_unit, norm_unit, mul_one]
    norm_num

end TauCeti.MatrixTraceExample
