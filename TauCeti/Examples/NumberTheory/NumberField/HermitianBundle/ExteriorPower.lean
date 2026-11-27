/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.HermitianBundle.ExteriorPower
public import TauCeti.NumberTheory.NumberField.HermitianBundle.Prod

/-!
# Exterior powers of hermitian vector bundles: checks

On the orthogonal sum `Ō_K ⊕ Ō_K` the 2-vector `e₁ ∧ e₂` has norm one at every complex
embedding, and the determinant of `Ō_K ⊕ Ō_K` is a line. Rescaling a metric by `c` rescales the
norm of a decomposable `n`-vector by `e^{-n c}`, not by `e^{-c}`.
-/

public section

open scoped TensorProduct

open NumberField TauCeti

namespace TauCeti.HermitianExteriorPowerChecks

variable {K : Type*} [Field K] [NumberField K]

/-- On `Ō_K ⊕ Ō_K`, the 2-vector `e₁ ∧ e₂` has norm one at every complex embedding. -/
example (σ : K →+* ℂ) :
    (((HermitianMetric.trivial K).prod (HermitianMetric.trivial K)).exteriorPower 2).norm σ
      (1 ⊗ₜ exteriorPower.ιMulti (𝓞 K) 2 ![(1, 0), (0, 1)]) = 1 := by
  refine (pow_left_inj₀ (HermitianMetric.norm_nonneg _ _ _) zero_le_one two_ne_zero).mp ?_
  rw [HermitianMetric.norm_exteriorPower_tmul_ιMulti_sq, one_pow]
  simp [Matrix.det_fin_two]

/-- The determinant of `Ō_K ⊕ Ō_K` is a line. -/
example : ((HermitianBundle.trivial K).prod (HermitianBundle.trivial K)).det.rank = 1 :=
  HermitianBundle.rank_det _

/-- Rescaling `Ō_K ⊕ Ō_K` by `c` multiplies the norm of `e₁ ∧ e₂` by `e^{-2c}`. -/
example (σ : K →+* ℂ) (c : ℝ) :
    ((((HermitianMetric.trivial K).prod (HermitianMetric.trivial K)).rescale c).exteriorPower
      2).norm σ (1 ⊗ₜ exteriorPower.ιMulti (𝓞 K) 2 ![(1, 0), (0, 1)]) = Real.exp (-(2 * c)) := by
  have h1 : (((HermitianMetric.trivial K).prod (HermitianMetric.trivial K)).exteriorPower 2).norm σ
      (1 ⊗ₜ exteriorPower.ιMulti (𝓞 K) 2 ![(1, 0), (0, 1)]) = 1 := by
    refine (pow_left_inj₀ (HermitianMetric.norm_nonneg _ _ _) zero_le_one two_ne_zero).mp ?_
    rw [HermitianMetric.norm_exteriorPower_tmul_ιMulti_sq, one_pow]
    simp [Matrix.det_fin_two]
  rw [HermitianMetric.exteriorPower_rescale, HermitianMetric.norm_rescale, h1, mul_one]
  norm_num

end TauCeti.HermitianExteriorPowerChecks
