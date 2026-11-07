/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Moments.SubExponential
public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Sub-Gaussian and sub-exponential moment bounds

A centered sub-Gaussian variable with variance proxy `c` is sub-exponential with any positive
parameter `K` such that `c / 2 ≤ K ^ 2`. In particular the standard Gaussian is sub-exponential
with parameter `1`.

## Main results

* `HasSubexponentialMGF.of_hasSubgaussianMGF` compares the two MGF conventions.
* `hasSubexponentialMGF_standardGaussian` verifies the standard Gaussian example.
-/

public section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

namespace TauCeti.Probability

/-- A centered sub-Gaussian variable is sub-exponential when the quadratic MGF constants
are compatible. -/
theorem HasSubexponentialMGF.of_hasSubgaussianMGF {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ} {c : ℝ≥0} {K : ℝ}
    (hX : HasSubgaussianMGF X c μ) (hmean : μ[X] = 0)
    (hK : 0 < K) (hc : (c : ℝ) / 2 ≤ K ^ 2) :
    HasSubexponentialMGF X K μ := by
  refine ⟨hK, hX.integrable, ?_, ?_⟩
  · intro t ht
    simpa [hmean] using hX.integrable_exp_mul t
  · intro t ht
    have hbound : (c : ℝ) * t ^ 2 / 2 ≤ K ^ 2 * t ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_right hc (sq_nonneg t)]
    simpa only [hmean, sub_zero] using (hX.mgf_le t).trans (Real.exp_le_exp.mpr hbound)

/-- The standard Gaussian satisfies the sub-exponential MGF bound with parameter `1`. -/
theorem hasSubexponentialMGF_standardGaussian :
    HasSubexponentialMGF (fun x : ℝ ↦ x) 1 (gaussianReal 0 1) := by
  have hX : HasSubgaussianMGF (fun x : ℝ ↦ x) 1 (gaussianReal 0 1) := by
    refine ⟨integrable_exp_mul_gaussianReal, ?_⟩
    intro t
    simp [mgf_fun_id_gaussianReal]
  apply HasSubexponentialMGF.of_hasSubgaussianMGF hX
  · simp
  · norm_num
  · norm_num

end TauCeti.Probability
