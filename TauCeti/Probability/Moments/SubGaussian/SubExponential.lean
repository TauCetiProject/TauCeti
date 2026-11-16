/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Moments.SubExponential
public import TauCeti.Probability.Moments.SubGaussian.Basic
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Sub-Gaussian and sub-exponential moment bounds

A centered sub-Gaussian variable with variance proxy `c` is sub-exponential with any positive
parameter `K` such that `c / 2 ≤ K ^ 2`. In particular the standard Gaussian is sub-exponential
with parameter `1`.

## Main results

* `ProbabilityTheory.HasSubgaussianMGF.hasSubexponentialMGF` compares the two MGF conventions.
* `hasSubexponentialMGF_fun_id_gaussianReal` treats Gaussian laws of any mean and variance.
-/

public section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

namespace ProbabilityTheory.HasSubgaussianMGF

/-- A sub-Gaussian bound on the centered variable implies a sub-exponential bound. -/
theorem hasSubexponentialMGF_of_centered {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ} {c : ℝ≥0} {K : ℝ}
    (hcenter : HasSubgaussianMGF (fun ω ↦ X ω - μ[X]) c μ)
    (hK : 0 < K) (hc : (c : ℝ) / 2 ≤ K ^ 2) :
    TauCeti.Probability.HasSubexponentialMGF X K μ := by
  have hX : Integrable X μ := by
    convert hcenter.integrable.add (integrable_const μ[X]) using 1
    funext ω
    simp
  refine ⟨hK, hX, ?_, ?_⟩
  · intro t _
    exact hcenter.integrable_exp_mul t
  · intro t _
    have hbound : (c : ℝ) * t ^ 2 / 2 ≤ K ^ 2 * t ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_right hc (sq_nonneg t)]
    exact (hcenter.mgf_le t).trans (Real.exp_le_exp.mpr hbound)

/-- A sub-Gaussian variable is sub-exponential when the quadratic MGF constants
are compatible. -/
theorem hasSubexponentialMGF {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ} {c : ℝ≥0} {K : ℝ}
    (hX : HasSubgaussianMGF X c μ)
    (hK : 0 < K) (hc : (c : ℝ) / 2 ≤ K ^ 2) :
    TauCeti.Probability.HasSubexponentialMGF X K μ := by
  apply hasSubexponentialMGF_of_centered _ hK hc
  simpa only [hX.integral_eq_zero, sub_zero] using hX

end ProbabilityTheory.HasSubgaussianMGF

namespace TauCeti.Probability

/-- A Gaussian satisfies the sub-exponential MGF bound for compatible parameters. -/
theorem hasSubexponentialMGF_fun_id_gaussianReal {m : ℝ} {v : ℝ≥0} {K : ℝ}
    (hK : 0 < K) (hv : (v : ℝ) / 2 ≤ K ^ 2) :
    HasSubexponentialMGF (fun x : ℝ ↦ x) K (gaussianReal m v) := by
  have hX : HasSubgaussianMGF (fun x : ℝ ↦ x) v (gaussianReal 0 v) := by
    refine ⟨integrable_exp_mul_gaussianReal, ?_⟩
    intro t
    simp [mgf_fun_id_gaussianReal]
  have hcenter : HasSubgaussianMGF (fun x : ℝ ↦ x - m) v (gaussianReal m v) := by
    have hmap : HasSubgaussianMGF (fun x : ℝ ↦ x) v
        ((gaussianReal m v).map (fun x ↦ x - m)) := by
      simpa [gaussianReal_map_sub_const] using hX
    have h := HasSubgaussianMGF.of_map (μ := gaussianReal m v)
      (Y := fun x : ℝ ↦ x - m) (by fun_prop) hmap
    convert h using 1
    funext x
    rfl
  apply ProbabilityTheory.HasSubgaussianMGF.hasSubexponentialMGF_of_centered _ hK hv
  simpa [integral_id_gaussianReal] using hcenter

end TauCeti.Probability
