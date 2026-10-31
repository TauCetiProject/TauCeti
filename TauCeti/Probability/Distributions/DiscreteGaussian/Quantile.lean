/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.DiscreteGaussian.Cdf
public import TauCeti.Probability.Quantile.Discrete

/-!
# Quantiles of the discrete Gaussian

At positive width and an interior probability level, the real-cast lower quantile is the
least integer whose convergent Gaussian cumulative series reaches that level. Equivalently,
the level is strictly above the preceding cumulative mass and at most the mass through the
selected integer. In particular, equality at a jump selects that integer.

The one-sided quantile limits at levels zero and one are minus and plus infinity in `EReal`.
The statements concern interior levels, independently of the totalized endpoint values.
They specialize the integer-cast quantile API and its general infinite-endpoint criteria.

## References

* C. L. Canonne, G. Kamath and T. Steinke, *The Discrete Gaussian for Differential Privacy*,
  2020, arXiv:2004.00010.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Real Set Topology

namespace TauCeti.Probability

/-- An integer is the discrete Gaussian lower quantile exactly when it is the least crossing
of the explicit cumulative series. The crossing is non-strict, retaining levels at jumps. -/
theorem quantile_map_intCast_discreteGaussianMeasure_eq_iff (c : ℝ) {s : ℝ} (hs : 0 < s)
    {u : ℝ} (hu : u ∈ Ioo 0 1) (k : ℤ) :
    ((discreteGaussianMeasure c s).map (Int.cast : ℤ → ℝ)).quantile u = k ↔
      IsLeast {j : ℤ | u ≤ ∑' n : ℤ, if n ≤ j then
        exp (-((n : ℝ) - c) ^ 2 / (2 * s ^ 2)) / gaussianLatticeSum c s else 0} k := by
  have := isProbabilityMeasure_discreteGaussianMeasure c hs
  rw [Measure.quantile_map_intCast_eq_iff _ hu]
  simp_rw [discreteGaussianMeasure_real_Iic c hs]

/-- The lower quantile selects `k` precisely for levels strictly above the cumulative mass
through `k - 1` and at most the cumulative mass through `k`. -/
theorem quantile_map_intCast_discreteGaussianMeasure_eq_iff_lt_le (c : ℝ) {s : ℝ}
    (hs : 0 < s) {u : ℝ} (hu : u ∈ Ioo 0 1) (k : ℤ) :
    ((discreteGaussianMeasure c s).map (Int.cast : ℤ → ℝ)).quantile u = k ↔
      (∑' n : ℤ, if n ≤ k - 1 then
        exp (-((n : ℝ) - c) ^ 2 / (2 * s ^ 2)) / gaussianLatticeSum c s else 0) < u ∧
      u ≤ ∑' n : ℤ, if n ≤ k then
        exp (-((n : ℝ) - c) ^ 2 / (2 * s ^ 2)) / gaussianLatticeSum c s else 0 := by
  have := isProbabilityMeasure_discreteGaussianMeasure c hs
  simp_rw [← discreteGaussianMeasure_real_Iic c hs]
  exact Measure.quantile_map_intCast_eq_iff_lt_le _ hu k

/-- Discrete Gaussian lower quantiles tend to minus infinity as the level tends to zero
from above. -/
theorem tendsto_quantile_map_intCast_discreteGaussianMeasure_nhdsGT_zero (c : ℝ) {s : ℝ}
    (hs : 0 < s) :
    Tendsto (fun u ↦
      (((discreteGaussianMeasure c s).map (Int.cast : ℤ → ℝ)).quantile u : EReal))
      (𝓝[>] 0) (𝓝 ⊥) := by
  have := isProbabilityMeasure_discreteGaussianMeasure c hs
  refine Measure.tendsto_quantile_nhdsGT_zero_of_cdf_pos _ fun x ↦ ?_
  rw [Measure.cdf_map_intCast]
  exact discreteGaussianMeasure_real_Iic_pos c hs _

/-- Discrete Gaussian lower quantiles tend to plus infinity as the level tends to one
from below. -/
theorem tendsto_quantile_map_intCast_discreteGaussianMeasure_nhdsLT_one (c : ℝ) {s : ℝ}
    (hs : 0 < s) :
    Tendsto (fun u ↦
      (((discreteGaussianMeasure c s).map (Int.cast : ℤ → ℝ)).quantile u : EReal))
      (𝓝[<] 1) (𝓝 ⊤) := by
  have := isProbabilityMeasure_discreteGaussianMeasure c hs
  refine Measure.tendsto_quantile_nhdsLT_one_of_cdf_lt_one _ fun x ↦ ?_
  rw [Measure.cdf_map_intCast]
  exact discreteGaussianMeasure_real_Iic_lt_one c hs _

end TauCeti.Probability
