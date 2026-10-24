/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.AsymmetricLaplace.Basic
public import TauCeti.Probability.Quantile

/-!
# Quantiles of asymmetric Laplace laws

For positive left and right rates `l` and `r`, put `w = r / (l + r)`, the probability mass
at or below the location `m`. The quantile is `m + log (u / w) / l` for `u ≤ w` and
`m - log ((1 - u) / (1 - w)) / r` otherwise. Both branches meet at the location.

Interior quantiles are continuous and strictly increasing, with one-sided limits minus
infinity and plus infinity. All finite formulas assume levels strictly between zero and one.

The inversion uses `cdf_asymmetricLaplaceMeasure_eq` and the shared cdf/quantile inverse API.
The regularity and endpoint arguments follow
`TauCeti.Probability.Distributions.GeneralizedNormal.Quantile`.

## References

* S. Kotz, T. J. Kozubowski, K. Podgórski, *The Laplace Distribution and Generalizations*,
  Birkhäuser (2001), ch. 3.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Real Set Topology

namespace TauCeti.Probability

variable {m l r u : ℝ}

/-- The asymmetric Laplace quantile, obtained by inverting its two exponential tails. -/
@[simp]
theorem quantile_asymmetricLaplaceMeasure (hl : 0 < l) (hr : 0 < r) (hu : u ∈ Ioo 0 1) :
    (asymmetricLaplaceMeasure m l r).quantile u =
      if u ≤ r / (l + r) then m + log (u / (r / (l + r))) / l
      else m - log ((1 - u) / (1 - r / (l + r))) / r := by
  let w := r / (l + r)
  have hw0 : 0 < w := div_pos hr (add_pos hl hr)
  have hw1 : w < 1 := (div_lt_one (add_pos hl hr)).2 (by linarith)
  have hcomp : l / (l + r) = 1 - w := by
    dsimp [w]
    field_simp
    ring
  have hinv (x : ℝ) := Measure.quantile_cdf (x := x) (asymmetricLaplaceMeasure m l r)
    ((strictMono_cdf_asymmetricLaplaceMeasure hl hr).strictMonoOn _)
  by_cases huw : u ≤ w
  · rw [ite_eq_left huw]
    have harg := div_pos hu.1 hw0
    have hlog : log (u / w) ≤ 0 := log_nonpos harg.le ((div_le_one hw0).2 huw)
    have hloc : m + log (u / w) / l ≤ m :=
      add_le_of_nonpos_right (div_nonpos_of_nonpos_of_nonneg hlog hl.le)
    have hroot : cdf (asymmetricLaplaceMeasure m l r) (m + log (u / w) / l) = u := by
      have hexp : l * (m + log (u / w) / l - m) = log (u / w) := by field_simp; ring
      rw [cdf_asymmetricLaplaceMeasure_eq hl hr, ite_eq_left hloc, hexp, exp_log harg]
      exact mul_div_cancel₀ u hw0.ne'
    exact (congrArg (asymmetricLaplaceMeasure m l r).quantile hroot).symm.trans
      (hinv _ (by rw [hroot]; exact hu))
  · rw [ite_eq_right huw]
    have harg := div_pos (sub_pos.mpr hu.2) (sub_pos.mpr hw1)
    have hlog : log ((1 - u) / (1 - w)) < 0 :=
      log_neg harg ((div_lt_one (sub_pos.mpr hw1)).2 (by linarith))
    have hloc : ¬ m - log ((1 - u) / (1 - w)) / r ≤ m := by
      have := div_neg_of_neg_of_pos hlog hr
      linarith
    have hroot :
        cdf (asymmetricLaplaceMeasure m l r) (m - log ((1 - u) / (1 - w)) / r) = u := by
      have hexp : -(r * (m - log ((1 - u) / (1 - w)) / r - m)) =
          log ((1 - u) / (1 - w)) := by field_simp; ring
      rw [cdf_asymmetricLaplaceMeasure_eq hl hr, ite_eq_right hloc, hexp, exp_log harg,
        hcomp, mul_div_cancel₀ _ (sub_pos.mpr hw1).ne']
      ring
    exact (congrArg (asymmetricLaplaceMeasure m l r).quantile hroot).symm.trans
      (hinv _ (by rw [hroot]; exact hu))

/-- The quantile at the mass to the left of the location is exactly the location. -/
@[simp]
theorem quantile_asymmetricLaplaceMeasure_location (hl : 0 < l) (hr : 0 < r) :
    (asymmetricLaplaceMeasure m l r).quantile (r / (l + r)) = m := by
  rw [quantile_asymmetricLaplaceMeasure hl hr
    ⟨div_pos hr (add_pos hl hr), (div_lt_one (add_pos hl hr)).2 (by linarith)⟩]
  simp [(div_pos hr (add_pos hl hr)).ne']

/-- Interior asymmetric Laplace quantiles increase strictly with the probability level. -/
theorem strictMonoOn_quantile_asymmetricLaplaceMeasure (hl : 0 < l) (hr : 0 < r) :
    StrictMonoOn (asymmetricLaplaceMeasure m l r).quantile (Ioo 0 1) :=
  Measure.strictMonoOn_quantile _ (continuous_cdf_asymmetricLaplaceMeasure hl hr)

/-- The asymmetric Laplace quantile is continuous on the interior probability levels. -/
theorem continuousOn_quantile_asymmetricLaplaceMeasure (hl : 0 < l) (hr : 0 < r) :
    ContinuousOn (asymmetricLaplaceMeasure m l r).quantile (Ioo 0 1) :=
  Measure.continuousOn_quantile _ (continuous_cdf_asymmetricLaplaceMeasure hl hr)
    ((strictMono_cdf_asymmetricLaplaceMeasure hl hr).strictMonoOn _)

/-- Asymmetric Laplace quantiles tend to minus infinity as the level decreases to zero. -/
theorem tendsto_quantile_asymmetricLaplaceMeasure_nhdsGT_zero (hl : 0 < l) (hr : 0 < r) :
    Tendsto (fun u ↦ ((asymmetricLaplaceMeasure m l r).quantile u : EReal))
      (𝓝[>] 0) (𝓝 ⊥) :=
  Measure.tendsto_quantile_nhdsGT_zero_of_cdf_pos _ fun x ↦
    (cdf_nonneg _ (x - 1)).trans_lt (strictMono_cdf_asymmetricLaplaceMeasure hl hr (by linarith))

/-- Asymmetric Laplace quantiles tend to plus infinity as the level increases to one. -/
theorem tendsto_quantile_asymmetricLaplaceMeasure_nhdsLT_one (hl : 0 < l) (hr : 0 < r) :
    Tendsto (fun u ↦ ((asymmetricLaplaceMeasure m l r).quantile u : EReal))
      (𝓝[<] 1) (𝓝 ⊤) :=
  Measure.tendsto_quantile_nhdsLT_one_of_cdf_lt_one _ fun x ↦
    (strictMono_cdf_asymmetricLaplaceMeasure hl hr (by linarith : x < x + 1)).trans_le
      (cdf_le_one _ (x + 1))

end TauCeti.Probability
