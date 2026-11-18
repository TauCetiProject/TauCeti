/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Gaussian.Mixture.Quantile
public import TauCeti.Probability.Distributions.Categorical.Support
import TauCeti.Probability.Quantile.Finite

/-!
# Support and quantile endpoints of scalar Gaussian mixtures

A positive-weight Gaussian component with nonzero variance gives the mixture full real
support and infinite quantile endpoints. Otherwise the mixture is the categorical law of
its means: its support consists of the distinct positive-weight means, and its quantile
endpoints are their minimum and maximum. These formulas cover all simplex weights and
nonnegative variances, including repeated means and arbitrary zero-weight components.

The categorical identification is `gaussianMixtureMeasure_eq_map_categoricalMeasure`.
The finite endpoint formulas use the finite-support quantile theory, so zero-weight means
are excluded before taking extrema.

## References

* G. McLachlan and D. Peel, *Finite Mixture Models*, Wiley (2000), Chapter 1.
-/

public section

noncomputable section

open Convexity Filter MeasureTheory ProbabilityTheory Set Topology
open scoped NNReal

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι]
variable (p : StdSimplex ℝ≥0 ι) (m : ι → ℝ) (v : ι → ℝ≥0)

open Classical in
/-- The support is the whole real line if an active component has nonzero variance;
otherwise it is exactly the finite set of positive-weight means. -/
@[simp]
theorem support_gaussianMixtureMeasure :
    (gaussianMixtureMeasure p m v).support =
      if ∃ i, 0 < p.weights i ∧ v i ≠ 0 then univ
      else (p.weights.support.image m : Set ℝ) := by
  let : MeasurableSpace ι := ⊤
  split_ifs with h
  · exact Measure.support_eq_univ_of_strictMono_cdf _
      (strictMono_cdf_gaussianMixtureMeasure h)
  · rw [gaussianMixtureMeasure_eq_map_categoricalMeasure (by simpa using h)]
    exact p.support_map_categoricalMeasure m

open Classical in
/-- At level zero the quantile tends to minus infinity if some positive-weight variance
is nonzero, and to the least positive-weight mean otherwise. -/
theorem tendsto_quantile_gaussianMixtureMeasure_nhdsGT_zero :
    Tendsto (fun u ↦ ((gaussianMixtureMeasure p m v).quantile u : EReal)) (𝓝[>] 0)
      (𝓝 (if ∃ i, 0 < p.weights i ∧ v i ≠ 0 then ⊥
        else (((p.weights.support.image m).min'
          (p.support_weights_nonempty.image m) : ℝ) : EReal))) := by
  let : MeasurableSpace ι := ⊤
  split_ifs with h
  · exact Measure.tendsto_quantile_nhdsGT_zero_of_strictMono_cdf _
      (strictMono_cdf_gaussianMixtureMeasure h)
  · rw [gaussianMixtureMeasure_eq_map_categoricalMeasure (by simpa using h)]
    exact Measure.tendsto_quantile_nhdsGT_zero_of_ae_mem_finset _
      (p.ae_mem_image_support_map_categoricalMeasure m) (p.support_weights_nonempty.image m)
      (p.map_categoricalMeasure_singleton_ne_zero m (Finset.min'_mem _ _))

open Classical in
/-- At level one the quantile tends to plus infinity if some positive-weight variance
is nonzero, and to the greatest positive-weight mean otherwise. -/
theorem tendsto_quantile_gaussianMixtureMeasure_nhdsLT_one :
    Tendsto (fun u ↦ ((gaussianMixtureMeasure p m v).quantile u : EReal)) (𝓝[<] 1)
      (𝓝 (if ∃ i, 0 < p.weights i ∧ v i ≠ 0 then ⊤
        else (((p.weights.support.image m).max'
          (p.support_weights_nonempty.image m) : ℝ) : EReal))) := by
  let : MeasurableSpace ι := ⊤
  split_ifs with h
  · exact Measure.tendsto_quantile_nhdsLT_one_of_strictMono_cdf _
      (strictMono_cdf_gaussianMixtureMeasure h)
  · rw [gaussianMixtureMeasure_eq_map_categoricalMeasure (by simpa using h)]
    exact Measure.tendsto_quantile_nhdsLT_one_of_ae_mem_finset _
      (p.ae_mem_image_support_map_categoricalMeasure m) (p.support_weights_nonempty.image m)
      (p.map_categoricalMeasure_singleton_ne_zero m (Finset.max'_mem _ _))

end TauCeti.Probability
