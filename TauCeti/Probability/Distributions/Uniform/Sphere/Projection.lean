/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Uniform.Sphere.Coordinate
public import TauCeti.Probability.Distributions.Uniform.Sphere.OneDimensional

/-!
# Quantile endpoints of uniform sphere projections

A real linear observable of a uniform unit vector takes values between minus and plus the
norm of its representing vector. In dimension at least two its quantiles are affine
inverse-Beta values. In dimension one its law is a scaled Rademacher law, with a jump
of its lower quantile at probability one half. The one-sided quantile limits are the two
extreme values in every positive dimension, including the constant-zero observable.

The measure identifications are those of `map_inner_uniformSphereMeasure` and
`map_inner_uniformSphereMeasure_of_finrank_eq_one`; the quantile formulas are provided by
`quantile_map_inner_uniformSphereMeasure` and
`quantile_map_inner_uniformSphereMeasure_of_finrank_eq_one`.

## References

* K.-T. Fang, S. Kotz, K. W. Ng, *Symmetric Multivariate and Related Distributions*,
  Chapman and Hall, 1990, Chapter 2.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter
open scoped Topology RealInnerProductSpace

namespace TauCeti.Probability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- In every positive dimension, projection quantiles tend to minus the norm of the
representing vector as the probability level tends to zero from above. -/
theorem tendsto_quantile_map_inner_uniformSphereMeasure_nhdsGT_zero
    (hd : 0 < Module.finrank ℝ E) (v : E) :
    Tendsto ((uniformSphereMeasure E).map (fun x : sphere (0 : E) 1 ↦ ⟪v, (x : E)⟫)).quantile
      (𝓝[>] 0) (𝓝 (-‖v‖)) := by
  by_cases hd1 : Module.finrank ℝ E = 1
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)] with u hu
    rw [quantile_map_inner_uniformSphereMeasure_of_finrank_eq_one hd1 v
      ⟨hu.1, hu.2.trans (by norm_num)⟩, ite_eq_left hu.2.le]
  have hd2 : 2 ≤ Module.finrank ℝ E := by omega
  have ha : 0 < ((Module.finrank ℝ E : ℝ) - 1) / 2 := by
    exact div_pos (sub_pos.mpr (by exact_mod_cast (by omega : 1 < Module.finrank ℝ E))) two_pos
  have h := ((tendsto_inverseRegularizedIncompleteBeta_zero ha ha).const_mul 2).const_add (-1)
    |>.const_mul ‖v‖
  simp only [mul_zero, add_zero, mul_neg_one] at h
  apply h.congr'
  filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with u hu
  exact (quantile_map_inner_uniformSphereMeasure hd2 v hu).symm

/-- In every positive dimension, projection quantiles tend to the norm of the representing
vector as the probability level tends to one from below. -/
theorem tendsto_quantile_map_inner_uniformSphereMeasure_nhdsLT_one
    (hd : 0 < Module.finrank ℝ E) (v : E) :
    Tendsto ((uniformSphereMeasure E).map (fun x : sphere (0 : E) 1 ↦ ⟪v, (x : E)⟫)).quantile
      (𝓝[<] 1) (𝓝 ‖v‖) := by
  by_cases hd1 : Module.finrank ℝ E = 1
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsLT (by norm_num : (1 / 2 : ℝ) < 1)] with u hu
    rw [quantile_map_inner_uniformSphereMeasure_of_finrank_eq_one hd1 v
      ⟨(by norm_num : (0 : ℝ) < 1 / 2).trans hu.1, hu.2⟩, ite_eq_right (not_le.mpr hu.1)]
  have hd2 : 2 ≤ Module.finrank ℝ E := by omega
  have ha : 0 < ((Module.finrank ℝ E : ℝ) - 1) / 2 := by
    exact div_pos (sub_pos.mpr (by exact_mod_cast (by omega : 1 < Module.finrank ℝ E))) two_pos
  have h := ((tendsto_inverseRegularizedIncompleteBeta_one ha ha).const_mul 2).const_add (-1)
    |>.const_mul ‖v‖
  norm_num only [mul_one, neg_add_cancel_left] at h
  apply h.congr'
  filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with u hu
  exact (quantile_map_inner_uniformSphereMeasure hd2 v hu).symm

end TauCeti.Probability
