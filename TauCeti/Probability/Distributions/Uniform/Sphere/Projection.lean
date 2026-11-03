/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Uniform.Sphere.Coordinate
public import TauCeti.Probability.Distributions.Uniform.Sphere.OneDimensional

/-!
# Cdfs and quantile endpoints of uniform sphere projections

A real linear observable of a uniform unit vector takes values between minus and plus the
norm of its representing vector. In dimension at least two its cdf is an affine symmetric
incomplete Beta function. In dimension one its law is a scaled Rademacher law, with a jump
of its lower quantile at probability one half. The one-sided quantile limits are the two
extreme values in every positive dimension, including the constant-zero observable.

The measure identifications are those of `map_inner_uniformSphereMeasure` and
`map_inner_uniformSphereMeasure_of_finrank_eq_one`; the scalar cdf and quantile calculations
reuse the Beta, Rademacher, and affine transport APIs.

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

/-- In dimension at least two, a nonzero real linear observable of a uniform sphere point
has the symmetric incomplete Beta cdf in the affine coordinate of its support interval. -/
theorem cdf_map_inner_uniformSphereMeasure (hd : 2 ≤ Module.finrank ℝ E) {v : E}
    (hv : v ≠ 0) (x : ℝ) :
    cdf ((uniformSphereMeasure E).map (fun u : sphere (0 : E) 1 ↦ ⟪v, (u : E)⟫)) x =
      regularizedIncompleteBeta (((Module.finrank ℝ E : ℝ) - 1) / 2)
        (((Module.finrank ℝ E : ℝ) - 1) / 2) ((x + ‖v‖) / (2 * ‖v‖)) := by
  have ha : 0 < ((Module.finrank ℝ E : ℝ) - 1) / 2 := by
    exact div_pos (sub_pos.mpr (by exact_mod_cast (by omega : 1 < Module.finrank ℝ E))) two_pos
  have := isProbabilityMeasureBeta ha ha
  have hfun : (fun y : ℝ ↦ ‖v‖ * (-1 + 2 * y)) =
      fun y ↦ -‖v‖ + (2 * ‖v‖) * y := by ext y; ring
  rw [map_inner_uniformSphereMeasure hd v, hfun,
    cdf_map_affine_of_pos (by positivity), cdf_betaMeasure_eq ha ha, sub_neg_eq_add]

/-- In dimension one, projection cdfs have two equally weighted atoms at the extreme
values. For the zero observable these coincide and give the Dirac cdf at zero. -/
theorem cdf_map_inner_uniformSphereMeasure_of_finrank_eq_one
    (hd : Module.finrank ℝ E = 1) (v : E) (x : ℝ) :
    cdf ((uniformSphereMeasure E).map (fun u : sphere (0 : E) 1 ↦ ⟪v, (u : E)⟫)) x =
      if x < -‖v‖ then 0 else if x < ‖v‖ then 1 / 2 else 1 := by
  rw [map_inner_uniformSphereMeasure_eq_map_rademacher_of_finrank_eq_one hd v]
  by_cases hv : v = 0
  · simp [hv, Measure.map_const, cdf_dirac]
    split_ifs <;> grind
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have h := cdf_map_affine_of_pos (μ := rademacherMeasure) (a := 0) hn x
  simpa only [zero_add, sub_zero, cdf_rademacherMeasure,
    div_lt_iff₀ hn, neg_one_mul, one_mul] using h

/-- In dimension one, projection quantiles equal the lower extreme through probability
one half and the upper extreme above it, including the constant-zero observable. -/
theorem quantile_map_inner_uniformSphereMeasure_of_finrank_eq_one
    (hd : Module.finrank ℝ E = 1) (v : E) {u : ℝ} (hu : u ∈ Ioo 0 1) :
    ((uniformSphereMeasure E).map (fun x : sphere (0 : E) 1 ↦ ⟪v, (x : E)⟫)).quantile u =
      if u ≤ 1 / 2 then -‖v‖ else ‖v‖ := by
  rw [map_inner_uniformSphereMeasure_eq_map_rademacher_of_finrank_eq_one hd v]
  by_cases hv : v = 0
  · simp [hv, Measure.map_const, Measure.quantile_dirac _ hu.1 hu.2.le]
  have h := quantile_map_affine_pos (μ := rademacherMeasure) (a := 0)
    (norm_pos_iff.mpr hv) hu.1 hu.2
  simpa only [zero_add, quantile_rademacherMeasure hu, mul_ite, mul_neg_one, mul_one] using h

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
