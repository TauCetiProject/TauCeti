/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Levy.Cdf
public import TauCeti.Probability.Distributions.Gaussian.Quantile
public import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# Quantiles of Lévy laws

For location `m` and positive scale `c`, the Lévy quantile at a level `0 < u < 1` is

`m + c / (2 * erfInv (1 - u) ^ 2)`,

which inverts the cdf `erfc (√(c / (2 (x - m))))`. Since the standard Gaussian quantile is
`z(p) = √2 * erfInv (2 * p - 1)`, the same value is `m + c / z(1 - u / 2) ^ 2`.

The quantile tends to the location `m` as the level tends to `0` and to `+∞` as the level tends
to `1`; these one-sided limits are stated in `EReal`.

## Main declarations

* `TauCeti.Probability.quantile_levyMeasure` — the quantile through the inverse error function;
* `TauCeti.Probability.quantile_levyMeasure_eq_quantile_gaussianReal` — the same quantile through
  the standard Gaussian quantile;
* `TauCeti.Probability.tendsto_quantile_levyMeasure_nhdsGT_zero` and
  `TauCeti.Probability.tendsto_quantile_levyMeasure_nhdsLT_one` — the one-sided endpoint limits.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set Topology

namespace TauCeti.Probability

variable {c u : ℝ}

/-- The quantile of a Lévy law with location `m` and positive scale `c` at an interior level `u`
is `m + c / (2 * erfInv (1 - u) ^ 2)`. -/
theorem quantile_levyMeasure (hc : 0 < c) (m : ℝ) (hu : u ∈ Ioo 0 1) :
    (levyMeasure m c).quantile u = m + c / (2 * Real.erfInv (1 - u) ^ 2) := by
  let _ := isProbabilityMeasure_levyMeasure hc m
  have hy : 1 - u ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hu.2], by linarith [hu.1]⟩
  have he : 0 < Real.erfInv (1 - u) :=
    Real.erfInv_pos_iff.2 ⟨by linarith [hu.2], by linarith [hu.1]⟩
  have hq : 0 < c / (2 * Real.erfInv (1 - u) ^ 2) := by positivity
  refine eq_of_forall_lt_iff fun x ↦ ?_
  rw [Measure.lt_quantile_iff _ hu.1 hu.2, cdf_levyMeasure_eq hc]
  by_cases hx : x ≤ m
  · rw [ite_eq_left hx]
    exact iff_of_true hu.1 (by linarith)
  · rw [ite_eq_right hx]
    have hxm : 0 < x - m := by linarith
    calc
      Real.erfc √(c / (2 * (x - m))) < u ↔ 1 - u < Real.erf √(c / (2 * (x - m))) := by
        rw [Real.erfc_def]
        constructor <;> intro h <;> linarith
      _ ↔ Real.erfInv (1 - u) < √(c / (2 * (x - m))) := (Real.erfInv_lt_iff hy).symm
      _ ↔ Real.erfInv (1 - u) ^ 2 < c / (2 * (x - m)) := Real.lt_sqrt he.le
      _ ↔ x < m + c / (2 * Real.erfInv (1 - u) ^ 2) := by
        rw [lt_div_iff₀ (by positivity), ← sub_lt_iff_lt_add', lt_div_iff₀ (by positivity)]
        constructor <;> intro h <;> linarith

/-- The Lévy quantile in terms of the standard Gaussian quantile `z`: at an interior level `u` it
is `m + c / z(1 - u / 2) ^ 2`. -/
theorem quantile_levyMeasure_eq_quantile_gaussianReal (hc : 0 < c) (m : ℝ) (hu : u ∈ Ioo 0 1) :
    (levyMeasure m c).quantile u = m + c / (gaussianReal 0 1).quantile (1 - u / 2) ^ 2 := by
  have hp : 1 - u / 2 ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hu.2], by linarith [hu.1]⟩
  rw [quantile_levyMeasure hc m hu, quantile_gaussianReal_zero_one hp, mul_pow,
    Real.sq_sqrt zero_le_two]
  ring_nf

/-- The Lévy quantile tends to the location `m` as the level tends to `0` from above. -/
theorem tendsto_quantile_levyMeasure_nhdsGT_zero (hc : 0 < c) (m : ℝ) :
    Tendsto (fun u ↦ ((levyMeasure m c).quantile u : EReal)) (𝓝[>] 0) (𝓝 (m : EReal)) := by
  have hcomp : Tendsto (fun u : ℝ ↦ 1 - u) (𝓝[>] 0) (𝓝[<] 1) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · simpa using ((continuous_id.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds).const_sub 1
    · filter_upwards [self_mem_nhdsWithin] with u hu
      exact sub_lt_self _ hu
  have hden : Tendsto (fun u ↦ 2 * Real.erfInv (1 - u) ^ 2) (𝓝[>] 0) atTop :=
    ((tendsto_pow_atTop two_ne_zero).comp
      (Real.tendsto_erfInv_nhdsLT_one.comp hcomp)).const_mul_atTop two_pos
  have hlim : Tendsto (fun u ↦ m + c / (2 * Real.erfInv (1 - u) ^ 2)) (𝓝[>] 0) (𝓝 m) := by
    simpa using tendsto_const_nhds.add (tendsto_const_nhds.div_atTop hden)
  apply (EReal.tendsto_coe.mpr hlim).congr'
  filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with u hu
  exact congrArg (fun x : ℝ ↦ (x : EReal)) (quantile_levyMeasure hc m hu).symm

/-- The Lévy quantile tends to `+∞` as the level tends to `1` from below. -/
theorem tendsto_quantile_levyMeasure_nhdsLT_one (hc : 0 < c) (m : ℝ) :
    Tendsto (fun u ↦ ((levyMeasure m c).quantile u : EReal)) (𝓝[<] 1) (𝓝 ⊤) := by
  have h0 : (0 : ℝ) ∈ Ioo (-1) 1 := ⟨by norm_num, by norm_num⟩
  have hcont : ContinuousAt (fun u : ℝ ↦ 2 * Real.erfInv (1 - u) ^ 2) 1 := by
    have herf : ContinuousAt (fun u : ℝ ↦ Real.erfInv (1 - u)) 1 :=
      (Real.continuousAt_erfInv h0).comp_of_eq (by fun_prop) (sub_self 1)
    exact continuousAt_const.mul (herf.pow 2)
  have hden : Tendsto (fun u ↦ 2 * Real.erfInv (1 - u) ^ 2) (𝓝[<] 1) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · simpa [Real.erfInv_zero] using hcont.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with u hu
      have he : 0 < Real.erfInv (1 - u) :=
        Real.erfInv_pos_iff.2 ⟨by linarith [hu.2], by linarith [hu.1]⟩
      exact mem_Ioi.mpr (by positivity)
  have hlim : Tendsto (fun u ↦ m + c / (2 * Real.erfInv (1 - u) ^ 2)) (𝓝[<] 1) atTop := by
    refine tendsto_atTop_add_const_left _ m ?_
    simpa only [div_eq_mul_inv, Function.comp_def] using
      (tendsto_inv_nhdsGT_zero.comp hden).const_mul_atTop hc
  apply EReal.tendsto_coe_nhds_top_iff.mpr
  apply hlim.congr'
  filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with u hu
  exact (quantile_levyMeasure hc m hu).symm

end TauCeti.Probability
