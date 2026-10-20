/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Exponential.Basic
public import TauCeti.Probability.Quantile
import TauCeti.MeasureTheory.Measure.Measurability

/-!
# The Gumbel distribution

The Gumbel law in the maximum convention, with location `m` and scale `s > 0`, is the law of
`m - s * log E` for a rate-one exponential variable `E`. Its cumulative distribution function is

`F(x) = exp (-exp (-(x - m) / s))`,

and its quantile at `0 < u < 1` is `m - s * log (-log u)`.

For a nonpositive scale there is no Gumbel law: `gumbelMeasure m s` is the zero measure. The
construction in this file is the starting point for its density, moments and transforms, and for
the representation of a logistic variable as a difference of independent Gumbel variables.

## Main results

* `TauCeti.Probability.gumbelMeasure` defines the law as an exponential pushforward;
* `TauCeti.Probability.isProbabilityMeasure_gumbelMeasure` proves normalization for positive scale;
* `TauCeti.Probability.hasLaw_gumbelMeasure_of_hasLaw_expMeasure` gives the random-variable
  construction;
* `TauCeti.Probability.map_affine_gumbelMeasure` gives positive affine transport, with the
  random-variable form `TauCeti.Probability.hasLaw_affine_gumbelMeasure`;
* `TauCeti.Probability.measurable_gumbelMeasure` proves measurability in the parameters;
* `TauCeti.Probability.cdf_gumbelMeasure_eq` computes the cdf;
* `TauCeti.Probability.support_gumbelMeasure` identifies its topological support;
* `TauCeti.Probability.quantile_gumbelMeasure` computes the quantile, and the two following
  theorems give its one-sided endpoint limits.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2, 2nd ed.,
  Wiley (1995), ch. 22.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set Topology

open scoped ENNReal Topology

namespace TauCeti

namespace Probability

variable {m s x : ℝ}

/-- The Gumbel probability measure in the maximum convention, with location `m` and scale `s`.

For `s > 0`, this is the image of a rate-one exponential law under `e ↦ m - s * log e`. For
`s ≤ 0`, it is the zero measure. -/
def gumbelMeasure (m s : ℝ) : Measure ℝ :=
  if 0 < s then (expMeasure 1).map fun e => m - s * Real.log e else 0

/-- For positive scale, the Gumbel law is the prescribed exponential pushforward. -/
theorem gumbelMeasure_of_pos (hs : 0 < s) (m : ℝ) :
    gumbelMeasure m s = (expMeasure 1).map fun e => m - s * Real.log e := by
  rw [gumbelMeasure, ite_eq_left hs]

/-- For nonpositive scale, the totalized Gumbel law is the zero measure. -/
@[simp]
theorem gumbelMeasure_of_nonpos (hs : s ≤ 0) (m : ℝ) : gumbelMeasure m s = 0 := by
  rw [gumbelMeasure, ite_eq_right (not_lt.mpr hs)]

/-- A Gumbel law with positive scale is a probability measure. -/
theorem isProbabilityMeasure_gumbelMeasure (hs : 0 < s) (m : ℝ) :
    IsProbabilityMeasure (gumbelMeasure m s) := by
  rw [gumbelMeasure_of_pos hs]
  let _ : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure one_pos
  infer_instance

/-- If `E` has the rate-one exponential law, then `m - s * log E` has the Gumbel law with
location `m` and positive scale `s`. -/
theorem hasLaw_gumbelMeasure_of_hasLaw_expMeasure {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {E : Ω → ℝ} (hs : 0 < s) (m : ℝ) (hE : HasLaw E (expMeasure 1) P) :
    HasLaw (fun ω => m - s * Real.log (E ω)) (gumbelMeasure m s) P := by
  rw [gumbelMeasure_of_pos hs]
  exact (hasLaw_map
    (measurable_const.sub (measurable_const.mul Real.measurable_log)).aemeasurable).comp hE

/-- A positive affine change of a Gumbel variable changes its location to `a + b * m` and its
scale to `b * s`. The identity also respects the nonpositive-scale zero-measure branch. -/
theorem map_affine_gumbelMeasure {b : ℝ} (hb : 0 < b) (a m s : ℝ) :
    (gumbelMeasure m s).map (fun x => a + b * x) =
      gumbelMeasure (a + b * m) (b * s) := by
  by_cases hs : 0 < s
  · rw [gumbelMeasure_of_pos hs, gumbelMeasure_of_pos (mul_pos hb hs),
      Measure.map_map (by fun_prop) (by fun_prop)]
    congr 1
    funext e
    simp only [Function.comp_apply]
    ring
  · rw [gumbelMeasure_of_nonpos (le_of_not_gt hs),
      gumbelMeasure_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hb.le (le_of_not_gt hs)),
      Measure.map_zero]

/-- The random-variable form of positive affine transport of the Gumbel law. -/
theorem hasLaw_affine_gumbelMeasure {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℝ} {b : ℝ} (hb : 0 < b) (a : ℝ)
    (hX : HasLaw X (gumbelMeasure m s) P) :
    HasLaw (fun ω => a + b * X ω) (gumbelMeasure (a + b * m) (b * s)) P := by
  rw [← map_affine_gumbelMeasure hb]
  exact (hasLaw_map
    (measurable_const.add (measurable_const.mul measurable_id)).aemeasurable).comp hX

/-- The Gumbel family is measurable in its location and scale parameters, including the
nonpositive-scale zero-measure branch. -/
@[fun_prop]
theorem measurable_gumbelMeasure : Measurable fun p : ℝ × ℝ => gumbelMeasure p.1 p.2 := by
  let _ : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure one_pos
  apply Measurable.ite (measurableSet_lt measurable_const measurable_snd)
  · exact TauCeti.MeasureTheory.measurable_map_of_measurable_uncurry
      (ν := expMeasure 1) (f := fun p : ℝ × ℝ => fun e => p.1 - p.2 * Real.log e) (by fun_prop)
  · exact measurable_const

/-- The mass of a Gumbel law below `x` is `exp (-exp (-(x - m) / s))`. -/
theorem gumbelMeasure_Iic (hs : 0 < s) (m x : ℝ) :
    gumbelMeasure m s (Iic x) = ENNReal.ofReal (Real.exp (-Real.exp (-((x - m) / s)))) := by
  have hpre :
      (fun e : ℝ => m - s * Real.log e) ⁻¹' Iic x =ᵐ[expMeasure 1]
        Ici (Real.exp (-((x - m) / s))) := by
    filter_upwards [ae_pos_expMeasure 1] with e he
    simp only [mem_preimage, mem_Iic, mem_Ici]
    rw [← Real.le_log_iff_exp_le he]
    have hrewrite : -((x - m) / s) = (m - x) / s := by ring
    rw [hrewrite, div_le_iff₀ hs]
    apply propext
    constructor <;> intro h <;> linarith
  have hsingleton : expMeasure 1 {Real.exp (-((x - m) / s))} = 0 := by
    rw [expMeasure_eq_withDensity]
    exact withDensity_absolutelyContinuous volume _ (measure_singleton _)
  have hmeas : Measurable (fun e : ℝ => m - s * Real.log e) :=
    measurable_const.sub (measurable_const.mul Real.measurable_log)
  rw [gumbelMeasure_of_pos hs, Measure.map_apply hmeas measurableSet_Iic,
    measure_congr hpre, ← measure_congr (Ioi_ae_eq_Ici' hsingleton),
    measure_Ioi_expMeasure one_pos, ite_eq_left (Real.exp_pos _).le, one_mul]

/-- The cdf of the Gumbel law is `exp (-exp (-(x - m) / s))`. -/
theorem cdf_gumbelMeasure_eq (hs : 0 < s) (m x : ℝ) :
    cdf (gumbelMeasure m s) x = Real.exp (-Real.exp (-((x - m) / s))) := by
  have := isProbabilityMeasure_gumbelMeasure hs m
  rw [cdf_eq_real, measureReal_def, gumbelMeasure_Iic hs,
    ENNReal.toReal_ofReal (Real.exp_nonneg _)]

/-- The cdf of a positive-scale Gumbel law is strictly increasing. -/
theorem strictMono_cdf_gumbelMeasure (hs : 0 < s) (m : ℝ) :
    StrictMono (cdf (gumbelMeasure m s)) := by
  intro x y hxy
  rw [cdf_gumbelMeasure_eq hs, cdf_gumbelMeasure_eq hs]
  apply Real.exp_lt_exp.mpr
  apply neg_lt_neg
  apply Real.exp_lt_exp.mpr
  exact neg_lt_neg (div_lt_div_of_pos_right (sub_lt_sub_right hxy m) hs)

/-- A positive-scale Gumbel law has full topological support. -/
@[simp]
theorem support_gumbelMeasure (hs : 0 < s) (m : ℝ) :
    (gumbelMeasure m s).support = Set.univ := by
  let _ := isProbabilityMeasure_gumbelMeasure hs m
  exact Measure.support_eq_univ_of_strictMono_cdf _ (strictMono_cdf_gumbelMeasure hs m)

/-- A nonpositive-scale Gumbel measure has empty topological support. -/
theorem support_gumbelMeasure_of_nonpos (hs : s ≤ 0) (m : ℝ) :
    (gumbelMeasure m s).support = ∅ := by
  rw [gumbelMeasure_of_nonpos hs, Measure.support_zero]

/-- The quantile of a positive-scale Gumbel law is `m - s * log (-log u)` for every interior
level `u`. -/
theorem quantile_gumbelMeasure (hs : 0 < s) (m : ℝ) {u : ℝ} (hu : u ∈ Ioo 0 1) :
    (gumbelMeasure m s).quantile u = m - s * Real.log (-Real.log u) := by
  have hlog : 0 < -Real.log u := neg_pos.mpr (Real.log_neg hu.1 hu.2)
  have hstandard : -((m - s * Real.log (-Real.log u) - m) / s) = Real.log (-Real.log u) := by
    field_simp [hs.ne']
    ring
  have hcdf : cdf (gumbelMeasure m s) (m - s * Real.log (-Real.log u)) = u := by
    rw [cdf_gumbelMeasure_eq hs, hstandard, Real.exp_log hlog, neg_neg, Real.exp_log hu.1]
  have hq := Measure.quantile_cdf (gumbelMeasure m s)
    ((strictMono_cdf_gumbelMeasure hs m).strictMonoOn _) (x := m - s * Real.log (-Real.log u))
    (by rw [hcdf]; exact hu)
  rwa [hcdf] at hq

/-- The Gumbel quantile tends to the lower endpoint `-∞` as the level tends to zero from
above. -/
theorem tendsto_quantile_gumbelMeasure_nhdsGT_zero (hs : 0 < s) (m : ℝ) :
    Tendsto (fun u => ((gumbelMeasure m s).quantile u : EReal)) (𝓝[>] 0) (𝓝 ⊥) := by
  apply EReal.tendsto_coe_nhds_bot_iff.2
  refine tendsto_atBot.2 fun b => ?_
  have hb : 0 < cdf (gumbelMeasure m s) b := by
    rw [cdf_gumbelMeasure_eq hs]
    exact Real.exp_pos _
  filter_upwards [Ioo_mem_nhdsGT hb] with u hu
  exact (Measure.quantile_le_iff _ hu.1
    (hu.2.trans_le (cdf_le_one (gumbelMeasure m s) b))).2 hu.2.le

/-- The Gumbel quantile tends to the upper endpoint `+∞` as the level tends to one from
below. -/
theorem tendsto_quantile_gumbelMeasure_nhdsLT_one (hs : 0 < s) (m : ℝ) :
    Tendsto (fun u => ((gumbelMeasure m s).quantile u : EReal)) (𝓝[<] 1) (𝓝 ⊤) := by
  apply EReal.tendsto_coe_nhds_top_iff.2
  refine tendsto_atTop.2 fun b => ?_
  have hb : cdf (gumbelMeasure m s) b < 1 := by
    rw [cdf_gumbelMeasure_eq hs, Real.exp_lt_one_iff]
    exact neg_neg_of_pos (Real.exp_pos _)
  filter_upwards [Ioo_mem_nhdsLT hb] with u hu
  exact ((Measure.lt_quantile_iff _
    ((cdf_nonneg (gumbelMeasure m s) b).trans_lt hu.1) hu.2).2 hu.1).le

end Probability

end TauCeti
