/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Gamma.Basic
public import TauCeti.Probability.StochasticOrder

/-!
# Stochastic comparison of Gamma laws

Increasing the positive shape or decreasing the positive rate makes a Gamma variable
stochastically larger. The shape comparison comes from adding an independent positive Gamma
increment; the rate comparison comes from multiplying a positive Gamma variable by a constant
at least one. Equal shapes are handled without introducing a Gamma law of shape zero.

The cdf inequalities yield ordered interior quantiles and an almost surely ordered
common-uniform quantile coupling. Its marginals are the two Gamma laws by
`MeasureTheory.Measure.isCoupling_quantileCoupling`.

## Main results

* `cdf_gammaMeasure_le_of_shape_le`: cdfs decrease as the shape increases.
* `cdf_gammaMeasure_le_of_rate_le`: cdfs increase as the rate increases.
* `cdf_gammaMeasure_le`: simultaneous comparison of shape and rate.
* `quantile_gammaMeasure_le`: the corresponding interior quantile inequality.
* `ae_fst_le_snd_quantileCoupling_gammaMeasure`: the common-uniform ordered coupling.

The constructions use `gammaMeasure_conv_gammaMeasure` and `gammaMeasure_map_const_mul`.

## References

* M. Shaked and J. G. Shanthikumar, *Stochastic Orders*, Springer, 2007, Chapter 1.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped MeasureTheory

namespace TauCeti.Probability

variable {a b r s u : ℝ}

/-- Increasing the positive shape at a fixed positive rate decreases the Gamma cdf. -/
theorem cdf_gammaMeasure_le_of_shape_le (ha : 0 < a) (hr : 0 < r) (hab : a ≤ b)
    (x : ℝ) : cdf (gammaMeasure b r) x ≤ cdf (gammaMeasure a r) x := by
  rcases hab.eq_or_lt with rfl | hab
  · exact le_rfl
  have hdiff : 0 < b - a := sub_pos.mpr hab
  let _ := isProbabilityMeasure_gammaMeasure ha hr
  let _ := isProbabilityMeasure_gammaMeasure hdiff hr
  have hfst : HasLaw Prod.fst (gammaMeasure a r)
      ((gammaMeasure a r).prod (gammaMeasure (b - a) r)) := measurePreserving_fst.hasLaw
  have hsum : HasLaw (fun z : ℝ × ℝ ↦ z.1 + z.2) (gammaMeasure b r)
      ((gammaMeasure a r).prod (gammaMeasure (b - a) r)) := by
    refine ⟨by fun_prop, ?_⟩
    rw [← Measure.conv, gammaMeasure_conv_gammaMeasure ha hdiff hr, add_sub_cancel]
  refine hfst.cdf_le_of_ae_le hsum ?_ x
  filter_upwards [ae_mem_prod_Ioi_gammaMeasure ha hdiff hr hr] with z hz
  exact le_add_of_nonneg_right hz.2.le

/-- Increasing the positive rate at a fixed positive shape increases the Gamma cdf. -/
theorem cdf_gammaMeasure_le_of_rate_le (ha : 0 < a) (hs : 0 < s) (hsr : s ≤ r)
    (x : ℝ) : cdf (gammaMeasure a s) x ≤ cdf (gammaMeasure a r) x := by
  have hr : 0 < r := hs.trans_le hsr
  let _ := isProbabilityMeasure_gammaMeasure ha hr
  have hscale : (gammaMeasure a r).map (r / s * ·) = gammaMeasure a s := by
    rw [gammaMeasure_map_const_mul ha hr (div_pos hr hs)]
    congr 1
    field_simp
  have hscaled : HasLaw (fun y : ℝ ↦ r / s * y) (gammaMeasure a s)
      (gammaMeasure a r) := ⟨by fun_prop, hscale⟩
  refine (HasLaw.id (μ := gammaMeasure a r)).cdf_le_of_ae_le hscaled ?_ x
  filter_upwards [ae_pos_gammaMeasure a r] with y hy
  exact le_mul_of_one_le_left hy.le ((le_div_iff₀ hs).2 (by simpa using hsr))

/-- A larger shape and smaller rate give a stochastically larger Gamma law, expressed as a
reversed cdf inequality. Only the smaller shape and smaller rate need positivity hypotheses. -/
theorem cdf_gammaMeasure_le (ha : 0 < a) (hs : 0 < s) (hab : a ≤ b) (hsr : s ≤ r)
    (x : ℝ) : cdf (gammaMeasure b s) x ≤ cdf (gammaMeasure a r) x :=
  (cdf_gammaMeasure_le_of_shape_le ha hs hab x).trans
    (cdf_gammaMeasure_le_of_rate_le ha hs hsr x)

/-- Gamma interior quantiles increase with shape and decrease with rate. -/
theorem quantile_gammaMeasure_le (ha : 0 < a) (hs : 0 < s) (hab : a ≤ b) (hsr : s ≤ r)
    (hu : u ∈ Set.Ioo 0 1) :
    (gammaMeasure a r).quantile u ≤ (gammaMeasure b s).quantile u :=
  (Measure.cdf_le_iff_quantile_le _ _).1 (cdf_gammaMeasure_le ha hs hab hsr) u hu.1 hu.2

/-- The common-uniform quantile coupling orders Gamma variables when their shapes increase
and their rates decrease. Its two marginals are the indicated Gamma laws. -/
theorem ae_fst_le_snd_quantileCoupling_gammaMeasure (ha : 0 < a) (hs : 0 < s)
    (hab : a ≤ b) (hsr : s ≤ r) :
    ∀ᵐ z ∂(gammaMeasure a r).quantileCoupling (gammaMeasure b s), z.1 ≤ z.2 :=
  Measure.ae_fst_le_snd_quantileCoupling _ _ (cdf_gammaMeasure_le ha hs hab hsr)

end TauCeti.Probability
