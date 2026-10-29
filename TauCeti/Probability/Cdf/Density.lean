/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import TauCeti.Probability.Cdf
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import TauCeti.Probability.Density

/-!
# Cumulative distribution functions of laws with densities

This file connects a density presentation of a real probability law to its cumulative
distribution function. The cdf is an indefinite integral of the density, so it is absolutely
continuous on compact intervals, differentiable almost everywhere, and differentiable at every
continuity point of the density.

## Main results

* `TauCeti.Probability.cdf_sub_cdf_eq_integral_of_eq_withDensity` identifies cdf increments with
  density integrals;
* `TauCeti.Probability.strictMono_cdf_of_eq_withDensity` proves strict increase for an
  everywhere positive density;
* `TauCeti.Probability.absolutelyContinuousOnInterval_cdf_of_eq_withDensity` proves absolute
  continuity of the cdf;
* `TauCeti.Probability.ae_hasDerivAt_cdf_of_eq_withDensity` identifies its derivative almost
  everywhere;
* `TauCeti.Probability.hasDerivAt_cdf_of_eq_withDensity` identifies its derivative where the
  density is continuous.
-/

public section

open Filter MeasureTheory ProbabilityTheory Set

namespace TauCeti.Probability

variable {μ : Measure ℝ} {f : ℝ → ℝ} [IsProbabilityMeasure μ]

/-- **The cdf increment of a law with a density.** For a law with nonnegative density `f`, the
increment of the cdf over `a..b` is the integral of the density over `a..b`. -/
theorem cdf_sub_cdf_eq_integral_of_eq_withDensity
    (hμ : μ = volume.withDensity fun t => ENNReal.ofReal (f t)) (hfm : AEMeasurable f)
    (hnn : 0 ≤ᵐ[volume] f) (a b : ℝ) :
    cdf μ b - cdf μ a = ∫ t in a..b, f t := by
  wlog hab : a ≤ b generalizing a b
  · rw [intervalIntegral.integral_symm, ← this b a (le_of_not_ge hab), neg_sub]
  rw [← Measure.measureReal_Ioc_eq_cdf_sub μ hab, intervalIntegral.integral_of_le hab, hμ]
  exact measureReal_withDensity_ofReal (ae_restrict_of_ae hnn) measurableSet_Ioc
    (integrable_of_eq_withDensity hμ hfm hnn).integrableOn

/-- A real probability law with an everywhere positive density has a strictly increasing cdf. -/
theorem strictMono_cdf_of_eq_withDensity
    (hμ : μ = volume.withDensity fun t ↦ ENNReal.ofReal (f t)) (hfm : AEMeasurable f)
    (hpos : ∀ t, 0 < f t) : StrictMono (cdf μ) := by
  intro x y hxy
  have hnn := ae_of_all volume fun t ↦ (hpos t).le
  have hsupport : Function.support f = univ :=
    eq_univ_iff_forall.mpr fun t ↦ (hpos t).ne'
  rw [← sub_pos, cdf_sub_cdf_eq_integral_of_eq_withDensity hμ hfm hnn,
    intervalIntegral.integral_of_le hxy.le,
    setIntegral_pos_iff_support_of_nonneg_ae (ae_restrict_of_ae hnn)
      (integrable_of_eq_withDensity hμ hfm hnn).integrableOn,
    hsupport, univ_inter, Real.volume_Ioc, ENNReal.ofReal_pos]
  exact sub_pos.mpr hxy

private theorem cdf_eq_add_integral_of_eq_withDensity
    (hμ : μ = volume.withDensity fun t => ENNReal.ofReal (f t)) (hfm : AEMeasurable f)
    (hnn : 0 ≤ᵐ[volume] f) (c : ℝ) :
    ⇑(cdf μ) = fun s => cdf μ c + ∫ t in c..s, f t := by
  ext s
  rw [← cdf_sub_cdf_eq_integral_of_eq_withDensity hμ hfm hnn c s]
  ring

/-- The cdf of a law with a nonnegative density is absolutely continuous on every compact
interval. -/
theorem absolutelyContinuousOnInterval_cdf_of_eq_withDensity
    (hμ : μ = volume.withDensity fun t => ENNReal.ofReal (f t)) (hfm : AEMeasurable f)
    (hnn : 0 ≤ᵐ[volume] f) (a b : ℝ) :
    AbsolutelyContinuousOnInterval (cdf μ) a b := by
  have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => cdf μ a) a b :=
    (LipschitzWith.const (cdf μ a)).lipschitzOnWith.absolutelyContinuousOnInterval
  rw [cdf_eq_add_integral_of_eq_withDensity hμ hfm hnn a]
  exact hc.add ((integrable_of_eq_withDensity hμ hfm hnn).intervalIntegrable
    |>.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc)

/-- **Lebesgue differentiation of the cdf.** The cdf of a law with a nonnegative density `f` has
derivative `f t` at almost every point `t`. -/
theorem ae_hasDerivAt_cdf_of_eq_withDensity
    (hμ : μ = volume.withDensity fun t => ENNReal.ofReal (f t)) (hfm : AEMeasurable f)
    (hnn : 0 ≤ᵐ[volume] f) :
    ∀ᵐ t, HasDerivAt (cdf μ) (f t) t := by
  filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral
    (integrable_of_eq_withDensity hμ hfm hnn).locallyIntegrable] with t ht
  rw [cdf_eq_add_integral_of_eq_withDensity hμ hfm hnn 0]
  exact (ht 0).const_add _

/-- The cdf of a law with a nonnegative density `f` has derivative `f t` at every point `t` where
the density is continuous. -/
theorem hasDerivAt_cdf_of_eq_withDensity
    (hμ : μ = volume.withDensity fun t => ENNReal.ofReal (f t)) (hfm : AEMeasurable f)
    (hnn : 0 ≤ᵐ[volume] f) {t : ℝ} (hft : ContinuousAt f t) :
    HasDerivAt (cdf μ) (f t) t := by
  have hfi := integrable_of_eq_withDensity hμ hfm hnn
  rw [cdf_eq_add_integral_of_eq_withDensity hμ hfm hnn 0]
  exact (intervalIntegral.integral_hasDerivAt_right hfi.intervalIntegrable
    hfi.aestronglyMeasurable.stronglyMeasurableAtFilter hft).const_add _

end TauCeti.Probability
