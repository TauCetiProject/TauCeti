/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Stieltjes
public import Mathlib.Probability.CDF
public import Mathlib.Topology.Order.LeftRightLim
public import TauCeti.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import TauCeti.Probability.Density
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

/-!
# Cumulative distribution functions

This file records basic properties of cumulative distribution functions. In particular, the cdf
of an atomless real probability measure is continuous, and the cdf of a law presented by a density
is an indefinite integral of that density.

A probability measure `μ` on `ℕ` becomes a real law by pushing it forward along the cast
`ℕ → ℝ`. The resulting cumulative distribution function is determined by the cumulative masses of
`μ` itself: it vanishes below the origin, where the pushforward has no mass at all, and at a
nonnegative point `x` it is the mass `μ` gives to the initial segment below the natural floor of
`x`. Every discrete law on `ℕ` therefore reads its real cdf off its own cumulative masses.

## Main results

* `MeasureTheory.Measure.continuous_cdf_of_noAtoms` proves continuity for atomless real laws;
* `MeasureTheory.Measure.cdf_eq_zero_of_measure_Iio_eq_zero` shows that an atomless law with no
  mass below a point has cdf zero there;
* `TauCeti.Probability.cdf_sub_cdf_eq_integral_of_eq_withDensity` identifies cdf increments with
  density integrals;
* `TauCeti.Probability.absolutelyContinuousOnInterval_cdf_of_eq_withDensity` and
  `TauCeti.Probability.ae_hasDerivAt_cdf_of_eq_withDensity` give absolute continuity and almost
  everywhere differentiability of the cdf of a law with a density;
* `MeasureTheory.Measure.cdf_sublevel_measure` evaluates the measure of a CDF sublevel set for
  an atomless real law;
* `MeasureTheory.Measure.cdf_map_natCast` evaluates the cdf at a nonnegative point;
* `MeasureTheory.Measure.cdf_map_natCast_of_neg` evaluates it below the origin.

## Adapted from

`continuous_cdf_of_noAtoms` and `cdf_sublevel_measure` are adapted from Cameron Freer's
independent implementation in `Graphon/MeasureIso.lean` at commit
`9f7be59fa754d260a544b4cfd83d6a5b94f7552e`:
<https://github.com/cameronfreer/graphon/commit/9f7be59fa754d260a544b4cfd83d6a5b94f7552e>,
under the same names; the graphon-specific packaging was removed. The original work is
copyright Cameron Freer and licensed under Apache 2.0.

These two results are the input to the probability integral transform
`MeasureTheory.Measure.cdf_map_eq_volume_restrict` in `TauCeti.Probability.Quantile`, which is
adapted from the same source, and they realize the measure-preserving equivalence of an
atomless standard-Borel space with the unit interval proved as Theorem A.7 in S. Janson,
*Graphons, cut norm and distance, couplings and rearrangements*, Arkiv för Matematik 52 (2014).
-/

public section

open Filter Function MeasureTheory ProbabilityTheory Set Topology

namespace MeasureTheory.Measure

variable (μ : Measure ℕ) [IsProbabilityMeasure μ]

/-- At a nonnegative point, the cdf of a natural-valued law cast to the reals is the cumulative
mass of the initial segment below the natural floor of that point. -/
theorem cdf_map_natCast {x : ℝ} (hx : 0 ≤ x) :
    cdf (μ.map (Nat.cast : ℕ → ℝ)) x = μ.real (Iic ⌊x⌋₊) := by
  have hpre : (Nat.cast : ℕ → ℝ) ⁻¹' Iic x = Iic ⌊x⌋₊ := by
    ext k
    simp only [mem_preimage, mem_Iic]
    exact (Nat.le_floor_iff hx).symm
  rw [cdf_eq_real, map_measureReal_apply (by fun_prop) measurableSet_Iic, hpre]

/-- Below the origin, the cdf of a natural-valued law cast to the reals vanishes: the law is
carried by the natural numbers. -/
theorem cdf_map_natCast_of_neg {x : ℝ} (hx : x < 0) :
    cdf (μ.map (Nat.cast : ℕ → ℝ)) x = 0 := by
  have hpre : (Nat.cast : ℕ → ℝ) ⁻¹' Iic x = ∅ := by
    ext k
    simp only [mem_preimage, mem_Iic, mem_empty_iff_false, iff_false, not_le]
    exact lt_of_lt_of_le hx (Nat.cast_nonneg k)
  rw [cdf_eq_real, map_measureReal_apply (by fun_prop) measurableSet_Iic, hpre,
    measureReal_empty]

/-- **CDF continuity from null singletons.** The cumulative distribution function of a
probability measure on `ℝ` is continuous when every singleton has measure zero. -/
theorem continuous_cdf_of_noAtoms (ν : Measure ℝ) [IsProbabilityMeasure ν]
    [NullSingletonClass ν] : Continuous (cdf ν) := by
  have hleft : ∀ x, leftLim (cdf ν) x = cdf ν x := by
    intro x
    have hsing : (cdf ν).measure {x} = 0 := by rw [measure_cdf]; exact measure_singleton x
    rw [StieltjesFunction.measure_singleton] at hsing
    have hle : leftLim (cdf ν) x ≤ cdf ν x := (cdf ν).mono.leftLim_le le_rfl
    have hz : cdf ν x - leftLim (cdf ν) x ≤ 0 := ENNReal.ofReal_eq_zero.mp hsing
    exact le_antisymm hle (by linarith)
  rw [continuous_iff_continuousAt]
  intro x
  rw [(cdf ν).mono.continuousAt_iff_leftLim_eq_rightLim, hleft x,
    ((cdf ν).right_continuous x).rightLim_eq]

/-- The mass of a bounded interval `Ioc a b` is the increment of the cumulative distribution
function between its endpoints. -/
theorem measureReal_Ioc_eq_cdf_sub (ν : Measure ℝ) [IsProbabilityMeasure ν] {a b : ℝ}
    (hab : a ≤ b) : ν.real (Ioc a b) = cdf ν b - cdf ν a := by
  rw [← Iic_sdiff_Iic, measureReal_sdiff (Iic_subset_Iic.2 hab) measurableSet_Iic, cdf_eq_real,
    cdf_eq_real]

/-- An atomless law that gives no mass to the open half-line below `c` has cdf zero at `c`. -/
theorem cdf_eq_zero_of_measure_Iio_eq_zero (ν : Measure ℝ) [IsProbabilityMeasure ν]
    [NullSingletonClass ν] {c : ℝ} (hc : ν (Iio c) = 0) : cdf ν c = 0 := by
  have h : ν (Iic c) = 0 := (measure_congr Iio_ae_eq_Iic).symm.trans hc
  rw [cdf_eq_real, measureReal_def, h, ENNReal.toReal_zero]

/-- The measure of the sublevel set `{x | cdf ν x ≤ y}` is `ENNReal.ofReal y` when
`y < 1`. -/
theorem cdf_sublevel_measure (ν : Measure ℝ) [IsProbabilityMeasure ν] [NullSingletonClass ν]
    (y : ℝ) (hy1 : y < 1) :
    ν {x | cdf ν x ≤ y} = ENNReal.ofReal y := by
  set S : Set ℝ := {x | cdf ν x ≤ y}
  have hScl : IsClosed S := isClosed_Iic.preimage (continuous_cdf_of_noAtoms ν)
  have hevt : ∀ᶠ x in atTop, y < cdf ν x :=
    (tendsto_cdf_atTop ν).eventually (eventually_gt_nhds hy1)
  obtain ⟨M, hM⟩ := eventually_atTop.mp hevt
  have hSbdd : BddAbove S := by
    refine ⟨M, fun x hx => ?_⟩
    by_contra hxM
    exact absurd (hM x (le_of_lt (not_le.mp hxM))) (not_lt.2 hx)
  by_cases hSne : S.Nonempty
  · set q := sSup S
    have hq_mem : q ∈ S := hScl.csSup_mem hSne hSbdd
    have hSeq : S = Iic q := by
      ext x
      constructor
      · intro hx; exact le_csSup hSbdd hx
      · intro hx
        exact le_trans ((cdf ν).mono hx) hq_mem
    have hcdfq : cdf ν q = y := by
      refine le_antisymm hq_mem ?_
      have htend : Tendsto (cdf ν) (𝓝[>] q) (𝓝 (cdf ν q)) :=
        ((continuous_cdf_of_noAtoms ν).tendsto q).mono_left nhdsWithin_le_nhds
      have hevt2 : ∀ᶠ x in 𝓝[>] q, y ≤ cdf ν x := by
        refine Filter.eventually_of_mem self_mem_nhdsWithin (fun x hx => ?_)
        have : x ∉ S := fun hxS => absurd (le_csSup hSbdd hxS) (not_le.2 hx)
        exact le_of_lt (not_le.mp this)
      exact ge_of_tendsto htend hevt2
    rw [hSeq, ← ofReal_cdf ν q, hcdfq]
  · rw [not_nonempty_iff_eq_empty] at hSne
    have hyle : y ≤ 0 := by
      have hfor : ∀ᶠ x in atBot, y ≤ cdf ν x := by
        refine Filter.Eventually.of_forall (fun x => ?_)
        have : x ∉ S := by rw [hSne]; simp
        exact le_of_lt (not_le.mp this)
      exact ge_of_tendsto (tendsto_cdf_atBot ν) hfor
    have hνS : ν S = 0 := by rw [hSne]; exact measure_empty
    rw [ENNReal.ofReal_eq_zero.mpr hyle]
    exact hνS

end MeasureTheory.Measure

namespace TauCeti.Probability

variable {μ : Measure ℝ} {f : ℝ → ℝ}

section Density

variable [IsProbabilityMeasure μ]

/-! ### Cdfs of laws with a density -/

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

end Density

end TauCeti.Probability
