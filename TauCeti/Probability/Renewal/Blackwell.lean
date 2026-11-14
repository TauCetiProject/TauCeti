/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Renewal.Compactness
public import TauCeti.Probability.Renewal.Translate.Limit
public import TauCeti.Probability.Renewal.HarmonicMeasure
public import TauCeti.Probability.Renewal.VagueLimit
public import TauCeti.Probability.Renewal.LimitCoefficient

/-!
# The nonlattice Blackwell renewal theorem

For a nonlattice interarrival law on the nonnegative half-line, the renewal mass of
an interval of fixed length tends to its length times the reciprocal extended mean.
Equivalently, the corresponding increment of the renewal function has this limit.
The inverse is taken before conversion to a real number, so infinite mean gives
limit zero. Interarrival laws with an atom at zero are allowed; nonlattice probability
laws automatically satisfy `F {0} < 1`.
Intervals are left-open and right-closed, retaining arrivals at the upper endpoint.

The compactness of translated renewal measures, harmonicity of their vague limits,
and nonlattice harmonic-measure rigidity identify each subsequential limit as a
multiple of Lebesgue measure. The renewal tail identity determines its coefficient.
These interval limits supply the input for the key renewal and excess-life theorems.

## References

* W. Feller, *An Introduction to Probability Theory and Its Applications*, volume II,
  second edition (1971), Chapter XI, the proof of Blackwell's renewal theorem.
-/

public section

open MeasureTheory Filter Set Topology
open scoped ENNReal NNReal CompactlySupported

namespace MeasureTheory.Measure

variable (F : Measure ℝ≥0) [IsProbabilityMeasure F]

/-- **Nonlattice Blackwell theorem, backward windows.** The mass of `(t - u, t]`
tends to the window length times the reciprocal extended mean. The subtraction
is truncated on `ℝ≥0`, which is immaterial as `t → ∞`. Infinite mean gives zero. -/
theorem tendsto_renewalMeasure_Ioc_sub (hNL : ¬ F.IsLattice)
    (u : ℝ≥0) :
    Tendsto (fun t : ℝ≥0 => F.renewalMeasure (Ioc (t - u) t)) atTop
      (𝓝 ((∫⁻ x, (x : ℝ≥0∞) ∂F)⁻¹ * u)) := by
  have hF := measure_singleton_zero_lt_one_of_not_isLattice hNL
  apply tendsto_of_subseq_tendsto
  intro t ht
  obtain ⟨η, φ, hη, hφ, hbound, hlim⟩ :=
    F.exists_subseq_tendsto_integral_translatedRenewalMeasure hF (fun n => t n)
  let : IsLocallyFiniteMeasure η := hη
  have htφ : Tendsto (fun n => t (φ n)) atTop atTop := ht.comp hφ.tendsto_atTop
  have hharm := F.map_coe_conv_eq_self_of_tendsto_integral hF
    (NNReal.tendsto_coe_atTop.2 htφ) η hlim
  let c : ℝ≥0 := (η (Ioc 0 1)).toNNReal
  have hc : (c : ℝ≥0∞) = η (Ioc 0 1) := ENNReal.coe_toNNReal measure_Ioc_lt_top.ne
  have hconst : η = c • (volume : Measure ℝ) := by
    rw [← coe_nnreal_smul, hc]
    exact eq_smul_volume_of_map_coe_conv_eq_self hNL
      (fun a => (hbound a).trans_eq
        (ENNReal.coe_toNNReal (F.renewalMeasure_Iic_lt_top hF 3).ne).symm) hharm
  have hwindows (v : ℝ≥0) : Tendsto
      (fun n => F.renewalMeasure (Ioc (t (φ n) - v) (t (φ n)))) atTop
      (𝓝 ((c : ℝ≥0∞) * v)) := by
    apply F.tendsto_renewalMeasure_Ioc_of_tendsto_integral_compactlySupported hF htφ c
    simpa only [← translatedRenewalMeasure_def, ← hconst] using hlim
  have hrate := F.eq_inv_mean_of_tendsto_renewalMeasure_Ioc hF htφ hwindows
  exact ⟨φ, by simpa only [hrate] using hwindows u⟩

/-- **Nonlattice Blackwell theorem, forward windows.** The real renewal mass of
`(t, t + u]` tends to `u` times the reciprocal extended mean, including infinite mean. -/
theorem tendsto_renewalMeasure_real_Ioc (hNL : ¬ F.IsLattice)
    (u : ℝ≥0) :
    Tendsto (fun t : ℝ≥0 => F.renewalMeasure.real (Ioc t (t + u))) atTop
      (𝓝 (((∫⁻ x, (x : ℝ≥0∞) ∂F)⁻¹).toReal * (u : ℝ))) := by
  have hF := measure_singleton_zero_lt_one_of_not_isLattice hNL
  have ht : Tendsto (fun t : ℝ≥0 => t + u) atTop atTop :=
    tendsto_atTop_mono (fun t => le_self_add) tendsto_id
  have hlim : Tendsto (fun t : ℝ≥0 => F.renewalMeasure (Ioc t (t + u))) atTop
      (𝓝 ((∫⁻ x, (x : ℝ≥0∞) ∂F)⁻¹ * u)) := by
    simpa only [Function.comp_def, add_tsub_cancel_right] using
      (F.tendsto_renewalMeasure_Ioc_sub hNL u).comp ht
  -- The local bound keeps the limit finite, permitting conversion to real masses.
  have hfinite : (∫⁻ x, (x : ℝ≥0∞) ∂F)⁻¹ * (u : ℝ≥0∞) ≠ ∞ :=
    ne_top_of_le_ne_top (F.renewalMeasure_Iic_lt_top hF u).ne
      (le_of_tendsto hlim (Eventually.of_forall fun t =>
        (measure_mono Ioc_subset_Icc_self).trans (F.renewalMeasure_Icc_add_le t u)))
  simpa only [Function.comp_def, measureReal_def, ENNReal.toReal_mul,
    ENNReal.coe_toReal] using (ENNReal.tendsto_toReal hfinite).comp hlim

/-- **Nonlattice Blackwell theorem.** The increase in the expected renewal count
from `t` to `t + u` tends to `u` times the real value of the reciprocal extended mean.
The artificial arrival at zero is excluded, while genuine zero-time arrivals cancel
in the difference. No finite-mean assumption is required. -/
theorem tendsto_renewalFunction_add_sub (hNL : ¬ F.IsLattice)
    (u : ℝ≥0) :
    Tendsto (fun t : ℝ≥0 => (F.renewalFunction (t + u)).toReal -
      (F.renewalFunction t).toReal) atTop
      (𝓝 (((∫⁻ x, (x : ℝ≥0∞) ∂F)⁻¹).toReal * (u : ℝ))) := by
  let : IsLocallyFiniteMeasure F.renewalMeasure :=
    F.isLocallyFiniteMeasure_renewalMeasure
      (measure_singleton_zero_lt_one_of_not_isLattice hNL)
  simpa only [F.toReal_renewalFunction_add_sub] using
    F.tendsto_renewalMeasure_real_Ioc hNL u

end MeasureTheory.Measure
