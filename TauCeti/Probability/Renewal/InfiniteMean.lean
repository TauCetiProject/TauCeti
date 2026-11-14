/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Renewal.Blackwell
public import TauCeti.Probability.Renewal.Lattice.InfiniteMean

/-!
# Vanishing renewal increments for infinite-mean interarrival laws

When a probability measure `F` on `ℝ≥0` has infinite extended mean, the expected number of
renewals in any bounded window of fixed length tends to zero as the observation time tends
to infinity through all nonnegative real numbers. Unlike the positive-rate renewal limit,
this zero-density limit requires neither a nonlattice assumption nor restriction to a
lattice grid: lattice laws are handled via the greatest lattice span and monotonicity, while
nonlattice laws follow from the nonlattice Blackwell renewal theorem.

Infinite extended mean automatically forces `F {0} < 1`, so no separate nondegeneracy
hypothesis at zero is needed, while genuine atoms `0 < F {0} < 1` are allowed.

## Main results

* `MeasureTheory.Measure.tendsto_renewalFunction_add_sub_of_mean_eq_top` — vanishing
  fixed-window increments of the real-valued renewal function for any infinite-mean law.
* `MeasureTheory.Measure.tendsto_renewalMeasure_real_Ioc_of_mean_eq_top` — vanishing real
  renewal mass of forward windows `(t, t + u]`.
* `MeasureTheory.Measure.tendsto_renewalMeasure_Ioc_of_mean_eq_top` and
  `MeasureTheory.Measure.tendsto_renewalMeasure_Ioc_sub_of_mean_eq_top` — extended
  nonnegative forward- and backward-window counterparts.

## References

* W. Feller, *An Introduction to Probability Theory and Its Applications*, volume II,
  second edition (1971), Chapter XI.
* V. Tassion, *Applied Stochastic Processes*, ETH Zürich lecture notes (2025), Chapter 6.
-/

public section

open MeasureTheory Filter Set Topology
open scoped ENNReal NNReal

namespace MeasureTheory.Measure

variable (F : Measure ℝ≥0) [IsProbabilityMeasure F]

/-- For any probability law on `ℝ≥0` of infinite extended mean, lattice or nonlattice, every
fixed-window increment of the renewal function tends to zero along all nonnegative real
observation times. -/
theorem tendsto_renewalFunction_add_sub_of_mean_eq_top
    (hmean : (∫⁻ u, (u : ℝ≥0∞) ∂F) = ∞) (u : ℝ≥0) :
    Tendsto (fun t : ℝ≥0 ↦ (F.renewalFunction (t + u)).toReal -
      (F.renewalFunction t).toReal) atTop (𝓝 0) := by
  by_cases hL : F.IsLattice
  · exact hL.tendsto_renewalFunction_add_sub_of_mean_eq_top hmean u
  · simpa [hmean] using F.tendsto_renewalFunction_add_sub hL u

/-- For any probability law on `ℝ≥0` of infinite extended mean, lattice or nonlattice, the
real renewal mass of `(t, t + u]` tends to zero as `t → ∞`. -/
theorem tendsto_renewalMeasure_real_Ioc_of_mean_eq_top
    (hmean : (∫⁻ u, (u : ℝ≥0∞) ∂F) = ∞) (u : ℝ≥0) :
    Tendsto (fun t : ℝ≥0 ↦ F.renewalMeasure.real (Ioc t (t + u))) atTop (𝓝 0) := by
  have hzero := F.measure_singleton_lt_one_of_lintegral_pos (f := fun x ↦ (x : ℝ≥0∞))
    (a := 0) (by simp) (hmean ▸ ENNReal.zero_lt_top)
  let : IsLocallyFiniteMeasure F.renewalMeasure := F.isLocallyFiniteMeasure_renewalMeasure hzero
  simpa only [F.toReal_renewalFunction_add_sub] using
    F.tendsto_renewalFunction_add_sub_of_mean_eq_top hmean u

/-- For any probability law on `ℝ≥0` of infinite extended mean, lattice or nonlattice, the
renewal mass `F.renewalMeasure (Ioc t (t + u))` tends to zero in `ℝ≥0∞` as `t → ∞`. -/
theorem tendsto_renewalMeasure_Ioc_of_mean_eq_top
    (hmean : (∫⁻ u, (u : ℝ≥0∞) ∂F) = ∞) (u : ℝ≥0) :
    Tendsto (fun t : ℝ≥0 ↦ F.renewalMeasure (Ioc t (t + u))) atTop (𝓝 0) := by
  have hzero := F.measure_singleton_lt_one_of_lintegral_pos (f := fun x ↦ (x : ℝ≥0∞))
    (a := 0) (by simp) (hmean ▸ ENNReal.zero_lt_top)
  let : IsLocallyFiniteMeasure F.renewalMeasure := F.isLocallyFiniteMeasure_renewalMeasure hzero
  have heq (t : ℝ≥0) : F.renewalMeasure (Ioc t (t + u)) =
      ENNReal.ofReal (F.renewalMeasure.real (Ioc t (t + u))) :=
    (ofReal_measureReal measure_Ioc_lt_top.ne).symm
  simp_rw [heq]
  simpa only [Function.comp_def, ENNReal.ofReal_zero] using
    (ENNReal.continuous_ofReal.tendsto 0).comp
      (F.tendsto_renewalMeasure_real_Ioc_of_mean_eq_top hmean u)

/-- For any probability law on `ℝ≥0` of infinite extended mean, lattice or nonlattice, the
backward-window renewal mass `F.renewalMeasure (Ioc (t - u) t)` tends to zero in `ℝ≥0∞` as
`t → ∞`. -/
theorem tendsto_renewalMeasure_Ioc_sub_of_mean_eq_top
    (hmean : (∫⁻ u, (u : ℝ≥0∞) ∂F) = ∞) (u : ℝ≥0) :
    Tendsto (fun t : ℝ≥0 ↦ F.renewalMeasure (Ioc (t - u) t)) atTop (𝓝 0) := by
  have ht : Tendsto (fun t : ℝ≥0 ↦ t - u) atTop atTop :=
    tendsto_atTop.2 fun b ↦ by
      filter_upwards [eventually_ge_atTop (b + u)] with t hbt
      exact le_tsub_of_add_le_right hbt
  have he : (fun t : ℝ≥0 ↦ F.renewalMeasure (Ioc (t - u) t)) =ᶠ[atTop]
      fun t ↦ F.renewalMeasure (Ioc (t - u) (t - u + u)) := by
    filter_upwards [eventually_ge_atTop u] with t htu
    rw [tsub_add_cancel_of_le htu]
  exact ((F.tendsto_renewalMeasure_Ioc_of_mean_eq_top hmean u).comp ht).congr' he.symm

end MeasureTheory.Measure
