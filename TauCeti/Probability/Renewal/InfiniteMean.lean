/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Renewal.Measure
import TauCeti.Probability.Renewal.Blackwell
import TauCeti.Probability.Renewal.Lattice.InfiniteMean

/-!
# Vanishing renewal increments for infinite-mean interarrival laws

For any probability measure `F` on `ℝ≥0` of infinite extended mean, whether lattice or
nonlattice, the expected number of renewals in a window `(t, t + x]` of fixed length `x`
tends to zero as `t → ∞` through all nonnegative real observation times. Equivalently,
both the real and extended renewal masses of `(t, t + x]` tend to zero.

Infinite extended mean automatically excludes concentration at zero (`F {0} < 1`), while
allowing a genuine positive atom at zero. These unconditional window limits supply the
renewal input for infinite-mean excess-life escape without distinguishing lattice and
nonlattice interarrival laws.

## References

* W. Feller, *An Introduction to Probability Theory and Its Applications*, volume II,
  second edition (1971), Chapter XI.
-/

public section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

namespace MeasureTheory.Measure

variable (F : Measure ℝ≥0) [IsProbabilityMeasure F]

/-- Infinite extended mean rules out concentration at zero, so the renewal measure is locally
finite. -/
theorem isLocallyFiniteMeasure_renewalMeasure_of_mean_eq_top
    (hmean : (∫⁻ u, (u : ℝ≥0∞) ∂F) = ∞) : IsLocallyFiniteMeasure F.renewalMeasure :=
  F.isLocallyFiniteMeasure_renewalMeasure <|
    F.measure_singleton_lt_one_of_lintegral_pos (f := fun u ↦ (u : ℝ≥0∞))
      (a := 0) (by simp) (hmean ▸ ENNReal.zero_lt_top)

/-- **Infinite-mean renewal increment limit.** For any probability law on `ℝ≥0` of infinite
extended mean, lattice or nonlattice, every fixed-window increment of the real-valued renewal
function tends to zero along all nonnegative real observation times. Genuine zero-time arrivals
are allowed. -/
theorem tendsto_renewalFunction_add_sub_of_mean_eq_top
    (hmean : (∫⁻ u, (u : ℝ≥0∞) ∂F) = ∞) (x : ℝ≥0) :
    Tendsto (fun t : ℝ≥0 ↦ (F.renewalFunction (t + x)).toReal -
      (F.renewalFunction t).toReal) atTop (𝓝 0) := by
  by_cases hF : F.IsLattice
  · exact hF.tendsto_renewalFunction_add_sub_of_mean_eq_top hmean x
  · simpa only [hmean, ENNReal.inv_top, ENNReal.toReal_zero, zero_mul] using
      F.tendsto_renewalFunction_add_sub hF x

/-- **Infinite-mean real renewal window limit.** For any probability law on `ℝ≥0` of infinite
extended mean, lattice or nonlattice, the real renewal mass of `(t, t + x]` tends to zero as
`t → ∞`. -/
theorem tendsto_renewalMeasure_real_Ioc_of_mean_eq_top
    (hmean : (∫⁻ u, (u : ℝ≥0∞) ∂F) = ∞) (x : ℝ≥0) :
    Tendsto (fun t : ℝ≥0 ↦ F.renewalMeasure.real (Ioc t (t + x))) atTop (𝓝 0) := by
  have := F.isLocallyFiniteMeasure_renewalMeasure_of_mean_eq_top hmean
  simpa only [F.toReal_renewalFunction_add_sub] using
    F.tendsto_renewalFunction_add_sub_of_mean_eq_top hmean x

/-- **Infinite-mean extended renewal window limit.** For any probability law on `ℝ≥0` of infinite
extended mean, lattice or nonlattice, the extended renewal mass of `(t, t + x]` tends to zero as
`t → ∞`. -/
theorem tendsto_renewalMeasure_Ioc_of_mean_eq_top
    (hmean : (∫⁻ u, (u : ℝ≥0∞) ∂F) = ∞) (x : ℝ≥0) :
    Tendsto (fun t : ℝ≥0 ↦ F.renewalMeasure (Ioc t (t + x))) atTop (𝓝 0) := by
  have := F.isLocallyFiniteMeasure_renewalMeasure_of_mean_eq_top hmean
  have hreal := (ENNReal.continuous_ofReal.tendsto 0).comp
    (F.tendsto_renewalMeasure_real_Ioc_of_mean_eq_top hmean x)
  simpa only [Function.comp_def, ofReal_measureReal measure_Ioc_lt_top.ne,
    ENNReal.ofReal_zero] using hreal

end MeasureTheory.Measure
