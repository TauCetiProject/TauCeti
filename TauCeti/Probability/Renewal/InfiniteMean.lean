/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Renewal.Blackwell
import TauCeti.MeasureTheory.Integral.Lebesgue.Support
import TauCeti.Probability.Renewal.Lattice.Blackwell
import TauCeti.Analysis.SpecificLimits.LatticeIncrements
public import TauCeti.Probability.Renewal.IntervalLimit

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

* `MeasureTheory.Measure.measure_singleton_zero_lt_one_of_mean_eq_top` and
  `MeasureTheory.Measure.isLocallyFiniteMeasure_renewalMeasure_of_mean_eq_top` — infinite mean
  excludes concentration at zero, so the renewal measure is locally finite.
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

/-- A probability measure on `ℝ≥0` of infinite extended mean has mass strictly less than one
at zero. -/
theorem measure_singleton_zero_lt_one_of_mean_eq_top
    (hmean : (∫⁻ u, (u : ℝ≥0∞) ∂F) = ∞) : F {0} < 1 :=
  F.measure_singleton_lt_one_of_lintegral_pos (f := fun u ↦ (u : ℝ≥0∞))
    (a := 0) (by simp) (hmean ▸ ENNReal.zero_lt_top)

/-- Infinite extended mean rules out concentration at zero, so the renewal measure is locally
finite. -/
theorem isLocallyFiniteMeasure_renewalMeasure_of_mean_eq_top
    (hmean : (∫⁻ u, (u : ℝ≥0∞) ∂F) = ∞) : IsLocallyFiniteMeasure F.renewalMeasure :=
  F.isLocallyFiniteMeasure_renewalMeasure (F.measure_singleton_zero_lt_one_of_mean_eq_top hmean)

/-- For any probability law on `ℝ≥0` of infinite extended mean, lattice or nonlattice, every
fixed-window increment of the renewal function tends to zero along all nonnegative real
observation times. -/
theorem tendsto_renewalFunction_add_sub_of_mean_eq_top
    (hmean : (∫⁻ u, (u : ℝ≥0∞) ∂F) = ∞) (u : ℝ≥0) :
    Tendsto (fun t : ℝ≥0 ↦ (F.renewalFunction (t + u)).toReal -
      (F.renewalFunction t).toReal) atTop (𝓝 0) := by
  by_cases hL : F.IsLattice
  · have hzero := F.measure_singleton_zero_lt_one_of_mean_eq_top hmean
    obtain ⟨a, hmax⟩ := hL.exists_isGreatest_of_measure_zero_lt_one hzero
    have hgrid : Tendsto (fun n : ℕ ↦ (F.renewalFunction (a * (n + 1))).toReal -
        (F.renewalFunction (a * n)).toReal) atTop (𝓝 0) := by
      simpa only [hmean, ENNReal.inv_top, ENNReal.toReal_zero, mul_zero,
        Nat.cast_add, Nat.cast_one, mul_comm] using
        hmax.1.tendsto_renewalFunction_succ_mul_sub hmax
    exact (F.monotone_toReal_renewalFunction hzero).tendsto_sub_add_of_tendsto_sub_lattice
      hmax.1.pos hgrid u
  · simpa [hmean] using F.tendsto_renewalFunction_add_sub hL u

/-- For any probability law on `ℝ≥0` of infinite extended mean, lattice or nonlattice, the
real renewal mass of `(t, t + u]` tends to zero as `t → ∞`. -/
theorem tendsto_renewalMeasure_real_Ioc_of_mean_eq_top
    (hmean : (∫⁻ u, (u : ℝ≥0∞) ∂F) = ∞) (u : ℝ≥0) :
    Tendsto (fun t : ℝ≥0 ↦ F.renewalMeasure.real (Ioc t (t + u))) atTop (𝓝 0) := by
  have := F.isLocallyFiniteMeasure_renewalMeasure_of_mean_eq_top hmean
  simpa only [F.toReal_renewalFunction_add_sub] using
    F.tendsto_renewalFunction_add_sub_of_mean_eq_top hmean u

/-- For any probability law on `ℝ≥0` of infinite extended mean, lattice or nonlattice, the
renewal mass `F.renewalMeasure (Ioc t (t + u))` tends to zero in `ℝ≥0∞` as `t → ∞`. -/
theorem tendsto_renewalMeasure_Ioc_of_mean_eq_top
    (hmean : (∫⁻ u, (u : ℝ≥0∞) ∂F) = ∞) (u : ℝ≥0) :
    Tendsto (fun t : ℝ≥0 ↦ F.renewalMeasure (Ioc t (t + u))) atTop (𝓝 0) := by
  have := F.isLocallyFiniteMeasure_renewalMeasure_of_mean_eq_top hmean
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

/-! ### Further results -/

public section

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace MeasureTheory.Measure

open TauCeti.Probability

variable (F : Measure ℝ≥0) [IsProbabilityMeasure F]

/-- For any probability measure on `ℝ≥0` of infinite extended mean, lattice or nonlattice, the
convolution of `F.renewalMeasure` with a forcing function bounded on `[0, A)` and cut off at age
`A` tends to zero at infinity. Neither monotonicity, measurability, nor any hypothesis at `A` is
required. -/
theorem tendsto_renewalConv_indicator_Iio_of_mean_eq_top
    (hmean : (∫⁻ u, (u : ℝ≥0∞) ∂F) = ∞) {h : ℝ≥0 → ℝ}
    (A : ℝ≥0) {C : ℝ} (hC : ∀ s < A, |h s| ≤ C) :
    Tendsto (renewalConv ((Iio A).indicator h) F.renewalMeasure) atTop (𝓝 0) := by
  let : IsLocallyFiniteMeasure F.renewalMeasure :=
    F.isLocallyFiniteMeasure_renewalMeasure
      (F.measure_singleton_lt_one_of_lintegral_pos ENNReal.coe_zero (hmean ▸ ENNReal.zero_lt_top))
  exact F.renewalMeasure.tendsto_renewalConv_indicator_Iio_of_tendsto_measureReal_Ioc_nhds_zero
    (F.tendsto_renewalMeasure_real_Ioc_of_mean_eq_top hmean A) hC

/-- For any probability measure on `ℝ≥0` of infinite extended mean, lattice or nonlattice, the
convolution of `F.renewalMeasure` with any nonnegative, nonincreasing, Lebesgue-integrable
forcing function tends to zero at infinity. -/
theorem tendsto_renewalConv_of_mean_eq_top
    (hmean : (∫⁻ u, (u : ℝ≥0∞) ∂F) = ∞) {h : ℝ≥0 → ℝ}
    (hh : Antitone h) (h₀ : ∀ x, 0 ≤ h x)
    (hint : IntegrableOn (fun x : ℝ => h x.toNNReal) (Ioi 0)) :
    Tendsto (renewalConv h F.renewalMeasure) atTop (𝓝 0) := by
  simpa using F.tendsto_renewalConv_of_tendsto_measureReal_Ioc
    (F.measure_singleton_lt_one_of_lintegral_pos ENNReal.coe_zero (hmean ▸ ENNReal.zero_lt_top))
    (r := 0) (fun d ↦ by simpa using F.tendsto_renewalMeasure_real_Ioc_of_mean_eq_top hmean d)
    hh h₀ hint

/-- For any probability measure on `ℝ≥0` of infinite extended mean, lattice or nonlattice, the
convolution of `F.renewalMeasure - dirac 0` with any nonnegative, nonincreasing,
Lebesgue-integrable forcing function tends to zero at infinity. -/
theorem tendsto_renewalConv_sub_dirac_of_mean_eq_top
    (hmean : (∫⁻ u, (u : ℝ≥0∞) ∂F) = ∞) {h : ℝ≥0 → ℝ}
    (hh : Antitone h) (h₀ : ∀ x, 0 ≤ h x)
    (hint : IntegrableOn (fun x : ℝ => h x.toNNReal) (Ioi 0)) :
    Tendsto (renewalConv h (F.renewalMeasure - dirac 0)) atTop (𝓝 0) := by
  simpa using F.tendsto_renewalConv_sub_dirac_of_tendsto_measureReal_Ioc
    (F.measure_singleton_lt_one_of_lintegral_pos ENNReal.coe_zero (hmean ▸ ENNReal.zero_lt_top))
    (r := 0) (fun d ↦ by simpa using F.tendsto_renewalMeasure_real_Ioc_of_mean_eq_top hmean d)
    hh h₀ hint

end MeasureTheory.Measure

namespace TauCeti.Probability

/-- For any probability measure `F` on `ℝ≥0` of infinite extended mean, lattice or nonlattice, and
a nonnegative, nonincreasing, Lebesgue-integrable forcing function `h : ℝ≥0 → ℝ`, every measurable,
locally bounded solution `g` of `g = h + g ∗ F` tends to zero at infinity. -/
theorem tendsto_of_eq_add_renewalConv_of_mean_eq_top
    {F : Measure ℝ≥0} [IsProbabilityMeasure F] (hmean : (∫⁻ u, (u : ℝ≥0∞) ∂F) = ∞)
    {h g : ℝ≥0 → ℝ} (hh : Antitone h) (h₀ : ∀ x, 0 ≤ h x)
    (hint : IntegrableOn (fun x : ℝ => h x.toNNReal) (Ioi 0))
    (hg : Measurable g) (hgb : ∀ t, ∃ C, ∀ s ≤ t, |g s| ≤ C)
    (hgeq : g = h + renewalConv g F) :
    Tendsto g atTop (𝓝 0) := by
  simpa using tendsto_of_eq_add_renewalConv_of_tendsto_measureReal_Ioc
    (F.measure_singleton_lt_one_of_lintegral_pos ENNReal.coe_zero (hmean ▸ ENNReal.zero_lt_top))
    (r := 0) (fun d ↦ by simpa using F.tendsto_renewalMeasure_real_Ioc_of_mean_eq_top hmean d)
    hh h₀ hint hg hgb hgeq

end TauCeti.Probability
