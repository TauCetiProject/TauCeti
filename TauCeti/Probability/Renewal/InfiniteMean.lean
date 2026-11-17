/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Renewal.IntervalLimit
import TauCeti.MeasureTheory.Integral.Lebesgue.Support
import TauCeti.Probability.Renewal.Blackwell
import TauCeti.Probability.Renewal.Lattice.InfiniteMean

/-!
# Vanishing renewal increments and convolutions for infinite-mean laws

For any probability measure `F` on `ℝ≥0` of infinite extended mean, whether lattice or
nonlattice, every fixed-window increment `(F.renewalFunction (t + x)).toReal -
(F.renewalFunction t).toReal` tends to zero as `t → ∞` through all nonnegative real observation
times. Equivalently, the renewal mass of `(t, t + x]` vanishes at infinity in both real and
extended-real form, and convolutions of `F.renewalMeasure` or `F.renewalMeasure - dirac 0`
against nonnegative, nonincreasing, Lebesgue-integrable forcing functions tend to zero.

No lattice or nonlattice assumption and no separate `F {0} < 1` hypothesis are required: infinite
mean implies `F {0} < 1`, and the proof splits into the lattice and nonlattice Blackwell
theorems. Atoms at zero are allowed.

## Main statements

* `MeasureTheory.Measure.tendsto_renewalFunction_add_sub_of_mean_eq_top`: fixed-window increments
  of the real-valued renewal function tend to zero for any infinite-mean law.
* `MeasureTheory.Measure.tendsto_renewalMeasure_real_Ioc_of_mean_eq_top`,
  `MeasureTheory.Measure.tendsto_renewalMeasure_Ioc_of_mean_eq_top`: the mass of `(t, t + x]`
  under `F.renewalMeasure` tends to zero.
* `MeasureTheory.Measure.tendsto_renewalConv_indicator_Iio_of_mean_eq_top`: vanishing of bounded
  forcing truncated to `[0, A)` under infinite mean, without monotonicity or measurability.
* `MeasureTheory.Measure.tendsto_renewalConv_of_mean_eq_top`,
  `MeasureTheory.Measure.tendsto_renewalConv_sub_dirac_of_mean_eq_top`: vanishing of monotone
  renewal convolutions under infinite mean.
* `TauCeti.Probability.tendsto_of_eq_add_renewalConv_of_mean_eq_top`: vanishing at infinity of
  measurable, locally bounded solutions of `g = h + g ∗ F` under infinite mean.

## References

* William Feller, *An Introduction to Probability Theory and Its Applications*, vol. II, 2nd
  edition, Wiley, 1971, Chapter XI, §1.
-/

public section

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace MeasureTheory.Measure

open TauCeti.Probability

variable (F : Measure ℝ≥0) [IsProbabilityMeasure F]

/-- For any probability measure on `ℝ≥0` of infinite extended mean, lattice or nonlattice, every
fixed-window increment of the real-valued renewal function tends to zero at infinity. Atoms at
zero are allowed. -/
theorem tendsto_renewalFunction_add_sub_of_mean_eq_top
    (hmean : (∫⁻ u, (u : ℝ≥0∞) ∂F) = ∞) (x : ℝ≥0) :
    Tendsto (fun t : ℝ≥0 ↦ (F.renewalFunction (t + x)).toReal -
      (F.renewalFunction t).toReal) atTop (𝓝 0) := by
  by_cases hL : F.IsLattice
  · exact hL.tendsto_renewalFunction_add_sub_of_mean_eq_top hmean x
  · simpa [hmean] using F.tendsto_renewalFunction_add_sub hL x

/-- For any probability measure on `ℝ≥0` of infinite extended mean, lattice or nonlattice, the
real renewal mass of `(t, t + x]` tends to zero as `t → ∞`. -/
theorem tendsto_renewalMeasure_real_Ioc_of_mean_eq_top
    (hmean : (∫⁻ u, (u : ℝ≥0∞) ∂F) = ∞) (x : ℝ≥0) :
    Tendsto (fun t : ℝ≥0 ↦ F.renewalMeasure.real (Ioc t (t + x))) atTop (𝓝 0) := by
  let : IsLocallyFiniteMeasure F.renewalMeasure :=
    F.isLocallyFiniteMeasure_renewalMeasure
      (F.measure_singleton_lt_one_of_lintegral_pos ENNReal.coe_zero (hmean ▸ ENNReal.zero_lt_top))
  simpa only [← F.toReal_renewalFunction_add_sub] using
    F.tendsto_renewalFunction_add_sub_of_mean_eq_top hmean x

/-- For any probability measure on `ℝ≥0` of infinite extended mean, lattice or nonlattice, the
extended renewal mass of `(t, t + x]` tends to zero as `t → ∞`. -/
theorem tendsto_renewalMeasure_Ioc_of_mean_eq_top
    (hmean : (∫⁻ u, (u : ℝ≥0∞) ∂F) = ∞) (x : ℝ≥0) :
    Tendsto (fun t : ℝ≥0 ↦ F.renewalMeasure (Ioc t (t + x))) atTop (𝓝 0) := by
  let : IsLocallyFiniteMeasure F.renewalMeasure :=
    F.isLocallyFiniteMeasure_renewalMeasure
      (F.measure_singleton_lt_one_of_lintegral_pos ENNReal.coe_zero (hmean ▸ ENNReal.zero_lt_top))
  simpa only [ofReal_measureReal measure_Ioc_lt_top.ne, ENNReal.ofReal_zero] using
    ENNReal.tendsto_ofReal (F.tendsto_renewalMeasure_real_Ioc_of_mean_eq_top hmean x)

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
