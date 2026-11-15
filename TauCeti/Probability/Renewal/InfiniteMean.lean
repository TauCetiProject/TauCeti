/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Renewal.Blackwell
public import TauCeti.Probability.Renewal.IntervalLimit
import TauCeti.Analysis.SpecificLimits.LatticeIncrements
import TauCeti.MeasureTheory.Integral.Lebesgue.Support
import TauCeti.Probability.Renewal.Lattice.Blackwell

/-!
# Vanishing renewal limits for infinite-mean interarrival laws

When a probability measure `F` on `ℝ≥0` has infinite extended mean (`∫⁻ u, (u : ℝ≥0∞) ∂F = ∞`), the
asymptotic renewal rate is zero whether `F` is lattice or nonlattice. Combining the lattice
Blackwell theorem (`MeasureTheory.Measure.IsLatticeSpan.tendsto_renewalFunction_succ_mul_sub`) and
monotone grid interpolation (`Monotone.tendsto_sub_add_of_tendsto_sub_lattice`) with the nonlattice
Blackwell theorem (`MeasureTheory.Measure.tendsto_renewalFunction_add_sub`) removes all
arithmetic-support hypotheses:

* every fixed-length increment `(F.renewalFunction (t + u)).toReal - (F.renewalFunction t).toReal`
  tends to `0` as `t → ∞`, along all nonnegative real observation times;
* the renewal mass `F.renewalMeasure (Ioc t (t + u))` (and backward window `Ioc (t - u) t`) tends
  to `0` in both `ℝ` and `ℝ≥0∞`;
* for any antitone function `h : ℝ≥0 → ℝ` integrable on `(0, ∞)`, both `h ∗ F.renewalMeasure` and
  `h ∗ (F.renewalMeasure - δ₀)` tend to `0`, as does any locally bounded measurable solution of the
  renewal equation `g = h + g ∗ F`.

Infinite mean automatically rules out full concentration at zero
(`MeasureTheory.Measure.measure_singleton_zero_lt_one_of_mean_eq_top`), while genuine atoms at zero
(`0 < F {0} < 1`) remain permitted throughout.

## Main results

* `MeasureTheory.Measure.measure_singleton_zero_lt_one_of_mean_eq_top`: a zero or probability
  measure on `ℝ≥0` of infinite extended mean satisfies `F {0} < 1`.
* `MeasureTheory.Measure.tendsto_renewalFunction_add_sub_of_mean_eq_top`: unconditional vanishing of
  fixed-window renewal-function increments for infinite-mean laws.
* `MeasureTheory.Measure.tendsto_renewalMeasure_real_Ioc_of_mean_eq_top`,
  `MeasureTheory.Measure.tendsto_renewalMeasure_Ioc_of_mean_eq_top`,
  `MeasureTheory.Measure.tendsto_renewalMeasure_Ioc_sub_of_mean_eq_top`: vanishing forward and
  backward interval masses of `F.renewalMeasure`.
* `MeasureTheory.Measure.tendsto_renewalConv_of_mean_eq_top`,
  `MeasureTheory.Measure.tendsto_renewalConv_sub_dirac_of_mean_eq_top`,
  `TauCeti.Probability.tendsto_of_eq_add_renewalConv_of_mean_eq_top`: unconditional infinite-mean
  key renewal limits.

## References

* William Feller, *An Introduction to Probability Theory and Its Applications*, vol. II, second
  edition, Wiley, 1971, Chapter XI, §1 and §4.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace MeasureTheory.Measure

open TauCeti.Probability

/-- A zero or probability measure on `ℝ≥0` of infinite extended mean has mass strictly below one at
zero. -/
theorem measure_singleton_zero_lt_one_of_mean_eq_top (F : Measure ℝ≥0)
    [IsZeroOrProbabilityMeasure F] (hmean : (∫⁻ u, (u : ℝ≥0∞) ∂F) = ∞) : F {0} < 1 :=
  F.measure_singleton_lt_one_of_lintegral_pos (f := fun x => (x : ℝ≥0∞)) (a := 0) (by simp)
    (hmean ▸ ENNReal.zero_lt_top)

variable (F : Measure ℝ≥0) [IsProbabilityMeasure F]

/-- **Infinite-mean Blackwell limit.** For any probability measure `F` on `ℝ≥0` of infinite extended
mean, lattice or nonlattice, every fixed-length increment of the renewal function tends to zero as
`t → ∞` through all nonnegative real times. Atoms at zero are allowed. -/
theorem tendsto_renewalFunction_add_sub_of_mean_eq_top
    (hmean : (∫⁻ u, (u : ℝ≥0∞) ∂F) = ∞) (u : ℝ≥0) :
    Tendsto (fun t : ℝ≥0 => (F.renewalFunction (t + u)).toReal - (F.renewalFunction t).toReal)
      atTop (𝓝 0) := by
  by_cases hL : F.IsLattice
  · have hzero := F.measure_singleton_zero_lt_one_of_mean_eq_top hmean
    obtain ⟨a, hmax⟩ := hL.exists_isGreatest_of_measure_zero_lt_one hzero
    have hgrid : Tendsto (fun n : ℕ => (F.renewalFunction (a * (n + 1))).toReal -
        (F.renewalFunction (a * n)).toReal) atTop (𝓝 0) := by
      simpa only [hmean, ENNReal.inv_top, ENNReal.toReal_zero, mul_zero,
        Nat.cast_add, Nat.cast_one, mul_comm] using
        hmax.1.tendsto_renewalFunction_succ_mul_sub hmax
    exact (F.monotone_toReal_renewalFunction hzero).tendsto_sub_add_of_tendsto_sub_lattice
      hmax.1.pos hgrid u
  · simpa [hmean] using F.tendsto_renewalFunction_add_sub hL u

/-- For any probability measure `F` on `ℝ≥0` of infinite extended mean, lattice or not, the real
renewal mass of `(t, t + u]` tends to zero as `t → ∞`. -/
theorem tendsto_renewalMeasure_real_Ioc_of_mean_eq_top
    (hmean : (∫⁻ u, (u : ℝ≥0∞) ∂F) = ∞) (u : ℝ≥0) :
    Tendsto (fun t : ℝ≥0 => F.renewalMeasure.real (Ioc t (t + u))) atTop (𝓝 0) := by
  let : IsLocallyFiniteMeasure F.renewalMeasure :=
    F.isLocallyFiniteMeasure_renewalMeasure (F.measure_singleton_zero_lt_one_of_mean_eq_top hmean)
  simpa only [← F.toReal_renewalFunction_add_sub] using
    F.tendsto_renewalFunction_add_sub_of_mean_eq_top hmean u

/-- For any probability measure `F` on `ℝ≥0` of infinite extended mean, lattice or not, the
`ℝ≥0∞`-valued renewal mass of `(t, t + u]` tends to zero as `t → ∞`. -/
theorem tendsto_renewalMeasure_Ioc_of_mean_eq_top
    (hmean : (∫⁻ u, (u : ℝ≥0∞) ∂F) = ∞) (u : ℝ≥0) :
    Tendsto (fun t : ℝ≥0 => F.renewalMeasure (Ioc t (t + u))) atTop (𝓝 0) := by
  have hzero := F.measure_singleton_zero_lt_one_of_mean_eq_top hmean
  have hfin (t : ℝ≥0) : F.renewalMeasure (Ioc t (t + u)) ≠ ∞ :=
    ne_top_of_le_ne_top (F.renewalMeasure_Iic_lt_top hzero (t + u)).ne
      (measure_mono Ioc_subset_Iic_self)
  simpa only [ofReal_measureReal (hfin _), ENNReal.ofReal_zero] using
    ENNReal.tendsto_ofReal (F.tendsto_renewalMeasure_real_Ioc_of_mean_eq_top hmean u)

/-- For any probability measure `F` on `ℝ≥0` of infinite extended mean, lattice or not, the
`ℝ≥0∞`-valued renewal mass of the backward window `(t - u, t]` tends to zero as `t → ∞`. -/
theorem tendsto_renewalMeasure_Ioc_sub_of_mean_eq_top
    (hmean : (∫⁻ u, (u : ℝ≥0∞) ∂F) = ∞) (u : ℝ≥0) :
    Tendsto (fun t : ℝ≥0 => F.renewalMeasure (Ioc (t - u) t)) atTop (𝓝 0) := by
  have ht : Tendsto (fun t : ℝ≥0 => t - u) atTop atTop :=
    tendsto_atTop.2 fun c => by
      filter_upwards [eventually_ge_atTop (c + u)] with t hct
      exact le_tsub_of_add_le_right hct
  refine ((F.tendsto_renewalMeasure_Ioc_of_mean_eq_top hmean u).comp ht).congr' ?_
  filter_upwards [eventually_ge_atTop u] with t htu
  simp [tsub_add_cancel_of_le htu]

/-- **Infinite-mean key renewal limit.** For any probability measure `F` on `ℝ≥0` of infinite
extended mean (lattice or nonlattice) and any antitone function `h : ℝ≥0 → ℝ` integrable on
`(0, ∞)`, the convolution `h ∗ F.renewalMeasure` tends to zero as `t → ∞`. -/
theorem tendsto_renewalConv_of_mean_eq_top
    (hmean : (∫⁻ u, (u : ℝ≥0∞) ∂F) = ∞) {h : ℝ≥0 → ℝ} (hh : Antitone h)
    (hint : IntegrableOn (fun x : ℝ => h x.toNNReal) (Ioi 0)) :
    Tendsto (renewalConv h F.renewalMeasure) atTop (𝓝 0) := by
  have hlim (d : ℝ≥0) :
      Tendsto (fun t : ℝ≥0 => F.renewalMeasure.real (Ioc t (t + d))) atTop (𝓝 ((0 : ℝ) * d)) := by
    simpa using F.tendsto_renewalMeasure_real_Ioc_of_mean_eq_top hmean d
  simpa using F.tendsto_renewalConv_of_tendsto_measureReal_Ioc
    (F.measure_singleton_zero_lt_one_of_mean_eq_top hmean) hlim hh hint

/-- **Infinite-mean key renewal limit for positive arrivals.** For any probability measure `F` on
`ℝ≥0` of infinite extended mean (lattice or nonlattice) and any antitone function `h : ℝ≥0 → ℝ`
integrable on `(0, ∞)`, `h ∗ (F.renewalMeasure - δ₀)` tends to zero as `t → ∞`. -/
theorem tendsto_renewalConv_sub_dirac_of_mean_eq_top
    (hmean : (∫⁻ u, (u : ℝ≥0∞) ∂F) = ∞) {h : ℝ≥0 → ℝ} (hh : Antitone h)
    (hint : IntegrableOn (fun x : ℝ => h x.toNNReal) (Ioi 0)) :
    Tendsto (renewalConv h (F.renewalMeasure - dirac 0)) atTop (𝓝 0) := by
  have hlim (d : ℝ≥0) :
      Tendsto (fun t : ℝ≥0 => F.renewalMeasure.real (Ioc t (t + d))) atTop (𝓝 ((0 : ℝ) * d)) := by
    simpa using F.tendsto_renewalMeasure_real_Ioc_of_mean_eq_top hmean d
  simpa using F.tendsto_renewalConv_sub_dirac_of_tendsto_measureReal_Ioc
    (F.measure_singleton_zero_lt_one_of_mean_eq_top hmean) hlim hh hint

end MeasureTheory.Measure

namespace TauCeti.Probability

/-- For any probability measure `F` on `ℝ≥0` of infinite extended mean (lattice or nonlattice) and
antitone forcing `h` integrable on `(0, ∞)`, every locally bounded measurable solution `g` of
`g = h + g ∗ F` tends to zero as `t → ∞`. -/
theorem tendsto_of_eq_add_renewalConv_of_mean_eq_top
    {F : Measure ℝ≥0} [IsProbabilityMeasure F] (hmean : (∫⁻ u, (u : ℝ≥0∞) ∂F) = ∞)
    {h g : ℝ≥0 → ℝ} (hh : Antitone h)
    (hint : IntegrableOn (fun x : ℝ => h x.toNNReal) (Ioi 0))
    (hg : Measurable g) (hgb : ∀ t, ∃ C, ∀ s ≤ t, |g s| ≤ C)
    (hgeq : g = h + renewalConv g F) :
    Tendsto g atTop (𝓝 0) := by
  have hlim (d : ℝ≥0) :
      Tendsto (fun t : ℝ≥0 => F.renewalMeasure.real (Ioc t (t + d))) atTop (𝓝 ((0 : ℝ) * d)) := by
    simpa using F.tendsto_renewalMeasure_real_Ioc_of_mean_eq_top hmean d
  simpa using tendsto_of_eq_add_renewalConv_of_tendsto_measureReal_Ioc
    (F.measure_singleton_zero_lt_one_of_mean_eq_top hmean) hlim hh hint hg hgb hgeq

end TauCeti.Probability
