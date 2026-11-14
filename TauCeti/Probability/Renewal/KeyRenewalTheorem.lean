/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Renewal.Blackwell
public import TauCeti.Probability.Renewal.IntervalLimit

/-!
# The key renewal theorem

For a nonlattice probability law `F` on the nonnegative half-line and a nonnegative,
nonincreasing, Lebesgue-integrable forcing function `h : ℝ≥0 → ℝ`, the convolution of `h`
with the renewal measure `U = F.renewalMeasure` converges as `t → ∞` to the reciprocal
extended mean of `F` times the Lebesgue integral of `h` over `(0, ∞)`. Removing the
artificial initial atom `δ₀` (equivalently, integrating against the positive-arrival
measure `F ∗ U`) gives the same limit because `h t → 0`. By uniqueness of locally bounded
measurable solutions to the renewal equation `g = h + g ∗ F`, every such solution has the
same asymptotic limit.

Bounded-age monotone forcing `(Iio A).indicator h` needs neither nonnegativity nor global
integrability. Throughout, the reciprocal mean `((∫⁻ u, (u : ℝ≥0∞) ∂F)⁻¹).toReal` is taken
in `ℝ≥0∞` before converting to `ℝ`, so infinite interarrival mean yields limit zero without
a separate case split, and an atom `0 < F {0} < 1` is allowed.

## Main results

* `MeasureTheory.Measure.tendsto_renewalConv_indicator_Iio_renewalMeasure` — key renewal
  limit for monotone forcing cut off at finite age `A`.
* `MeasureTheory.Measure.tendsto_renewalConv_renewalMeasure_sub_dirac` — key renewal theorem
  for `U - δ₀`.
* `MeasureTheory.Measure.tendsto_renewalConv_conv_renewalMeasure` — key renewal theorem for
  the positive-arrival measure `F ∗ U`.
* `MeasureTheory.Measure.tendsto_renewalConv_renewalMeasure` — key renewal theorem for `U`.
* `TauCeti.Probability.tendsto_of_eq_add_renewalConv` — asymptotic limit of any locally
  bounded measurable solution of the renewal equation `g = h + g ∗ F`.

## References

* W. Feller, *An Introduction to Probability Theory and Its Applications*, volume II,
  second edition (1971), Chapter XI, §1, the key renewal theorem.
* V. Tassion, *Applied Stochastic Processes*, ETH Zürich lecture notes (2025), Chapter 6.
-/

public section

open MeasureTheory Filter Set Topology
open scoped ENNReal NNReal

namespace MeasureTheory.Measure

open TauCeti.Probability

variable (F : Measure ℝ≥0) [IsProbabilityMeasure F]

/-- **Key renewal limit for bounded-age monotone forcing.** For a nonlattice interarrival law
`F` and a forcing function `h` that is nonincreasing on `[0, A]`, the convolution of
`(Iio A).indicator h` with `F.renewalMeasure` converges to the reciprocal extended mean times
`∫ x in 0..A, h x.toNNReal`. Neither nonnegativity nor global integrability of `h` is needed. -/
theorem tendsto_renewalConv_indicator_Iio_renewalMeasure (hNL : ¬ F.IsLattice)
    {h : ℝ≥0 → ℝ} (A : ℝ≥0) (hh : AntitoneOn h (Iic A)) :
    Tendsto (renewalConv ((Iio A).indicator h) F.renewalMeasure) atTop
      (𝓝 (((∫⁻ u, (u : ℝ≥0∞) ∂F)⁻¹).toReal * ∫ x in (0 : ℝ)..A, h x.toNNReal)) := by
  let : IsLocallyFiniteMeasure F.renewalMeasure :=
    F.isLocallyFiniteMeasure_renewalMeasure
      (measure_singleton_zero_lt_one_of_not_isLattice hNL)
  exact F.renewalMeasure.tendsto_renewalConv_indicator_Iio_of_tendsto_measureReal_Ioc
    (F.tendsto_renewalMeasure_real_Ioc hNL) A hh

/-- **Key renewal theorem, positive-arrival form (`U - δ₀`).** For a nonlattice interarrival
law `F` and a nonnegative, nonincreasing, Lebesgue-integrable forcing function `h`, the
convolution `renewalConv h (F.renewalMeasure - dirac 0)` converges to the reciprocal extended
mean of `F` times `∫ x in Ioi 0, h x.toNNReal`. Infinite mean gives limit zero, and genuine
zero-time arrivals remain in `F.renewalMeasure - dirac 0`. -/
theorem tendsto_renewalConv_renewalMeasure_sub_dirac (hNL : ¬ F.IsLattice)
    {h : ℝ≥0 → ℝ} (hh : Antitone h) (h₀ : ∀ x, 0 ≤ h x)
    (hint : IntegrableOn (fun x : ℝ ↦ h x.toNNReal) (Ioi 0)) :
    Tendsto (renewalConv h (F.renewalMeasure - dirac 0)) atTop
      (𝓝 (((∫⁻ u, (u : ℝ≥0∞) ∂F)⁻¹).toReal * ∫ x in Ioi (0 : ℝ), h x.toNNReal)) :=
  F.tendsto_renewalConv_sub_dirac_of_tendsto_measureReal_Ioc
    (measure_singleton_zero_lt_one_of_not_isLattice hNL)
    (F.tendsto_renewalMeasure_real_Ioc hNL) hh h₀ hint

/-- **Key renewal theorem for `F ∗ U`.** Integrating against the positive-arrival measure
`F ∗ F.renewalMeasure` yields the same key renewal limit as `F.renewalMeasure - dirac 0`. -/
theorem tendsto_renewalConv_conv_renewalMeasure (hNL : ¬ F.IsLattice)
    {h : ℝ≥0 → ℝ} (hh : Antitone h) (h₀ : ∀ x, 0 ≤ h x)
    (hint : IntegrableOn (fun x : ℝ ↦ h x.toNNReal) (Ioi 0)) :
    Tendsto (renewalConv h (F ∗ F.renewalMeasure)) atTop
      (𝓝 (((∫⁻ u, (u : ℝ≥0∞) ∂F)⁻¹).toReal * ∫ x in Ioi (0 : ℝ), h x.toNNReal)) := by
  have hmeasure : F.renewalMeasure - dirac 0 = F ∗ F.renewalMeasure := by
    conv_lhs => rw [renewalMeasure_eq_dirac_add_conv, add_comm, Measure.add_sub_cancel]
  rw [← hmeasure]
  exact F.tendsto_renewalConv_renewalMeasure_sub_dirac hNL hh h₀ hint

/-- **Key renewal theorem (`U`).** For a nonlattice interarrival law `F` and a nonnegative,
nonincreasing, Lebesgue-integrable forcing function `h`, the renewal convolution
`renewalConv h F.renewalMeasure` converges to the reciprocal extended mean of `F` times
`∫ x in Ioi 0, h x.toNNReal`. Infinite mean gives limit zero, and atoms at zero with mass
strictly below one are allowed. -/
theorem tendsto_renewalConv_renewalMeasure (hNL : ¬ F.IsLattice)
    {h : ℝ≥0 → ℝ} (hh : Antitone h) (h₀ : ∀ x, 0 ≤ h x)
    (hint : IntegrableOn (fun x : ℝ ↦ h x.toNNReal) (Ioi 0)) :
    Tendsto (renewalConv h F.renewalMeasure) atTop
      (𝓝 (((∫⁻ u, (u : ℝ≥0∞) ∂F)⁻¹).toReal * ∫ x in Ioi (0 : ℝ), h x.toNNReal)) :=
  F.tendsto_renewalConv_of_tendsto_measureReal_Ioc
    (measure_singleton_zero_lt_one_of_not_isLattice hNL)
    (F.tendsto_renewalMeasure_real_Ioc hNL) hh h₀ hint

end MeasureTheory.Measure

namespace TauCeti.Probability

/-- **Asymptotics of solutions to the renewal equation.** For a nonlattice probability law `F`
and a nonnegative, nonincreasing, Lebesgue-integrable forcing function `h`, every measurable
solution `g` of `g = h + renewalConv g F` that is bounded on bounded intervals converges as
`t → ∞` to `((∫⁻ u, (u : ℝ≥0∞) ∂F)⁻¹).toReal * ∫ x in Ioi 0, h x.toNNReal`. -/
theorem tendsto_of_eq_add_renewalConv {F : Measure ℝ≥0} [IsProbabilityMeasure F]
    (hNL : ¬ F.IsLattice) {h g : ℝ≥0 → ℝ} (hh : Antitone h) (h₀ : ∀ x, 0 ≤ h x)
    (hint : IntegrableOn (fun x : ℝ ↦ h x.toNNReal) (Ioi 0))
    (hg : Measurable g) (hgb : ∀ t, ∃ C, ∀ s ≤ t, |g s| ≤ C)
    (hgeq : g = h + renewalConv g F) :
    Tendsto g atTop
      (𝓝 (((∫⁻ u, (u : ℝ≥0∞) ∂F)⁻¹).toReal * ∫ x in Ioi (0 : ℝ), h x.toNNReal)) := by
  let : IsLocallyFiniteMeasure F.renewalMeasure :=
    F.isLocallyFiniteMeasure_renewalMeasure
      (Measure.measure_singleton_zero_lt_one_of_not_isLattice hNL)
  have hhb : ∀ t, ∃ C, ∀ s ≤ t, |h s| ≤ C := fun _ ↦
    ⟨h 0, fun s _ ↦ by rw [abs_of_nonneg (h₀ s)]; exact hh bot_le⟩
  rw [eq_renewalConv_renewalMeasure hh.measurable hhb hg hgb hgeq]
  exact F.tendsto_renewalConv_renewalMeasure hNL hh h₀ hint

end TauCeti.Probability
