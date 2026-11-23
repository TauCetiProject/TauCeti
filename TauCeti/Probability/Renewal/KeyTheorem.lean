/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Renewal.Blackwell
public import TauCeti.Probability.Renewal.IntervalLimit

/-!
# The key renewal theorem for decreasing forcing

For a nonlattice probability law `F` on the nonnegative half-line and a nonnegative,
decreasing, Lebesgue-integrable real forcing function `h`, convolution against the
renewal measure converges to the integral of `h` times the reciprocal extended mean
of `F`. The same limit holds after removing the artificial arrival at zero, and transfers
by uniqueness to every measurable locally bounded solution of the renewal equation
`g = h + g ∗ F`. Bounded-age monotone forcing `(Iio A).indicator h` needs neither
nonnegativity nor global integrability.

The inverse is taken in `ℝ≥0∞` before conversion to `ℝ`, so infinite mean gives
limit zero. An atom of `F` at zero is allowed: removing `dirac 0` removes only the
artificial arrival, not genuine zero-increment arrivals. No continuity of `h` is
required, and both endpoints are retained in the convolution integral.

For a forcing function that is merely decreasing up to a finite age cutoff `A`, without
any sign or global integrability assumption, convolution of its truncation
`(Iio A).indicator h` with the renewal measure converges to the reciprocal extended mean
times `∫ x in 0..A, h x.toNNReal`.

The nonlattice Blackwell theorem supplies interval limits; the monotone-forcing
transfer theorem supplies the step-function approximation and uniform tail control.
These results apply directly to renewal equations with decreasing forcing, including
excess-life tail probabilities.

## Main statements

* `MeasureTheory.Measure.tendsto_renewalConv_indicator_Iio`: bounded-age decreasing
  forcing limit for nonlattice interarrival laws.
* `MeasureTheory.Measure.tendsto_renewalConv_sub_dirac`: **key renewal theorem**
  excluding the artificial arrival `dirac 0`.
* `MeasureTheory.Measure.tendsto_renewalConv`: **key renewal theorem** for the full
  renewal measure.
* `TauCeti.Probability.tendsto_of_eq_add_renewalConv`: convergence at infinity of
  measurable, locally bounded solutions of `g = h + g ∗ F`.

## References

* W. Feller, *An Introduction to Probability Theory and Its Applications*, volume II,
  second edition (1971), Chapter XI, the key renewal theorem.
* V. Tassion, *Applied Stochastic Processes*, ETH Zürich lecture notes (2025), Chapter 6.
-/

public section

open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal

namespace MeasureTheory.Measure

open TauCeti.Probability

variable (F : Measure ℝ≥0) [IsProbabilityMeasure F]

/-- **Key renewal limit for bounded-age monotone forcing.** For a nonlattice interarrival law
`F` and a forcing function `h` that is nonincreasing on `[0, A]`, the convolution of
`(Iio A).indicator h` with `F.renewalMeasure` converges to the reciprocal extended mean times
`∫ x in 0..A, h x.toNNReal`. Neither nonnegativity nor global integrability of `h` is needed. -/
theorem tendsto_renewalConv_indicator_Iio (hNL : ¬ F.IsLattice)
    {h : ℝ≥0 → ℝ} (A : ℝ≥0) (hh : AntitoneOn h (Iic A)) :
    Tendsto (renewalConv ((Iio A).indicator h) F.renewalMeasure) atTop
      (𝓝 (((∫⁻ x, (x : ℝ≥0∞) ∂F)⁻¹).toReal * ∫ x in (0 : ℝ)..A, h x.toNNReal)) := by
  let : IsLocallyFiniteMeasure F.renewalMeasure :=
    F.isLocallyFiniteMeasure_renewalMeasure
      (measure_singleton_zero_lt_one_of_not_isLattice hNL)
  exact F.renewalMeasure.tendsto_renewalConv_indicator_Iio_of_tendsto_measureReal_Ioc
    (F.tendsto_renewalMeasure_real_Ioc hNL) A hh

/-- **Key renewal theorem, excluding the artificial arrival.** For nonnegative decreasing
integrable forcing and a nonlattice interarrival law, convolution against `U - δ₀`
converges to the forcing integral times the reciprocal extended mean. Infinite mean
gives limit zero; genuine arrivals at zero are retained. -/
theorem tendsto_renewalConv_sub_dirac (hNL : ¬ F.IsLattice)
    {h : ℝ≥0 → ℝ} (hh : Antitone h) (h₀ : ∀ x, 0 ≤ h x)
    (hint : IntegrableOn (fun x : ℝ => h x.toNNReal) (Ioi 0)) :
    Tendsto (renewalConv h (F.renewalMeasure - dirac 0)) atTop
      (𝓝 (((∫⁻ x, (x : ℝ≥0∞) ∂F)⁻¹).toReal *
        ∫ x in Ioi (0 : ℝ), h x.toNNReal)) := by
  exact F.tendsto_renewalConv_sub_dirac_of_tendsto_measureReal_Ioc
    (measure_singleton_zero_lt_one_of_not_isLattice hNL)
    (F.tendsto_renewalMeasure_real_Ioc hNL) hh h₀ hint

/-- **Key renewal theorem.** For nonnegative decreasing integrable forcing and a
nonlattice interarrival law, convolution against the full renewal measure converges
to the forcing integral times the reciprocal extended mean. This includes infinite
mean and interarrival laws with an atom at zero. -/
theorem tendsto_renewalConv (hNL : ¬ F.IsLattice)
    {h : ℝ≥0 → ℝ} (hh : Antitone h) (h₀ : ∀ x, 0 ≤ h x)
    (hint : IntegrableOn (fun x : ℝ => h x.toNNReal) (Ioi 0)) :
    Tendsto (renewalConv h F.renewalMeasure) atTop
      (𝓝 (((∫⁻ x, (x : ℝ≥0∞) ∂F)⁻¹).toReal *
        ∫ x in Ioi (0 : ℝ), h x.toNNReal)) := by
  exact F.tendsto_renewalConv_of_tendsto_measureReal_Ioc
    (measure_singleton_zero_lt_one_of_not_isLattice hNL)
    (F.tendsto_renewalMeasure_real_Ioc hNL) hh h₀ hint

end MeasureTheory.Measure

namespace TauCeti.Probability

/-- **Asymptotics of solutions to the renewal equation.** For a nonlattice probability law `F`
and a nonnegative, nonincreasing, Lebesgue-integrable forcing function `h`, every measurable
solution `g` of `g = h + renewalConv g F` that is bounded on bounded intervals converges as
`t → ∞` to `((∫⁻ x, (x : ℝ≥0∞) ∂F)⁻¹).toReal * ∫ x in Ioi 0, h x.toNNReal`. -/
theorem tendsto_of_eq_add_renewalConv {F : Measure ℝ≥0} [IsProbabilityMeasure F]
    (hNL : ¬ F.IsLattice) {h g : ℝ≥0 → ℝ} (hh : Antitone h) (h₀ : ∀ x, 0 ≤ h x)
    (hint : IntegrableOn (fun x : ℝ => h x.toNNReal) (Ioi 0))
    (hg : Measurable g) (hgb : ∀ t, ∃ C, ∀ s ≤ t, |g s| ≤ C)
    (hgeq : g = h + renewalConv g F) :
    Tendsto g atTop
      (𝓝 (((∫⁻ x, (x : ℝ≥0∞) ∂F)⁻¹).toReal * ∫ x in Ioi (0 : ℝ), h x.toNNReal)) := by
  let : IsLocallyFiniteMeasure F.renewalMeasure :=
    F.isLocallyFiniteMeasure_renewalMeasure
      (Measure.measure_singleton_zero_lt_one_of_not_isLattice hNL)
  have hhb : ∀ t, ∃ C, ∀ s ≤ t, |h s| ≤ C := fun _ =>
    ⟨h 0, fun s _ => by rw [abs_of_nonneg (h₀ s)]; exact hh bot_le⟩
  rw [eq_renewalConv_renewalMeasure hh.measurable hhb hg hgb hgeq]
  exact F.tendsto_renewalConv hNL hh h₀ hint

end TauCeti.Probability
