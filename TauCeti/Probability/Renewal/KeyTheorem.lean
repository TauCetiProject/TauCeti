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
of `F`. The same limit holds after removing the artificial arrival at zero.

The inverse is taken in `ℝ≥0∞` before conversion to `ℝ`, so infinite mean gives
limit zero. An atom of `F` at zero is allowed: removing `dirac 0` removes only the
artificial arrival, not genuine zero-increment arrivals. No continuity of `h` is
required, and both endpoints are retained in the convolution integral.

The nonlattice Blackwell theorem supplies interval limits; the monotone-forcing
transfer theorem supplies the step-function approximation and uniform tail control.
These results apply directly to renewal equations with decreasing forcing, including
excess-life tail probabilities.

## References

* W. Feller, *An Introduction to Probability Theory and Its Applications*, volume II,
  second edition (1971), Chapter XI, the key renewal theorem.
-/

public section

open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal

namespace MeasureTheory.Measure

open TauCeti.Probability

variable (F : Measure ℝ≥0) [IsProbabilityMeasure F]

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
