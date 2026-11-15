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

For a nonlattice probability measure `F` on `ℝ≥0` with renewal measure `U = F.renewalMeasure` and
rate `r = ((∫⁻ x, (x : ℝ≥0∞) ∂F)⁻¹).toReal`, Smith's key renewal theorem identifies the long-time
limit of convolutions against `U` and against the positive-arrival renewal measure `U - δ₀`: for
every decreasing (`Antitone`) forcing function `h : ℝ≥0 → ℝ` whose extension to `(0, ∞)` is
Lebesgue-integrable,

```text
(h ∗ (U - δ₀)) t ⟶ r * ∫ x in (0, ∞), h x,
(h ∗ U) t        ⟶ r * ∫ x in (0, ∞), h x
```

as `t → ∞` in `ℝ≥0`.

Combining the nonlattice Blackwell interval limit
(`MeasureTheory.Measure.tendsto_renewalMeasure_real_Ioc`) with the monotone-forcing transfer
(`MeasureTheory.Measure.tendsto_renewalConv_of_tendsto_measureReal_Ioc`) establishes these limits
without an extra positivity hypothesis on `h`: any function that is
antitone on `ℝ≥0` and integrable on `(0, ∞)` is automatically nonnegative everywhere
(`Antitone.nonneg_of_integrableOn_Ioi_toNNReal`). Infinite interarrival mean (`r = 0`) and atoms of
`F` at zero (`0 ≤ F {0} < 1`, automatic for nonlattice probability laws) are both included. On a
bounded age cutoff `[0, A)`, neither global monotonicity nor a sign condition is needed
(`MeasureTheory.Measure.tendsto_renewalConv_indicator_Iio`). Finally, uniqueness for the renewal
equation `g = h + g ∗ F` (`TauCeti.Probability.eq_renewalConv_renewalMeasure`) transfers the limit
to any locally bounded measurable solution `g`.

## Main results

* `MeasureTheory.Measure.tendsto_renewalConv_indicator_Iio`: convergence of
  `((Iio A).indicator h) ∗ U` for any `h` antitone on `[0, A]`.
* `MeasureTheory.Measure.tendsto_renewalConv_sub_dirac`: the key renewal theorem for the
  positive-arrival renewal measure `U - δ₀`.
* `MeasureTheory.Measure.tendsto_renewalConv`: the key renewal theorem for the full renewal measure
  `U`.
* `TauCeti.Probability.tendsto_of_eq_add_renewalConv`: asymptotic limit of any locally bounded
  measurable solution `g` of `g = h + g ∗ F` with antitone integrable forcing `h`.

## References

* Walter L. Smith, *Asymptotic renewal theorems*, Proceedings of the Royal Society of Edinburgh,
  Section A 64 (1954), 9–48.
* William Feller, *An Introduction to Probability Theory and Its Applications*, vol. II, second
  edition, Wiley, 1971, Chapter XI, §1 and §4.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace MeasureTheory.Measure

open TauCeti.Probability

/-- **Bounded-cutoff key renewal limit.** For a nonlattice probability measure `F` on `ℝ≥0` and any
forcing `h` that is antitone on `[0, A]`, convolution of `h` cut off to `[0, A)` with
`F.renewalMeasure` converges to the renewal rate times the integral of `h` over `0..A`. Neither a
sign condition nor global integrability of `h` is required, and infinite mean gives limit zero. -/
theorem tendsto_renewalConv_indicator_Iio (F : Measure ℝ≥0) [IsProbabilityMeasure F]
    (hNL : ¬ F.IsLattice) {h : ℝ≥0 → ℝ} (A : ℝ≥0) (hh : AntitoneOn h (Iic A)) :
    Tendsto (renewalConv ((Iio A).indicator h) F.renewalMeasure) atTop
      (𝓝 (((∫⁻ x, (x : ℝ≥0∞) ∂F)⁻¹).toReal * ∫ x in (0 : ℝ)..A, h x.toNNReal)) := by
  let : IsLocallyFiniteMeasure F.renewalMeasure :=
    F.isLocallyFiniteMeasure_renewalMeasure (measure_singleton_zero_lt_one_of_not_isLattice hNL)
  exact F.renewalMeasure.tendsto_renewalConv_indicator_Iio_of_tendsto_measureReal_Ioc
    (F.tendsto_renewalMeasure_real_Ioc hNL) A hh

/-- **Smith's key renewal theorem for positive arrivals.** For a nonlattice probability measure `F`
on `ℝ≥0` and an antitone function `h : ℝ≥0 → ℝ` integrable on `(0, ∞)`, the convolution
`h ∗ (F.renewalMeasure - δ₀)` converges as `t → ∞` to the renewal rate times `∫_{(0, ∞)} h`.
Nonnegativity of `h` is deduced from antitonicity and integrability; infinite mean and genuine zero
increments are allowed. -/
theorem tendsto_renewalConv_sub_dirac (F : Measure ℝ≥0) [IsProbabilityMeasure F]
    (hNL : ¬ F.IsLattice) {h : ℝ≥0 → ℝ} (hh : Antitone h)
    (hint : IntegrableOn (fun x : ℝ => h x.toNNReal) (Ioi 0)) :
    Tendsto (renewalConv h (F.renewalMeasure - dirac 0)) atTop
      (𝓝 (((∫⁻ x, (x : ℝ≥0∞) ∂F)⁻¹).toReal * ∫ x in Ioi (0 : ℝ), h x.toNNReal)) :=
  F.tendsto_renewalConv_sub_dirac_of_tendsto_measureReal_Ioc
    (measure_singleton_zero_lt_one_of_not_isLattice hNL)
    (F.tendsto_renewalMeasure_real_Ioc hNL) hh hint

/-- **Smith's key renewal theorem.** For a nonlattice probability measure `F` on `ℝ≥0` and an
antitone function `h : ℝ≥0 → ℝ` integrable on `(0, ∞)`, the convolution `h ∗ F.renewalMeasure`
converges as `t → ∞` to the renewal rate times `∫_{(0, ∞)} h`. Nonnegativity of `h` follows
automatically from antitonicity and integrability; infinite mean gives limit zero. -/
theorem tendsto_renewalConv (F : Measure ℝ≥0) [IsProbabilityMeasure F]
    (hNL : ¬ F.IsLattice) {h : ℝ≥0 → ℝ} (hh : Antitone h)
    (hint : IntegrableOn (fun x : ℝ => h x.toNNReal) (Ioi 0)) :
    Tendsto (renewalConv h F.renewalMeasure) atTop
      (𝓝 (((∫⁻ x, (x : ℝ≥0∞) ∂F)⁻¹).toReal * ∫ x in Ioi (0 : ℝ), h x.toNNReal)) :=
  F.tendsto_renewalConv_of_tendsto_measureReal_Ioc
    (measure_singleton_zero_lt_one_of_not_isLattice hNL)
    (F.tendsto_renewalMeasure_real_Ioc hNL) hh hint

end MeasureTheory.Measure

namespace TauCeti.Probability

/-- **Asymptotic limit of renewal-equation solutions.** If `F` is a nonlattice probability measure
on `ℝ≥0`, `h : ℝ≥0 → ℝ` is antitone and integrable on `(0, ∞)`, and `g : ℝ≥0 → ℝ` is a measurable
locally bounded solution of `g = h + g ∗ F`, then `g t` converges as `t → ∞` to the renewal rate of
`F` times `∫_{(0, ∞)} h`. -/
theorem tendsto_of_eq_add_renewalConv {F : Measure ℝ≥0} [IsProbabilityMeasure F]
    (hNL : ¬ F.IsLattice) {h g : ℝ≥0 → ℝ} (hh : Antitone h)
    (hint : IntegrableOn (fun x : ℝ => h x.toNNReal) (Ioi 0))
    (hg : Measurable g) (hgb : ∀ t, ∃ C, ∀ s ≤ t, |g s| ≤ C)
    (hgeq : g = h + renewalConv g F) :
    Tendsto g atTop
      (𝓝 (((∫⁻ x, (x : ℝ≥0∞) ∂F)⁻¹).toReal * ∫ x in Ioi (0 : ℝ), h x.toNNReal)) :=
  tendsto_of_eq_add_renewalConv_of_tendsto_measureReal_Ioc
    (Measure.measure_singleton_zero_lt_one_of_not_isLattice hNL)
    (F.tendsto_renewalMeasure_real_Ioc hNL) hh hint hg hgb hgeq

end TauCeti.Probability
