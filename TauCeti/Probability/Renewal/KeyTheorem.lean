/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Renewal.IntervalLimit
public import TauCeti.Probability.Renewal.Lattice.Basic
import TauCeti.Probability.Renewal.Blackwell

/-!
# The key renewal theorem

For a nonlattice probability measure `F` on the nonnegative half-line and a nonnegative,
nonincreasing, Lebesgue-integrable forcing function `h : ℝ≥0 → ℝ`, the convolution of `h` with
the positive-arrival renewal measure `U - δ₀` converges at infinity to the renewal rate times
the improper Lebesgue integral of `h`:

```text
(h ∗ (U - δ₀)) t ⟶ (𝔼[T₁])⁻¹ · ∫_{(0, ∞)} h(s) ds.
```

Because `h` is nonnegative, nonincreasing, and integrable, `h t → 0` as `t → ∞`, so the full
renewal convolution `(h ∗ U) t` has the same limit. Consequently, every measurable, locally
bounded solution `g` of the renewal equation `g = h + g ∗ F` converges to the same limit.

The reciprocal extended mean is taken in `ℝ≥0∞` before converting to `ℝ`, so infinite mean gives
limit zero without separate casework. Atoms of `F` at zero are permitted: nonlattice probability
measures automatically satisfy `F {0} < 1`, so `U` is locally finite.

For a forcing function that is merely nonincreasing up to a finite age cutoff `A`, without any
sign or global integrability assumption, convolution of its truncation `(Iio A).indicator h` with
`U` converges to the renewal rate times `∫ x in 0..A, h x.toNNReal`.

## Main statements

* `MeasureTheory.Measure.tendsto_renewalConv_indicator_Iio`: bounded-age monotone forcing limit
  for nonlattice interarrival laws.
* `MeasureTheory.Measure.tendsto_renewalConv_sub_dirac`: **the key renewal theorem** for the
  positive-arrival measure `U - δ₀`.
* `MeasureTheory.Measure.tendsto_renewalConv`: **the key renewal theorem** for the full renewal
  measure `U`.
* `TauCeti.Probability.tendsto_of_eq_add_renewalConv`: convergence at infinity of measurable,
  locally bounded solutions of `g = h + g ∗ F`.

## References

* William Feller, *An Introduction to Probability Theory and Its Applications*, vol. II, 2nd
  edition, Wiley, 1971, Chapter XI, §1, Key Renewal Theorem.
* Vincent Tassion, *Applied Stochastic Processes*, lecture notes, ETH Zürich, 2025, Chapter 6.
-/

public section

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace MeasureTheory.Measure

open TauCeti.Probability

variable (F : Measure ℝ≥0) [IsProbabilityMeasure F]

/-- For a nonlattice interarrival law `F` and a forcing function `h` that is nonincreasing on
`[0, A]`, convolution of `(Iio A).indicator h` with `F.renewalMeasure` converges to the renewal
rate times `∫ x in 0..A, h x.toNNReal`. Neither positivity nor global integrability of `h` is
required, and infinite mean gives limit zero. -/
theorem tendsto_renewalConv_indicator_Iio (hNL : ¬ F.IsLattice)
    {h : ℝ≥0 → ℝ} (A : ℝ≥0) (hh : AntitoneOn h (Iic A)) :
    Tendsto (renewalConv ((Iio A).indicator h) F.renewalMeasure) atTop
      (𝓝 (((∫⁻ x, (x : ℝ≥0∞) ∂F)⁻¹).toReal * ∫ x in (0 : ℝ)..A, h x.toNNReal)) := by
  let : IsLocallyFiniteMeasure F.renewalMeasure :=
    F.isLocallyFiniteMeasure_renewalMeasure
      (measure_singleton_zero_lt_one_of_not_isLattice hNL)
  exact F.renewalMeasure.tendsto_renewalConv_indicator_Iio_of_tendsto_measureReal_Ioc
    (F.tendsto_renewalMeasure_real_Ioc hNL) A hh

/-- **The key renewal theorem for `U - δ₀`.** For a nonlattice probability measure `F` on `ℝ≥0`
and a nonnegative, nonincreasing, Lebesgue-integrable forcing function `h : ℝ≥0 → ℝ`, the
convolution of `h` with the positive-arrival measure `F.renewalMeasure - dirac 0` converges at
infinity to `((∫⁻ x, (x : ℝ≥0∞) ∂F)⁻¹).toReal * ∫ x in Ioi 0, h x.toNNReal`. Zero increments and
infinite mean are permitted. -/
theorem tendsto_renewalConv_sub_dirac (hNL : ¬ F.IsLattice)
    {h : ℝ≥0 → ℝ} (hh : Antitone h) (h₀ : ∀ x, 0 ≤ h x)
    (hint : IntegrableOn (fun x : ℝ => h x.toNNReal) (Ioi 0)) :
    Tendsto (renewalConv h (F.renewalMeasure - dirac 0)) atTop
      (𝓝 (((∫⁻ x, (x : ℝ≥0∞) ∂F)⁻¹).toReal * ∫ x in Ioi (0 : ℝ), h x.toNNReal)) :=
  F.tendsto_renewalConv_sub_dirac_of_tendsto_measureReal_Ioc
    (measure_singleton_zero_lt_one_of_not_isLattice hNL)
    (F.tendsto_renewalMeasure_real_Ioc hNL) hh h₀ hint

/-- **The key renewal theorem.** For a nonlattice probability measure `F` on `ℝ≥0` and a
nonnegative, nonincreasing, Lebesgue-integrable forcing function `h : ℝ≥0 → ℝ`, the convolution of
`h` with `F.renewalMeasure` converges at infinity to
`((∫⁻ x, (x : ℝ≥0∞) ∂F)⁻¹).toReal * ∫ x in Ioi 0, h x.toNNReal`. Zero increments and infinite
mean are permitted. -/
theorem tendsto_renewalConv (hNL : ¬ F.IsLattice)
    {h : ℝ≥0 → ℝ} (hh : Antitone h) (h₀ : ∀ x, 0 ≤ h x)
    (hint : IntegrableOn (fun x : ℝ => h x.toNNReal) (Ioi 0)) :
    Tendsto (renewalConv h F.renewalMeasure) atTop
      (𝓝 (((∫⁻ x, (x : ℝ≥0∞) ∂F)⁻¹).toReal * ∫ x in Ioi (0 : ℝ), h x.toNNReal)) :=
  F.tendsto_renewalConv_of_tendsto_measureReal_Ioc
    (measure_singleton_zero_lt_one_of_not_isLattice hNL)
    (F.tendsto_renewalMeasure_real_Ioc hNL) hh h₀ hint

end MeasureTheory.Measure

namespace TauCeti.Probability

/-- **Asymptotics of renewal-equation solutions.** Let `F` be a nonlattice probability measure on
`ℝ≥0` and `h : ℝ≥0 → ℝ` be nonnegative, nonincreasing, and Lebesgue-integrable. Every measurable,
locally bounded solution `g` of `g = h + g ∗ F` converges as `t → ∞` to the renewal rate times
`∫ x in Ioi 0, h x.toNNReal`. -/
theorem tendsto_of_eq_add_renewalConv {F : Measure ℝ≥0} [IsProbabilityMeasure F]
    (hNL : ¬ F.IsLattice) {h g : ℝ≥0 → ℝ}
    (hh : Antitone h) (h₀ : ∀ x, 0 ≤ h x)
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
