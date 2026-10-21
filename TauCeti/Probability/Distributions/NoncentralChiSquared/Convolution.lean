/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.NoncentralChiSquared.Basic

/-!
# Addition of independent noncentral chi-squared variables

Convolution adds both the nonnegative degrees and the noncentralities. This includes the
degree-zero mixed laws and the Dirac law at zero degree and zero noncentrality. The proof
combines the Poisson mixture with central chi-squared convolution and Poisson convolution.
The independent-sum law makes this construction available for random variables.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2,
  second edition, Wiley, 1995, chapter 29.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal MeasureTheory

namespace TauCeti.Probability

/-- Independent noncentral chi-squared laws add their degrees and noncentralities, including
the degree-zero mixed and Dirac boundaries. -/
theorem noncentralChiSquaredMeasure_conv_noncentralChiSquaredMeasure
    {k₁ k₂ : ℝ} (hk₁ : 0 ≤ k₁) (hk₂ : 0 ≤ k₂) (l₁ l₂ : ℝ≥0) :
    noncentralChiSquaredMeasure k₁ l₁ ∗ noncentralChiSquaredMeasure k₂ l₂ =
      noncentralChiSquaredMeasure (k₁ + k₂) (l₁ + l₂) := by
  have hcentral (n : ℕ) : IsProbabilityMeasure (chiSquaredMeasure (k₂ + 2 * n)) :=
    isProbabilityMeasure_chiSquaredMeasure (by positivity)
  rw [noncentralChiSquaredMeasure_eq_sum hk₁,
    noncentralChiSquaredMeasure_eq_sum hk₂, Measure.conv, Measure.prod_sum,
    Measure.map_sum (by fun_prop)]
  have hcomponent (p : ℕ × ℕ) :
      ((poissonMeasure (l₁ / 2) {p.1} • chiSquaredMeasure (k₁ + 2 * p.1)).prod
        (poissonMeasure (l₂ / 2) {p.2} • chiSquaredMeasure (k₂ + 2 * p.2))).map
          (fun z ↦ z.1 + z.2) =
      (poissonMeasure (l₁ / 2) {p.1} * poissonMeasure (l₂ / 2) {p.2}) •
        chiSquaredMeasure (k₁ + k₂ + 2 * (p.1 + p.2)) := by
    rw [Measure.prod_smul_left, Measure.prod_smul_right,
      Measure.map_smul _ (by fun_prop), Measure.map_smul _ (by fun_prop), smul_smul,
      ← Measure.conv, chiSquaredMeasure_conv_chiSquaredMeasure (by positivity) (by positivity)]
    congr 2
    ring
  simp_rw [hcomponent]
  rw [noncentralChiSquaredMeasure_of_nonneg (add_nonneg hk₁ hk₂), add_div,
    ← poissonMeasure_conv_poissonMeasure, Measure.conv,
    Measure.bind_map (by fun_prop) (.of_discrete)]
  ext s hs
  rw [Measure.sum_apply _ hs, Measure.bind_apply hs (.of_discrete), lintegral_countable']
  apply tsum_congr
  rintro ⟨m, n⟩
  rw [Measure.smul_apply, ← Set.singleton_prod_singleton, Measure.prod_prod]
  simp [Nat.cast_add, mul_comm]

end TauCeti.Probability

namespace ProbabilityTheory.IndepFun

open TauCeti.Probability

/-- The sum of independent noncentral chi-squared variables has the sum of their degrees
and noncentralities. -/
theorem hasLaw_add_noncentralChiSquaredMeasure
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X Y : Ω → ℝ}
    {k₁ k₂ : ℝ} {l₁ l₂ : ℝ≥0} (hXY : IndepFun X Y P)
    (hX : HasLaw X (noncentralChiSquaredMeasure k₁ l₁) P)
    (hY : HasLaw Y (noncentralChiSquaredMeasure k₂ l₂) P)
    (hk₁ : 0 ≤ k₁) (hk₂ : 0 ≤ k₂) :
    HasLaw (X + Y) (noncentralChiSquaredMeasure (k₁ + k₂) (l₁ + l₂)) P := by
  let _ := isProbabilityMeasure_noncentralChiSquaredMeasure hk₁ l₁
  let _ := isProbabilityMeasure_noncentralChiSquaredMeasure hk₂ l₂
  simpa only [noncentralChiSquaredMeasure_conv_noncentralChiSquaredMeasure hk₁ hk₂] using
    hXY.hasLaw_add hX hY

end ProbabilityTheory.IndepFun
