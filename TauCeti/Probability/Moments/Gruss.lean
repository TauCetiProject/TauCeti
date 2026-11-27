/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Moments.Variance
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Grüss's inequality

For two real random variables bounded almost everywhere in intervals `[m, M]` and `[r, R]`,
Grüss's inequality bounds the absolute covariance by `(M - m) * (R - r) / 4`.
We combine the covariance Cauchy–Schwarz inequality with Popoviciu's variance bound.

## Main results

* `ProbabilityTheory.covariance_sq_le_variance_mul`: the square of the covariance is at most
  the product of the variances, for square-integrable functions on a finite measure space.
* `TauCeti.abs_integral_mul_sub_le`: Grüss's inequality on a probability space.

## References

D. S. Mitrinović, *Analytic Inequalities*, Springer, 1970, §2.13, inequality (1), p. 70.
-/

public section

open MeasureTheory ProbabilityTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → ℝ}

namespace ProbabilityTheory

/-- The covariance Cauchy–Schwarz inequality for square-integrable real functions
on a finite measure space. -/
theorem covariance_sq_le_variance_mul [IsFiniteMeasure μ]
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    covariance f g μ ^ 2 ≤ variance f μ * variance g μ := by
  have hquad : ∀ t : ℝ,
      0 ≤ variance g μ * (t * t) + (2 * covariance f g μ) * t + variance f μ := by
    intro t
    have h := variance_nonneg (fun a ↦ f a + t * g a) μ
    rw [variance_fun_add hf (hg.const_mul t), variance_const_mul, covariance_const_mul_right] at h
    nlinarith only [h]
  have hdisc := discrim_le_zero hquad
  unfold discrim at hdisc
  nlinarith only [hdisc]

end ProbabilityTheory

namespace TauCeti

/-- **Grüss's inequality.** For two real random variables bounded almost everywhere in
intervals, the absolute covariance is at most one quarter of the product of the interval widths. -/
theorem abs_integral_mul_sub_le [IsProbabilityMeasure μ]
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) {m M r R : ℝ}
    (hfb : ∀ᵐ a ∂μ, f a ∈ Set.Icc m M) (hgb : ∀ᵐ a ∂μ, g a ∈ Set.Icc r R) :
    |∫ a, f a * g a ∂μ - (∫ a, f a ∂μ) * ∫ a, g a ∂μ| ≤ (M - m) * (R - r) / 4 := by
  have hf2 := memLp_of_bounded hfb hf 2
  have hg2 := memLp_of_bounded hgb hg 2
  have hmM : m ≤ M := by
    obtain ⟨a, ha⟩ := hfb.exists
    exact ha.1.trans ha.2
  have hrR : r ≤ R := by
    obtain ⟨a, ha⟩ := hgb.exists
    exact ha.1.trans ha.2
  have hcov := covariance_sq_le_variance_mul hf2 hg2
  have hfvar := variance_le_sq_of_bounded hfb hf.aemeasurable
  have hgvar := variance_le_sq_of_bounded hgb hg.aemeasurable
  have hprod := mul_le_mul hfvar hgvar (variance_nonneg g μ) (sq_nonneg ((M - m) / 2))
  change |(∫ a, (f * g) a ∂μ) - (∫ a, f a ∂μ) * ∫ a, g a ∂μ| ≤ _
  rw [← covariance_eq_sub hf2 hg2]
  apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp
  rw [sq_abs]
  nlinarith only [hcov, hprod]

end TauCeti
