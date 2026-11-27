/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Gaussian.Moments

/-!
# Observable formulas for real Gaussian random variables

This file transfers the elementary observable formulas for `ProbabilityTheory.gaussianReal` to
random variables carrying that law. It gives expectation, variance, the exact exponential-
integrability domain, the characteristic function of the image law, integrability of every
centered natural power, and the absolute, even, and odd centered moment formulas.

The measure-level formulas remain in `TauCeti.Probability.Distributions.Gaussian.Moments`; the
declarations here are the `ProbabilityTheory.HasLaw` interface used when a random variable, rather
than its distribution, is the input.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 1, 2nd ed.,
  Wiley (1994), ch. 13.
-/

public section

open MeasureTheory
open scoped ENNReal Nat NNReal Real

namespace ProbabilityTheory.HasLaw

open TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ} {m : ℝ} {v : ℝ≥0}

/-- A real Gaussian random variable is integrable. -/
theorem integrable_gaussianReal (hX : HasLaw X (gaussianReal m v) P) : Integrable X P :=
  hX.integrable ((memLp_id_gaussianReal' 1 (by simp)).integrable le_rfl)

/-- The expectation of a real Gaussian random variable is its mean parameter. -/
theorem integral_gaussianReal (hX : HasLaw X (gaussianReal m v) P) :
    ∫ ω, X ω ∂P = m := by
  rw [hX.integral_eq, integral_id_gaussianReal]

/-- The variance of a real Gaussian random variable is its variance parameter. -/
theorem variance_gaussianReal (hX : HasLaw X (gaussianReal m v) P) :
    variance X P = v := by
  rw [hX.variance_eq, variance_id_gaussianReal]

/-- Every real exponential moment of a real Gaussian random variable is integrable. -/
theorem integrable_exp_mul_gaussianReal (hX : HasLaw X (gaussianReal m v) P) (t : ℝ) :
    Integrable (fun ω ↦ Real.exp (t * X ω)) P := by
  simpa only [Function.comp_def] using
    hX.integrable_comp (ProbabilityTheory.integrable_exp_mul_gaussianReal t)

/-- The exact exponential-integrability domain of a real Gaussian random variable is all of the
real line. -/
theorem integrableExpSet_gaussianReal (hX : HasLaw X (gaussianReal m v) P) :
    integrableExpSet X P = Set.univ := by
  ext t
  simp only [integrableExpSet, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  exact hX.integrable_exp_mul_gaussianReal t

/-- The characteristic function of the image law of a real Gaussian random variable. -/
theorem charFun_map_gaussianReal (hX : HasLaw X (gaussianReal m v) P) (t : ℝ) :
    charFun (P.map X) t = Complex.exp (t * m * Complex.I - v * t ^ 2 / 2) := by
  rw [hX.map_eq, ProbabilityTheory.charFun_gaussianReal]

/-- Every natural power of the absolute deviation of a real Gaussian random variable from its
mean is integrable. -/
theorem integrable_abs_sub_pow_gaussianReal (hX : HasLaw X (gaussianReal m v) P) (n : ℕ) :
    Integrable (fun ω ↦ |X ω - m| ^ n) P := by
  let _ : IsProbabilityMeasure P := hX.isProbabilityMeasure
  have hmem : MemLp (fun ω ↦ X ω - m) (n : ℝ≥0∞) P :=
    (ProbabilityTheory.gaussianReal_sub_const hX m).memLp
      (memLp_id_gaussianReal' (n : ℝ≥0∞) (by simp))
  simpa only [Real.norm_eq_abs] using hmem.integrable_norm_pow'

/-- The absolute centered moments of a real Gaussian random variable. -/
theorem integral_abs_sub_pow_gaussianReal (hX : HasLaw X (gaussianReal m v) P) (n : ℕ) :
    ∫ ω, |X ω - m| ^ n ∂P =
      (2 * (v : ℝ)) ^ ((n : ℝ) / 2) * Real.Gamma (((n : ℝ) + 1) / 2) / √Real.pi := by
  rw [← Function.comp_def (f := fun x : ℝ ↦ |x - m| ^ n),
    hX.integral_comp (by fun_prop),
    TauCeti.Probability.integral_abs_sub_pow_gaussianReal]

/-- The mean absolute value of a centered real Gaussian random variable. -/
theorem integral_abs_gaussianReal (hX : HasLaw X (gaussianReal 0 v) P) :
    ∫ ω, |X ω| ∂P = √(2 * v / Real.pi) := by
  rw [← Function.comp_def (f := fun x : ℝ ↦ |x|), hX.integral_comp (by fun_prop),
    TauCeti.Probability.integral_abs_gaussianReal]

/-- Every natural power of the deviation of a real Gaussian random variable from its mean is
integrable. -/
theorem integrable_sub_pow_gaussianReal (hX : HasLaw X (gaussianReal m v) P) (n : ℕ) :
    Integrable (fun ω ↦ (X ω - m) ^ n) P := by
  rw [← integrable_norm_iff
    ((hX.aemeasurable.sub_const m).pow_const n).aestronglyMeasurable]
  simpa only [Real.norm_eq_abs, norm_pow] using hX.integrable_abs_sub_pow_gaussianReal n

/-- The even centered moments of a real Gaussian random variable. -/
theorem integral_sub_pow_two_mul_gaussianReal
    (hX : HasLaw X (gaussianReal m v) P) (n : ℕ) :
    ∫ ω, (X ω - m) ^ (2 * n) ∂P = (v : ℝ) ^ n * (2 * n - 1 : ℕ)‼ := by
  rw [← Function.comp_def (f := fun x : ℝ ↦ (x - m) ^ (2 * n)),
    hX.integral_comp (by fun_prop),
    TauCeti.Probability.integral_sub_pow_two_mul_gaussianReal]

/-- The even central moments of a real Gaussian random variable. -/
theorem centralMoment_two_mul_gaussianReal
    (hX : HasLaw X (gaussianReal m v) P) (n : ℕ) :
    centralMoment X (2 * n) P = (v : ℝ) ^ n * (2 * n - 1 : ℕ)‼ := by
  rw [centralMoment, hX.integral_gaussianReal]
  exact hX.integral_sub_pow_two_mul_gaussianReal n

/-- The second raw moment of a real Gaussian random variable. -/
theorem integral_sq_gaussianReal (hX : HasLaw X (gaussianReal m v) P) :
    ∫ ω, X ω ^ 2 ∂P = v + m ^ 2 := by
  rw [← Function.comp_def (f := fun x : ℝ ↦ x ^ 2), hX.integral_comp (by fun_prop),
    TauCeti.Probability.integral_sq_gaussianReal]

/-- The fourth centered moment of a real Gaussian random variable. -/
theorem integral_sub_pow_four_gaussianReal (hX : HasLaw X (gaussianReal m v) P) :
    ∫ ω, (X ω - m) ^ 4 ∂P = 3 * (v : ℝ) ^ 2 := by
  rw [← Function.comp_def (f := fun x : ℝ ↦ (x - m) ^ 4),
    hX.integral_comp (by fun_prop),
    TauCeti.Probability.integral_sub_pow_four_gaussianReal]

/-- The odd centered moments of a real Gaussian random variable vanish. -/
theorem integral_sub_pow_two_mul_add_one_gaussianReal
    (hX : HasLaw X (gaussianReal m v) P) (n : ℕ) :
    ∫ ω, (X ω - m) ^ (2 * n + 1) ∂P = 0 := by
  rw [← Function.comp_def (f := fun x : ℝ ↦ (x - m) ^ (2 * n + 1)),
    hX.integral_comp (by fun_prop),
    TauCeti.Probability.integral_sub_pow_two_mul_add_one_gaussianReal]

/-- The odd central moments of a real Gaussian random variable vanish. -/
theorem centralMoment_two_mul_add_one_gaussianReal
    (hX : HasLaw X (gaussianReal m v) P) (n : ℕ) :
    centralMoment X (2 * n + 1) P = 0 := by
  rw [centralMoment, hX.integral_gaussianReal]
  exact hX.integral_sub_pow_two_mul_add_one_gaussianReal n

end ProbabilityTheory.HasLaw
