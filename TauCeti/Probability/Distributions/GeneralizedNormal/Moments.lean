/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.GeneralizedNormal.Basic
public import Mathlib.Probability.Moments.Variance
import TauCeti.Probability.Distributions.GeneralizedNormal.Affine

/-!
# Moments of the generalized normal distribution

For a generalized normal law with location `m`, positive scale `s` and positive shape `p`:

* every odd central moment vanishes, by the symmetry of the law about `m`;
* the even central moment of order `n` is `s ^ n * Γ ((n + 1) / p) / Γ (1 / p)`;
* the mean is `m` and the variance is `s ^ 2 * Γ (3 / p) / Γ (1 / p)`.

The even moments specialize the absolute central moments of
`TauCeti.Probability.integral_rpow_abs_sub_generalizedNormalMeasure`. The natural central moments
are integrable at every parameter, since invalid parameters give the zero measure.
-/

public section

open MeasureTheory ProbabilityTheory

namespace TauCeti.Probability

variable {m s p : ℝ}

/-- The natural central moments of a generalized normal law are integrable at every parameter. -/
theorem integrable_pow_sub_generalizedNormalMeasure (m s p : ℝ) (n : ℕ) :
    Integrable (fun x => (x - m) ^ n) (generalizedNormalMeasure m s p) := by
  by_cases h : 0 < s ∧ 0 < p
  · refine (integrable_norm_iff (by fun_prop)).mp ?_
    simp_rw [Real.norm_eq_abs, abs_pow, ← Real.rpow_natCast]
    exact (integrable_rpow_abs_sub_generalizedNormalMeasure_iff h.1 h.2 m).mpr
      (by linarith [n.cast_nonneg (α := ℝ)])
  · rw [generalizedNormalMeasure_of_not_pos h]
    exact integrable_zero_measure

/-- **Odd central moments vanish.** By the symmetry of a generalized normal law about its
location, `E (X - m) ^ n = 0` for odd `n`, at every parameter. -/
theorem integral_pow_sub_generalizedNormalMeasure_of_odd {n : ℕ} (hn : Odd n) (m s p : ℝ) :
    ∫ x, (x - m) ^ n ∂generalizedNormalMeasure m s p = 0 := by
  have h := congrArg (fun μ => ∫ x, (x - m) ^ n ∂μ)
    (generalizedNormalMeasure_map_two_mul_sub m s p)
  rw [integral_map (by fun_prop) (by fun_prop)] at h
  have hneg : ∀ x : ℝ, (2 * m - x - m) ^ n = -(x - m) ^ n := fun x => by
    rw [show 2 * m - x - m = -(x - m) by ring, hn.neg_pow]
  simp_rw [hneg, integral_neg] at h
  linarith

/-- **Even central moments.** For positive scale and shape and even `n`,
`E (X - m) ^ n = s ^ n * Γ ((n + 1) / p) / Γ (1 / p)`. -/
theorem integral_pow_sub_generalizedNormalMeasure_of_even (hs : 0 < s) (hp : 0 < p) {n : ℕ}
    (hn : Even n) (m : ℝ) :
    ∫ x, (x - m) ^ n ∂generalizedNormalMeasure m s p =
      s ^ n * Real.Gamma ((n + 1) / p) / Real.Gamma p⁻¹ := by
  have h := integral_rpow_abs_sub_generalizedNormalMeasure (q := n) hs hp
    (by linarith [n.cast_nonneg (α := ℝ)]) m
  simp_rw [Real.rpow_natCast, hn.pow_abs] at h
  exact h

/-- The identity is integrable against a generalized normal law at every parameter. -/
theorem integrable_id_generalizedNormalMeasure (m s p : ℝ) :
    Integrable id (generalizedNormalMeasure m s p) := by
  refine ((integrable_pow_sub_generalizedNormalMeasure m s p 1).add (integrable_const m)).congr
    (ae_of_all _ fun x => ?_)
  simp

/-- **The mean of a generalized normal law is its location.** -/
theorem integral_id_generalizedNormalMeasure (hs : 0 < s) (hp : 0 < p) (m : ℝ) :
    ∫ x, x ∂generalizedNormalMeasure m s p = m := by
  have := isProbabilityMeasure_generalizedNormalMeasure hs hp m
  have h := integral_pow_sub_generalizedNormalMeasure_of_odd odd_one m s p
  simp only [pow_one] at h
  have hid : Integrable (fun x : ℝ => x) (generalizedNormalMeasure m s p) :=
    integrable_id_generalizedNormalMeasure m s p
  rw [integral_sub hid (integrable_const m),
    integral_const, probReal_univ, one_smul, sub_eq_zero] at h
  exact h

/-- **The variance of a generalized normal law** is `s ^ 2 * Γ (3 / p) / Γ (1 / p)`. -/
theorem variance_id_generalizedNormalMeasure (hs : 0 < s) (hp : 0 < p) (m : ℝ) :
    variance id (generalizedNormalMeasure m s p) =
      s ^ 2 * Real.Gamma (3 / p) / Real.Gamma p⁻¹ := by
  have := isProbabilityMeasure_generalizedNormalMeasure hs hp m
  rw [variance_eq_integral measurable_id.aemeasurable]
  simp only [id_eq]
  rw [integral_id_generalizedNormalMeasure hs hp m,
    integral_pow_sub_generalizedNormalMeasure_of_even hs hp even_two m]
  norm_num

end TauCeti.Probability
