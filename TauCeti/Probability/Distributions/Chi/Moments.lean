/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Chi.Basic

/-!
# Moments of chi laws

Real powers of a positive-degree chi variable have finite expectation exactly above minus its
degrees of freedom. In particular, all natural moments exist. This file computes these moments,
the mean and variance, and proves finiteness of every exponential moment, without asserting a
closed form for the moment-generating function. Degree zero is handled by its Dirac law.

The real-power formulas follow from Gamma moments through the defining square-root pushforward.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 1,
  second edition, Wiley, 1994, chapter 18.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set

namespace TauCeti.Probability

variable {k s q t : ℝ}

private theorem mul_sqrt_rpow_ae_eq_gammaMeasure (hs : 0 < s) (q : ℝ) :
    (fun x : ℝ ↦ (s * √x) ^ q) =ᵐ[gammaMeasure (k / 2) (1 / 2)]
      fun x ↦ s ^ q * x ^ (q / 2) := by
  filter_upwards [ae_pos_gammaMeasure (k / 2) (1 / 2)] with x hx
  rw [mul_rpow hs.le (sqrt_nonneg x), ← rpow_div_two_eq_sqrt q hx.le]

/-- A real power is integrable under a positive-degree chi law exactly above minus its degree. -/
@[simp]
theorem integrable_rpow_chiMeasure_iff (hk : 0 < k) (hs : 0 < s) (q : ℝ) :
    Integrable (fun x : ℝ ↦ x ^ q) (chiMeasure k s) ↔ -k < q := by
  rw [chiMeasure_eq_map_gammaMeasure hk hs,
    integrable_map_measure (by fun_prop) (by fun_prop)]
  simp only [Function.comp_def]
  rw [integrable_congr (mul_sqrt_rpow_ae_eq_gammaMeasure hs q),
    integrable_const_mul_iff (isUnit_iff_ne_zero.2 (rpow_pos_of_pos hs q).ne'),
    integrable_rpow_gammaMeasure_iff (half_pos hk) one_half_pos]
  constructor <;> intro h <;> linarith

/-- Real-power moments of a chi law on their exact domain of integrability. -/
theorem integral_rpow_chiMeasure (hk : 0 < k) (hs : 0 < s) (hq : -k < q) :
    ∫ x, x ^ q ∂chiMeasure k s =
      s ^ q * (2 : ℝ) ^ (q / 2) * Real.Gamma ((k + q) / 2) / Real.Gamma (k / 2) := by
  rw [chiMeasure_eq_map_gammaMeasure hk hs,
    integral_map (by fun_prop) (by fun_prop)]
  rw [integral_congr_ae (mul_sqrt_rpow_ae_eq_gammaMeasure hs q), integral_const_mul,
    integral_rpow_gammaMeasure (half_pos hk) one_half_pos (by linarith : -(k / 2) < q / 2)]
  simp only [rpow_neg_eq_inv_rpow, inv_div, div_one]
  rw [show k / 2 + q / 2 = (k + q) / 2 by ring]
  ring

/-- Every natural power is integrable under a chi law, including its Dirac and zero regimes. -/
theorem integrable_pow_chiMeasure (k s : ℝ) (n : ℕ) :
    Integrable (fun x : ℝ ↦ x ^ n) (chiMeasure k s) := by
  by_cases hs : 0 < s
  · rcases lt_trichotomy k 0 with hk | rfl | hk
    · simp [chiMeasure_of_neg hk]
    · rw [chiMeasure_zero hs]
      exact integrable_dirac (by simp)
    · simpa only [rpow_natCast] using
        (integrable_rpow_chiMeasure_iff hk hs (n : ℝ)).2 (by
          linarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n])
  · simp [chiMeasure_of_scale_nonpos (le_of_not_gt hs)]

/-- At degree zero and positive scale, the zeroth chi moment is one and all others vanish. -/
theorem integral_pow_chiMeasure_zero (hs : 0 < s) (n : ℕ) :
    ∫ x, x ^ n ∂chiMeasure 0 s = if n = 0 then 1 else 0 := by
  rw [chiMeasure_zero hs, integral_dirac, zero_pow_eq]

/-- Natural moments of positive-degree chi laws. -/
@[simp]
theorem integral_pow_chiMeasure (hk : 0 < k) (hs : 0 < s) (n : ℕ) :
    ∫ x, x ^ n ∂chiMeasure k s =
      s ^ n * (2 : ℝ) ^ ((n : ℝ) / 2) * Real.Gamma ((k + n) / 2) /
        Real.Gamma (k / 2) := by
  simpa only [rpow_natCast] using
    integral_rpow_chiMeasure hk hs (q := (n : ℝ)) (by
      linarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n])

/-- The chi mean at nonnegative degrees and positive scale, including degree zero. -/
@[simp]
theorem integral_id_chiMeasure (hk : 0 ≤ k) (hs : 0 < s) :
    ∫ x, x ∂chiMeasure k s =
      s * √2 * Real.Gamma ((k + 1) / 2) / Real.Gamma (k / 2) := by
  rcases hk.eq_or_lt' with rfl | hk
  · simp [chiMeasure_zero hs]
  · simpa only [pow_one, Nat.cast_one, ← sqrt_eq_rpow] using integral_pow_chiMeasure hk hs 1

/-- The second chi moment is scale squared times degrees, including degree zero. -/
@[simp high]
theorem integral_sq_chiMeasure (hk : 0 ≤ k) (hs : 0 < s) :
    ∫ x, x ^ 2 ∂chiMeasure k s = s ^ 2 * k := by
  let _ := isProbabilityMeasure_chiMeasure hk hs
  have h := congrArg (fun μ : Measure ℝ ↦ ∫ x, x ∂μ) (chiMeasure_map_sq (k := k) hs)
  rw [integral_map (by fun_prop) (by fun_prop),
    integral_map (by fun_prop) (by fun_prop), integral_const_mul,
    integral_id_chiSquaredMeasure hk] at h
  exact h

/-- The chi variance at nonnegative degrees and positive scale, including degree zero. -/
@[simp]
theorem variance_id_chiMeasure (hk : 0 ≤ k) (hs : 0 < s) :
    variance id (chiMeasure k s) =
      s ^ 2 * (k - 2 * (Real.Gamma ((k + 1) / 2) / Real.Gamma (k / 2)) ^ 2) := by
  let _ := isProbabilityMeasure_chiMeasure hk hs
  have hLp : MemLp id 2 (chiMeasure k s) :=
    (memLp_two_iff_integrable_sq aestronglyMeasurable_id).2 (integrable_pow_chiMeasure k s 2)
  rw [variance_eq_sub hLp]
  simp only [Pi.pow_apply, id_eq, integral_sq_chiMeasure hk hs, integral_id_chiMeasure hk hs]
  rw [div_pow, mul_pow, mul_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring

/-- Every exponential moment of a chi law is integrable in every parameter regime. -/
theorem integrable_exp_mul_id_chiMeasure (k s t : ℝ) :
    Integrable (fun x : ℝ ↦ exp (t * x)) (chiMeasure k s) := by
  by_cases hs : 0 < s
  swap
  · simp [chiMeasure_of_scale_nonpos (le_of_not_gt hs)]
  rcases lt_trichotomy k 0 with hk | rfl | hk
  · simp [chiMeasure_of_neg hk]
  · rw [chiMeasure_zero hs]
    exact integrable_dirac (by simp)
  · rw [chiMeasure_eq_map_gammaMeasure hk hs,
      integrable_map_measure (by fun_prop) (by fun_prop)]
    simp only [Function.comp_def]
    have hdom := (integrable_exp_mul_id_gammaMeasure (half_pos hk) one_half_pos
      (t := 1 / 4) (by norm_num)).const_mul (exp ((t * s) ^ 2))
    apply hdom.mono' (by fun_prop)
    filter_upwards [ae_pos_gammaMeasure (k / 2) (1 / 2)] with x hx
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _), ← exp_add]
    apply exp_le_exp.2
    have hsq := sq_nonneg (t * s - √x / 2)
    have hsqrt := sq_sqrt hx.le
    nlinarith

/-- The exact exponential-integrability domain of every chi law is the whole real line. -/
@[simp]
theorem integrableExpSet_id_chiMeasure (k s : ℝ) :
    integrableExpSet id (chiMeasure k s) = univ := by
  ext t
  simp only [integrableExpSet, id_eq, mem_ofPred_eq, mem_univ, iff_true]
  exact integrable_exp_mul_id_chiMeasure k s t

end TauCeti.Probability
