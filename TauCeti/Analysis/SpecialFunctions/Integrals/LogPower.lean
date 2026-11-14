/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-!
# Logarithmic moment integrals on the unit interval

Under the substitution `t = exp (-u)`, the unit interval `(0, 1]` corresponds to the positive
half-line `(0, ∞)` with density `exp (-u)`, and the logarithmic moment
`∫ t in 0..1, t ^ r * (-log t) ^ s` becomes Euler's Gamma integral
`∫ u in Ioi 0, u ^ s * exp (-(r + 1) * u) = Γ(s + 1) / (r + 1) ^ (s + 1)` whenever `r > -1` and
`s > -1`.

Specialising `r` and `s` to natural exponents evaluates `∫ t in 0..1, t ^ m * (-log t) ^ k` as
`k! / (m + 1) ^ (k + 1)`, which supplies the termwise radial moments of the polylogarithm power
series and the value of the radial derivative integral at zero.

## Main declarations

* `TauCeti.integral_zero_one_eq_integral_exp_neg_Ioi`: the substitution `t = exp (-u)` turning
  `∫ t in 0..1, g t` into `∫ u in Ioi 0, exp (-u) • g (exp (-u))`.
* `TauCeti.intervalIntegrable_zero_one_iff_integrableOn_exp_neg_Ioi`: the matching integrability
  equivalence.
* `TauCeti.intervalIntegrable_rpow_mul_neg_log_rpow` and
  `TauCeti.integral_rpow_mul_neg_log_rpow`: integrability and closed form
  `Γ(s + 1) / (r + 1) ^ (s + 1)` for `r > -1` and `s > -1`.
* `TauCeti.integral_pow_mul_neg_log_pow`, `TauCeti.integral_neg_log_pow`, and
  `TauCeti.integral_log_pow`: the natural-exponent specialisations in terms of factorials.
-/

public section

open MeasureTheory Real Set

namespace TauCeti

/-- Substitution `t = exp (-u)` on the unit interval: `∫ t in 0..1, g t` equals the integral of
`exp (-u) • g (exp (-u))` over `(0, ∞)`. -/
theorem integral_zero_one_eq_integral_exp_neg_Ioi {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (g : ℝ → E) :
    ∫ t in (0 : ℝ)..1, g t = ∫ u in Ioi (0 : ℝ), exp (-u) • g (exp (-u)) := by
  rw [intervalIntegral.integral_of_le zero_le_one]
  have himg : exp '' Iic (0 : ℝ) = Ioc 0 1 := by simp
  rw [← himg, integral_image_eq_integral_abs_deriv_smul measurableSet_Iic
    (fun x _ ↦ (hasDerivAt_exp x).hasDerivWithinAt) (fun x _ y _ hxy ↦ exp_injective hxy) g]
  simp only [abs_of_pos (exp_pos _)]
  simpa using (integral_comp_neg_Ioi (0 : ℝ) (fun x ↦ exp x • g (exp x))).symm

/-- Integrability version of the substitution `t = exp (-u)` between `[0, 1]` and `(0, ∞)`. -/
theorem intervalIntegrable_zero_one_iff_integrableOn_exp_neg_Ioi {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (g : ℝ → E) :
    IntervalIntegrable g volume 0 1 ↔
      IntegrableOn (fun u : ℝ ↦ exp (-u) • g (exp (-u))) (Ioi 0) := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  have himg : exp '' Iic (0 : ℝ) = Ioc 0 1 := by simp
  rw [← himg, integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Iic
    (fun x _ ↦ (hasDerivAt_exp x).hasDerivWithinAt) (fun x _ y _ hxy ↦ exp_injective hxy) g]
  simp only [abs_of_pos (exp_pos _)]
  rw [← ((Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
    (Homeomorph.neg ℝ).measurableEmbedding (f := fun x ↦ exp x • g (exp x)) (s := Iic 0))]
  simp_rw [Function.comp_def, neg_preimage, neg_Iic, neg_zero]
  exact integrableOn_Ici_iff_integrableOn_Ioi

/-- For `r > -1` and `s > -1`, the logarithmic moment `t ↦ t ^ r * (-log t) ^ s` is interval
integrable on `[0, 1]`. Both endpoints may be singular when `-1 < r < 0` or `-1 < s < 0`. -/
theorem intervalIntegrable_rpow_mul_neg_log_rpow {r s : ℝ} (hr : -1 < r) (hs : -1 < s) :
    IntervalIntegrable (fun t : ℝ ↦ t ^ r * (-log t) ^ s) volume 0 1 := by
  rw [intervalIntegrable_zero_one_iff_integrableOn_exp_neg_Ioi]
  have hr1 : 0 < r + 1 := by linarith
  have hs1 : 0 < s + 1 := by linarith
  have hgam := Real.GammaIntegral_convergent hs1
  rw [add_sub_cancel_right, ← mul_zero (r + 1),
    ← integrableOn_Ioi_comp_mul_left_iff _ 0 hr1] at hgam
  refine IntegrableOn.congr_fun (hgam.const_mul ((r + 1) ^ (-s)))
    (fun u (hu : 0 < u) ↦ ?_) measurableSet_Ioi
  dsimp only [smul_eq_mul]
  rw [mul_rpow hr1.le hu.le, log_exp, neg_neg, rpow_def_of_pos (exp_pos (-u)), log_exp]
  calc
    (r + 1) ^ (-s) * (exp (-((r + 1) * u)) * ((r + 1) ^ s * u ^ s))
      = ((r + 1) ^ (-s) * (r + 1) ^ s) * (exp (-u + -u * r) * u ^ s) := by
          rw [show -((r + 1) * u) = -u + -u * r by ring]
          ring
    _ = exp (-u) * (exp (-u * r) * u ^ s) := by
          rw [← rpow_add hr1, neg_add_cancel, rpow_zero, one_mul, exp_add, mul_assoc]

/-- Euler's logarithmic moment integral on `(0, 1]`: for `r > -1` and `s > -1`,
`∫ t in 0..1, t ^ r * (-log t) ^ s = Γ(s + 1) / (r + 1) ^ (s + 1)`. -/
theorem integral_rpow_mul_neg_log_rpow {r s : ℝ} (hr : -1 < r) (hs : -1 < s) :
    ∫ t : ℝ in (0 : ℝ)..1, t ^ r * (-log t) ^ s = Gamma (s + 1) / (r + 1) ^ (s + 1) := by
  have hr1 : 0 < r + 1 := by linarith
  have hs1 : 0 < s + 1 := by linarith
  rw [integral_zero_one_eq_integral_exp_neg_Ioi]
  have hcongr : EqOn (fun u : ℝ ↦ exp (-u) • (exp (-u) ^ r * (-log (exp (-u))) ^ s))
      (fun u : ℝ ↦ u ^ (s + 1 - 1) * exp (-((r + 1) * u))) (Ioi 0) := by
    intro u _
    dsimp only [smul_eq_mul]
    rw [log_exp, neg_neg, add_sub_cancel_right, rpow_def_of_pos (exp_pos (-u)), log_exp,
      mul_comm _ (u ^ s), ← mul_assoc, mul_comm (exp (-u)) (u ^ s), mul_assoc, ← exp_add]
    congr 2
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr,
    integral_rpow_mul_exp_neg_mul_Ioi hs1 hr1, one_div, inv_rpow hr1.le, inv_mul_eq_div]

/-- Natural-exponent logarithmic moment on `[0, 1]`:
`∫ t in 0..1, t ^ m * (-log t) ^ k = k! / (m + 1) ^ (k + 1)`. -/
theorem integral_pow_mul_neg_log_pow (m k : ℕ) :
    ∫ t : ℝ in (0 : ℝ)..1, t ^ m * (-log t) ^ k =
      (k.factorial : ℝ) / ((m + 1 : ℝ) ^ (k + 1)) := by
  have h := integral_rpow_mul_neg_log_rpow (r := (m : ℝ)) (s := (k : ℝ))
    (by linarith [m.cast_nonneg (α := ℝ)]) (by linarith [k.cast_nonneg (α := ℝ)])
  rw [Gamma_nat_eq_factorial, show ((k : ℝ) + 1) = ((k + 1 : ℕ) : ℝ) by push_cast; ring,
    rpow_natCast] at h
  refine (intervalIntegral.integral_congr fun t _ ↦ ?_).trans h
  rw [rpow_natCast, rpow_natCast]

/-- Unweighted logarithmic moment on `[0, 1]`: `∫ t in 0..1, (-log t) ^ k = k!`. -/
@[simp] theorem integral_neg_log_pow (k : ℕ) :
    ∫ t : ℝ in (0 : ℝ)..1, (-log t) ^ k = (k.factorial : ℝ) := by
  simpa using integral_pow_mul_neg_log_pow 0 k

/-- Signed logarithmic moment on `[0, 1]`: `∫ t in 0..1, (log t) ^ k = (-1) ^ k * k!`. -/
theorem integral_log_pow (k : ℕ) :
    ∫ t : ℝ in (0 : ℝ)..1, log t ^ k = (-1 : ℝ) ^ k * (k.factorial : ℝ) := by
  have h : (fun t : ℝ ↦ log t ^ k) = fun t : ℝ ↦ (-1 : ℝ) ^ k * (-log t) ^ k := by
    ext t
    rw [← mul_pow, neg_one_mul, neg_neg]
  rw [h, intervalIntegral.integral_const_mul, integral_neg_log_pow]

end TauCeti
