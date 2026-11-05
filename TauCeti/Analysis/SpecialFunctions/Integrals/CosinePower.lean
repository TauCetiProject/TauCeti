/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Beta
public import TauCeti.MeasureTheory.Integral.RpowLaplace
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Power-weighted cosine integrals

This file evaluates the singular half-line integral

`∫ x in (0, ∞), x ^ (-(q + 1)) * (1 - cos (t * x))`.

For `0 < q < 2`, the quadratic cancellation of `1 - cos (t * x)` at zero and the negative
power at infinity make this integral finite. Writing the negative power as a Gamma mixture of
exponentials reduces its value to Euler's second beta integral.

## Main results

* `TauCeti.integrableOn_rpow_neg_mul_one_sub_cos`: integrability for `0 < q < 2`;
* `TauCeti.integrableOn_exp_neg_mul_mul_cos`: integrability of the cosine Laplace transform;
* `TauCeti.integral_Ioi_exp_neg_mul_mul_cos`: the cosine Laplace transform;
* `TauCeti.integral_Ioi_exp_neg_mul_mul_one_sub_cos`: the Laplace transform of the cosine
  difference;
* `TauCeti.integral_Ioi_rpow_neg_mul_one_sub_cos`: the closed form of the power-weighted
  cosine integral.
-/

public section

noncomputable section

open MeasureTheory Real Set

namespace TauCeti

/-- For `0 < q < 2`, the quadratic cancellation of `1 - cos (t x)` at zero makes the
power-weighted cosine difference integrable on the positive half-line. -/
theorem integrableOn_rpow_neg_mul_one_sub_cos {q t : ℝ} (hq : 0 < q) (hq2 : q < 2) :
    IntegrableOn (fun x : ℝ ↦ x ^ (-(q + 1)) * (1 - cos (t * x))) (Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one : (0 : ℝ) ≤ 1)]
  apply IntegrableOn.union
  · have hpow : IntegrableOn (fun x : ℝ ↦ x ^ (1 - q)) (Ioc 0 1) := by
      rw [integrableOn_Ioc_iff_integrableOn_Ioo]
      exact (intervalIntegral.integrableOn_Ioo_rpow_iff one_pos).2 (by linarith)
    refine (hpow.const_mul (t ^ 2 / 2)).mono' (by fun_prop) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have hx0 : 0 < x := hx.1
    have hcos0 : 0 ≤ 1 - cos (t * x) := sub_nonneg.mpr (cos_le_one _)
    have hcos : 1 - cos (t * x) ≤ (t * x) ^ 2 / 2 := by
      linarith [Real.one_sub_sq_div_two_le_cos (x := t * x)]
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hx0.le _) hcos0)]
    calc
      x ^ (-(q + 1)) * (1 - cos (t * x))
          ≤ x ^ (-(q + 1)) * ((t * x) ^ 2 / 2) :=
            mul_le_mul_of_nonneg_left hcos (Real.rpow_nonneg hx0.le _)
      _ = t ^ 2 / 2 * x ^ (1 - q) := by
        rw [mul_pow]
        have hmul : x ^ (-(q + 1)) * (t ^ 2 * x ^ 2 / 2) =
            t ^ 2 / 2 * (x ^ (-(q + 1)) * x ^ 2) := by ring
        rw [hmul, ← Real.rpow_natCast x 2, ← Real.rpow_add hx0]
        congr 2
        ring
  · have hpow : IntegrableOn (fun x : ℝ ↦ x ^ (-(q + 1))) (Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) one_pos
    refine (hpow.const_mul 2).mono' (by fun_prop) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 < x := zero_lt_one.trans hx
    have hcos0 : 0 ≤ 1 - cos (t * x) := sub_nonneg.mpr (cos_le_one _)
    have hcos2 : 1 - cos (t * x) ≤ 2 := by linarith [neg_one_le_cos (t * x)]
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hx0.le _) hcos0)]
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hcos2 (Real.rpow_nonneg hx0.le (-(q + 1)))

/-- The exponentially damped cosine is integrable on the positive half-line. -/
theorem integrableOn_exp_neg_mul_mul_cos {s : ℝ} (hs : 0 < s) (t : ℝ) :
    IntegrableOn (fun x : ℝ ↦ exp (-(x * s)) * cos (t * x)) (Ioi 0) := by
  have hexp : IntegrableOn (fun x : ℝ ↦ exp (-(x * s))) (Ioi 0) := by
    simpa [neg_mul, mul_comm] using integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hs) 0
  refine hexp.mono' (by fun_prop) ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_mul, abs_exp, mul_le_iff_le_one_right (exp_pos _)]
  exact abs_cos_le_one _

/-- The Laplace transform of the cosine is
`∫ x in (0, ∞), exp (-s x) cos (t x) = s / (s² + t²)`. -/
theorem integral_Ioi_exp_neg_mul_mul_cos {s : ℝ} (hs : 0 < s) (t : ℝ) :
    ∫ x in Ioi (0 : ℝ), exp (-(x * s)) * cos (t * x) = s / (s ^ 2 + t ^ 2) := by
  have hcomp : IntegrableOn (fun x : ℝ ↦ exp (-(x * s)) •
      (Complex.exp ((t * x : ℝ) * Complex.I) - 1 - (t * sin x : ℝ) * Complex.I))
      (Ioi 0) := by
    have hexp : IntegrableOn (fun x : ℝ ↦ exp (-(x * s))) (Ioi 0) := by
      simpa [neg_mul, mul_comm] using integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hs) 0
    refine (hexp.const_mul (2 + |t|)).mono' (by fun_prop) ?_
    filter_upwards with x
    rw [norm_smul, Real.norm_eq_abs, abs_exp]
    calc
      exp (-(x * s)) * ‖Complex.exp ((t * x : ℝ) * Complex.I) - 1 -
          (t * sin x : ℝ) * Complex.I‖ ≤ exp (-(x * s)) * (2 + |t|) := by
            gcongr
            calc
              _ ≤ ‖Complex.exp ((t * x : ℝ) * Complex.I)‖ + ‖(1 : ℂ)‖ +
                  ‖(t * sin x : ℝ) * Complex.I‖ := by
                grw [norm_sub_le, norm_sub_le]
              _ ≤ 2 + |t| := by
                simp only [Complex.norm_exp, Complex.mul_re, Complex.ofReal_re,
                  Complex.I_re, Complex.ofReal_im, Complex.I_im, mul_zero, mul_one,
                  sub_zero, exp_zero, norm_one, norm_mul, Complex.norm_real, Complex.norm_I,
                  mul_one]
                have hbound := mul_le_mul_of_nonneg_left (abs_sin_le_one x) (abs_nonneg t)
                simp only [Real.norm_eq_abs]
                linarith
      _ = (2 + |t|) * exp (-(x * s)) := by ring
  have hreal0 := congrArg Complex.re
    (integral_Ioi_exp_neg_mul_smul_cexp_sub_one_sub_sin hs t)
  have hreal := (integral_re hcomp).trans hreal0
  have hfun : (fun x : ℝ ↦ RCLike.re (exp (-(x * s)) •
      (Complex.exp ((t * x : ℝ) * Complex.I) - 1 - (t * sin x : ℝ) * Complex.I))) =
      fun x : ℝ ↦ exp (-(x * s)) * (cos (t * x) - 1) := by
    funext x
    rw [Complex.real_smul]
    have hkernel : (Complex.exp ((t * x : ℝ) * Complex.I) - 1 -
        (t * sin x : ℝ) * Complex.I).re = cos (t * x) - 1 := by
      simp [Complex.exp_re, Complex.mul_re, Complex.mul_im, mul_comm]
    change ((exp (-(x * s)) : ℂ) * (Complex.exp ((t * x : ℝ) * Complex.I) - 1 -
      (t * sin x : ℝ) * Complex.I)).re = exp (-(x * s)) * (cos (t * x) - 1)
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, hkernel]
  rw [hfun] at hreal
  have hdiff : ∫ x in Ioi (0 : ℝ), exp (-(x * s)) * (cos (t * x) - 1) =
      s / (s ^ 2 + t ^ 2) - s⁻¹ := by
    simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, mul_one, add_zero] using hreal
  have hexp : IntegrableOn (fun x : ℝ ↦ exp (-(x * s))) (Ioi 0) := by
    simpa [neg_mul, mul_comm] using integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hs) 0
  have hcos := integrableOn_exp_neg_mul_mul_cos hs t
  have hexp_value := integral_exp_mul_Ioi (a := -s) (neg_lt_zero.mpr hs) 0
  have hexp_value' : ∫ x in Ioi (0 : ℝ), exp (-(x * s)) = s⁻¹ := by
    simpa [mul_comm, hs.ne'] using hexp_value
  have hdiff' : (∫ x in Ioi (0 : ℝ), exp (-(x * s)) * cos (t * x)) -
      ∫ x in Ioi (0 : ℝ), exp (-(x * s)) = s / (s ^ 2 + t ^ 2) - s⁻¹ := by
    rw [← integral_sub hcos hexp]
    simpa [mul_sub] using hdiff
  rw [hexp_value'] at hdiff'
  linarith

/-- The Laplace transform of the cosine difference is
`∫ x in (0, ∞), exp (-s x) (1 - cos (t x)) = s⁻¹ - s / (s² + t²)`. -/
theorem integral_Ioi_exp_neg_mul_mul_one_sub_cos {s : ℝ} (hs : 0 < s) (t : ℝ) :
    ∫ x in Ioi (0 : ℝ), exp (-(x * s)) * (1 - cos (t * x)) =
      s⁻¹ - s / (s ^ 2 + t ^ 2) := by
  have hexp : IntegrableOn (fun x : ℝ ↦ exp (-(x * s))) (Ioi 0) := by
    simpa [neg_mul, mul_comm] using integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hs) 0
  have hcos := integrableOn_exp_neg_mul_mul_cos hs t
  calc
    _ = (∫ x in Ioi (0 : ℝ), exp (-(x * s))) -
        ∫ x in Ioi (0 : ℝ), exp (-(x * s)) * cos (t * x) := by
      rw [← integral_sub hexp hcos]
      congr 1
      funext x
      ring
    _ = s⁻¹ - s / (s ^ 2 + t ^ 2) := by
      have hexp_value := integral_exp_mul_Ioi (a := -s) (neg_lt_zero.mpr hs) 0
      have hexp_value' : ∫ x in Ioi (0 : ℝ), exp (-(x * s)) = s⁻¹ := by
        simpa [mul_comm, hs.ne'] using hexp_value
      rw [hexp_value', integral_Ioi_exp_neg_mul_mul_cos hs t]

/-- For `0 < q < 2`, the singular power-weighted cosine integral has the closed form
`π |t|^q / (2 Γ(q + 1) sin(π q / 2))`. -/
theorem integral_Ioi_rpow_neg_mul_one_sub_cos {q : ℝ} (hq : 0 < q) (hq2 : q < 2) (t : ℝ) :
    ∫ x in Ioi (0 : ℝ), x ^ (-(q + 1)) * (1 - cos (t * x)) =
      |t| ^ q * (Real.pi / (2 * Gamma (q + 1) * sin (Real.pi * q / 2))) := by
  have hm := integral_Ioi_rpow_neg_smul (E := ℝ) (α := q)
    (g := fun x : ℝ ↦ 1 - cos (t * x)) (by linarith)
    (integrableOn_rpow_neg_mul_one_sub_cos hq hq2)
  simp only [smul_eq_mul] at hm
  rw [hm]
  have hlaplace :
      (∫ s in Ioi (0 : ℝ), s ^ q *
          ∫ x in Ioi (0 : ℝ), exp (-(x * s)) * (1 - cos (t * x))) =
        -∫ s in Ioi (0 : ℝ), s ^ q * (s / (s ^ 2 + t ^ 2) - s⁻¹) := by
    rw [← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioi fun s (hs : 0 < s) ↦ ?_
    rw [integral_Ioi_exp_neg_mul_mul_one_sub_cos hs t]
    ring
  rw [hlaplace, integral_rpow_mul_div_sq_add_sq_sub_inv hq hq2 t]
  have hGamma : 0 < Gamma (q + 1) := Gamma_pos_of_pos (by linarith)
  have hsin : 0 < sin (Real.pi * q / 2) :=
    sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])
  field_simp [hGamma.ne', hsin.ne']

end TauCeti
