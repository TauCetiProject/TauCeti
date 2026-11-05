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
      calc
        1 - cos (t * x) = 2 * sin (t * x / 2) ^ 2 := by
          rw [show t * x = 2 * (t * x / 2) by ring, cos_two_mul_eq_one_sub]
          ring_nf
        _ ≤ 2 * |t * x / 2| ^ 2 := by
          have hsine := sq_le_sq.mpr (@Real.abs_sin_le_abs (t * x / 2))
          rw [sq_abs]
          nlinarith
        _ = (t * x) ^ 2 / 2 := by rw [sq_abs]; ring
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hx0.le _) hcos0)]
    calc
      x ^ (-(q + 1)) * (1 - cos (t * x))
          ≤ x ^ (-(q + 1)) * ((t * x) ^ 2 / 2) :=
            mul_le_mul_of_nonneg_left hcos (Real.rpow_nonneg hx0.le _)
      _ = t ^ 2 / 2 * x ^ (1 - q) := by
        rw [mul_pow, show x ^ (-(q + 1)) * (t ^ 2 * x ^ 2 / 2) =
          t ^ 2 / 2 * (x ^ (-(q + 1)) * x ^ 2) by ring, ← Real.rpow_natCast x 2,
          ← Real.rpow_add hx0]
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

/-- The Laplace transform of the cosine difference is
`∫ x in (0, ∞), exp (-s x) (1 - cos (t x)) = t² / (s (s² + t²))`. -/
theorem integral_Ioi_exp_neg_mul_mul_one_sub_cos {s : ℝ} (hs : 0 < s) (t : ℝ) :
    ∫ x in Ioi (0 : ℝ), exp (-(x * s)) * (1 - cos (t * x)) =
      t ^ 2 / (s * (s ^ 2 + t ^ 2)) := by
  have hexp : IntegrableOn (fun x : ℝ ↦ exp (-(x * s))) (Ioi 0) := by
    simpa [neg_mul, mul_comm] using integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hs) 0
  have hcos : IntegrableOn (fun x : ℝ ↦ exp (-(x * s)) * cos (t * x)) (Ioi 0) := by
    refine hexp.mono' (by fun_prop) ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_mul, abs_exp, mul_le_iff_le_one_right (exp_pos _)]
    exact abs_cos_le_one _
  have hcomplex := congrArg Complex.re
    (integral_exp_mul_complex_Ioi (a := (-s : ℂ) + t * Complex.I) (by simpa using hs) 0)
  have htransform :
      ∫ x in Ioi (0 : ℝ), exp (-(x * s)) * cos (t * x) = s / (s ^ 2 + t ^ 2) := by
    have hcomplex_int : IntegrableOn
        (fun x : ℝ ↦ Complex.exp (((-s : ℂ) + t * Complex.I) * x)) (Ioi 0) :=
      integrableOn_exp_mul_complex_Ioi (by simpa using hs) 0
    have hcomplex' := (integral_re hcomplex_int).trans hcomplex
    have hfun : (fun x : ℝ ↦ RCLike.re (Complex.exp (((-s : ℂ) + t * Complex.I) * x))) =
        fun x : ℝ ↦ exp (-(x * s)) * cos (t * x) := by
      funext x
      simp [Complex.exp_re, Complex.mul_re, Complex.mul_im, mul_comm]
    rw [hfun] at hcomplex'
    simpa [Complex.div_re, Complex.normSq_apply, div_eq_mul_inv, mul_comm, pow_two] using hcomplex'
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
      rw [hexp_value', htransform]
    _ = _ := by
      field_simp [hs.ne', ne_of_gt (by positivity : 0 < s ^ 2 + t ^ 2)]
      ring

/-- For `0 < q < 2`, the singular power-weighted cosine integral has the closed form
`π |t|^q / (2 Γ(q + 1) sin(π q / 2))`. -/
theorem integral_Ioi_rpow_neg_mul_one_sub_cos {q : ℝ} (hq : 0 < q) (hq2 : q < 2) (t : ℝ) :
    ∫ x in Ioi (0 : ℝ), x ^ (-(q + 1)) * (1 - cos (t * x)) =
      |t| ^ q * (Real.pi / (2 * Gamma (q + 1) * sin (Real.pi * q / 2))) := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp [hq.ne']
  have hm := integral_Ioi_rpow_neg_smul (E := ℝ) (α := q)
    (g := fun x : ℝ ↦ 1 - cos (t * x)) (by linarith)
    (integrableOn_rpow_neg_mul_one_sub_cos hq hq2)
  simp only [smul_eq_mul] at hm
  rw [hm]
  have hlaplace :
      (∫ s in Ioi (0 : ℝ), s ^ q *
          ∫ x in Ioi (0 : ℝ), exp (-(x * s)) * (1 - cos (t * x))) =
        t ^ 2 * ∫ s in Ioi (0 : ℝ), s ^ (q - 1) / (s ^ 2 + t ^ 2) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun s (hs : 0 < s) ↦ ?_
    rw [integral_Ioi_exp_neg_mul_mul_one_sub_cos hs t,
      Real.rpow_sub_one hs.ne' q]
    field_simp [hs.ne', ne_of_gt (by positivity : 0 < s ^ 2 + t ^ 2)]
  rw [hlaplace, integral_rpow_div_sq_add_sq hq hq2 ht]
  have ht0 : 0 < |t| := abs_pos.mpr ht
  rw [show t ^ 2 = |t| ^ (2 : ℝ) by simp [sq_abs],
    show |t| ^ (2 : ℝ) * (|t| ^ (q - 2) *
      (Real.pi / (2 * sin (Real.pi * q / 2)))) =
        (|t| ^ (2 : ℝ) * |t| ^ (q - 2)) *
          (Real.pi / (2 * sin (Real.pi * q / 2))) by ring,
    ← Real.rpow_add ht0, show (2 : ℝ) + (q - 2) = q by ring]
  have hGamma : 0 < Gamma (q + 1) := Gamma_pos_of_pos (by linarith)
  have hsin : 0 < sin (Real.pi * q / 2) :=
    sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])
  field_simp [hGamma.ne', hsin.ne']

end TauCeti
