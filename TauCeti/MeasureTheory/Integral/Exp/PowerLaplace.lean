/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import TauCeti.Analysis.SpecialFunctions.Gamma.IntegralComplexRate
import TauCeti.MeasureTheory.Integral.Exp.Decay

/-!
# Half-line superlinear exponential-power Laplace integrals

For a real exponent `p > 1` and decay rate `b` with `0 < b.re`, absorbing any linear tilt `z * t`
into half the superlinear decay `-b.re * t ^ p` shows that the half-line integral

`∫ t in Ioi (0 : ℝ), (t : ℂ) ^ s * Complex.exp (z * t - b * (t : ℂ) ^ (p : ℂ))`

converges absolutely whenever `-1 < s.re` and `0 < b.re`, for every `z : ℂ`. Expanding
`exp (z * t)` as its power series and integrating term by term by dominated convergence evaluates
the integral as the everywhere convergent Gamma-coefficient series

`∑' n, z ^ n / n! * (b ^ (-(s + n + 1) / p) * (1 / p) * Γ ((s + n + 1) / p))`.

At `p = 3`, `b = 1 / 12`, and `s = -1 / 2`, this is the cubic-exponential Laplace integral giving
`Ai(z)² + Bi(z)²`.

## Main results

* `TauCeti.norm_cpow_mul_cexp_mul_sub_mul_cpow`: pointwise norm formula on `(0, ∞)` for
  `(t : ℂ) ^ s * exp (z * t - b * t ^ p)`.
* `TauCeti.integrableOn_cpow_mul_cexp_mul_sub_mul_cpow_Ioi`: complex integrability of
  `t ↦ t ^ s * exp (z * t - b * t ^ p)` on `(0, ∞)` for `1 < p`, `0 < b.re`, `-1 < s.re`.
* `TauCeti.integral_cpow_mul_cexp_neg_mul_cpow_Ioi`: complex-exponent and complex-rate
  counterpart of Mathlib's `integral_rpow_mul_exp_neg_mul_rpow`.
* `TauCeti.hasSum_integral_cpow_mul_cexp_mul_sub_mul_cpow_Ioi`: the everywhere convergent
  Maclaurin series in `z` of the half-line superlinear exponential-power Laplace integral.
-/

public section

noncomputable section

open Complex MeasureTheory Real Set
open scoped Nat

namespace TauCeti

/-- For `0 < t`, any `p : ℝ`, and any `b s z : ℂ`, the norm of
`(t : ℂ) ^ s * cexp (z * t - b * (t : ℂ) ^ (p : ℂ))` is
`t ^ s.re * rexp (z.re * t - b.re * t ^ p)`. -/
theorem norm_cpow_mul_cexp_mul_sub_mul_cpow (p : ℝ) (b s z : ℂ) {t : ℝ} (ht : 0 < t) :
    ‖(t : ℂ) ^ s * cexp (z * t - b * (t : ℂ) ^ (p : ℂ))‖ =
      t ^ s.re * rexp (z.re * t - b.re * t ^ p) := by
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.norm_exp,
    ← Complex.ofReal_cpow ht.le]
  simp

/-- For `1 < p`, `0 < b.re`, and `-1 < s.re`, the complex integrand
`t ↦ t ^ s * exp (z * t - b * t ^ p)` is integrable on `(0, ∞)` for every `z : ℂ`. -/
theorem integrableOn_cpow_mul_cexp_mul_sub_mul_cpow_Ioi {p : ℝ} (hp : 1 < p) {b s : ℂ}
    (hb : 0 < b.re) (hs : -1 < s.re) (z : ℂ) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ s * cexp (z * t - b * (t : ℂ) ^ (p : ℂ))) (Ioi 0) := by
  have hmaj := integrableOn_rpow_mul_exp_mul_sub_mul_rpow hp hs hb z.re
  refine hmaj.mono' (Measurable.aestronglyMeasurable (by fun_prop)) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t)
  rw [norm_cpow_mul_cexp_mul_sub_mul_cpow p b s z ht]

/-- For `0 < p`, `0 < b.re`, and `-1 < s.re`,
`∫ t in Ioi 0, (t : ℂ) ^ s * exp (-b * (t : ℂ) ^ (p : ℂ)) =
  b ^ (-(s + 1) / p) * (1 / p) * Γ ((s + 1) / p)`,
the complex-exponent and complex-rate counterpart of `integral_rpow_mul_exp_neg_mul_rpow`. -/
theorem integral_cpow_mul_cexp_neg_mul_cpow_Ioi {p : ℝ} (hp : 0 < p) {b s : ℂ}
    (hb : 0 < b.re) (hs : -1 < s.re) :
    ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ s * cexp (-b * (t : ℂ) ^ (p : ℂ)) =
      b ^ (-(s + 1) / p) * (1 / (p : ℂ)) * Complex.Gamma ((s + 1) / p) := by
  have hp_ne : (p : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hp.ne'
  have hre : 0 < ((s + 1) / (p : ℂ)).re := by
    rw [Complex.div_ofReal_re, Complex.add_re, Complex.one_re]
    exact div_pos (by linarith) hp
  calc
    ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ s * cexp (-b * (t : ℂ) ^ (p : ℂ))
        = ∫ x in Ioi (0 : ℝ),
            ((1 / p) * x ^ (1 / p - 1)) •
              (((x ^ (1 / p) : ℝ) : ℂ) ^ s *
                cexp (-b * ((x ^ (1 / p) : ℝ) : ℂ) ^ (p : ℂ))) := by
          rw [← integral_comp_rpow_Ioi_of_pos (one_div_pos.mpr hp)]
    _ = ∫ x in Ioi (0 : ℝ),
          (1 / (p : ℂ)) * ((x : ℂ) ^ ((s + 1) / p - 1) * cexp (-(b * x))) := by
          refine setIntegral_congr_fun measurableSet_Ioi fun x (hx : 0 < x) => ?_
          have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
          have hpow : ((x ^ (1 / p) : ℝ) : ℂ) ^ s = (x : ℂ) ^ (((1 / p : ℝ) : ℂ) * s) :=
            (Complex.cpow_mul_ofReal_nonneg hx.le (1 / p) s).symm
          have hxp : ((x ^ (1 / p) : ℝ) : ℂ) ^ (p : ℂ) = (x : ℂ) := by
            rw [← Complex.ofReal_cpow (by positivity), ← Real.rpow_mul hx.le,
              one_div_mul_cancel hp.ne', Real.rpow_one]
          have hexp : ((1 / p - 1 : ℝ) : ℂ) + ((1 / p : ℝ) : ℂ) * s = (s + 1) / p - 1 := by
            push_cast
            field_simp
            ring
          rw [Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_one,
            Complex.ofReal_cpow hx.le, hpow, hxp, neg_mul]
          calc (1 / (p : ℂ) * (x : ℂ) ^ ((1 / p - 1 : ℝ) : ℂ)) *
                ((x : ℂ) ^ (((1 / p : ℝ) : ℂ) * s) * cexp (-(b * x)))
              = (1 / (p : ℂ)) * (((x : ℂ) ^ ((1 / p - 1 : ℝ) : ℂ) *
                  (x : ℂ) ^ (((1 / p : ℝ) : ℂ) * s)) * cexp (-(b * x))) := by ring
            _ = _ := by rw [← Complex.cpow_add _ _ hx0, hexp]
    _ = b ^ (-(s + 1) / p) * (1 / (p : ℂ)) * Complex.Gamma ((s + 1) / p) := by
          rw [integral_const_mul, Complex.integral_cpow_mul_exp_neg_mul_Ioi_of_re_pos hre hb,
            neg_div]
          ring

/-- **Series expansion of a superlinear exponential-power Laplace integral.** For `1 < p`,
`0 < b.re`, `-1 < s.re`, and every `z : ℂ`,
`∫ t in Ioi 0, (t : ℂ) ^ s * exp (z * t - b * (t : ℂ) ^ (p : ℂ)) =
  ∑' n, z ^ n / n! * (b ^ (-(s + n + 1) / p) * (1 / p) * Γ ((s + n + 1) / p))`. -/
theorem hasSum_integral_cpow_mul_cexp_mul_sub_mul_cpow_Ioi {p : ℝ} (hp : 1 < p) {b s : ℂ}
    (hb : 0 < b.re) (hs : -1 < s.re) (z : ℂ) :
    HasSum
      (fun n : ℕ =>
        z ^ n / (n ! : ℂ) *
          (b ^ (-(s + n + 1) / p) * (1 / (p : ℂ)) * Complex.Gamma ((s + n + 1) / p)))
      (∫ t in Ioi (0 : ℝ), (t : ℂ) ^ s * cexp (z * t - b * (t : ℂ) ^ (p : ℂ))) := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  let F : ℕ → ℝ → ℂ := fun n t =>
    (z ^ n / (n ! : ℂ)) * ((t : ℂ) ^ (s + n) * cexp (-b * (t : ℂ) ^ (p : ℂ)))
  let bound : ℕ → ℝ → ℝ := fun n t =>
    (‖z‖ ^ n / (n ! : ℝ)) * (t ^ (s.re + n) * rexp (-b.re * t ^ p))
  have hbound_sum : ∀ t : ℝ, 0 < t →
      HasSum (fun n => bound n t) (t ^ s.re * rexp (‖z‖ * t - b.re * t ^ p)) := fun t ht => by
    have hexp := Real.exp_eq_exp_ℝ ▸ NormedSpace.expSeries_div_hasSum_exp (‖z‖ * t)
    convert hexp.mul_right (t ^ s.re * rexp (-b.re * t ^ p)) using 1
    · ext n
      simp only [bound]
      rw [mul_pow, Real.rpow_add ht, Real.rpow_natCast]
      ring
    · rw [← mul_assoc, mul_comm (rexp (‖z‖ * t)), mul_assoc, ← Real.exp_add, sub_eq_add_neg,
        neg_mul]
  have hdom : HasSum (fun n => ∫ t in Ioi (0 : ℝ), F n t)
      (∫ t in Ioi (0 : ℝ), (t : ℂ) ^ s * cexp (z * t - b * (t : ℂ) ^ (p : ℂ))) := by
    refine hasSum_integral_of_dominated_convergence bound
      (fun n => Measurable.aestronglyMeasurable (by fun_prop))
      (fun n => ?_) ?_ ?_ ?_
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t)
      have hnorm := norm_cpow_mul_cexp_mul_sub_mul_cpow p b (s + n) 0 ht
      simp only [zero_mul, zero_sub, zero_re, add_re, natCast_re, ← neg_mul] at hnorm
      dsimp only [F, bound]
      rw [norm_mul, norm_div, norm_pow, Complex.norm_natCast, hnorm]
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t)
      exact (hbound_sum t ht).summable
    · refine (integrableOn_rpow_mul_exp_mul_sub_mul_rpow hp hs hb ‖z‖).congr_fun
        (fun t (ht : 0 < t) => (hbound_sum t ht).tsum_eq.symm) measurableSet_Ioi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t)
      have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
      have hexp := Complex.exp_eq_exp_ℂ ▸ NormedSpace.expSeries_div_hasSum_exp (z * (t : ℂ))
      convert hexp.mul_right ((t : ℂ) ^ s * cexp (-b * (t : ℂ) ^ (p : ℂ))) using 1
      · ext n
        simp only [F]
        rw [mul_pow, Complex.cpow_add _ _ ht0, Complex.cpow_natCast]
        ring
      · rw [← mul_assoc, mul_comm (cexp (z * t)), mul_assoc, ← Complex.exp_add, sub_eq_add_neg,
          neg_mul]
  refine hdom.congr_fun fun n => ?_
  have hsn : -1 < (s + n).re := by
    rw [Complex.add_re, Complex.natCast_re]
    linarith [n.cast_nonneg (α := ℝ)]
  simp only [F]
  rw [integral_const_mul, integral_cpow_mul_cexp_neg_mul_cpow_Ioi hp0 hb hsn]

end TauCeti
