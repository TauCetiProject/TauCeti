/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The interval kernel `(b ^ s - a ^ s) / s`

For real numbers `0 < a ≤ b` and a complex exponent `s`, the kernel `(b ^ s - a ^ s) / s` is the
integral `∫_a^b t ^ (s - 1) dt`. It is entire in `s`, with value `log (b / a)` at `s = 0`, but the
totalized quotient in Lean is `0` there; the bounds below hold for the totalized quotient. On the
closed half-plane `0 ≤ Re s` this file bounds it in two ways:

* by `b ^ Re s * log (b / a)`, from the integral, a bound that stays finite as `s → 0`;
* by `2 b ^ Re s / ‖s‖`, from the numerator, a bound that decays as `‖s‖ → ∞`.

Together they give the low-zero-safe bound for the half-interval kernel used in explicit formulas
over a dyadic interval `(x / 2, x]`: for `0 ≤ x` and `0 ≤ Re ρ`,
`‖(x ^ ρ - (x / 2) ^ ρ) / ρ‖ ≤ 2 x ^ Re ρ min 1 ‖ρ‖⁻¹`. The bound is uniform near `ρ = 0`, so a sum
of such kernels over zeros needs no division by `Im ρ`.

## Main results

* `Complex.norm_ofReal_cpow_sub_ofReal_cpow_div_le_mul_log`: the logarithmic bound.
* `Complex.norm_ofReal_cpow_sub_ofReal_cpow_div_le_two_mul_div`: the reciprocal bound.
* `Complex.norm_ofReal_cpow_sub_ofReal_div_two_cpow_div_le`: the half-interval bound
  `‖(x ^ ρ - (x / 2) ^ ρ) / ρ‖ ≤ 2 x ^ Re ρ min 1 ‖ρ‖⁻¹`.

## References

* M. A. Bennett and S. Siksek, *A conjecture of Erdős, supersingular primes and short character
  sums*, Ann. of Math. (2) 191 (2020), §12, Proposition 12.2, where the half-interval kernel
  appears in an explicit formula for primes in a dyadic interval.
-/

public section

namespace Complex

/-- For `0 < a ≤ b` and `0 ≤ Re s`, the interval kernel `(b ^ s - a ^ s) / s` has norm at most
`b ^ Re s * log (b / a)`: it is `∫_a^b t ^ (s - 1) dt`, and `‖t ^ (s - 1)‖ ≤ b ^ Re s / t` on
`[a, b]`. -/
theorem norm_ofReal_cpow_sub_ofReal_cpow_div_le_mul_log {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    {s : ℂ} (hs : 0 ≤ s.re) :
    ‖((b : ℂ) ^ s - (a : ℂ) ^ s) / s‖ ≤ b ^ s.re * Real.log (b / a) := by
  have hb : 0 < b := ha.trans_le hab
  have hlog : 0 ≤ Real.log (b / a) := Real.log_nonneg ((one_le_div ha).2 hab)
  rcases eq_or_ne s 0 with rfl | hs₀
  · simpa using hlog
  have hzero : (0 : ℝ) ∉ Set.uIcc a b := by
    rw [Set.uIcc_of_le hab]
    exact fun h ↦ ha.not_ge h.1
  have hint := integral_cpow (a := a) (b := b) (r := s - 1)
    (Or.inr ⟨fun h ↦ hs₀ (by linear_combination h), hzero⟩)
  rw [sub_add_cancel] at hint
  have hpos {t : ℝ} (ht : t ∈ Set.Icc a b) : 0 < t := ha.trans_le ht.1
  calc ‖((b : ℂ) ^ s - (a : ℂ) ^ s) / s‖
      = ‖∫ t in a..b, (t : ℂ) ^ (s - 1)‖ := by rw [hint]
    _ ≤ ∫ t in a..b, ‖(t : ℂ) ^ (s - 1)‖ := intervalIntegral.norm_integral_le_integral_norm hab
    _ ≤ ∫ t in a..b, b ^ s.re * t⁻¹ := by
      refine intervalIntegral.integral_mono_on hab ?_ ?_ fun t ht ↦ ?_
      · refine ContinuousOn.intervalIntegrable fun t ht ↦ ?_
        rw [Set.uIcc_of_le hab] at ht
        exact (continuousAt_ofReal_cpow_const _ _ (Or.inr (hpos ht).ne')).norm.continuousWithinAt
      · refine ContinuousOn.intervalIntegrable fun t ht ↦ ?_
        rw [Set.uIcc_of_le hab] at ht
        exact (continuousAt_const.mul (continuousAt_inv₀ (hpos ht).ne')).continuousWithinAt
      · rw [norm_cpow_eq_rpow_re_of_pos (hpos ht), sub_re, one_re,
          Real.rpow_sub_one (hpos ht).ne', div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (hpos ht).le ht.2 hs)
          (inv_nonneg.2 (hpos ht).le)
    _ = b ^ s.re * Real.log (b / a) := by
      rw [intervalIntegral.integral_const_mul, integral_inv_of_pos ha hb]

/-- For `0 ≤ a ≤ b` and `0 ≤ Re s`, the interval kernel `(b ^ s - a ^ s) / s` has norm at most
`2 b ^ Re s / ‖s‖`, since both powers have norm at most `b ^ Re s`. -/
theorem norm_ofReal_cpow_sub_ofReal_cpow_div_le_two_mul_div {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    {s : ℂ} (hs : 0 ≤ s.re) :
    ‖((b : ℂ) ^ s - (a : ℂ) ^ s) / s‖ ≤ 2 * b ^ s.re / ‖s‖ := by
  rcases eq_or_ne s 0 with rfl | hs₀
  · simp
  have hpow {c : ℝ} (hc : 0 ≤ c) (hcb : c ≤ b) : ‖(c : ℂ) ^ s‖ ≤ b ^ s.re := by
    rcases hc.eq_or_lt with rfl | hc
    · rw [ofReal_zero, zero_cpow hs₀, norm_zero]
      exact Real.rpow_nonneg (ha.trans hab) _
    · rw [norm_cpow_eq_rpow_re_of_pos hc]
      exact Real.rpow_le_rpow hc.le hcb hs
  rw [norm_div, two_mul]
  gcongr
  exact (norm_sub_le _ _).trans (add_le_add (hpow (ha.trans hab) le_rfl) (hpow ha hab))

/-- **The low-zero-safe half-interval kernel.** For `0 ≤ x` and `0 ≤ Re ρ`,
`‖(x ^ ρ - (x / 2) ^ ρ) / ρ‖ ≤ 2 x ^ Re ρ min 1 ‖ρ‖⁻¹`. The bound stays finite as `ρ → 0`, where
the kernel tends to `log 2`. -/
theorem norm_ofReal_cpow_sub_ofReal_div_two_cpow_div_le {x : ℝ} (hx : 0 ≤ x) {ρ : ℂ}
    (hρ : 0 ≤ ρ.re) :
    ‖((x : ℂ) ^ ρ - ((x : ℂ) / 2) ^ ρ) / ρ‖ ≤ 2 * x ^ ρ.re * min 1 ‖ρ‖⁻¹ := by
  rcases hx.eq_or_lt with rfl | hx
  · simpa using mul_nonneg (mul_nonneg zero_le_two (Real.rpow_nonneg le_rfl ρ.re))
      (le_min zero_le_one (inv_nonneg.2 (norm_nonneg ρ)))
  have hhalf : ((x : ℂ) / 2) = ((x / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [hhalf, mul_min_of_nonneg _ _ (by positivity), mul_one]
  refine le_min ?_ ?_
  · refine (norm_ofReal_cpow_sub_ofReal_cpow_div_le_mul_log (a := x / 2) (b := x) (by positivity)
      (by linarith) hρ).trans ?_
    rw [div_div_cancel₀ hx.ne', mul_comm 2 (x ^ ρ.re)]
    have := Real.log_le_sub_one_of_pos (zero_lt_two' ℝ)
    exact mul_le_mul_of_nonneg_left (by linarith) (Real.rpow_nonneg hx.le _)
  · simpa [div_eq_mul_inv] using norm_ofReal_cpow_sub_ofReal_cpow_div_le_two_mul_div
      (a := x / 2) (b := x) (by positivity) (by linarith) hρ

end Complex
