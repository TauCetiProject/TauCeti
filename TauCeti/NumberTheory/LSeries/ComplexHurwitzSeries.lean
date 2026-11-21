/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.HurwitzZeta
public import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.PSeries
import TauCeti.Analysis.SpecialFunctions.Gamma.IntegralComplexRate

/-!
# The Hurwitz series with a complex parameter

For complex `s` and `c` the Hurwitz series is
`ζ_H(s, c) = ∑_{n ≥ 0} exp (-s log (n + c))`,
with Mathlib's principal logarithm. On `1 < re s` it converges absolutely for every `c`, and
whenever `n + c ≠ 0` for all `n : ℕ` its terms are the principal powers `(n + c) ^ (-s)`.
Mathlib's `hurwitzZeta` only takes a parameter on the circle `ℝ / ℤ`; on the right half-plane
`0 < re c` the complex parameter is the one in which the Hurwitz function is continued jointly
in `(s, c)`, and the Gamma integral below is the starting point of that continuation.

## Main definitions

* `TauCeti.complexHurwitzSeries s c`: the Hurwitz series `∑_{n ≥ 0} exp (-s log (n + c))`.

## Main results

* `TauCeti.summable_norm_complexHurwitzSeries`, `TauCeti.hasSum_complexHurwitzSeries`: absolute
  convergence on `1 < re s`, for every `c : ℂ`.
* `TauCeti.complexHurwitzSeries_eq_tsum_cpow`: the terms are principal powers `(n + c) ^ (-s)`
  when `c` is not a nonpositive integer.
* `TauCeti.complexHurwitzSeries_add_natCast`, `TauCeti.complexHurwitzSeries_add_one`: the shift
  `ζ_H(s, c + 1) = ζ_H(s, c) - exp (-s log c)` and its iterates.
* `TauCeti.complexHurwitzSeries_ofReal`: for real `0 < a ≤ 1` the series is Mathlib's
  `hurwitzZeta a s`, read at the representative `a` of its class in `ℝ / ℤ`.
* `TauCeti.complexHurwitzSeries_one`, `TauCeti.complexHurwitzSeries_one_half`:
  `ζ_H(s, 1) = ζ(s)` and `ζ_H(s, 1 / 2) = (2 ^ s - 1) ζ(s)`.
* `TauCeti.complexHurwitzSeries_eq_integral`: the Gamma integral
  `ζ_H(s, c) = Γ(s)⁻¹ ∫₀^∞ t ^ (s - 1) e^{-ct} / (1 - e^{-t}) dt` for `1 < re s` and `0 < re c`.

## References

* A. Hurwitz, *Einige Eigenschaften der Dirichlet'schen Functionen
  `F(s) = ∑ (D/n) ⋅ 1/n^s`, die bei der Bestimmung der Classenanzahlen binärer quadratischer
  Formen auftreten*, Z. Math. Phys. **27** (1882), 86–101.
* [NIST DLMF, §25.11](https://dlmf.nist.gov/25.11), equations (25.11.1), (25.11.3) and
  (25.11.25).
-/

public section

open Complex Set MeasureTheory Filter

namespace TauCeti

/-- Away from `0`, `exp (y * log x)` is the principal power `x ^ y`; this rewrites the terms
`exp (-s * log (n + c))` of the Hurwitz series as powers `(n + c) ^ (-s)`. -/
theorem exp_mul_log_eq_cpow {x : ℂ} (hx : x ≠ 0) (y : ℂ) : exp (y * log x) = x ^ y := by
  rw [cpow_def_of_ne_zero hx, mul_comm]

/-- The Hurwitz series `ζ_H(s, c) = ∑_{n ≥ 0} exp (-s log (n + c))` with a complex parameter `c`,
using Mathlib's principal logarithm. It converges absolutely on `1 < re s`
(`TauCeti.hasSum_complexHurwitzSeries`); outside that half-plane the sum carries no meaning. -/
noncomputable def complexHurwitzSeries (s c : ℂ) : ℂ :=
  ∑' n : ℕ, exp (-s * log (n + c))

/-- The defining series of `TauCeti.complexHurwitzSeries`. -/
theorem complexHurwitzSeries_def (s c : ℂ) :
    complexHurwitzSeries s c = ∑' n : ℕ, exp (-s * log (n + c)) :=
  (rfl)

/-- On `1 < re s` the Hurwitz series converges absolutely, for every complex parameter `c`. -/
theorem summable_norm_complexHurwitzSeries (c : ℂ) {s : ℂ} (hs : 1 < s.re) :
    Summable fun n : ℕ ↦ ‖exp (-s * log (n + c))‖ := by
  refine Summable.of_norm_bounded_eventually_nat
    (((Real.summable_one_div_nat_add_rpow c.re s.re).mpr hs).mul_left
      (Real.exp (Real.pi * |s.im|))) ?_
  filter_upwards [tendsto_natCast_atTop_atTop.eventually_gt_atTop (-c.re)] with n hn
  have hw : 0 < (n : ℝ) + c.re := by linarith
  have hlog : Real.log ((n : ℝ) + c.re) ≤ Real.log ‖(n : ℂ) + c‖ :=
    Real.log_le_log hw (by simpa using re_le_norm ((n : ℂ) + c))
  have harg : s.im * arg ((n : ℂ) + c) ≤ Real.pi * |s.im| := by
    calc s.im * arg ((n : ℂ) + c) ≤ |s.im| * |arg ((n : ℂ) + c)| := by
          rw [← abs_mul]; exact le_abs_self _
      _ ≤ |s.im| * Real.pi := by gcongr; exact abs_arg_le_pi _
      _ = Real.pi * |s.im| := mul_comm _ _
  have hre : (-s * log ((n : ℂ) + c)).re =
      -s.re * Real.log ‖(n : ℂ) + c‖ + s.im * arg ((n : ℂ) + c) := by
    simp only [mul_re, neg_re, neg_im, log_re, log_im]
    ring
  rw [norm_norm, norm_exp, hre, abs_of_pos hw, one_div, ← Real.rpow_neg hw.le,
    Real.rpow_def_of_pos hw, ← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  linarith [mul_le_mul_of_nonneg_left hlog (by linarith : (0 : ℝ) ≤ s.re)]

/-- On `1 < re s` the Hurwitz series converges, for every complex parameter `c`. -/
theorem summable_complexHurwitzSeries (c : ℂ) {s : ℂ} (hs : 1 < s.re) :
    Summable fun n : ℕ ↦ exp (-s * log (n + c)) :=
  (summable_norm_complexHurwitzSeries c hs).of_norm

/-- On `1 < re s` the Hurwitz series has sum `TauCeti.complexHurwitzSeries s c`. -/
theorem hasSum_complexHurwitzSeries (c : ℂ) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n : ℕ ↦ exp (-s * log (n + c))) (complexHurwitzSeries s c) :=
  (summable_complexHurwitzSeries c hs).hasSum

/-- When `c` is not a nonpositive integer, the terms of the Hurwitz series are the principal
powers `(n + c) ^ (-s)`. -/
theorem complexHurwitzSeries_eq_tsum_cpow (s : ℂ) {c : ℂ} (hc : ∀ n : ℕ, c ≠ -n) :
    complexHurwitzSeries s c = ∑' n : ℕ, ((n : ℂ) + c) ^ (-s) := by
  refine tsum_congr fun n ↦ ?_
  have hw : (n : ℂ) + c ≠ 0 := by
    rw [add_comm, ← sub_neg_eq_add]
    exact sub_ne_zero.mpr (hc n)
  exact exp_mul_log_eq_cpow hw _

/-- Shifting the parameter by `k : ℕ` removes the first `k` terms of the Hurwitz series. -/
theorem complexHurwitzSeries_add_natCast (c : ℂ) {s : ℂ} (hs : 1 < s.re) (k : ℕ) :
    complexHurwitzSeries s (c + k) =
      complexHurwitzSeries s c - ∑ j ∈ Finset.range k, exp (-s * log (j + c)) := by
  rw [complexHurwitzSeries, complexHurwitzSeries,
    ← (summable_complexHurwitzSeries c hs).sum_add_tsum_nat_add k, add_sub_cancel_left]
  refine tsum_congr fun n ↦ ?_
  push_cast
  ring_nf

/-- The shift relation `ζ_H(s, c + 1) = ζ_H(s, c) - exp (-s log c)` of the Hurwitz series. -/
theorem complexHurwitzSeries_add_one (c : ℂ) {s : ℂ} (hs : 1 < s.re) :
    complexHurwitzSeries s (c + 1) = complexHurwitzSeries s c - exp (-s * log c) := by
  simpa using complexHurwitzSeries_add_natCast c hs 1

/-- For real `0 < a ≤ 1` the Hurwitz series is Mathlib's Hurwitz zeta function at the class of
`a` in `ℝ / ℤ`, whose representative in `(0, 1]` is `a` itself. -/
theorem complexHurwitzSeries_ofReal {a : ℝ} (ha : 0 < a) (ha' : a ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    complexHurwitzSeries s a = HurwitzZeta.hurwitzZeta a s := by
  rw [← (HurwitzZeta.hasSum_hurwitzZeta_of_one_lt_re ⟨ha.le, ha'⟩ hs).tsum_eq]
  refine tsum_congr fun n ↦ ?_
  have hw : (n : ℂ) + a ≠ 0 := by
    rw [← ofReal_natCast, ← ofReal_add, ofReal_ne_zero]; positivity
  rw [one_div, ← cpow_neg, exp_mul_log_eq_cpow hw]

/-- At `c = 1` the Hurwitz series is the Riemann zeta function. -/
theorem complexHurwitzSeries_one {s : ℂ} (hs : 1 < s.re) :
    complexHurwitzSeries s 1 = riemannZeta s := by
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
  refine tsum_congr fun n ↦ ?_
  rw [one_div, ← cpow_neg, exp_mul_log_eq_cpow (Nat.cast_add_one_ne_zero n)]

/-- At `c = 1 / 2` the Hurwitz series is `(2 ^ s - 1) ζ(s)`: the odd terms of `ζ(s)` contribute
`(1 - 2 ^ (-s)) ζ(s)`, and `(n + 1 / 2) ^ (-s) = 2 ^ s (2 n + 1) ^ (-s)`. -/
theorem complexHurwitzSeries_one_half {s : ℂ} (hs : 1 < s.re) :
    complexHurwitzSeries s (1 / 2) = (2 ^ s - 1) * riemannZeta s := by
  have h2 : (2 : ℂ) ^ s ≠ 0 := by simp
  -- `ζ(s) = ∑ (m + 1) ^ (-s)`, split into odd and even `m + 1`.
  have hζ : HasSum (fun m : ℕ ↦ ((m : ℂ) + 1) ^ (-s)) (riemannZeta s) := by
    rw [← complexHurwitzSeries_one hs]
    exact (hasSum_complexHurwitzSeries 1 hs).congr_fun fun m ↦
      (exp_mul_log_eq_cpow (Nat.cast_add_one_ne_zero m) _).symm
  have hodd : HasSum (fun k : ℕ ↦ (((2 * k + 1 : ℕ) : ℂ) + 1) ^ (-s))
      ((2 : ℂ) ^ (-s) * riemannZeta s) := by
    refine (hζ.mul_left _).congr_fun fun k ↦ ?_
    have : (((2 * k + 1 : ℕ) : ℂ) + 1) = ((2 : ℝ) : ℂ) * ((k + 1 : ℝ) : ℂ) := by
      push_cast; ring
    rw [this, mul_cpow_ofReal_nonneg (by norm_num) (by positivity)]
    norm_num
  have heven : HasSum (fun k : ℕ ↦ (((2 * k : ℕ) : ℂ) + 1) ^ (-s))
      (∑' k : ℕ, (((2 * k : ℕ) : ℂ) + 1) ^ (-s)) :=
    (hζ.summable.comp_injective (mul_right_injective₀ two_ne_zero)).hasSum
  have hE : ∑' k : ℕ, (((2 * k : ℕ) : ℂ) + 1) ^ (-s) = (1 - 2 ^ (-s)) * riemannZeta s := by
    linear_combination (heven.even_add_odd hodd).unique hζ
  rw [complexHurwitzSeries_eq_tsum_cpow s (c := 1 / 2) (fun n h ↦ ?_)]
  · calc ∑' n : ℕ, ((n : ℂ) + 1 / 2) ^ (-s)
        = ∑' k : ℕ, 2 ^ s * (((2 * k : ℕ) : ℂ) + 1) ^ (-s) := by
          refine tsum_congr fun k ↦ ?_
          have : (k : ℂ) + 1 / 2 = ((2 * k + 1 : ℝ) : ℂ) * ((2⁻¹ : ℝ) : ℂ) := by
            push_cast; ring
          rw [this, mul_cpow_ofReal_nonneg (by positivity) (by norm_num), mul_comm]
          push_cast
          have harg : arg 2 ≠ Real.pi := by
            rw [← ofReal_ofNat, arg_ofReal_of_nonneg zero_le_two]; exact Real.pi_pos.ne
          rw [inv_cpow _ _ harg, cpow_neg, inv_inv]
      _ = (2 ^ s - 1) * riemannZeta s := by
          rw [tsum_mul_left, hE, ← mul_assoc, mul_sub, mul_one, cpow_neg, mul_inv_cancel₀ h2]
  · have := congrArg re h
    norm_num at this
    linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]

/-- The Gamma integral of the Hurwitz series: for `1 < re s` and `0 < re c`,
`ζ_H(s, c) = Γ(s)⁻¹ ∫₀^∞ t ^ (s - 1) e^{-ct} / (1 - e^{-t}) dt`. -/
theorem complexHurwitzSeries_eq_integral {s c : ℂ} (hs : 1 < s.re) (hc : 0 < c.re) :
    complexHurwitzSeries s c = (Gamma s)⁻¹ *
      ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) * (exp (-(c * t)) / (1 - exp (-t))) := by
  have hs0 : 0 < s.re := by linarith
  have hnc (n : ℕ) : 0 < ((n : ℂ) + c).re := by
    simp only [add_re, natCast_re]; positivity
  -- For `t > 0` the kernel is the sum of the Gamma integrands `t ^ (s - 1) e^{-(n + c)t}`.
  have hker {t : ℝ} (ht : 0 < t) :
      HasSum (fun n : ℕ ↦ (t : ℂ) ^ (s - 1) * exp (-(((n : ℂ) + c) * t)))
        ((t : ℂ) ^ (s - 1) * (exp (-(c * t)) / (1 - exp (-t)))) := by
    have hq : ‖exp (-(t : ℂ))‖ < 1 := by
      rw [norm_exp, neg_re, ofReal_re, Real.exp_lt_one_iff]; linarith
    convert (hasSum_geometric_of_norm_lt_one hq).mul_left ((t : ℂ) ^ (s - 1) * exp (-(c * t)))
      using 1
    · ext n
      rw [mul_assoc, ← exp_nat_mul, ← exp_add]
      congr 2
      ring
    · rw [div_eq_mul_inv, mul_assoc]
  -- Integrate the Gamma integrands term by term.
  have hint : HasSum
      (fun n : ℕ ↦ ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) * exp (-(((n : ℂ) + c) * t)))
      (∫ t in Ioi (0 : ℝ), ∑' n : ℕ, (t : ℂ) ^ (s - 1) * exp (-(((n : ℂ) + c) * t))) := by
    refine hasSum_integral_of_summable_integral_norm
      (fun n ↦ integrableOn_cpow_mul_exp_neg_mul_Ioi hs0 (hnc n)) ?_
    have hnorm (n : ℕ) : ∫ t in Ioi (0 : ℝ), ‖(t : ℂ) ^ (s - 1) * exp (-(((n : ℂ) + c) * t))‖ =
        Real.Gamma s.re * (1 / |(n : ℝ) + c.re| ^ s.re) := by
      have hr : 0 < (n : ℝ) + c.re := by simpa using hnc n
      rw [abs_of_pos hr, one_div, ← Real.inv_rpow hr.le, mul_comm, ← one_div,
        ← Real.integral_rpow_mul_exp_neg_mul_Ioi hs0 hr]
      refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) ↦ ?_
      rw [norm_mul, norm_cpow_eq_rpow_re_of_pos ht, norm_exp]
      simp [mul_comm]
    simp_rw [hnorm]
    exact ((Real.summable_one_div_nat_add_rpow c.re s.re).mpr hs).mul_left _
  have hΓ : Gamma s * complexHurwitzSeries s c = ∫ t in Ioi (0 : ℝ),
      (t : ℂ) ^ (s - 1) * (exp (-(c * t)) / (1 - exp (-t))) := by
    rw [← (setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) ↦
      (hker ht).tsum_eq), ← hint.tsum_eq,
      complexHurwitzSeries, ← tsum_mul_left]
    refine tsum_congr fun n ↦ ?_
    rw [integral_cpow_mul_exp_neg_mul_Ioi_of_re_pos hs0 (hnc n),
      exp_mul_log_eq_cpow (fun h ↦ by simpa [h] using hnc n)]
  rw [← hΓ, inv_mul_cancel_left₀ (Gamma_ne_zero_of_re_pos hs0)]

end TauCeti
