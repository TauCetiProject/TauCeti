/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.HurwitzZeta
public import Mathlib.NumberTheory.LSeries.RiemannZeta
import TauCeti.Analysis.SpecialFunctions.Gamma.IntegralComplexRate
import TauCeti.NumberTheory.LSeries.RiemannZeta.Basic

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
  when `c` is not a nonpositive integer; `TauCeti.complexHurwitzSeries_eq_tsum_cpow_of_re_pos`
  specializes this to `0 < re c`.
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
  have hbound : ‖exp (-s * log ((n : ℂ) + c))‖ ≤
      Real.exp (Real.pi * |s.im|) * Real.exp (-(Real.log ((n : ℝ) + c.re) * s.re)) := by
    rw [norm_exp, hre, ← Real.exp_add]
    exact Real.exp_le_exp.mpr
      (by linarith [mul_le_mul_of_nonneg_left hlog (by linarith : (0 : ℝ) ≤ s.re)])
  simpa [abs_of_pos hw, Real.rpow_def_of_pos hw, Real.exp_neg] using hbound

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
  rw [cpow_def_of_ne_zero hw, mul_comm]

/-- On the right half-plane `0 < re c` the terms of the Hurwitz series are the principal powers
`(n + c) ^ (-s)`. -/
theorem complexHurwitzSeries_eq_tsum_cpow_of_re_pos (s : ℂ) {c : ℂ} (hc : 0 < c.re) :
    complexHurwitzSeries s c = ∑' n : ℕ, ((n : ℂ) + c) ^ (-s) := by
  refine complexHurwitzSeries_eq_tsum_cpow s fun n h ↦ ?_
  have := congrArg re h
  simp only [neg_re, natCast_re] at this
  linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]

/-- Shifting the parameter by `k : ℕ` removes the first `k` terms of the Hurwitz series. -/
theorem complexHurwitzSeries_add_natCast (c : ℂ) {s : ℂ} (hs : 1 < s.re) (k : ℕ) :
    complexHurwitzSeries s (c + k) =
      complexHurwitzSeries s c - ∑ j ∈ Finset.range k, exp (-s * log (j + c)) := by
  rw [complexHurwitzSeries, complexHurwitzSeries,
    ← (summable_complexHurwitzSeries c hs).sum_add_tsum_nat_add k, add_sub_cancel_left]
  refine tsum_congr fun n ↦ ?_
  congr 3
  push_cast
  ring

/-- The shift relation `ζ_H(s, c + 1) = ζ_H(s, c) - exp (-s log c)` of the Hurwitz series. -/
theorem complexHurwitzSeries_add_one (c : ℂ) {s : ℂ} (hs : 1 < s.re) :
    complexHurwitzSeries s (c + 1) = complexHurwitzSeries s c - exp (-s * log c) := by
  simpa using complexHurwitzSeries_add_natCast c hs 1

/-- For real `0 < a ≤ 1` the Hurwitz series is Mathlib's Hurwitz zeta function at the class of
`a` in `ℝ / ℤ`, whose representative in `(0, 1]` is `a` itself. -/
theorem complexHurwitzSeries_ofReal {a : ℝ} (ha : 0 < a) (ha' : a ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    complexHurwitzSeries s a = HurwitzZeta.hurwitzZeta a s := by
  rw [← (HurwitzZeta.hasSum_hurwitzZeta_of_one_lt_re ⟨ha.le, ha'⟩ hs).tsum_eq,
    complexHurwitzSeries_eq_tsum_cpow_of_re_pos s (by simpa using ha)]
  simp_rw [one_div, cpow_neg]

/-- At `c = 1` the Hurwitz series is the Riemann zeta function. -/
theorem complexHurwitzSeries_one {s : ℂ} (hs : 1 < s.re) :
    complexHurwitzSeries s 1 = riemannZeta s := by
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs,
    complexHurwitzSeries_eq_tsum_cpow_of_re_pos s (by norm_num)]
  simp_rw [one_div, cpow_neg]

/-- At `c = 1 / 2` the Hurwitz series is `(2 ^ s - 1) ζ(s)`: the odd terms of `ζ(s)` contribute
`(1 - 2 ^ (-s)) ζ(s)`, and `(n + 1 / 2) ^ (-s) = 2 ^ s (2 n + 1) ^ (-s)`. -/
theorem complexHurwitzSeries_one_half {s : ℂ} (hs : 1 < s.re) :
    complexHurwitzSeries s (1 / 2) = (2 ^ s - 1) * riemannZeta s := by
  have h2 : (2 : ℂ) ^ s ≠ 0 := by simp
  rw [complexHurwitzSeries_eq_tsum_cpow_of_re_pos s (c := 1 / 2) (by norm_num)]
  calc ∑' n : ℕ, ((n : ℂ) + 1 / 2) ^ (-s)
        = ∑' k : ℕ, 2 ^ s * (2 * (k : ℂ) + 1) ^ (-s) := by
          refine tsum_congr fun k ↦ ?_
          have : (k : ℂ) + 1 / 2 = ((2 * k + 1 : ℝ) : ℂ) * ((2⁻¹ : ℝ) : ℂ) := by
            push_cast; ring
          rw [this, ofReal_mul_cpow (by positivity),
            mul_comm (((2 * k + 1 : ℝ) : ℂ) ^ (-s))]
          push_cast
          have harg : arg 2 ≠ Real.pi := by
            rw [← ofReal_ofNat, arg_ofReal_of_nonneg zero_le_two]; exact Real.pi_pos.ne
          rw [inv_cpow _ _ harg, cpow_neg, inv_inv]
      _ = (2 ^ s - 1) * riemannZeta s := by
          rw [tsum_mul_left, (hasSum_two_mul_add_one_cpow_neg_riemannZeta hs).tsum_eq, cpow_neg]
          field_simp

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
      rw [mul_assoc, ← exp_natCast_mul, ← exp_add]
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
      calc ∫ t in Ioi (0 : ℝ), ‖(t : ℂ) ^ (s - 1) * exp (-(((n : ℂ) + c) * t))‖
          = ∫ t in Ioi (0 : ℝ), t ^ (s.re - 1) * Real.exp (-(((n : ℝ) + c.re) * t)) := by
            refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) ↦ ?_
            rw [norm_mul, norm_cpow_eq_rpow_re_of_pos ht, norm_exp]
            simp
        _ = (1 / ((n : ℝ) + c.re)) ^ s.re * Real.Gamma s.re :=
            Real.integral_rpow_mul_exp_neg_mul_Ioi hs0 hr
        _ = Real.Gamma s.re * (1 / |(n : ℝ) + c.re| ^ s.re) := by
            rw [abs_of_pos hr, Real.div_rpow zero_le_one hr.le, Real.one_rpow]
            ring
    simp_rw [hnorm]
    exact ((Real.summable_one_div_nat_add_rpow c.re s.re).mpr hs).mul_left _
  have hΓ : Gamma s * complexHurwitzSeries s c = ∫ t in Ioi (0 : ℝ),
      (t : ℂ) ^ (s - 1) * (exp (-(c * t)) / (1 - exp (-t))) := by
    rw [← (setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) ↦
      (hker ht).tsum_eq), ← hint.tsum_eq,
      complexHurwitzSeries_eq_tsum_cpow_of_re_pos s hc, ← tsum_mul_left]
    exact tsum_congr fun n ↦ (integral_cpow_mul_exp_neg_mul_Ioi_of_re_pos hs0 (hnc n)).symm
  rw [← hΓ, inv_mul_cancel_left₀ (Gamma_ne_zero_of_re_pos hs0)]

end TauCeti
