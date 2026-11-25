/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import TauCeti.NumberTheory.LSeries.Lerch.Series
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import TauCeti.Analysis.SpecialFunctions.Exp.Periodic
import TauCeti.NumberTheory.LSeries.RiemannZeta.Basic

/-!
# Comparisons between the Lerch series and Hurwitz / Riemann zeta functions

On the convergence boundary `‖z‖ ≤ 1` with `1 < s.re`, this module relates `TauCeti.lerchSeries`
at `z = 1` and real `0 < c ≤ 1` to Mathlib's `HurwitzZeta.hurwitzZeta`, and relates
`TauCeti.lerchSeries` and `TauCeti.lerchZeta` at `c = 1` to Mathlib's periodic zeta
`HurwitzZeta.expZeta` and `riemannZeta`.

## Main declarations

* `TauCeti.expZeta_eq_mul_lerchZeta`:
  `HurwitzZeta.expZeta a s = Complex.exp (2 * π * I * a) * lerchZeta s a 1` for `a : ℝ`, `1 < s.re`.
* `TauCeti.lerchSeries_one_left_eq_hurwitzZeta`:
  `lerchSeries 1 s c = HurwitzZeta.hurwitzZeta c s` for `c ∈ Set.Ioc 0 1`, `1 < s.re`.
* `TauCeti.lerchSeries_one_left_one_right_eq_riemannZeta`:
  `lerchSeries 1 s 1 = riemannZeta s` for `1 < s.re`.
* `TauCeti.lerchSeries_neg_one_left_one_right_eq_mul_riemannZeta`:
  `lerchSeries (-1) s 1 = (1 - 2 ^ (1 - s)) * riemannZeta s` for `1 < s.re`.

## References

* J. C. Lagarias and W.-C. W. Li, *The Lerch zeta function I–II*, Forum Math. 24 (2012), 1–84.
* J. C. Lagarias and W.-C. W. Li, *The Lerch zeta function III. Polylogarithms and special values*,
  arXiv:1506.06161, (1.1), §6 Theorem 6.1.
-/

public section

open Complex

namespace TauCeti

/-- On `1 < s.re`, Mathlib's periodic zeta `HurwitzZeta.expZeta a s` differs from the `c = 1`
boundary `lerchZeta s a 1` by the prefactor `exp (2πia)`. -/
theorem expZeta_eq_mul_lerchZeta (a : ℝ) {s : ℂ} (hs : 1 < s.re) :
    HurwitzZeta.expZeta a s = Complex.exp (2 * Real.pi * I * a) * lerchZeta s a 1 := by
  have hs0 : s ≠ 0 := Complex.ne_zero_of_re_pos (by linarith)
  have hsum := HurwitzZeta.hasSum_expZeta_of_one_lt_re a hs
  rw [← hsum.tsum_eq, hsum.summable.tsum_eq_zero_add]
  simp only [Nat.cast_zero, mul_zero, Complex.zero_cpow hs0, div_zero, zero_add]
  rw [lerchZeta_def, lerchSeries_eq_tsum_cpow _ s fun n => by exact_mod_cast Nat.succ_ne_zero n,
    ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  have hden : (((n + 1 : ℕ) : ℂ) ^ s)⁻¹ = ((n : ℂ) + 1) ^ (-s) := by
    rw [← Complex.cpow_neg, Nat.cast_succ]
  have hphase : Complex.exp (2 * Real.pi * I * a * ((n + 1 : ℕ) : ℂ)) =
      Complex.exp (2 * Real.pi * I * a) * Complex.exp (2 * Real.pi * I * a) ^ n := by
    rw [mul_right_comm _ (a : ℂ), ← Complex.exp_two_pi_mul_I_mul_pow, pow_succ']
  rw [div_eq_mul_inv, hden, hphase, mul_assoc]

/-- At `z = 1` and real `0 < c ≤ 1`, `lerchSeries 1 s c = HurwitzZeta.hurwitzZeta c s` for
`1 < s.re`. Note `c = 0` is excluded because the `n = 0` term of `lerchSeries` is
`exp (-s * log 0) = 1`, whereas Mathlib's `1 / 0 ^ s = 0`. -/
theorem lerchSeries_one_left_eq_hurwitzZeta {c : ℝ} (hc : c ∈ Set.Ioc 0 1) {s : ℂ}
    (hs : 1 < s.re) :
    lerchSeries 1 s c = HurwitzZeta.hurwitzZeta c s := by
  have hne : ∀ n : ℕ, (n : ℂ) + c ≠ 0 := fun n => by
    exact_mod_cast (by linarith [Nat.cast_nonneg (α := ℝ) n, hc.1] : (0 : ℝ) < n + c).ne'
  have hsum := HurwitzZeta.hasSum_hurwitzZeta_of_one_lt_re (Set.Ioc_subset_Icc_self hc) hs
  rw [lerchSeries_eq_tsum_cpow 1 s hne, ← hsum.tsum_eq]
  exact tsum_congr fun n => by rw [one_pow, one_mul, Complex.cpow_neg, one_div]

/-- At `z = 1` and `c = 1`, `lerchSeries 1 s 1 = riemannZeta s` for `1 < s.re`. -/
theorem lerchSeries_one_left_one_right_eq_riemannZeta {s : ℂ} (hs : 1 < s.re) :
    lerchSeries 1 s 1 = riemannZeta s := by
  have h := lerchSeries_one_left_eq_hurwitzZeta (Set.right_mem_Ioc.mpr zero_lt_one) hs
  rwa [ofReal_one, AddCircle.coe_period 1, HurwitzZeta.hurwitzZeta_zero] at h

/-- At `z = -1` and `c = 1`, `lerchSeries (-1) s 1 = (1 - 2 ^ (1 - s)) * riemannZeta s` for
`1 < s.re`. -/
theorem lerchSeries_neg_one_left_one_right_eq_mul_riemannZeta {s : ℂ} (hs : 1 < s.re) :
    lerchSeries (-1) s 1 = (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s := by
  rw [← LSeries_neg_one_pow_add_one_eq_mul_riemannZeta hs, LSeries]
  have hterm (n : ℕ) :
      LSeries.term (fun k => (-1 : ℂ) ^ (k + 1)) s (n + 1) =
        (-1 : ℂ) ^ n * ((n : ℂ) + 1) ^ (-s) := by
    rw [LSeries.term_of_ne_zero (Nat.succ_ne_zero n), div_eq_mul_inv, ← Complex.cpow_neg]
    push_cast
    rw [pow_succ, pow_succ]
    ring
  have hsum : Summable (LSeries.term (fun k => (-1 : ℂ) ^ (k + 1)) s) :=
    LSeriesSummable_of_bounded_of_one_lt_re (m := 1) (fun n _ => by simp) hs
  rw [hsum.tsum_eq_zero_add, LSeries.term_zero, zero_add,
    lerchSeries_eq_tsum_cpow (-1) s fun n => by exact_mod_cast Nat.succ_ne_zero n]
  exact tsum_congr fun n => (hterm n).symm

-- Alternating Basel check `lerchSeries (-1) 2 1 = π ^ 2 / 12`.
example : lerchSeries (-1) 2 1 = (Real.pi : ℂ) ^ 2 / 12 := by
  have hsub : (1 : ℂ) - 2 = (-1 : ℤ) := by norm_num
  rw [lerchSeries_neg_one_left_one_right_eq_mul_riemannZeta (by norm_num : 1 < (2 : ℂ).re),
    riemannZeta_two, hsub, cpow_intCast, zpow_neg_one]
  ring

-- Sign-distinguishing check against `HurwitzZeta.expZeta`: at `a = 1 / 2` and `s = 2`,
-- `expZeta (1 / 2) 2 = -π ^ 2 / 12`, opposite in sign to `lerchSeries (-1) 2 1 = π ^ 2 / 12` due to
-- the prefactor `exp (2πi · (1 / 2)) = -1`.
example : HurwitzZeta.expZeta ((1 / 2 : ℝ) : UnitAddCircle) 2 = -(Real.pi : ℂ) ^ 2 / 12 := by
  have harg : 2 * (Real.pi : ℂ) * I * ((1 / 2 : ℝ) : ℂ) = Real.pi * I := by push_cast; ring
  have hsub : (1 : ℂ) - 2 = (-1 : ℤ) := by norm_num
  rw [expZeta_eq_mul_lerchZeta (1 / 2 : ℝ) (by norm_num : 1 < (2 : ℂ).re), lerchZeta_def, harg,
    Complex.exp_pi_mul_I,
    lerchSeries_neg_one_left_one_right_eq_mul_riemannZeta (by norm_num : 1 < (2 : ℂ).re),
    riemannZeta_two, hsub, cpow_intCast, zpow_neg_one]
  ring

end TauCeti
