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
and `TauCeti.lerchZeta` at `c = 1` to Mathlib's periodic zeta `HurwitzZeta.expZeta` and
`riemannZeta`.

## Main declarations

* `TauCeti.expZeta_eq_mul_lerchZeta`:
  `HurwitzZeta.expZeta a s = Complex.exp (2 * π * I * a) * lerchZeta s a 1` for `a : ℝ`, `1 < s.re`.
* `TauCeti.lerchSeries_one_one_eq_riemannZeta`: `lerchSeries 1 s 1 = riemannZeta s` for `1 < s.re`.
* `TauCeti.lerchSeries_neg_one_one_eq_mul_riemannZeta`:
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
  have hs0 : s ≠ 0 := by rintro rfl; simp only [zero_re] at hs; linarith
  have hsum := HurwitzZeta.hasSum_expZeta_of_one_lt_re a hs
  rw [← hsum.tsum_eq, hsum.summable.tsum_eq_zero_add]
  simp only [Nat.cast_zero, mul_zero, Complex.zero_cpow hs0, div_zero, zero_add]
  rw [lerchZeta_def, lerchSeries_eq_tsum_cpow _ s fun n => by exact_mod_cast Nat.succ_ne_zero n,
    ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  have hden : (((n + 1 : ℕ) : ℂ) ^ s)⁻¹ = ((n : ℂ) + 1) ^ (-s) := by
    rw [← Complex.cpow_neg]; push_cast; rfl
  have hphase : Complex.exp (2 * Real.pi * I * a * ((n + 1 : ℕ) : ℂ)) =
      Complex.exp (2 * Real.pi * I * a) * Complex.exp (2 * Real.pi * I * a) ^ n := by
    rw [mul_right_comm _ (a : ℂ), ← Complex.exp_two_pi_mul_I_mul_pow, pow_succ']
  rw [div_eq_mul_inv, hden, hphase, mul_assoc]

/-- At `z = 1` and `c = 1`, `lerchSeries 1 s 1 = riemannZeta s` for `1 < s.re`. -/
theorem lerchSeries_one_one_eq_riemannZeta {s : ℂ} (hs : 1 < s.re) :
    lerchSeries 1 s 1 = riemannZeta s := by
  simpa [lerchZeta_def, HurwitzZeta.expZeta_zero] using (expZeta_eq_mul_lerchZeta 0 hs).symm

/-- At `z = -1` and `c = 1`, `lerchSeries (-1) s 1 = (1 - 2 ^ (1 - s)) * riemannZeta s` for
`1 < s.re`. -/
theorem lerchSeries_neg_one_one_eq_mul_riemannZeta {s : ℂ} (hs : 1 < s.re) :
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
    (summable_nat_add_iff 1).mp <|
      ((summable_lerchSeries_term_of_norm_le_one (z := -1) (by simp) hs 1).congr fun n => by
        rw [cpow_def_of_ne_zero (by exact_mod_cast Nat.succ_ne_zero n),
          mul_comm (Complex.log _)]).congr fun n => (hterm n).symm
  rw [hsum.tsum_eq_zero_add, LSeries.term_zero, zero_add,
    lerchSeries_eq_tsum_cpow (-1) s fun n => by exact_mod_cast Nat.succ_ne_zero n]
  exact tsum_congr fun n => (hterm n).symm

-- Alternating Basel check `lerchSeries (-1) 2 1 = π ^ 2 / 12`.
example : lerchSeries (-1) 2 1 = (Real.pi : ℂ) ^ 2 / 12 := by
  have hsub : (1 : ℂ) - 2 = (-1 : ℤ) := by norm_num
  rw [lerchSeries_neg_one_one_eq_mul_riemannZeta (by norm_num : 1 < (2 : ℂ).re), riemannZeta_two,
    hsub, cpow_intCast, zpow_neg_one]
  ring

-- Sign-distinguishing check against `HurwitzZeta.expZeta`: at `a = 1 / 2` and `s = 2`,
-- `expZeta (1 / 2) 2 = -π ^ 2 / 12`, opposite in sign to `lerchSeries (-1) 2 1 = π ^ 2 / 12` due to
-- the prefactor `exp (2πi · (1 / 2)) = -1`.
example : HurwitzZeta.expZeta ((1 / 2 : ℝ) : UnitAddCircle) 2 = -(Real.pi : ℂ) ^ 2 / 12 := by
  have harg : 2 * (Real.pi : ℂ) * I * ((1 / 2 : ℝ) : ℂ) = Real.pi * I := by push_cast; ring
  have hsub : (1 : ℂ) - 2 = (-1 : ℤ) := by norm_num
  rw [expZeta_eq_mul_lerchZeta (1 / 2 : ℝ) (by norm_num : 1 < (2 : ℂ).re), lerchZeta_def, harg,
    Complex.exp_pi_mul_I, lerchSeries_neg_one_one_eq_mul_riemannZeta (by norm_num : 1 < (2 : ℂ).re),
    riemannZeta_two, hsub, cpow_intCast, zpow_neg_one]
  ring

end TauCeti
