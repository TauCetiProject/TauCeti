/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Gamma.Stirling.Series
import TauCeti.Analysis.SpecialFunctions.Beta.Basic
import TauCeti.Analysis.SpecialFunctions.Gamma.LogConvex
import TauCeti.NumberTheory.Bernoulli.Values
import TauCeti.NumberTheory.ZetaValues

/-!
# Brent's bound for the Stirling remainder

`norm_stirlingSeriesRemainder_succ_le_of_re_nonneg` bounds the remainder after the `n`-th
term by that term times `√π Γ(n + 1/2) / Γ(n)` in the closed right half-plane away from zero.
The strict bounds `norm_stirlingSeriesRemainder_succ_lt_of_re_nonneg` and
`norm_stirlingSeriesRemainder_lt_of_re_nonneg` replace the Gamma quotient by a square root.
The estimate uses `stirlingSeriesRemainder_succ_eq_neg_integral`,
`abs_bernoulliFun_even_fract_le` and `integral_one_add_sq_div_rpow`.

## References

* R. P. Brent, *On asymptotic approximations to the log-Gamma and Riemann-Siegel theta
  functions*, J. Aust. Math. Soc. 107 (2019), Theorem 1 and Corollary 1.
-/

public section

open Complex MeasureTheory ProbabilityTheory Set

namespace TauCeti

/-- Brent's bound for the remainder after the `n`-th Stirling term in the closed right
half-plane, away from zero. -/
theorem norm_stirlingSeriesRemainder_succ_le_of_re_nonneg {n : ℕ} (hn : 1 ≤ n) {z : ℂ}
    (hz : 0 ≤ z.re) (hz₀ : z ≠ 0) :
    ‖stirlingSeriesRemainder (n + 1) z‖ ≤
      Real.sqrt Real.pi * Real.Gamma ((n : ℝ) + 1 / 2) / Real.Gamma n * ‖stirlingTerm n z‖ := by
  have hn' : (1 : ℝ) ≤ n := Nat.one_le_cast.mpr hn
  have hhalf : (1 / 2 : ℝ) < n := by linarith
  have hr : 0 < ‖z‖ := norm_pos_iff.mpr hz₀
  have hslit : z ∈ slitPlane := by
    rw [mem_slitPlane_iff]
    by_contra! h
    exact hz₀ (Complex.ext (le_antisymm h.1 hz) h.2)
  let K (u : ℝ) : ℝ := (1 + u ^ 2 / ‖z‖ ^ 2) ^ (-(n : ℝ))
  let C : ℝ := |(bernoulli (2 * n) : ℝ)| / ((2 * n : ℝ) * (‖z‖ ^ 2) ^ n)
  have hK : Integrable K := integrable_one_add_sq_div_rpow (sq_pos_of_pos hr) hhalf
  have hmass : ∫ u in Ioi (0 : ℝ), K u =
      ‖z‖ * beta (1 / 2) ((n : ℝ) - 1 / 2) / 2 := by
    have heven := integral_comp_abs
      (f := fun u : ℝ ↦ (1 + u ^ 2 / ‖z‖ ^ 2) ^ (-(n : ℝ)))
    simp only [sq_abs, integral_one_add_sq_div_rpow (sq_pos_of_pos hr) hhalf,
      Real.sqrt_sq hr.le] at heven
    linarith
  have hpoint (u : ℝ) (hu : 0 < u) :
      ‖(bernoulliFun (2 * n) (Int.fract u) : ℂ) / ((2 * n : ℂ) * ((u : ℂ) + z) ^ (2 * n))‖
        ≤ C * K u := by
    have hsq : u ^ 2 + ‖z‖ ^ 2 ≤ ‖(u : ℂ) + z‖ ^ 2 := by
      simp only [Complex.sq_norm, normSq_apply, add_re, add_im, ofReal_re, ofReal_im, zero_add]
      nlinarith only [mul_nonneg hu.le hz]
    have hbase : 0 ≤ 1 + u ^ 2 / ‖z‖ ^ 2 := by positivity
    have hnorm : C * K u = |(bernoulli (2 * n) : ℝ)| / ((2 * n : ℝ) * (u ^ 2 + ‖z‖ ^ 2) ^ n) := by
      simp only [C, K]
      rw [Real.rpow_neg hbase, Real.rpow_natCast, one_add_div (pow_ne_zero _ hr.ne'),
        add_comm (‖z‖ ^ 2), div_pow]
      field_simp
    rw [hnorm]
    simp only [norm_div, norm_mul, norm_pow, Complex.norm_ofNat, Complex.norm_natCast,
      Complex.norm_real, Real.norm_eq_abs]
    rw [pow_mul]
    gcongr ?_ / (_ * ?_ ^ _)
    exact abs_bernoulliFun_even_fract_le n u
  have hconst : C * (‖z‖ * beta (1 / 2) ((n : ℝ) - 1 / 2) / 2) =
      Real.sqrt Real.pi * Real.Gamma ((n : ℝ) + 1 / 2) / Real.Gamma n * ‖stirlingTerm n z‖ := by
    have harg : (1 / 2 : ℝ) + (n - 1 / 2) = n := by ring
    have hsucc : (n : ℝ) + 1 / 2 = (n - 1 / 2) + 1 := by ring
    have hpow : (‖z‖ ^ 2) ^ n = ‖z‖ ^ (2 * n - 1) * ‖z‖ := by
      rw [← pow_mul, ← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ 2 * n)]
    rw [beta.eq_1, harg, Real.Gamma_one_half_eq]
    rw [norm_stirlingTerm, hsucc, Real.Gamma_add_one (sub_ne_zero.mpr hhalf.ne')]
    simp only [C, hpow]
    field_simp [ne_of_gt (Real.Gamma_pos_of_pos (by linarith : (0 : ℝ) < n)),
      ne_of_gt (by linarith : (0 : ℝ) < 2 * n - 1)]
  rw [stirlingSeriesRemainder_succ_eq_neg_integral hn hslit, norm_neg, ← hconst, ← hmass,
    ← integral_const_mul]
  exact norm_integral_le_of_norm_le (hK.const_mul C).restrict
    ((ae_restrict_iff' measurableSet_Ioi).mpr (.of_forall hpoint))

/-- Brent's strict square-root bound for the remainder after the `n`-th Stirling term
in the closed right half-plane, away from zero. -/
theorem norm_stirlingSeriesRemainder_succ_lt_of_re_nonneg {n : ℕ} (hn : 1 ≤ n) {z : ℂ}
    (hz : 0 ≤ z.re) (hz₀ : z ≠ 0) :
    ‖stirlingSeriesRemainder (n + 1) z‖ < Real.sqrt (Real.pi * n) * ‖stirlingTerm n z‖ := by
  have hn' : (1 : ℝ) ≤ n := Nat.one_le_cast.mpr hn
  have hcoef : Real.sqrt Real.pi * Real.Gamma ((n : ℝ) + 1 / 2) / Real.Gamma n <
      Real.sqrt (Real.pi * n) := by
    rw [Real.sqrt_mul Real.pi_pos.le, mul_div_assoc]
    exact mul_lt_mul_of_pos_left (Real.Gamma_add_half_div_Gamma_lt_sqrt (by linarith))
      (Real.sqrt_pos.2 Real.pi_pos)
  have hterm : 0 < ‖stirlingTerm n z‖ := by
    have hB : (bernoulli (2 * n) : ℝ) ≠ 0 := by exact_mod_cast bernoulli_two_mul_ne_zero n
    rw [norm_stirlingTerm]
    exact div_pos (abs_pos.mpr hB)
      (mul_pos (mul_pos (mul_pos two_pos (by linarith)) (by linarith))
        (pow_pos (norm_pos_iff.mpr hz₀) _))
  exact (norm_stirlingSeriesRemainder_succ_le_of_re_nonneg hn hz hz₀).trans_lt
    (mul_lt_mul_of_pos_right hcoef hterm)

/-- Brent's strict square-root bound for the remainder before the `n`-th Stirling term
in the closed right half-plane, away from zero. -/
theorem norm_stirlingSeriesRemainder_lt_of_re_nonneg {n : ℕ} (hn : 1 ≤ n) {z : ℂ}
    (hz : 0 ≤ z.re) (hz₀ : z ≠ 0) :
    ‖stirlingSeriesRemainder n z‖ < (1 + Real.sqrt (Real.pi * n)) * ‖stirlingTerm n z‖ := by
  have hsum : stirlingSeriesRemainder n z =
      stirlingTerm n z + stirlingSeriesRemainder (n + 1) z := by
    rw [stirlingSeriesRemainder_succ]
    ring
  rw [hsum, add_mul, one_mul]
  exact (norm_add_le _ _).trans_lt
    (add_lt_add_right (norm_stirlingSeriesRemainder_succ_lt_of_re_nonneg hn hz hz₀) _)

end TauCeti
