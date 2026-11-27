/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.PrimesInAP
import TauCeti.NumberTheory.ArithmeticFunction.VonMangoldt

/-!
# Higher prime powers in Gaussian-weighted logarithmic windows

In a logarithmic window with no primes of a given residue class, only higher prime powers
contribute to its von Mangoldt sum. Normalizing by a Gaussian factor still leaves a bound
uniform in the residue class and modulus, obtained from absolute convergence at `3/4`.
This is the middle-window estimate in `New.exists_prime_modEq_one_log_mem` in
[`Lib/Analytic/Primes.lean`][short-proof]. The lower and upper tails are not included here.

[short-proof]: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/Lib/Analytic/Primes.lean
-/

public section

open Complex Filter Finset
open scoped Topology

namespace ArithmeticFunction.vonMangoldt

-- On the middle window the linear and quadratic terms each cost at most `X` in the exponent.
private theorem re_gaussian_window_le {X U L : ℝ} {z : ℂ}
    (hX : 0 ≤ X) (hz : ‖(X : ℂ) * z‖ ≤ 1) (hL : L ∈ Set.Icc U (U + X ^ 2)) :
    ((U : ℂ) * z + (X : ℂ) / 4 * (1 + X * z) ^ 2 - 2).re - L * (1 + z.re) ≤
      2 * X - U / 4 - 2 - L * (3 / 4) := by
  have hlog : |U - L| ≤ X ^ 2 :=
    abs_le.mpr ⟨by linarith [hL.2], by linarith [hL.1, sq_nonneg X]⟩
  have hlin : (U - L) * z.re ≤ X := calc
    _ ≤ |U - L| * |z.re| := by rw [← abs_mul]; exact le_abs_self _
    _ ≤ X ^ 2 * |z.re| := mul_le_mul_of_nonneg_right hlog (abs_nonneg _)
    _ = X * |((X : ℂ) * z).re| := by
      simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero, abs_mul, abs_of_nonneg hX]
      ring
    _ ≤ X := mul_le_of_le_one_right hX ((abs_re_le_norm _).trans hz)
  have hquad : ((X : ℂ) / 4 * (1 + X * z) ^ 2).re ≤ X := calc
    _ ≤ ‖(X : ℂ) / 4 * (1 + X * z) ^ 2‖ := re_le_norm _
    _ ≤ X := by
      have hadd := (norm_add_le (1 : ℂ) ((X : ℂ) * z)).trans (add_le_add_right hz ‖(1 : ℂ)‖)
      simp only [norm_mul, norm_div, norm_real, Real.norm_eq_abs, abs_of_nonneg hX, norm_pow]
      calc
        _ ≤ X / 4 * 2 ^ 2 := by
          rw [Complex.norm_ofNat]
          gcongr
          norm_num at hadd ⊢
          exact hadd
        _ = X := by ring
  have hfirst : ((U : ℂ) * z).re = U * z.re := by simp [mul_re]
  have htwo : (2 : ℂ).re = 2 := by norm_num
  rw [sub_re, add_re, htwo, hfirst]
  nlinarith only [hlin, hquad, hL.1]

/-- A finite sum of progression terms in a prime-free logarithmic window of width `X²`.
After Gaussian normalization its bound is the absolute series of nonprime terms at `3/4`,
times `exp (2 * X - U / 4 - 2)`. No coprimality of the residue class is required. -/
theorem norm_gaussian_window_sum_le_of_no_primes {q : ℕ} (a : ZMod q) (S : Finset ℕ)
    {X U : ℝ} {z : ℂ} (hX : 0 ≤ X) (hz : ‖(X : ℂ) * z‖ ≤ 1)
    (hS : ∀ n ∈ S, Real.log n ∈ Set.Icc U (U + X ^ 2))
    (hprime : ∀ p ∈ S, Nat.Prime p → (p : ZMod q) ≠ a) :
    ‖Complex.exp ((U : ℂ) * z + (X : ℂ) / 4 * (1 + X * z) ^ 2 - 2) *
        ∑ n ∈ S, LSeries.term (fun n ↦ (residueClass a n : ℂ)) (1 + z) n‖ ≤
      Real.exp (2 * X - U / 4 - 2) *
        ∑' n : ℕ, (if n.Prime then 0 else vonMangoldt n) / (n : ℝ) ^ (3 / 4 : ℝ) := by
  let E := (U : ℂ) * z + (X : ℂ) / 4 * (1 + X * z) ^ 2 - 2
  let b (n : ℕ) := (if n.Prime then 0 else vonMangoldt n) / (n : ℝ) ^ (3 / 4 : ℝ)
  have hnonneg : ∀ n, 0 ≤ b n := fun n ↦
    div_nonneg (ite_nonneg le_rfl vonMangoldt_nonneg) (by positivity)
  have hterm (n : ℕ) (hn : n ∈ S) :
      ‖Complex.exp E * LSeries.term (fun k ↦ (residueClass a k : ℂ)) (1 + z) n‖ ≤
        Real.exp (2 * X - U / 4 - 2) * b n := by
    rcases eq_or_ne n 0 with rfl | hn₀
    · simpa using mul_nonneg (Real.exp_pos _).le (hnonneg 0)
    have hE := re_gaussian_window_le hX hz (hS n hn)
    have hc : residueClass a n ≤ if n.Prime then 0 else vonMangoldt n := by
      split_ifs with hp
      · simp [residueClass, hprime n hn hp]
      · exact residueClass_le a n
    rw [norm_mul, norm_exp, LSeries.norm_term_eq, ite_eq_right hn₀, norm_real,
      Real.norm_eq_abs, abs_of_nonneg (residueClass_nonneg a n), add_re, one_re]
    have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn₀)
    calc
      _ = Real.exp (E.re - Real.log n * (1 + z.re)) * residueClass a n := by
        rw [Real.rpow_def_of_pos hnpos, Real.exp_sub]
        ring
      _ ≤ Real.exp (2 * X - U / 4 - 2 - Real.log n * (3 / 4)) *
          (if n.Prime then 0 else vonMangoldt n) :=
        mul_le_mul (Real.exp_le_exp.mpr hE) hc (residueClass_nonneg a n) (Real.exp_pos _).le
      _ = Real.exp (2 * X - U / 4 - 2) * b n := by
        dsimp only [b]
        rw [Real.exp_sub, Real.rpow_def_of_pos hnpos]
        ring
  rw [mul_sum]
  refine (norm_sum_le _ _).trans ((sum_le_sum hterm).trans ?_)
  rw [← mul_sum]
  exact mul_le_mul_of_nonneg_left
    ((summable_nonprime_div_rpow (by norm_num : 1 / 2 < (3 / 4 : ℝ))).sum_le_tsum S
      fun n _ ↦ hnonneg n) (Real.exp_pos _).le

/-- For sufficiently large `X`, the middle-window contribution is at most `1`, uniformly in
the modulus, the residue class and the starting point `U ≥ X²`. -/
theorem eventually_norm_gaussian_window_sum_le_one :
    ∀ᶠ X : ℝ in atTop, ∀ {q : ℕ} (a : ZMod q) (S : Finset ℕ) {U : ℝ} {z : ℂ},
      X ^ 2 ≤ U → ‖(X : ℂ) * z‖ ≤ 1 →
      (∀ n ∈ S, Real.log n ∈ Set.Icc U (U + X ^ 2)) →
      (∀ p ∈ S, Nat.Prime p → (p : ZMod q) ≠ a) →
      ‖Complex.exp ((U : ℂ) * z + (X : ℂ) / 4 * (1 + X * z) ^ 2 - 2) *
        ∑ n ∈ S, LSeries.term (fun n ↦ (residueClass a n : ℂ)) (1 + z) n‖ ≤ 1 := by
  let C := ∑' n : ℕ, (if n.Prime then 0 else vonMangoldt n) / (n : ℝ) ^ (3 / 4 : ℝ)
  have hC : 0 ≤ C := tsum_nonneg fun _ ↦
    div_nonneg (ite_nonneg le_rfl vonMangoldt_nonneg) (by positivity)
  have hdecay : Tendsto (fun X : ℝ ↦ Real.exp (-X) * C) atTop (𝓝 0) := by
    simpa using Real.tendsto_exp_neg_atTop_nhds_zero.mul_const C
  filter_upwards [eventually_ge_atTop (12 : ℝ), hdecay.eventually (gt_mem_nhds zero_lt_one)]
    with X hX hsmall q a S U z hU hz hS hp
  have hexp : 2 * X - U / 4 - 2 ≤ -X := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ X) (sub_nonneg.mpr hX)]
  exact (norm_gaussian_window_sum_le_of_no_primes a S (by linarith) hz hS hp).trans
    ((mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hexp) hC).trans hsmall.le)

end ArithmeticFunction.vonMangoldt
