/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds
import TauCeti.Algebra.Order.Floor.Semifield
import TauCeti.Analysis.SpecialFunctions.Log.Base
import TauCeti.Analysis.SpecialFunctions.Log.Bounds
import TauCeti.Analysis.SpecialFunctions.Pow.Bounds
import TauCeti.NumberTheory.Chebyshev.Basic
import TauCeti.NumberTheory.PrimeCounting

/-!
# Explicit bounds for the difference `ψ − θ`, prime-power counts, and `ψ ↔ θ` transfers

For real `x ≥ 0`, Mathlib's `Chebyshev.psi_eq_sum_theta` writes `ψ(x) = ∑_{k ≥ 1} θ(x^{1/k})`, the
terms with `k > log x / log 2` vanishing. Splitting off `k = 1` and `k = 2`,

`ψ(x) − θ(x) = θ(√x) + ∑_{3 ≤ k ≤ log x / log 2} θ(x^{1/k})`,

and this file turns that decomposition into the explicit two-sided bounds for `ψ − θ` used to pass
between bounds for `ψ` and for `θ`:

* from any bound `θ(y) ≤ c y` on `y ≥ 2`,
  `ψ(x) − θ(x) ≤ c (√x + (log x / log 2 − 2)⁺ x^{1/3})`; at `c = log 4`
  (`Chebyshev.theta_le_log4_mul_x`) this is unconditional;
* from relative bounds `a y ≤ θ(y)` and `θ(y) ≤ c' y` for `y ≥ y₀`, the sharper
  `a √x + θ(x^{1/3}) ≤ ψ(x) − θ(x) ≤ c' √x + c (log x / log 2 − 2) x^{1/3}`
  for `x ≥ y₀²` (and `x ≥ 4` on the right);
* controlling the cube-root tail by the dimensionless coefficient
  `Chebyshev.psiSubThetaTailCoeff x = ∑ k ∈ Icc 3 ⌊log x / log 2⌋₊, x ^ (1 / k - 1 / 3)`, which
  vanishes for `0 ≤ x < 8`, is strictly decreasing on `[2 ^ n, 2 ^ (n + 1))` for `n ≥ 4`,
  satisfies `f (2 ^ (n + 1)) < f (2 ^ n)` for `n ≥ 9`, and is bounded uniformly for `x ≥ X ≥ 2 ^ 8`
  by the antitone envelope
  `Chebyshev.psiSubThetaTailBound X = max (f X) (f (2 ^ (⌊log X / log 2⌋₊ + 1)))`, yielding
  Propositions 3–4, Corollary 3.1, and Theorem 5 of Broadbent, Kadiri, Lumley, Ng, and Wilk
  (2021);
* conversely, a bound for `ψ` gives one for `θ` through Costa Pereira's comparison
  `ψ(x) − θ(x) ≤ ψ(x^{1/2}) + ψ(x^{1/3}) + ψ(x^{1/5})` (Lemma 11 of Broadbent et al.).

It also counts the prime powers: the prime powers `m ≤ x` number `∑_{k ≥ 1} π(x^{1/k})`, which is at
most `π(x) + (log x / log 2 − 1) √x ≤ 6 x / log x` for `x ≥ 2`, giving `O(x / log x)`.

## Main definitions

* `Chebyshev.psiSubThetaTailCoeff`: the cube-root tail coefficient
  `∑ k ∈ Icc 3 ⌊log x / log 2⌋₊, x ^ (1 / k - 1 / 3)`.
* `Chebyshev.psiSubThetaTailBound`: the uniform dyadic envelope
  `max (psiSubThetaTailCoeff X) (psiSubThetaTailCoeff (2 ^ (⌊log X / log 2⌋₊ + 1)))`.
* `Chebyshev.psiSubThetaSqrtCoeff`: the square-root coefficient in Theorem 5 of Broadbent et al.,
  `1 + ε (log x₁)` for `b ≤ 2 * log x₁` and `1 + ε (b / 2)` otherwise.
* `Chebyshev.psiSubThetaCbrtCoeff`: the cube-root coefficient
  `(1 + ε (log x₁)) * psiSubThetaTailBound (exp b)` in Theorem 5 of Broadbent et al.

## Main results

* `Chebyshev.psi_eq_theta_add_theta_sqrt_add_sum`, `Chebyshev.psi_sub_theta_eq_theta_sqrt_add_sum`,
  `Chebyshev.psi_sub_theta_eq_sum_theta`: the exact decompositions of `ψ(x)` and `ψ(x) − θ(x)`.
* `Chebyshev.theta_sqrt_add_theta_rpow_le_psi_sub_theta`, `Chebyshev.theta_sqrt_le_psi_sub_theta`:
  unconditional lower bounds on `ψ(x) − θ(x)`.
* `Chebyshev.sum_rpow_one_div_le`:
  `∑_{3 ≤ k ≤ log x / log 2} x^{1/k} ≤ (log x / log 2 − 2)⁺ x^{1/3}`.
* `Chebyshev.psi_sub_theta_le_add_max_mul_rpow`, `Chebyshev.psi_sub_theta_le_of_theta_le`,
  `Chebyshev.psi_sub_theta_le_log_four_mul`, `Chebyshev.psi_sub_theta_le_add_mul_rpow`,
  `Chebyshev.mul_sqrt_add_theta_rpow_le_psi_sub_theta`,
  `Chebyshev.psi_sub_theta_le_mul_rpow_of_theta_le`: unconditional and general-`θ` bounds on
  `ψ − θ`.
* `Chebyshev.theta_ge_psi_sub_mul`: lower bound for `θ` from a linear upper bound for `ψ`.
* `Chebyshev.abs_theta_sub_self_le_of_theta_le`, `Chebyshev.abs_psi_sub_self_le_of_theta_le`,
  `Chebyshev.abs_theta_sub_self_le_mul_of_theta_le_of_abs_psi_sub_self_le`,
  `Chebyshev.abs_theta_sub_self_le_mul_of_abs_psi_sub_self_le`,
  `Chebyshev.abs_psi_sub_self_le_mul_of_theta_le_of_abs_theta_sub_self_le`,
  `Chebyshev.abs_psi_sub_self_le_mul_of_abs_theta_sub_self_le`: additive and relative-error
  conversions between bounds for `|ψ(x) − x|` and `|θ(x) − x|`.
* `Chebyshev.card_filter_isPrimePow_eq_sum_primeCounting`,
  `Chebyshev.card_filter_isPrimePow_le_six_mul_div_log`,
  `Chebyshev.card_filter_range_isPrimePow_le_six_mul_div_log`,
  `Chebyshev.isBigO_card_filter_isPrimePow_div_log`: the number of prime powers up to `x`,
  below an integer `N`, and its `O(x / log x)` asymptotic form.
* `Chebyshev.psiSubThetaTailCoeff_eq_zero_iff`,
  `Chebyshev.psiSubThetaTailCoeff_mul_rpow`,
  `Chebyshev.psiSubThetaTailCoeff_eq_sum_of_mem_Ico`,
  `Chebyshev.sum_theta_rpow_le`,
  `Chebyshev.strictAntiOn_psiSubThetaTailCoeff_Ico_two_pow`,
  `Chebyshev.psiSubThetaTailCoeff_two_pow_succ_lt`,
  `Chebyshev.psiSubThetaTailCoeff_two_pow_eight_lt_two_pow_nine`,
  `Chebyshev.psiSubThetaTailCoeff_le_psiSubThetaTailBound`,
  `Chebyshev.psiSubThetaTailBound_le_iff_forall`,
  `Chebyshev.antitoneOn_psiSubThetaTailBound`: vanishing, dyadic monotonicity, sharpness, and
  uniform least-upper-bound envelope for `psiSubThetaTailCoeff`.
* `Chebyshev.psi_sub_theta_sub_theta_sqrt_le`,
  `Chebyshev.psi_sub_theta_le_add_psiSubThetaTailBound`,
  `Chebyshev.theta_le_of_theta_le_self_of_psi_le`,
  `Chebyshev.psiSubThetaSqrtCoeff_of_le`, `Chebyshev.psiSubThetaSqrtCoeff_of_lt`,
  `Chebyshev.psiSubThetaSqrtCoeff_eq_one_add_max`,
  `Chebyshev.psi_sub_theta_le_of_psi_le_exp`, `Chebyshev.psi_sub_theta_le_mul_rpow_add`,
  `Chebyshev.psi_sub_theta_le_mul_exp_add`: general-input transfer bounds of Broadbent, Kadiri,
  Lumley, Ng, and Wilk.

## References

* J. B. Rosser and L. Schoenfeld, *Approximate formulas for some functions of prime numbers*,
  Illinois J. Math. 6 (1962), 64–94.
* L. Schoenfeld, *Sharper bounds for the Chebyshev functions θ(x) and ψ(x). II*, Math. Comp. 30
  (1976), 337–360, which displays the same decomposition of `ψ − θ`.
* N. Costa Pereira, *Estimates for the Chebyshev function `ψ(x) - θ(x)`*,
  Math. Comp. 44 (1985), 211–221.
* S. Broadbent, H. Kadiri, A. Lumley, N. Ng, K. Wilk, *Sharper bounds for the Chebyshev function
  θ(x)*, Math. Comp. 90 (2021), 2281–2315: (2.4), Propositions 3–4, Corollary 3.1, Theorem 5,
  and Lemma 11.
-/

public section

open Finset Filter Real
open scoped Chebyshev Asymptotics

namespace Chebyshev

/-! ### The decomposition of `ψ − θ` -/

/-- For `x ≥ 0` and every `N ≥ log x / log 2`,
`ψ(x) = θ(x) + θ(√x) + ∑_{3 ≤ k ≤ N} θ(x^{1/k})`. -/
theorem psi_eq_theta_add_theta_sqrt_add_sum' {x : ℝ} (hx : 0 ≤ x) {N : ℕ}
    (hN : ⌊log x / log 2⌋₊ ≤ N) :
    ψ x = θ x + θ √x + ∑ k ∈ Icc 3 N, θ (x ^ ((1 : ℝ) / k)) := by
  have hIcc : Icc 3 (max N 2) = Icc 3 N := by
    rcases le_total N 2 with h | h
    · rw [max_eq_right h, Icc_eq_empty (by omega), Icc_eq_empty (by omega)]
    · rw [max_eq_left h]
  have hsplit : Icc 1 (max N 2) = insert 1 (insert 2 (Icc 3 (max N 2))) := by
    ext k
    simp only [mem_Icc, mem_insert]
    omega
  rw [psi_eq_sum_theta' hx (hN.trans (le_max_left N 2)), hsplit, sum_insert (by simp),
    sum_insert (by simp), hIcc]
  simp [sqrt_eq_rpow, add_assoc]

/-- For `x ≥ 0`, `ψ(x) = θ(x) + θ(√x) + ∑_{3 ≤ k ≤ log x / log 2} θ(x^{1/k})`. -/
theorem psi_eq_theta_add_theta_sqrt_add_sum {x : ℝ} (hx : 0 ≤ x) :
    ψ x = θ x + θ √x + ∑ k ∈ Icc 3 ⌊log x / log 2⌋₊, θ (x ^ ((1 : ℝ) / k)) :=
  psi_eq_theta_add_theta_sqrt_add_sum' hx le_rfl

/-- For `x ≥ 0` and every `N ≥ log x / log 2`,
`ψ(x) − θ(x) = θ(√x) + ∑_{3 ≤ k ≤ N} θ(x^{1/k})`. -/
theorem psi_sub_theta_eq_theta_sqrt_add_sum' {x : ℝ} (hx : 0 ≤ x) {N : ℕ}
    (hN : ⌊log x / log 2⌋₊ ≤ N) :
    ψ x - θ x = θ √x + ∑ k ∈ Icc 3 N, θ (x ^ ((1 : ℝ) / k)) := by
  rw [psi_eq_theta_add_theta_sqrt_add_sum' hx hN, add_assoc, add_sub_cancel_left]

/-- For `x ≥ 0`, `ψ(x) − θ(x) = θ(√x) + ∑_{3 ≤ k ≤ log x / log 2} θ(x^{1/k})`. -/
theorem psi_sub_theta_eq_theta_sqrt_add_sum {x : ℝ} (hx : 0 ≤ x) :
    ψ x - θ x = θ √x + ∑ k ∈ Icc 3 ⌊log x / log 2⌋₊, θ (x ^ ((1 : ℝ) / k)) :=
  psi_sub_theta_eq_theta_sqrt_add_sum' hx le_rfl

/-- For every `x ≥ 0`, `ψ x - θ x = ∑ k ∈ Icc 2 ⌊log x / log 2⌋₊, θ (x ^ (1 / k))`. -/
theorem psi_sub_theta_eq_sum_theta {x : ℝ} (hx : 0 ≤ x) :
    ψ x - θ x = ∑ k ∈ Icc 2 ⌊log x / log 2⌋₊, θ (x ^ ((1 : ℝ) / k)) := by
  rcases lt_or_ge x 2 with hx2 | hx2
  · rw [psi_eq_zero_of_lt_two hx2, theta_eq_zero_of_lt_two hx2, sub_zero]
    have hlt : ⌊log x / log 2⌋₊ < 1 := by
      rw [← Real.logb, Real.natFloor_logb_lt_iff_lt_pow one_lt_two hx one_ne_zero, pow_one]
      exact hx2
    rw [Icc_eq_empty (by omega), sum_empty]
  · rw [psi_eq_theta_add_sum_theta hx2, add_sub_cancel_left]

/-- The square-root and cube-root terms of the decomposition bound `ψ − θ` from below:
`θ(√x) + θ(x^{1/3}) ≤ ψ(x) − θ(x)` for `x ≥ 0`. -/
theorem theta_sqrt_add_theta_rpow_le_psi_sub_theta {x : ℝ} (hx : 0 ≤ x) :
    θ √x + θ (x ^ ((1 : ℝ) / 3)) ≤ ψ x - θ x := by
  rw [psi_sub_theta_eq_theta_sqrt_add_sum' hx (le_max_left _ 3)]
  have h3 := single_le_sum (f := fun k : ℕ ↦ θ (x ^ ((1 : ℝ) / k))) (fun _ _ ↦ theta_nonneg _)
    (mem_Icc.mpr ⟨le_rfl, le_max_right ⌊log x / log 2⌋₊ 3⟩)
  simp only [Nat.cast_ofNat] at h3
  linarith

/-- Unconditional square-root lower bound: `θ √x ≤ ψ x - θ x` for every real `x`. -/
theorem theta_sqrt_le_psi_sub_theta (x : ℝ) : θ √x ≤ ψ x - θ x := by
  rcases le_or_gt 0 x with hx | hx
  · exact (le_add_of_nonneg_right (theta_nonneg _)).trans
      (theta_sqrt_add_theta_rpow_le_psi_sub_theta hx)
  · rw [Real.sqrt_eq_zero_of_nonpos hx.le, theta_eq_zero_of_lt_two (by norm_num),
      psi_eq_zero_of_lt_two (by linarith), theta_eq_zero_of_lt_two (by linarith), sub_zero]

/-- The terms with `k ≥ 3` of the decomposition: if `θ(y) ≤ c y` for every `y ≥ 2`, then
`∑_{3 ≤ k ≤ N} θ(x^{1/k}) ≤ c ∑_{3 ≤ k ≤ N} x^{1/k}` for `x ≥ 0`. -/
theorem sum_theta_rpow_le_mul_sum_rpow {c x : ℝ} (hc : ∀ y, 2 ≤ y → θ y ≤ c * y) (hx : 0 ≤ x)
    (N : ℕ) :
    ∑ k ∈ Icc 3 N, θ (x ^ ((1 : ℝ) / k)) ≤ c * ∑ k ∈ Icc 3 N, x ^ ((1 : ℝ) / k) := by
  rw [mul_sum]
  exact sum_le_sum fun k _ ↦ theta_le_mul_of_two_le (rpow_nonneg hx _) hc

/-- The roots `x^{1/k}` with `3 ≤ k ≤ log x / log 2` add up to at most
`(log x / log 2 − 2)⁺ x^{1/3}`, for `x ≥ 0`. -/
theorem sum_rpow_one_div_le {x : ℝ} (hx : 0 ≤ x) :
    ∑ k ∈ Icc 3 ⌊log x / log 2⌋₊, x ^ ((1 : ℝ) / k) ≤
      max (log x / log 2 - 2) 0 * x ^ ((1 : ℝ) / 3) := by
  rcases lt_or_ge x 1 with hx1 | hx1
  · have : ⌊log x / log 2⌋₊ = 0 :=
      Nat.floor_eq_zero.mpr ((div_nonpos_of_nonpos_of_nonneg
        (log_nonpos hx hx1.le) (log_nonneg one_le_two)).trans_lt one_pos)
    simp only [this, Icc_eq_empty_of_lt (by norm_num : 0 < 3), sum_empty]
    positivity
  refine (TauCeti.sum_Icc_floor_le_max_mul (div_nonneg (log_nonneg hx1) (log_nonneg one_le_two))
    (rpow_nonneg hx ((1 : ℝ) / 3)) 3 fun k hk ↦
      rpow_le_rpow_of_exponent_le hx1
        (one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast (mem_Icc.mp hk).1))).trans_eq ?_
  congr 2
  push_cast
  ring

/-! ### Upper and lower bounds for `ψ − θ` and `ψ ↔ θ` conversions -/

/-- Upper transfer from a global `θ`-bound `θ y ≤ c * y` on `[2, ∞)` and a bound
`θ y ≤ c' * y` on `[y₀, ∞)`: for `y₀ ^ 2 ≤ x`,
`ψ x - θ x ≤ c' * √x + c * max (log x / log 2 - 2) 0 * x ^ (1 / 3)`. -/
theorem psi_sub_theta_le_add_max_mul_rpow {c c' y₀ x : ℝ} (hyx : y₀ ^ 2 ≤ x)
    (hθ : ∀ y, 2 ≤ y → θ y ≤ c * y) (hθ' : ∀ y, y₀ ≤ y → θ y ≤ c' * y) :
    ψ x - θ x ≤ c' * √x + c * max (log x / log 2 - 2) 0 * x ^ ((1 : ℝ) / 3) := by
  have hx : 0 ≤ x := le_trans (sq_nonneg y₀) hyx
  have hc : 0 < c := pos_of_theta_le hθ
  have h1 : θ √x ≤ c' * √x := hθ' √x (Real.le_sqrt_of_sq_le hyx)
  have h2 := (sum_theta_rpow_le_mul_sum_rpow hθ hx ⌊log x / log 2⌋₊).trans
    (mul_le_mul_of_nonneg_left (sum_rpow_one_div_le hx) hc.le)
  rw [psi_sub_theta_eq_theta_sqrt_add_sum hx]
  linarith

/-- General upper bound for `ψ - θ`: if `θ y ≤ c * y` for all `y ≥ 2`, then for every `x ≥ 0`,
`ψ x - θ x ≤ c * (√x + max (log x / log 2 - 2) 0 * x ^ (1 / 3))`. -/
theorem psi_sub_theta_le_of_theta_le {c x : ℝ} (hx : 0 ≤ x)
    (hθ : ∀ y, 2 ≤ y → θ y ≤ c * y) :
    ψ x - θ x ≤ c * (√x + max (log x / log 2 - 2) 0 * x ^ ((1 : ℝ) / 3)) :=
  (psi_sub_theta_le_add_max_mul_rpow (y₀ := 0) (by simpa using hx) hθ
    fun _ hy ↦ theta_le_mul_of_two_le hy hθ).trans_eq (by ring)

/-- The unconditional bound
`0 ≤ ψ(x) − θ(x) ≤ (log 4) (√x + (log x / log 2 − 2)⁺ x^{1/3})` for `x ≥ 0`; the lower bound is
`Chebyshev.theta_le_psi`. -/
theorem psi_sub_theta_le_log_four_mul {x : ℝ} (hx : 0 ≤ x) :
    ψ x - θ x ≤ log 4 * (√x + max (log x / log 2 - 2) 0 * x ^ ((1 : ℝ) / 3)) :=
  psi_sub_theta_le_of_theta_le hx fun _ hy ↦ theta_le_log4_mul_x (by linarith)

/-- Upper transfer from `θ`-bounds for `x ≥ max 4 (y₀ ^ 2)`:
`ψ x - θ x ≤ c' * √x + c * (log x / log 2 - 2) * x ^ (1 / 3)`. -/
theorem psi_sub_theta_le_add_mul_rpow {c c' y₀ x : ℝ} (hx : 4 ≤ x) (hyx : y₀ ^ 2 ≤ x)
    (hθ : ∀ y, 2 ≤ y → θ y ≤ c * y) (hθ' : ∀ y, y₀ ≤ y → θ y ≤ c' * y) :
    ψ x - θ x ≤ c' * √x + c * (log x / log 2 - 2) * x ^ ((1 : ℝ) / 3) := by
  have h2 : (2 : ℝ) ≤ log x / log 2 := by
    rw [← Real.logb, Real.le_logb_iff_rpow_le one_lt_two (by linarith), Real.rpow_two]
    linarith
  simpa only [max_eq_left (sub_nonneg.mpr h2)] using
    psi_sub_theta_le_add_max_mul_rpow hyx hθ hθ'

/-- Lower transfer from a `θ`-bound on `[y₀, ∞)`: if `y₀ ^ 2 ≤ x` and `a * y ≤ θ y` for `y ≥ y₀`,
then `a * √x + θ (x ^ (1 / 3)) ≤ ψ x - θ x`. -/
theorem mul_sqrt_add_theta_rpow_le_psi_sub_theta {a y₀ x : ℝ} (hyx : y₀ ^ 2 ≤ x)
    (hθ : ∀ y, y₀ ≤ y → a * y ≤ θ y) :
    a * √x + θ (x ^ ((1 : ℝ) / 3)) ≤ ψ x - θ x := by
  have hx : 0 ≤ x := (sq_nonneg y₀).trans hyx
  have h1 : a * √x ≤ θ √x := hθ √x (Real.le_sqrt_of_sq_le hyx)
  linarith [theta_sqrt_add_theta_rpow_le_psi_sub_theta hx]

private lemma mul_sqrt_add_max_rpow_eq {c x : ℝ} (hx : 0 ≤ x) :
    c * (√x + max (log x / log 2 - 2) 0 * x ^ ((1 : ℝ) / 3)) =
      c * (x ^ (-(1 : ℝ) / 2) +
        max (log x / log 2 - 2) 0 * x ^ (-(2 : ℝ) / 3)) * x := by
  rcases hx.eq_or_lt with rfl | hx0
  · simp
  · have h1 : x ^ (-(1 : ℝ) / 2) * x = √x := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add_one hx0.ne']
      norm_num
    have h2 : x ^ (-(2 : ℝ) / 3) * x = x ^ ((1 : ℝ) / 3) := by
      rw [← Real.rpow_add_one hx0.ne']
      norm_num
    rw [← h1, ← h2]
    ring

/-- Relative-error form of `psi_sub_theta_le_of_theta_le`: if `θ y ≤ c * y` for all `y ≥ 2`, then
for every `x ≥ 0`,
`ψ x - θ x ≤ c * (x ^ (-1 / 2) + max (log x / log 2 - 2) 0 * x ^ (-2 / 3)) * x`. -/
theorem psi_sub_theta_le_mul_rpow_of_theta_le {c x : ℝ} (hx : 0 ≤ x)
    (hθ : ∀ y, 2 ≤ y → θ y ≤ c * y) :
    ψ x - θ x ≤
      c * (x ^ (-(1 : ℝ) / 2) +
        max (log x / log 2 - 2) 0 * x ^ (-(2 : ℝ) / 3)) * x :=
  (psi_sub_theta_le_of_theta_le hx hθ).trans_eq (mul_sqrt_add_max_rpow_eq hx)

/-- A linear upper bound for `ψ` gives a lower bound for `θ` through Costa Pereira's comparison
`ψ(x) − θ(x) ≤ ψ(x^{1/2}) + ψ(x^{1/3}) + ψ(x^{1/5})`: if `ψ(y) ≤ c₀ y` for every `y ≥ 2`, then
`ψ(x) − c₀ (√x + x^{1/3} + x^{1/5}) ≤ θ(x)` for `x ≥ 0`. -/
theorem theta_ge_psi_sub_mul {c₀ x : ℝ} (hc₀ : ∀ y, 2 ≤ y → ψ y ≤ c₀ * y) (hx : 0 ≤ x) :
    ψ x - c₀ * (√x + x ^ ((1 : ℝ) / 3) + x ^ ((1 : ℝ) / 5)) ≤ θ x := by
  have := psi_sub_theta_le_psi_add_psi_add_psi x
  rw [← one_div, ← one_div, ← one_div, ← sqrt_eq_rpow] at this
  have h2 := psi_le_mul_of_two_le (sqrt_nonneg x) hc₀
  have h3 := psi_le_mul_of_two_le (rpow_nonneg hx ((1 : ℝ) / 3)) hc₀
  have h5 := psi_le_mul_of_two_le (rpow_nonneg hx ((1 : ℝ) / 5)) hc₀
  linarith

/-- Additive transfer from `|ψ x - x|` to `|θ x - x|` using a linear bound `θ y ≤ c * y`
on `[2, ∞)`. -/
theorem abs_theta_sub_self_le_of_theta_le {c x : ℝ} (hx : 0 ≤ x)
    (hθ : ∀ y, 2 ≤ y → θ y ≤ c * y) :
    |θ x - x| ≤
      |ψ x - x| + c * (√x + max (log x / log 2 - 2) 0 * x ^ ((1 : ℝ) / 3)) := by
  have h1 := psi_sub_theta_le_of_theta_le hx hθ
  have h2 := theta_le_psi x
  rw [abs_le]
  constructor <;> linarith [neg_abs_le (ψ x - x), le_abs_self (ψ x - x)]

/-- Additive transfer from `|θ x - x|` to `|ψ x - x|` using a linear bound `θ y ≤ c * y`
on `[2, ∞)`. -/
theorem abs_psi_sub_self_le_of_theta_le {c x : ℝ} (hx : 0 ≤ x)
    (hθ : ∀ y, 2 ≤ y → θ y ≤ c * y) :
    |ψ x - x| ≤
      |θ x - x| + c * (√x + max (log x / log 2 - 2) 0 * x ^ ((1 : ℝ) / 3)) := by
  have h1 := psi_sub_theta_le_of_theta_le hx hθ
  have h2 := theta_le_psi x
  rw [abs_le]
  constructor <;> linarith [neg_abs_le (θ x - x), le_abs_self (θ x - x)]

/-- Unconditional additive transfer from `|ψ x - x|` to `|θ x - x|`. -/
theorem abs_theta_sub_self_le_abs_psi_sub_self_add {x : ℝ} (hx : 0 ≤ x) :
    |θ x - x| ≤
      |ψ x - x| + log 4 * (√x + max (log x / log 2 - 2) 0 * x ^ ((1 : ℝ) / 3)) :=
  abs_theta_sub_self_le_of_theta_le hx fun _ hy ↦ theta_le_log4_mul_x (by linarith)

/-- Unconditional additive transfer from `|θ x - x|` to `|ψ x - x|`. -/
theorem abs_psi_sub_self_le_abs_theta_sub_self_add {x : ℝ} (hx : 0 ≤ x) :
    |ψ x - x| ≤
      |θ x - x| + log 4 * (√x + max (log x / log 2 - 2) 0 * x ^ ((1 : ℝ) / 3)) :=
  abs_psi_sub_self_le_of_theta_le hx fun _ hy ↦ theta_le_log4_mul_x (by linarith)

/-- Relative-error transfer from `|ψ x - x| ≤ ε * x` to `|θ x - x|` using `θ y ≤ c * y`
on `[2, ∞)`. -/
theorem abs_theta_sub_self_le_mul_of_theta_le_of_abs_psi_sub_self_le {c ε x : ℝ} (hx : 0 ≤ x)
    (hθ : ∀ y, 2 ≤ y → θ y ≤ c * y) (hψ : |ψ x - x| ≤ ε * x) :
    |θ x - x| ≤
      (ε + c * (x ^ (-(1 : ℝ) / 2) +
        max (log x / log 2 - 2) 0 * x ^ (-(2 : ℝ) / 3))) * x := by
  calc |θ x - x|
      ≤ |ψ x - x| + c * (√x + max (log x / log 2 - 2) 0 * x ^ ((1 : ℝ) / 3)) :=
        abs_theta_sub_self_le_of_theta_le hx hθ
    _ = |ψ x - x| + c * (x ^ (-(1 : ℝ) / 2) +
          max (log x / log 2 - 2) 0 * x ^ (-(2 : ℝ) / 3)) * x := by
        rw [mul_sqrt_add_max_rpow_eq hx]
    _ ≤ ε * x + c * (x ^ (-(1 : ℝ) / 2) +
          max (log x / log 2 - 2) 0 * x ^ (-(2 : ℝ) / 3)) * x :=
        add_le_add hψ le_rfl
    _ = _ := by ring

/-- Unconditional relative-error transfer from `|ψ x - x| ≤ ε * x` to `|θ x - x|`. -/
theorem abs_theta_sub_self_le_mul_of_abs_psi_sub_self_le {ε x : ℝ} (hx : 0 ≤ x)
    (hψ : |ψ x - x| ≤ ε * x) :
    |θ x - x| ≤
      (ε + log 4 * (x ^ (-(1 : ℝ) / 2) +
        max (log x / log 2 - 2) 0 * x ^ (-(2 : ℝ) / 3))) * x :=
  abs_theta_sub_self_le_mul_of_theta_le_of_abs_psi_sub_self_le hx
    (fun _ hy ↦ theta_le_log4_mul_x (by linarith)) hψ

/-- Relative-error transfer from `|θ x - x| ≤ ε * x` to `|ψ x - x|` using `θ y ≤ c * y`
on `[2, ∞)`. -/
theorem abs_psi_sub_self_le_mul_of_theta_le_of_abs_theta_sub_self_le {c ε x : ℝ} (hx : 0 ≤ x)
    (hθ : ∀ y, 2 ≤ y → θ y ≤ c * y) (hθx : |θ x - x| ≤ ε * x) :
    |ψ x - x| ≤
      (ε + c * (x ^ (-(1 : ℝ) / 2) +
        max (log x / log 2 - 2) 0 * x ^ (-(2 : ℝ) / 3))) * x := by
  calc |ψ x - x|
      ≤ |θ x - x| + c * (√x + max (log x / log 2 - 2) 0 * x ^ ((1 : ℝ) / 3)) :=
        abs_psi_sub_self_le_of_theta_le hx hθ
    _ = |θ x - x| + c * (x ^ (-(1 : ℝ) / 2) +
          max (log x / log 2 - 2) 0 * x ^ (-(2 : ℝ) / 3)) * x := by
        rw [mul_sqrt_add_max_rpow_eq hx]
    _ ≤ ε * x + c * (x ^ (-(1 : ℝ) / 2) +
          max (log x / log 2 - 2) 0 * x ^ (-(2 : ℝ) / 3)) * x :=
        add_le_add hθx le_rfl
    _ = _ := by ring

/-- Unconditional relative-error transfer from `|θ x - x| ≤ ε * x` to `|ψ x - x|`. -/
theorem abs_psi_sub_self_le_mul_of_abs_theta_sub_self_le {ε x : ℝ} (hx : 0 ≤ x)
    (hθx : |θ x - x| ≤ ε * x) :
    |ψ x - x| ≤
      (ε + log 4 * (x ^ (-(1 : ℝ) / 2) +
        max (log x / log 2 - 2) 0 * x ^ (-(2 : ℝ) / 3))) * x :=
  abs_psi_sub_self_le_mul_of_theta_le_of_abs_theta_sub_self_le hx
    (fun _ hy ↦ theta_le_log4_mul_x (by linarith)) hθx

/-! ### The number of prime powers -/

/-- The prime powers `m ≤ x` number `∑_{1 ≤ k ≤ log x / log 2} π(x^{1/k})`, for `x ≥ 0`. -/
theorem card_filter_isPrimePow_eq_sum_primeCounting {x : ℝ} (hx : 0 ≤ x) :
    #{n ∈ Ioc 0 ⌊x⌋₊ | IsPrimePow n} =
      ∑ k ∈ Icc 1 ⌊log x / log 2⌋₊, Nat.primeCounting ⌊x ^ ((1 : ℝ) / k)⌋₊ := by
  rw [card_eq_sum_ones]
  convert sum_PrimePow_eq_sum_sum (fun _ ↦ 1) hx using 2 with k
  rw [← card_eq_sum_ones, ← Nat.primesLE_eq_filter_Ioc_zero, Nat.primesLE_card_eq_primeCounting]

/-- For `x ≥ 2`, the prime powers `m ≤ x` number at most `π(x) + (log x / log 2 − 1) √x`: each
`π(x^{1/k})` with `k ≥ 2` is at most `√x`. -/
theorem card_filter_isPrimePow_le {x : ℝ} (hx : 2 ≤ x) :
    (#{n ∈ Ioc 0 ⌊x⌋₊ | IsPrimePow n} : ℝ) ≤
      Nat.primeCounting ⌊x⌋₊ + (log x / log 2 - 1) * √x := by
  have hx0 : 0 ≤ x := by linarith
  have hL : 1 ≤ log x / log 2 := by
    rw [le_div_iff₀ (log_pos one_lt_two), one_mul]
    exact log_le_log two_pos hx
  have hK : 1 ≤ ⌊log x / log 2⌋₊ := Nat.le_floor (by exact_mod_cast hL)
  have hsplit : Icc 1 ⌊log x / log 2⌋₊ = insert 1 (Icc 2 ⌊log x / log 2⌋₊) := by
    ext k
    simp only [mem_Icc, mem_insert]
    omega
  rw [card_filter_isPrimePow_eq_sum_primeCounting hx0, hsplit, sum_insert (by simp),
    Nat.cast_add, Nat.cast_sum]
  simp only [Nat.cast_one, div_one, rpow_one]
  gcongr
  refine (TauCeti.sum_Icc_floor_le_max_mul (by linarith) (sqrt_nonneg x) 2
    fun k hk ↦ ?_).trans_eq ?_
  · have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast (mem_Icc.mp hk).1
    calc (Nat.primeCounting ⌊x ^ ((1 : ℝ) / k)⌋₊ : ℝ)
        ≤ ⌊x ^ ((1 : ℝ) / k)⌋₊ := by exact_mod_cast Nat.primeCounting_le_self _
      _ ≤ x ^ ((1 : ℝ) / k) := Nat.floor_le (rpow_nonneg hx0 _)
      _ ≤ x ^ ((1 : ℝ) / 2) := rpow_le_rpow_of_exponent_le (by linarith) (by gcongr)
      _ = √x := (sqrt_eq_rpow x).symm
  · rw [max_eq_left (by push_cast; linarith)]
    push_cast
    ring

/-- For `x ≥ 2`, the prime powers `m ≤ x` number at most `6 x / log x`. -/
theorem card_filter_isPrimePow_le_six_mul_div_log {x : ℝ} (hx : 2 ≤ x) :
    (#{n ∈ Ioc 0 ⌊x⌋₊ | IsPrimePow n} : ℝ) ≤ 6 * x / log x := by
  have hx0 : 0 < x := by linarith
  have hL : 0 < log x := log_pos (by linarith)
  have hl2 := log_two_gt_d9
  have hl2' := log_two_lt_d9
  have he := exp_one_gt_d9
  have hsx : √x * √x = x := mul_self_sqrt hx0.le
  have hπ := pi_le_log4_mul_div (by linarith : 1 < x)
  rw [log_sqrt hx0.le, show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow] at hπ
  have hkey := sq_log_mul_exp_one_le_sixteen_mul_sqrt (by linarith : (1 : ℝ) ≤ x)
  have hcount := card_filter_isPrimePow_le hx
  rw [le_div_iff₀ hL]
  -- `π(x) ≤ 4 log 2 · x / log x + √x`, and `(log x)² √x ≤ 16 x / e²`.
  have hπ' : (Nat.primeCounting ⌊x⌋₊ : ℝ) * log x ≤ 4 * log 2 * x + √x * log x := by
    have e : ((2 : ℕ) : ℝ) * log 2 * x / (log x / 2) * log x = 4 * log 2 * x := by
      field_simp
      norm_num
    have := mul_le_mul_of_nonneg_right hπ hL.le
    rw [add_mul, e] at this
    exact this
  have hsq : log x ^ 2 * √x * exp 1 ^ 2 ≤ 16 * x := by
    nlinarith [sqrt_nonneg x]
  have hpos : 0 < log 2 := by linarith
  calc (#{n ∈ Ioc 0 ⌊x⌋₊ | IsPrimePow n} : ℝ) * log x
      ≤ (Nat.primeCounting ⌊x⌋₊ + (log x / log 2 - 1) * √x) * log x :=
        mul_le_mul_of_nonneg_right hcount hL.le
    _ ≤ 4 * log 2 * x + log x ^ 2 * √x / log 2 := by
        have : (log x / log 2 - 1) * √x * log x = log x ^ 2 * √x / log 2 - √x * log x := by
          field_simp
        nlinarith
    _ ≤ 6 * x := by
        -- numerically, `4 log 2 + 16 / (e² log 2) < 5.9`
        have he2 : 7.38 < exp 1 ^ 2 := by nlinarith
        have hl : 2.23 < (6 - 4 * log 2) * log 2 := by nlinarith
        have h16 : (16 : ℝ) ≤ (6 - 4 * log 2) * log 2 * exp 1 ^ 2 := by nlinarith
        have : log x ^ 2 * √x / log 2 ≤ (6 - 4 * log 2) * x := by
          rw [div_le_iff₀ hpos]
          refine le_of_mul_le_mul_right ?_ (by positivity : 0 < exp 1 ^ 2)
          nlinarith
        linarith

/-- For every integer `N ≥ 2`, the prime powers below `N` number at most `6 N / log N`. -/
theorem card_filter_range_isPrimePow_le_six_mul_div_log {N : ℕ} (hN : 2 ≤ N) :
    (#{m ∈ range N | IsPrimePow m} : ℝ) ≤ 6 * N / log N := by
  refine le_trans ?_ (card_filter_isPrimePow_le_six_mul_div_log (by exact_mod_cast hN))
  rw [Nat.floor_natCast]
  exact_mod_cast card_le_card fun m hm ↦ by
    simp only [mem_filter, mem_range, mem_Ioc] at hm ⊢
    exact ⟨⟨hm.2.pos, hm.1.le⟩, hm.2⟩

/-- Asymptotic bound for the prime-power count on `ℝ`:
`#{n ∈ Ioc 0 ⌊x⌋₊ | IsPrimePow n} = O(x / log x)` as `x → ∞`. -/
theorem isBigO_card_filter_isPrimePow_div_log :
    (fun x : ℝ ↦ (#{n ∈ Ioc 0 ⌊x⌋₊ | IsPrimePow n} : ℝ)) =O[atTop]
      (fun x : ℝ ↦ x / log x) := by
  refine Asymptotics.IsBigO.of_bound 6 ?_
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
  have hlog : 0 < log x := log_pos (by linarith)
  rw [norm_of_nonneg (Nat.cast_nonneg _), norm_of_nonneg (by positivity)]
  simpa only [mul_div_assoc] using card_filter_isPrimePow_le_six_mul_div_log hx

/-! ### The cube-root tail coefficient and its dyadic envelope -/

/-- The dimensionless coefficient `f(x) = ∑ k ∈ Icc 3 ⌊log x / log 2⌋₊, x ^ (1 / k - 1 / 3)`
controlling the cube-root tail `∑ k ≥ 3, θ (x ^ (1 / k))` of `ψ x - θ x` (Broadbent, Kadiri,
Lumley, Ng, and Wilk 2021). -/
noncomputable def psiSubThetaTailCoeff (x : ℝ) : ℝ :=
  ∑ k ∈ Icc 3 ⌊log x / log 2⌋₊, x ^ ((1 : ℝ) / k - 1 / 3)

/-- Definitional equation for `psiSubThetaTailCoeff`. -/
theorem psiSubThetaTailCoeff_def (x : ℝ) :
    psiSubThetaTailCoeff x = ∑ k ∈ Icc 3 ⌊log x / log 2⌋₊, x ^ ((1 : ℝ) / k - 1 / 3) := (rfl)

/-- `psiSubThetaTailCoeff x = 0` for `0 ≤ x < 8`. -/
theorem psiSubThetaTailCoeff_eq_zero_of_lt_eight {x : ℝ} (hx0 : 0 ≤ x) (hx8 : x < 8) :
    psiSubThetaTailCoeff x = 0 := by
  rw [psiSubThetaTailCoeff_def]
  have hlt : ⌊log x / log 2⌋₊ < 3 := by
    rw [← Real.logb, Real.natFloor_logb_lt_iff_lt_pow one_lt_two hx0 (by norm_num)]
    linarith
  rw [Icc_eq_empty (by omega), sum_empty]

/-- For `x ≥ 0`, `psiSubThetaTailCoeff x = 0` if and only if `x < 8`. -/
@[simp]
theorem psiSubThetaTailCoeff_eq_zero_iff {x : ℝ} (hx : 0 ≤ x) :
    psiSubThetaTailCoeff x = 0 ↔ x < 8 := by
  refine ⟨fun h0 ↦ ?_, psiSubThetaTailCoeff_eq_zero_of_lt_eight hx⟩
  by_contra! hx8
  have h3 : 3 ≤ ⌊log x / log 2⌋₊ := by
    rw [← Real.logb, Real.le_natFloor_logb_iff_pow_le one_lt_two hx (by norm_num)]
    linarith
  have h1 : (1 : ℝ) ≤ psiSubThetaTailCoeff x := by
    rw [psiSubThetaTailCoeff_def]
    have hmem : (3 : ℕ) ∈ Icc 3 ⌊log x / log 2⌋₊ := mem_Icc.mpr ⟨le_rfl, h3⟩
    simpa using single_le_sum (f := fun k : ℕ ↦ x ^ ((1 : ℝ) / k - 1 / 3))
      (fun _ _ ↦ rpow_nonneg hx _) hmem
  linarith

/-- `psiSubThetaTailCoeff 0 = 0`. -/
@[simp]
theorem psiSubThetaTailCoeff_zero : psiSubThetaTailCoeff 0 = 0 :=
  psiSubThetaTailCoeff_eq_zero_of_lt_eight le_rfl (by norm_num)

/-- `psiSubThetaTailCoeff 1 = 0`. -/
@[simp]
theorem psiSubThetaTailCoeff_one : psiSubThetaTailCoeff 1 = 0 :=
  psiSubThetaTailCoeff_eq_zero_of_lt_eight zero_le_one (by norm_num)

/-- `psiSubThetaTailCoeff x ≥ 0` for every `x ≥ 0`. -/
@[simp]
theorem psiSubThetaTailCoeff_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ psiSubThetaTailCoeff x :=
  sum_nonneg fun _ _ ↦ rpow_nonneg hx _

/-- Multiplying `psiSubThetaTailCoeff x` by `x ^ (1 / 3)` recovers the tail power sum
`∑ k ∈ Icc 3 ⌊log x / log 2⌋₊, x ^ (1 / k)` for every `x ≥ 0`. -/
theorem psiSubThetaTailCoeff_mul_rpow {x : ℝ} (hx : 0 ≤ x) :
    psiSubThetaTailCoeff x * x ^ ((1 : ℝ) / 3) =
      ∑ k ∈ Icc 3 ⌊log x / log 2⌋₊, x ^ ((1 : ℝ) / k) := by
  rcases hx.eq_or_lt with rfl | hx0
  · simp
  · rw [psiSubThetaTailCoeff_def, sum_mul]
    refine sum_congr rfl fun k _ ↦ ?_
    rw [← rpow_add hx0, sub_add_cancel]

/-- Crude upper bound `psiSubThetaTailCoeff x ≤ max (log x / log 2 - 2) 0` for every `x ≥ 0`. -/
theorem psiSubThetaTailCoeff_le_max_sub_two {x : ℝ} (hx : 0 ≤ x) :
    psiSubThetaTailCoeff x ≤ max (log x / log 2 - 2) 0 := by
  rcases hx.eq_or_lt with rfl | hx0
  · simp
  · refine le_of_mul_le_mul_right ?_ (rpow_pos_of_pos hx0 ((1 : ℝ) / 3))
    exact (psiSubThetaTailCoeff_mul_rpow hx).trans_le (sum_rpow_one_div_le hx)

/-- Exponential evaluation of `psiSubThetaTailCoeff`:
`psiSubThetaTailCoeff (exp b) = ∑ k ∈ Icc 3 ⌊b / log 2⌋₊, exp (b * (1 / k - 1 / 3))`. -/
theorem psiSubThetaTailCoeff_exp (b : ℝ) :
    psiSubThetaTailCoeff (exp b) =
      ∑ k ∈ Icc 3 ⌊b / log 2⌋₊, exp (b * ((1 : ℝ) / k - 1 / 3)) := by
  rw [psiSubThetaTailCoeff_def, log_exp]
  refine sum_congr rfl fun k _ ↦ ?_
  rw [← exp_mul]

/-- On the dyadic interval `[2 ^ n, 2 ^ (n + 1))`, `psiSubThetaTailCoeff` has the fixed upper
summation limit `n`. -/
theorem psiSubThetaTailCoeff_eq_sum_of_mem_Ico {n : ℕ} {x : ℝ}
    (hx : x ∈ Set.Ico ((2 : ℝ) ^ n) ((2 : ℝ) ^ (n + 1))) :
    psiSubThetaTailCoeff x = ∑ k ∈ Icc 3 n, x ^ ((1 : ℝ) / k - 1 / 3) := by
  rw [psiSubThetaTailCoeff_def, ← Real.logb, Real.natFloor_logb_eq_of_mem_Ico one_lt_two hx]

/-- Bound on the cube-root tail `∑ k ≥ 3, θ (x ^ (1 / k))` in terms of `psiSubThetaTailCoeff`:
if `θ y ≤ c * y` for all `y ≥ 2`, then for every `x ≥ 0`,
`∑ k ∈ Icc 3 ⌊log x / log 2⌋₊, θ (x ^ (1 / k)) ≤ c * psiSubThetaTailCoeff x * x ^ (1 / 3)`. -/
theorem sum_theta_rpow_le {c x : ℝ} (hx : 0 ≤ x) (hθ : ∀ y, 2 ≤ y → θ y ≤ c * y) :
    ∑ k ∈ Icc 3 ⌊log x / log 2⌋₊, θ (x ^ ((1 : ℝ) / k)) ≤
      c * psiSubThetaTailCoeff x * x ^ ((1 : ℝ) / 3) :=
  (sum_theta_rpow_le_mul_sum_rpow hθ hx _).trans_eq <| by
    rw [mul_assoc, psiSubThetaTailCoeff_mul_rpow hx]

/-- Exact value of `psiSubThetaTailCoeff` at powers of `2`: for `n ≥ 3`,
`psiSubThetaTailCoeff (2 ^ n) = 1 + ∑ k ∈ Icc 4 n, 2 ^ (n / k - n / 3)`. -/
theorem psiSubThetaTailCoeff_two_pow {n : ℕ} (hn : 3 ≤ n) :
    psiSubThetaTailCoeff ((2 : ℝ) ^ n) =
      1 + ∑ k ∈ Icc 4 n, (2 : ℝ) ^ ((n : ℝ) / k - (n : ℝ) / 3) := by
  rw [psiSubThetaTailCoeff_def, ← Real.logb, Real.natFloor_logb_pow_self one_lt_two,
    ← add_sum_Ioc_eq_sum_Icc hn, ← Icc_add_one_left_eq_Ioc]
  congr 1
  · norm_num
  · refine sum_congr rfl fun k _ ↦ ?_
    rw [← rpow_natCast, ← rpow_mul zero_le_two]
    congr 1
    ring

/-- On every dyadic interval `[2 ^ n, 2 ^ (n + 1))`, `psiSubThetaTailCoeff` is antitone. -/
theorem antitoneOn_psiSubThetaTailCoeff_Ico_two_pow (n : ℕ) :
    AntitoneOn psiSubThetaTailCoeff (Set.Ico ((2 : ℝ) ^ n) ((2 : ℝ) ^ (n + 1))) := by
  intro x hx y hy hxy
  rw [psiSubThetaTailCoeff_eq_sum_of_mem_Ico hx, psiSubThetaTailCoeff_eq_sum_of_mem_Ico hy]
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx.1
  exact sum_le_sum fun k hk ↦
    rpow_le_rpow_of_nonpos hx0 hxy
      (sub_nonpos.mpr
        (one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast (mem_Icc.mp hk).1)))

/-- On every dyadic interval `[2 ^ n, 2 ^ (n + 1))` with `n ≥ 4`, `psiSubThetaTailCoeff` is
strictly decreasing. -/
theorem strictAntiOn_psiSubThetaTailCoeff_Ico_two_pow {n : ℕ} (hn : 4 ≤ n) :
    StrictAntiOn psiSubThetaTailCoeff (Set.Ico ((2 : ℝ) ^ n) ((2 : ℝ) ^ (n + 1))) := by
  intro x hx y hy hxy
  rw [psiSubThetaTailCoeff_eq_sum_of_mem_Ico hx, psiSubThetaTailCoeff_eq_sum_of_mem_Ico hy]
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx.1
  exact sum_lt_sum
    (fun k hk ↦ rpow_le_rpow_of_nonpos hx0 hxy.le
      (sub_nonpos.mpr (one_div_le_one_div_of_le (by norm_num)
        (by exact_mod_cast (mem_Icc.mp hk).1))))
    ⟨4, mem_Icc.mpr ⟨by omega, hn⟩, rpow_lt_rpow_of_neg hx0 hxy (by norm_num)⟩

private lemma two_rpow_mul_sub_psiSubThetaTailCoeff_two_pow {n : ℕ} (hn : 3 ≤ n) :
    (2 : ℝ) ^ (((n : ℝ) + 1) / 3) *
      (psiSubThetaTailCoeff ((2 : ℝ) ^ n) - psiSubThetaTailCoeff ((2 : ℝ) ^ (n + 1))) =
      (∑ k ∈ Icc 4 n, (2 : ℝ) ^ (((n : ℝ) + 1) / k) *
        ((2 : ℝ) ^ ((1 : ℝ) / 3 - 1 / k) - 1)) - 2 := by
  rw [psiSubThetaTailCoeff_two_pow hn, psiSubThetaTailCoeff_two_pow (by omega : 3 ≤ n + 1)]
  rw [sum_Icc_succ_top (by omega : 4 ≤ n + 1), Nat.cast_add, Nat.cast_one]
  have hdiv : ((n : ℝ) + 1) / ((n : ℝ) + 1) = 1 := div_self (by positivity)
  rw [hdiv]
  have hsub : (1 + ∑ k ∈ Icc 4 n, (2 : ℝ) ^ ((n : ℝ) / k - (n : ℝ) / 3)) -
      (1 + ((∑ k ∈ Icc 4 n, (2 : ℝ) ^ (((n : ℝ) + 1) / k - ((n : ℝ) + 1) / 3)) +
        (2 : ℝ) ^ (1 - ((n : ℝ) + 1) / 3))) =
      (∑ k ∈ Icc 4 n, ((2 : ℝ) ^ ((n : ℝ) / k - (n : ℝ) / 3) -
        (2 : ℝ) ^ (((n : ℝ) + 1) / k - ((n : ℝ) + 1) / 3))) -
      (2 : ℝ) ^ (1 - ((n : ℝ) + 1) / 3) := by
    rw [sum_sub_distrib]
    ring
  rw [hsub, mul_sub, mul_sum]
  congr 1
  · refine sum_congr rfl fun k _ ↦ ?_
    rw [mul_sub, mul_sub, mul_one, ← rpow_add zero_lt_two, ← rpow_add zero_lt_two,
      ← rpow_add zero_lt_two]
    -- Match the exponents `((n+1)/3) + (n/k - n/3)` and `((n+1)/3) + ((n+1)/k - (n+1)/3)`
    -- against `((n+1)/k) + (1/3 - 1/k)` and `(n+1)/k`.
    rw [show ((n : ℝ) + 1) / 3 + ((n : ℝ) / k - (n : ℝ) / 3) =
          ((n : ℝ) + 1) / k + ((1 : ℝ) / 3 - 1 / k) by ring,
      show ((n : ℝ) + 1) / 3 + (((n : ℝ) + 1) / k - ((n : ℝ) + 1) / 3) =
          ((n : ℝ) + 1) / k by ring]
  · rw [← rpow_add zero_lt_two, add_sub_cancel, rpow_one]

private lemma two_lt_sum_Icc_four_nine_term :
    (2 : ℝ) < ∑ k ∈ Icc (4 : ℕ) 9,
      (2 : ℝ) ^ ((10 : ℝ) / k) * ((2 : ℝ) ^ ((1 : ℝ) / 3 - 1 / k) - 1) := by
  let L : ℝ := 6931 / 10000
  have hL : L < log 2 := by dsimp only [L]; linarith [log_two_gt_d9]
  have hterm : ∀ k ∈ Icc (4 : ℕ) 9,
      2 * (1 + ((10 : ℝ) / k - 1) * L + (((10 : ℝ) / k - 1) * L) ^ 2 / 2) *
        (((1 : ℝ) / 3 - 1 / k) * L) ≤
      (2 : ℝ) ^ ((10 : ℝ) / k) * ((2 : ℝ) ^ ((1 : ℝ) / 3 - 1 / k) - 1) := by
    intro k hk
    have hk4 : (4 : ℝ) ≤ k := Nat.cast_le.mpr (mem_Icc.mp hk).1
    have hk9 : (k : ℝ) ≤ 9 := Nat.cast_le.mpr (mem_Icc.mp hk).2
    have hu1 : 0 ≤ (10 : ℝ) / k - 1 :=
      sub_nonneg.mpr ((one_le_div (by linarith)).mpr (by linarith))
    have hu2 : 0 ≤ (1 : ℝ) / 3 - 1 / k :=
      sub_nonneg.mpr (one_div_le_one_div_of_le (by norm_num) (by linarith))
    have h1 : 2 * (1 + ((10 : ℝ) / k - 1) * L + (((10 : ℝ) / k - 1) * L) ^ 2 / 2) ≤
        (2 : ℝ) ^ ((10 : ℝ) / k) := by
      calc 2 * (1 + ((10 : ℝ) / k - 1) * L + (((10 : ℝ) / k - 1) * L) ^ 2 / 2)
          ≤ 2 * exp (((10 : ℝ) / k - 1) * L) := by
            gcongr; exact quadratic_le_exp_of_nonneg (by positivity)
        _ ≤ 2 * exp (((10 : ℝ) / k - 1) * log 2) := by gcongr
        _ = (2 : ℝ) ^ (1 : ℝ) * (2 : ℝ) ^ ((10 : ℝ) / k - 1) := by
            rw [rpow_one, rpow_def_of_pos zero_lt_two, mul_comm (log 2)]
        _ = (2 : ℝ) ^ ((10 : ℝ) / k) := by rw [← rpow_add zero_lt_two, add_sub_cancel]
    have h2 : ((1 : ℝ) / 3 - 1 / k) * L ≤ (2 : ℝ) ^ ((1 : ℝ) / 3 - 1 / k) - 1 := by
      have hexp := add_one_le_exp (((1 : ℝ) / 3 - 1 / k) * log 2)
      rw [rpow_def_of_pos zero_lt_two, mul_comm (log 2)]
      have hmul : ((1 : ℝ) / 3 - 1 / k) * L ≤ ((1 : ℝ) / 3 - 1 / k) * log 2 := by gcongr
      linarith
    exact mul_le_mul h1 h2 (by positivity) (by positivity)
  have hnum : (2 : ℝ) < ∑ k ∈ Icc (4 : ℕ) 9,
      2 * (1 + ((10 : ℝ) / k - 1) * L + (((10 : ℝ) / k - 1) * L) ^ 2 / 2) *
        (((1 : ℝ) / 3 - 1 / k) * L) := by
    have hIcc : Icc (4 : ℕ) 9 = {4, 5, 6, 7, 8, 9} := by decide
    rw [hIcc]
    norm_num [L]
  exact hnum.trans_le (sum_le_sum hterm)

/-- Strict decrease of `psiSubThetaTailCoeff` at powers of `2` starting at `n = 9`:
`psiSubThetaTailCoeff (2 ^ (n + 1)) < psiSubThetaTailCoeff (2 ^ n)` for every `n ≥ 9`.
The threshold `9` is sharp since `f (2 ^ 8) < f (2 ^ 9)`. -/
theorem psiSubThetaTailCoeff_two_pow_succ_lt {n : ℕ} (hn : 9 ≤ n) :
    psiSubThetaTailCoeff ((2 : ℝ) ^ (n + 1)) < psiSubThetaTailCoeff ((2 : ℝ) ^ n) := by
  have hpos : 0 < (2 : ℝ) ^ (((n : ℝ) + 1) / 3) := by positivity
  suffices h : 0 < (2 : ℝ) ^ (((n : ℝ) + 1) / 3) *
      (psiSubThetaTailCoeff ((2 : ℝ) ^ n) - psiSubThetaTailCoeff ((2 : ℝ) ^ (n + 1))) by
    nlinarith
  rw [two_rpow_mul_sub_psiSubThetaTailCoeff_two_pow (by omega)]
  have hge : ∑ k ∈ Icc (4 : ℕ) 9,
        (2 : ℝ) ^ ((10 : ℝ) / k) * ((2 : ℝ) ^ ((1 : ℝ) / 3 - 1 / k) - 1) ≤
      ∑ k ∈ Icc 4 n, (2 : ℝ) ^ (((n : ℝ) + 1) / k) * ((2 : ℝ) ^ ((1 : ℝ) / 3 - 1 / k) - 1) := by
    calc ∑ k ∈ Icc (4 : ℕ) 9, (2 : ℝ) ^ ((10 : ℝ) / k) * ((2 : ℝ) ^ ((1 : ℝ) / 3 - 1 / k) - 1)
        ≤ ∑ k ∈ Icc (4 : ℕ) 9,
            (2 : ℝ) ^ (((n : ℝ) + 1) / k) * ((2 : ℝ) ^ ((1 : ℝ) / 3 - 1 / k) - 1) := by
          refine sum_le_sum fun k hk ↦ ?_
          have hk4 : 4 ≤ k := (mem_Icc.mp hk).1
          have hfac : 0 ≤ (2 : ℝ) ^ ((1 : ℝ) / 3 - 1 / k) - 1 := sub_nonneg.mpr <|
            one_le_rpow one_le_two <| sub_nonneg.mpr <|
              one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast (by omega : 3 ≤ k))
          have h10 : (10 : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast (by omega : 10 ≤ n + 1)
          gcongr
          exact one_le_two
      _ ≤ ∑ k ∈ Icc 4 n,
            (2 : ℝ) ^ (((n : ℝ) + 1) / k) * ((2 : ℝ) ^ ((1 : ℝ) / 3 - 1 / k) - 1) :=
          sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right hn) fun k hk _ ↦
            mul_nonneg (by positivity) <| sub_nonneg.mpr <| one_le_rpow one_le_two <|
              sub_nonneg.mpr <| one_div_le_one_div_of_le (by norm_num)
                (by exact_mod_cast (by have := (mem_Icc.mp hk).1; omega : 3 ≤ k))
  linarith [two_lt_sum_Icc_four_nine_term]

/-- Monotonicity of `psiSubThetaTailCoeff` along powers of `2` for `9 ≤ m ≤ n`. -/
theorem psiSubThetaTailCoeff_two_pow_anti {m n : ℕ} (hm : 9 ≤ m) (hmn : m ≤ n) :
    psiSubThetaTailCoeff ((2 : ℝ) ^ n) ≤ psiSubThetaTailCoeff ((2 : ℝ) ^ m) := by
  induction hmn with
  | refl => exact le_rfl
  | @step k hmk ih => exact (psiSubThetaTailCoeff_two_pow_succ_lt (hm.trans hmk)).le.trans ih

private lemma psiSubThetaTailCoeff_two_pow_eight_lt :
    psiSubThetaTailCoeff ((2 : ℝ) ^ 8) < 16 / 5 := by
  -- Expand the sum over `Icc 4 8` and bound each term `2 ^ (8 / k - 8 / 3)` from above.
  rw [psiSubThetaTailCoeff_two_pow (by norm_num)]
  rw [show Icc (4 : ℕ) 8 = {4, 5, 6, 7, 8} by decide]
  norm_num
  have bound {e u : ℝ} {p q : ℕ} (hq : q ≠ 0) (hu : 0 ≤ u) (he : e ≤ -(p : ℝ) / q)
      (hnum : 1 < u ^ q * (2 : ℝ) ^ p) : (2 : ℝ) ^ e < u :=
    (rpow_le_rpow_of_exponent_le one_le_two he).trans_lt
      ((rpow_neg_div_lt_iff zero_lt_two hu hq).2 hnum)
  have h4 : (2 : ℝ) ^ ((8 : ℝ) / 4 - 8 / 3) < 63 / 100 :=
    bound (p := 2) (q := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h5 : (2 : ℝ) ^ ((8 : ℝ) / 5 - 8 / 3) < 48 / 100 :=
    bound (p := 16) (q := 15) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h6 : (2 : ℝ) ^ ((8 : ℝ) / 6 - 8 / 3) < 40 / 100 :=
    bound (p := 4) (q := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h7 : (2 : ℝ) ^ ((8 : ℝ) / 7 - 8 / 3) < 36 / 100 :=
    bound (p := 3) (q := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h8 : (2 : ℝ) ^ ((8 : ℝ) / 8 - 8 / 3) < 32 / 100 :=
    bound (p := 5) (q := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  linarith

private lemma lt_psiSubThetaTailCoeff_two_pow_nine :
    (16 : ℝ) / 5 < psiSubThetaTailCoeff ((2 : ℝ) ^ 9) := by
  -- Expand the sum over `Icc 4 9` and bound each term `2 ^ (9 / k - 9 / 3)` from below.
  rw [psiSubThetaTailCoeff_two_pow (by norm_num)]
  rw [show Icc (4 : ℕ) 9 = {4, 5, 6, 7, 8, 9} by decide]
  norm_num
  have bound {e u : ℝ} {p q : ℕ} (hq : q ≠ 0) (hu : 0 ≤ u) (he : -(p : ℝ) / q ≤ e)
      (hnum : u ^ q * (2 : ℝ) ^ p < 1) : u < (2 : ℝ) ^ e :=
    ((lt_rpow_neg_div_iff zero_lt_two hu hq).2 hnum).trans_le
      (rpow_le_rpow_of_exponent_le one_le_two he)
  have h4 : (19 : ℝ) / 32 < (2 : ℝ) ^ (-(3 / 4 : ℝ)) :=
    bound (p := 3) (q := 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h5 : (43 : ℝ) / 100 < (2 : ℝ) ^ (-(6 / 5 : ℝ)) :=
    bound (p := 6) (q := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h6 : (353 : ℝ) / 1000 < (2 : ℝ) ^ (-(3 / 2 : ℝ)) :=
    bound (p := 3) (q := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h7 : (304 : ℝ) / 1000 < (2 : ℝ) ^ (-(12 / 7 : ℝ)) :=
    bound (p := 12) (q := 7) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h8 : (27 : ℝ) / 100 < (2 : ℝ) ^ (-(15 / 8 : ℝ)) :=
    bound (p := 15) (q := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  linarith

/-- Sharpness of the threshold `n = 9` in `psiSubThetaTailCoeff_two_pow_succ_lt`:
at `n = 8`, `psiSubThetaTailCoeff (2 ^ 8) < psiSubThetaTailCoeff (2 ^ 9)`. -/
theorem psiSubThetaTailCoeff_two_pow_eight_lt_two_pow_nine :
    psiSubThetaTailCoeff ((2 : ℝ) ^ 8) < psiSubThetaTailCoeff ((2 : ℝ) ^ 9) :=
  psiSubThetaTailCoeff_two_pow_eight_lt.trans lt_psiSubThetaTailCoeff_two_pow_nine

/-- The uniform dyadic upper envelope
`F(X) = max (f X) (f (2 ^ (⌊log X / log 2⌋₊ + 1)))` bounding `psiSubThetaTailCoeff x`
for all `x ≥ X` once `X ≥ 2 ^ 8`. -/
noncomputable def psiSubThetaTailBound (X : ℝ) : ℝ :=
  max (psiSubThetaTailCoeff X) (psiSubThetaTailCoeff ((2 : ℝ) ^ (⌊log X / log 2⌋₊ + 1)))

/-- Definitional equation for `psiSubThetaTailBound`. -/
theorem psiSubThetaTailBound_def (X : ℝ) :
    psiSubThetaTailBound X =
      max (psiSubThetaTailCoeff X) (psiSubThetaTailCoeff ((2 : ℝ) ^ (⌊log X / log 2⌋₊ + 1))) :=
  (rfl)

/-- Exponential evaluation of `psiSubThetaTailBound`:
`psiSubThetaTailBound (exp b) = max (f (exp b)) (f (2 ^ (⌊b / log 2⌋₊ + 1)))`. -/
theorem psiSubThetaTailBound_exp (b : ℝ) :
    psiSubThetaTailBound (exp b) =
      max (psiSubThetaTailCoeff (exp b))
        (psiSubThetaTailCoeff ((2 : ℝ) ^ (⌊b / log 2⌋₊ + 1))) := by
  rw [psiSubThetaTailBound_def, log_exp]

/-- `psiSubThetaTailBound X ≥ 0` for every real `X`. -/
@[simp]
theorem psiSubThetaTailBound_nonneg (X : ℝ) : 0 ≤ psiSubThetaTailBound X :=
  le_max_of_le_right (psiSubThetaTailCoeff_nonneg (by positivity))

/-- `psiSubThetaTailCoeff X ≤ psiSubThetaTailBound X` for every real `X`. -/
theorem psiSubThetaTailCoeff_le_psiSubThetaTailBound_self (X : ℝ) :
    psiSubThetaTailCoeff X ≤ psiSubThetaTailBound X :=
  le_max_left _ _

/-- Uniform bound on `psiSubThetaTailCoeff`: for every `X ≥ 2 ^ 8` and every `x ≥ X`,
`psiSubThetaTailCoeff x ≤ psiSubThetaTailBound X`. -/
theorem psiSubThetaTailCoeff_le_psiSubThetaTailBound {X x : ℝ} (hX : (2 : ℝ) ^ 8 ≤ X)
    (hXx : X ≤ x) :
    psiSubThetaTailCoeff x ≤ psiSubThetaTailBound X := by
  set m := ⌊Real.logb 2 X⌋₊
  set n := ⌊Real.logb 2 x⌋₊
  have hm8 : 8 ≤ m :=
    (Real.le_natFloor_logb_iff_pow_le one_lt_two (by positivity) (by norm_num)).2 hX
  have hX1 : 1 ≤ X := le_trans (one_le_pow₀ one_le_two) hX
  have hx1 : 1 ≤ x := hX1.trans hXx
  have hmn : m ≤ n := Nat.floor_mono
    (div_le_div_of_nonneg_right (log_le_log (by linarith) hXx) (log_pos one_lt_two).le)
  have hXmem : X ∈ Set.Ico ((2 : ℝ) ^ m) ((2 : ℝ) ^ (m + 1)) :=
    ⟨Real.pow_natFloor_logb_le_self one_lt_two hX1,
      Real.lt_pow_natFloor_logb_add_one one_lt_two (by positivity)⟩
  have hxmem : x ∈ Set.Ico ((2 : ℝ) ^ n) ((2 : ℝ) ^ (n + 1)) :=
    ⟨Real.pow_natFloor_logb_le_self one_lt_two hx1,
      Real.lt_pow_natFloor_logb_add_one one_lt_two (by positivity)⟩
  rw [psiSubThetaTailBound_def, ← Real.logb]
  rcases hmn.eq_or_lt with hEq | hLt
  · rw [← hEq] at hxmem
    exact le_max_of_le_left
      (antitoneOn_psiSubThetaTailCoeff_Ico_two_pow m hXmem hxmem hXx)
  · have h2n_mem : (2 : ℝ) ^ n ∈ Set.Ico ((2 : ℝ) ^ n) ((2 : ℝ) ^ (n + 1)) :=
      ⟨le_rfl, pow_lt_pow_right₀ one_lt_two (Nat.lt_succ_self n)⟩
    refine le_max_of_le_right ?_
    calc psiSubThetaTailCoeff x
        ≤ psiSubThetaTailCoeff ((2 : ℝ) ^ n) :=
          antitoneOn_psiSubThetaTailCoeff_Ico_two_pow n h2n_mem hxmem hxmem.1
      _ ≤ psiSubThetaTailCoeff ((2 : ℝ) ^ (m + 1)) :=
          psiSubThetaTailCoeff_two_pow_anti (by omega) hLt

/-- Least-bound characterization of `psiSubThetaTailBound`: for every `X ≥ 2 ^ 8`,
`psiSubThetaTailBound X` is the least upper bound of `psiSubThetaTailCoeff` on `[X, ∞)`. -/
theorem psiSubThetaTailBound_le_iff_forall {X u : ℝ} (hX : (2 : ℝ) ^ 8 ≤ X) :
    psiSubThetaTailBound X ≤ u ↔ ∀ x, X ≤ x → psiSubThetaTailCoeff x ≤ u := by
  refine ⟨fun h x hx ↦ (psiSubThetaTailCoeff_le_psiSubThetaTailBound hX hx).trans h, fun h ↦ ?_⟩
  have hXpos : 0 < X := lt_of_lt_of_le (by positivity) hX
  rw [psiSubThetaTailBound_def, max_le_iff]
  refine ⟨h X le_rfl, h _ ?_⟩
  rw [← Real.logb]
  exact (Real.lt_pow_natFloor_logb_add_one one_lt_two hXpos).le

/-- The uniform envelope `psiSubThetaTailBound` is antitone on `[2 ^ 8, ∞)`. -/
theorem antitoneOn_psiSubThetaTailBound :
    AntitoneOn psiSubThetaTailBound (Set.Ici ((2 : ℝ) ^ 8)) :=
  fun _ hX₁ _ hX₂ hle ↦ (psiSubThetaTailBound_le_iff_forall hX₂).mpr fun _ hx ↦
    psiSubThetaTailCoeff_le_psiSubThetaTailBound hX₁ (hle.trans hx)

/-! ### General-input transfer bounds of Broadbent, Kadiri, Lumley, Ng, and Wilk -/

/-- Cube-root tail bound of Broadbent, Kadiri, Lumley, Ng, and Wilk (Proposition 3 / Corollary 3.1):
if `θ y ≤ c * y` for all `y ≥ 2`, then for every `X ≥ 2 ^ 8` and `x ≥ X`,
`ψ x - θ x - θ √x ≤ c * psiSubThetaTailBound X * x ^ (1 / 3)`. -/
theorem psi_sub_theta_sub_theta_sqrt_le {c X x : ℝ} (hX : (2 : ℝ) ^ 8 ≤ X) (hXx : X ≤ x)
    (hθ : ∀ y, 2 ≤ y → θ y ≤ c * y) :
    ψ x - θ x - θ √x ≤ c * psiSubThetaTailBound X * x ^ ((1 : ℝ) / 3) := by
  have hx : 0 ≤ x := le_trans (le_trans (by positivity) hX) hXx
  have hc : 0 < c := pos_of_theta_le hθ
  rw [psi_sub_theta_eq_theta_sqrt_add_sum hx, add_sub_cancel_left]
  exact (sum_theta_rpow_le hx hθ).trans (by
    gcongr
    exact psiSubThetaTailCoeff_le_psiSubThetaTailBound hX hXx)

/-- General-input upper bound on `ψ - θ` (Broadbent, Kadiri, Lumley, Ng, and Wilk,
Proposition 4, upper half): if `θ y ≤ c * y` for `y ≥ 2` and `θ y ≤ c' * y` for `y ≥ √X`, then
for every `X ≥ 2 ^ 8` and `x ≥ X`,
`ψ x - θ x ≤ c' * √x + c * psiSubThetaTailBound X * x ^ (1 / 3)`. -/
theorem psi_sub_theta_le_add_psiSubThetaTailBound {c c' X x : ℝ} (hX : (2 : ℝ) ^ 8 ≤ X)
    (hXx : X ≤ x) (hθ : ∀ y, 2 ≤ y → θ y ≤ c * y) (hθ' : ∀ y, √X ≤ y → θ y ≤ c' * y) :
    ψ x - θ x ≤ c' * √x + c * psiSubThetaTailBound X * x ^ ((1 : ℝ) / 3) := by
  have h1 : θ √x ≤ c' * √x := hθ' √x (sqrt_le_sqrt hXx)
  have h2 := psi_sub_theta_sub_theta_sqrt_le hX hXx hθ
  linarith

/-- Global linear upper bound on `θ` from a finite-range verification `θ y ≤ y` on `[2, x₁]`
and a `ψ`-bound `ψ y ≤ c * y` on `[x₁, ∞)` with `1 ≤ c` (Broadbent, Kadiri, Lumley, Ng, and Wilk,
Lemma 11, upper half). -/
theorem theta_le_of_theta_le_self_of_psi_le {c x₁ x : ℝ} (hc : 1 ≤ c) (hx : 0 ≤ x)
    (hθ : ∀ y, 2 ≤ y → y ≤ x₁ → θ y ≤ y) (hψ : ∀ y, x₁ ≤ y → ψ y ≤ c * y) :
    θ x ≤ c * x := by
  rcases le_or_gt x x₁ with hxx₁ | hx₁x
  · rcases lt_or_ge x 2 with hx2 | hx2
    · rw [theta_eq_zero_of_lt_two hx2]
      exact mul_nonneg (by linarith) hx
    · exact (hθ x hx2 hxx₁).trans (by nlinarith)
  · exact (theta_le_psi x).trans (hψ x hx₁x.le)

/-- The square-root coefficient in Theorem 5 of Broadbent, Kadiri, Lumley, Ng, and Wilk:
`1 + ε (log x₁)` for `b ≤ 2 * log x₁` and `1 + ε (b / 2)` otherwise. -/
noncomputable def psiSubThetaSqrtCoeff (ε : ℝ → ℝ) (x₁ b : ℝ) : ℝ :=
  if b ≤ 2 * log x₁ then 1 + ε (log x₁) else 1 + ε (b / 2)

/-- Evaluation of `psiSubThetaSqrtCoeff` in the small-`b` regime `b ≤ 2 * log x₁`. -/
@[simp]
theorem psiSubThetaSqrtCoeff_of_le {ε : ℝ → ℝ} {x₁ b : ℝ} (h : b ≤ 2 * log x₁) :
    psiSubThetaSqrtCoeff ε x₁ b = 1 + ε (log x₁) := by
  simp [psiSubThetaSqrtCoeff, h]

/-- Evaluation of `psiSubThetaSqrtCoeff` in the large-`b` regime `2 * log x₁ < b`. -/
@[simp]
theorem psiSubThetaSqrtCoeff_of_lt {ε : ℝ → ℝ} {x₁ b : ℝ} (h : 2 * log x₁ < b) :
    psiSubThetaSqrtCoeff ε x₁ b = 1 + ε (b / 2) := by
  simp [psiSubThetaSqrtCoeff, h.not_ge]

/-- Maximum-argument evaluation of `psiSubThetaSqrtCoeff`:
`psiSubThetaSqrtCoeff ε x₁ b = 1 + ε (max (log x₁) (b / 2))`. -/
theorem psiSubThetaSqrtCoeff_eq_one_add_max (ε : ℝ → ℝ) (x₁ b : ℝ) :
    psiSubThetaSqrtCoeff ε x₁ b = 1 + ε (max (log x₁) (b / 2)) := by
  rcases le_or_gt b (2 * log x₁) with h | h
  · rw [psiSubThetaSqrtCoeff_of_le h, max_eq_left (by linarith)]
  · rw [psiSubThetaSqrtCoeff_of_lt h, max_eq_right (by linarith)]

/-- The cube-root coefficient `(1 + ε (log x₁)) * psiSubThetaTailBound (exp b)` in Theorem 5 of
Broadbent, Kadiri, Lumley, Ng, and Wilk. -/
noncomputable def psiSubThetaCbrtCoeff (ε : ℝ → ℝ) (x₁ b : ℝ) : ℝ :=
  (1 + ε (log x₁)) * psiSubThetaTailBound (exp b)

/-- Definitional equation for `psiSubThetaCbrtCoeff`. -/
theorem psiSubThetaCbrtCoeff_def (ε : ℝ → ℝ) (x₁ b : ℝ) :
    psiSubThetaCbrtCoeff ε x₁ b = (1 + ε (log x₁)) * psiSubThetaTailBound (exp b) := (rfl)

/-- Nonnegativity of `psiSubThetaCbrtCoeff` when `0 ≤ 1 + ε (log x₁)`. -/
theorem psiSubThetaCbrtCoeff_nonneg {ε : ℝ → ℝ} {x₁ : ℝ}
    (hε : 0 ≤ 1 + ε (log x₁)) (b : ℝ) :
    0 ≤ psiSubThetaCbrtCoeff ε x₁ b :=
  mul_nonneg hε (psiSubThetaTailBound_nonneg _)

/-- General-input `ψ - θ` upper bound from a `ψ`-table and a finite verification `θ y ≤ y`
up to `x₁` (Broadbent, Kadiri, Lumley, Ng, and Wilk, Theorem 5): for `x₁ > 0`, `8 * log 2 ≤ b`
(in particular for every `b ≥ 6`), and `x ≥ exp b`,
`ψ x - θ x ≤ psiSubThetaSqrtCoeff ε x₁ b * √x + psiSubThetaCbrtCoeff ε x₁ b * x ^ (1 / 3)`. -/
theorem psi_sub_theta_le_of_psi_le_exp {ε : ℝ → ℝ} {x₁ b x : ℝ}
    (hx₁ : 0 < x₁) (hb : 8 * log 2 ≤ b) (hbx : exp b ≤ x)
    (hε : 0 ≤ ε (log x₁))
    (hθ : ∀ y, 2 ≤ y → y ≤ x₁ → θ y ≤ y)
    (hψ : ∀ b', log x₁ ≤ b' → ∀ y, exp b' ≤ y → ψ y ≤ (1 + ε b') * y) :
    ψ x - θ x ≤
      psiSubThetaSqrtCoeff ε x₁ b * √x + psiSubThetaCbrtCoeff ε x₁ b * x ^ ((1 : ℝ) / 3) := by
  have hX : (2 : ℝ) ^ 8 ≤ exp b := by
    calc (2 : ℝ) ^ 8
        = exp (log ((2 : ℝ) ^ (8 : ℕ))) := (exp_log (by positivity)).symm
      _ = exp (8 * log 2) := by rw [log_pow]; norm_num
      _ ≤ exp b := exp_le_exp.mpr hb
  have hθ_all : ∀ y, 2 ≤ y → θ y ≤ (1 + ε (log x₁)) * y := fun y hy ↦
    theta_le_of_theta_le_self_of_psi_le (by linarith) (by linarith) hθ fun t ht ↦
      hψ (log x₁) le_rfl t (by rwa [exp_log hx₁])
  rw [psiSubThetaCbrtCoeff_def]
  refine psi_sub_theta_le_add_psiSubThetaTailBound hX hbx hθ_all fun y hy ↦ ?_
  rcases le_or_gt b (2 * log x₁) with hble | hblt
  · rw [psiSubThetaSqrtCoeff_of_le hble]
    exact theta_le_mul_of_two_le (le_trans (sqrt_nonneg _) hy) hθ_all
  · rw [psiSubThetaSqrtCoeff_of_lt hblt]
    rw [← exp_half] at hy
    exact (theta_le_psi y).trans (hψ (b / 2) (by linarith) y hy)

/-- Upper bound on `ψ x - θ x` from Costa Pereira's inequality
`Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi` and a global bound `ψ y ≤ c₀ * y` on `[2, ∞)`:
for `0 < X ≤ x`, `ψ x - θ x ≤ c₀ * (X ^ (-1 / 2) + X ^ (-2 / 3) + X ^ (-4 / 5)) * x`. -/
theorem psi_sub_theta_le_mul_rpow_add {c₀ X x : ℝ} (hX : 0 < X) (hXx : X ≤ x)
    (hψ : ∀ y, 2 ≤ y → ψ y ≤ c₀ * y) :
    ψ x - θ x ≤
      c₀ * (X ^ (-(1 : ℝ) / 2) + X ^ (-(2 : ℝ) / 3) + X ^ (-(4 : ℝ) / 5)) * x := by
  have hx : 0 ≤ x := hX.le.trans hXx
  have hc₀ : 0 < c₀ := pos_of_psi_le hψ
  have key {p s : ℝ} (hs : s ≤ 0) (hps : s + 1 = p) : x ^ p ≤ X ^ s * x :=
    hps ▸ rpow_add_one_le_rpow_mul hX hXx hs
  have h2 : √x ≤ X ^ (-(1 : ℝ) / 2) * x :=
    sqrt_eq_rpow x ▸ key (by norm_num) (by norm_num)
  have h3 : x ^ ((1 : ℝ) / 3) ≤ X ^ (-(2 : ℝ) / 3) * x := key (by norm_num) (by norm_num)
  have h5 : x ^ ((1 : ℝ) / 5) ≤ X ^ (-(4 : ℝ) / 5) * x := key (by norm_num) (by norm_num)
  nlinarith [theta_ge_psi_sub_mul hψ hx]

/-- Exponential-cutoff form of `psi_sub_theta_le_mul_rpow_add` (Broadbent, Kadiri, Lumley,
Ng, and Wilk, Lemma 11, lower half): for `exp b ≤ x` and `ψ y ≤ c₀ * y` on `[2, ∞)`,
`ψ x - θ x ≤ c₀ * (exp (-b / 2) + exp (-2 * b / 3) + exp (-4 * b / 5)) * x`. -/
theorem psi_sub_theta_le_mul_exp_add {c₀ b x : ℝ} (hbx : exp b ≤ x)
    (hψ : ∀ y, 2 ≤ y → ψ y ≤ c₀ * y) :
    ψ x - θ x ≤
      c₀ * (exp (-b / 2) + exp (-(2 * b) / 3) + exp (-(4 * b) / 5)) * x := by
  have h := psi_sub_theta_le_mul_rpow_add (exp_pos b) hbx hψ
  have he1 : exp b ^ (-(1 : ℝ) / 2) = exp (-b / 2) := by
    rw [← exp_mul]; congr 1; ring
  have he2 : exp b ^ (-(2 : ℝ) / 3) = exp (-(2 * b) / 3) := by
    rw [← exp_mul]; congr 1; ring
  have he3 : exp b ^ (-(4 : ℝ) / 5) = exp (-(4 * b) / 5) := by
    rw [← exp_mul]; congr 1; ring
  rwa [he1, he2, he3] at h

end Chebyshev
