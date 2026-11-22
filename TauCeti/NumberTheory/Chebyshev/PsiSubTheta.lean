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
import TauCeti.NumberTheory.Chebyshev.Basic
import TauCeti.NumberTheory.PrimeCounting

/-!
# Explicit bounds for the difference `ψ − θ`, prime-power counts, and `ψ ↔ θ` transfers

For real `x ≥ 0`, Mathlib's `Chebyshev.psi_eq_sum_theta` writes `ψ(x) = ∑_{k ≥ 1} θ(x^{1/k})`, the
terms with `k > log x / log 2` vanishing. Splitting off `k = 1` and `k = 2`,

`ψ(x) − θ(x) = θ(√x) + ∑_{3 ≤ k ≤ log x / log 2} θ(x^{1/k})`,

and this file turns that decomposition into the explicit two-sided bounds for `ψ − θ` used to pass
between bounds for `ψ` and for `θ`:

* from any bound `θ(y) ≤ c y` on `y > 0` (or `y ≥ 2`),
  `ψ(x) − θ(x) ≤ c (√x + (log x / log 2 − 2)⁺ x^{1/3})`; at `c = log 4`
  (`Chebyshev.theta_le_log4_mul_x`) this is unconditional;
* from relative bounds `(1 − ε) y ≤ θ(y) ≤ (1 + ε) y` for `y ≥ y₀`, the sharper
  `(1 − ε) √x + θ(x^{1/3}) ≤ ψ(x) − θ(x) ≤ (1 + ε) √x + c (log x / log 2 − 2) x^{1/3}`
  for `x ≥ y₀²` (and `x ≥ 4` on the right);
* controlling the cube-root tail by the dimensionless coefficient
  `TauCeti.psiSubThetaTailCoeff x = ∑ k ∈ Icc 3 ⌊log x / log 2⌋₊, x ^ (1 / k - 1 / 3)`, which
  vanishes for `0 ≤ x < 8`, is strictly decreasing on `[2 ^ n, 2 ^ (n + 1))` for `n ≥ 4`,
  satisfies `f (2 ^ (n + 1)) < f (2 ^ n)` for `n ≥ 9`, and is bounded uniformly for `x ≥ X ≥ 2 ^ 8`
  by the antitone envelope
  `TauCeti.psiSubThetaTailBound X = max (f X) (f (2 ^ (⌊log X / log 2⌋₊ + 1)))`, yielding
  Propositions 3–4, Corollary 3.1, and Theorem 5 of Broadbent, Kadiri, Lumley, Ng, and Wilk
  (2021);
* conversely, a bound for `ψ` gives one for `θ` through Costa Pereira's comparison
  `ψ(x) − θ(x) ≤ ψ(x^{1/2}) + ψ(x^{1/3}) + ψ(x^{1/5})` (Lemma 11 of Broadbent et al.).

It also counts the prime powers: the prime powers `m ≤ x` number `∑_{k ≥ 1} π(x^{1/k})`, which is at
most `π(x) + (log x / log 2 − 1) √x ≤ 6 x / log x` for `x ≥ 2`, giving `O(x / log x)`.

## Main definitions

* `TauCeti.psiSubThetaTailCoeff`: the cube-root tail coefficient
  `∑ k ∈ Icc 3 ⌊log x / log 2⌋₊, x ^ (1 / k - 1 / 3)`.
* `TauCeti.psiSubThetaTailBound`: the uniform dyadic envelope
  `max (psiSubThetaTailCoeff X) (psiSubThetaTailCoeff (2 ^ (⌊log X / log 2⌋₊ + 1)))`.

## Main results

* `Chebyshev.psi_eq_theta_add_theta_sqrt_add_sum`, `TauCeti.psi_sub_theta_eq_sum_theta`:
  the exact decompositions of `ψ(x)` and `ψ(x) − θ(x)`.
* `Chebyshev.theta_sqrt_add_theta_rpow_le_psi_sub_theta`, `TauCeti.theta_sqrt_le_psi_sub_theta`:
  unconditional lower bounds on `ψ(x) − θ(x)`.
* `Chebyshev.sum_rpow_one_div_le`:
  `∑_{3 ≤ k ≤ log x / log 2} x^{1/k} ≤ (log x / log 2 − 2)⁺ x^{1/3}`.
* `Chebyshev.theta_le_mul_of_nonneg`, `Chebyshev.psi_le_mul_of_nonneg`,
  `Chebyshev.nonneg_of_forall_theta_le`, `Chebyshev.nonneg_of_forall_psi_le`: a linear bound for
  `θ` or `ψ` on `y > 0` extends to `y = 0` and has a nonnegative constant.
* `TauCeti.sum_theta_rpow_le`: bounds the `k ≥ 3` sum by `c * psiSubThetaTailCoeff x * x ^ (1 / 3)`.
* `TauCeti.psiSubThetaTailCoeff_eq_zero_iff`,
  `TauCeti.psiSubThetaTailCoeff_eq_sum_of_mem_Ico`,
  `TauCeti.strictAntiOn_psiSubThetaTailCoeff_Ico_two_pow`,
  `TauCeti.psiSubThetaTailCoeff_two_pow_succ_lt`,
  `TauCeti.psiSubThetaTailCoeff_two_pow_eight_lt_two_pow_nine`,
  `TauCeti.psiSubThetaTailCoeff_le_psiSubThetaTailBound`,
  `TauCeti.psiSubThetaTailBound_le_iff_forall`,
  `TauCeti.antitoneOn_psiSubThetaTailBound`: vanishing, dyadic monotonicity, sharpness, and
  uniform least-upper-bound envelope for `psiSubThetaTailCoeff`.
* `Chebyshev.psi_sub_theta_le_of_forall_theta_le`, `Chebyshev.psi_sub_theta_le_log_four_mul`,
  `TauCeti.psi_sub_theta_le_of_theta_le`, `TauCeti.psi_sub_theta_le_add_max_mul_cbrt`,
  `TauCeti.psi_sub_theta_le_add_mul_cbrt`, `TauCeti.mul_sqrt_le_psi_sub_theta`,
  `TauCeti.psi_sub_theta_le_mul_rpow_of_theta_le`: unconditional and general-`θ` bounds on `ψ − θ`.
* `Chebyshev.psi_sub_theta_le_one_add_mul_sqrt_add`,
  `Chebyshev.one_sub_mul_sqrt_add_theta_rpow_le_psi_sub_theta`: the transfer of a relative bound
  for `θ` to `ψ − θ`.
* `Chebyshev.abs_theta_sub_le_abs_psi_sub_add`, `Chebyshev.abs_psi_sub_le_abs_theta_sub_add`,
  `TauCeti.abs_theta_sub_self_le_of_theta_le`, `TauCeti.abs_psi_sub_self_le_of_theta_le`,
  `TauCeti.abs_theta_sub_self_le_mul_of_theta_le_of_abs_psi_sub_self_le`,
  `TauCeti.abs_theta_sub_self_le_mul_of_abs_psi_sub_self_le`,
  `TauCeti.abs_psi_sub_self_le_mul_of_theta_le_of_abs_theta_sub_self_le`,
  `TauCeti.abs_psi_sub_self_le_mul_of_abs_theta_sub_self_le`: additive and relative-error
  conversions between bounds for `|ψ(x) − x|` and `|θ(x) − x|`.
* `Chebyshev.theta_le_one_add_mul_of_psi_le`, `Chebyshev.theta_ge_psi_sub_mul`,
  `Chebyshev.theta_ge_of_psi_ge_of_exp_le`,
  `TauCeti.psi_sub_theta_sub_theta_sqrt_le`, `TauCeti.psi_sub_theta_le_add_psiSubThetaTailBound`,
  `TauCeti.mul_sqrt_add_theta_cbrt_le_psi_sub_theta`, `TauCeti.theta_le_of_theta_le_self_of_psi_le`,
  `TauCeti.psi_sub_theta_le_of_psi_le_exp`, `TauCeti.psi_sub_theta_le_mul_rpow_sum`,
  `TauCeti.psi_sub_theta_le_mul_exp_sum`, `TauCeti.le_theta_of_le_psi_rpow`,
  `TauCeti.le_theta_of_le_psi_exp`: general-input transfer bounds of Broadbent, Kadiri, Lumley,
  Ng, and Wilk.
* `Chebyshev.card_filter_isPrimePow_eq_sum_primeCounting`,
  `Chebyshev.card_filter_isPrimePow_le_six_mul_div_log`,
  `Chebyshev.card_filter_range_isPrimePow_le_six_mul_div_log`,
  `TauCeti.card_filter_isPrimePow_Ioc_nat_le_six_mul_div_log`,
  `TauCeti.isBigO_card_filter_isPrimePow_Ioc_div_log`,
  `TauCeti.isBigO_card_filter_isPrimePow_Ioc_nat_div_log`: the number of prime powers up to `x`,
  below or at an integer `N`, and its `O(x / log x)` asymptotic form.

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

section ChebyshevBounds

open Finset Real
open scoped Chebyshev

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

/-- The square-root and cube-root terms of the decomposition bound `ψ − θ` from below:
`θ(√x) + θ(x^{1/3}) ≤ ψ(x) − θ(x)` for `x ≥ 0`. -/
theorem theta_sqrt_add_theta_rpow_le_psi_sub_theta {x : ℝ} (hx : 0 ≤ x) :
    θ √x + θ (x ^ ((1 : ℝ) / 3)) ≤ ψ x - θ x := by
  rw [psi_eq_theta_add_theta_sqrt_add_sum' hx (le_max_left _ 3)]
  have h3 := single_le_sum (f := fun k : ℕ ↦ θ (x ^ ((1 : ℝ) / k))) (fun _ _ ↦ theta_nonneg _)
    (mem_Icc.mpr ⟨le_rfl, le_max_right ⌊log x / log 2⌋₊ 3⟩)
  simp only [Nat.cast_ofNat] at h3
  linarith

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
    (rpow_nonneg hx ((1 : ℝ) / 3)) 3 fun k hk ↦ rpow_le_rpow_of_exponent_le hx1 ?_).trans_eq ?_
  · have : (3 : ℝ) ≤ k := by exact_mod_cast (mem_Icc.mp hk).1
    gcongr
  · congr 2
    push_cast
    ring

/-- A bound `θ(y) ≤ c y` for `y > 0` extends to `y = 0`. -/
theorem theta_le_mul_of_nonneg {c y : ℝ} (hc : ∀ y, 0 < y → θ y ≤ c * y)
    (hy : 0 ≤ y) : θ y ≤ c * y := by
  rcases hy.eq_or_lt with rfl | hy
  · simp [theta_zero]
  · exact hc y hy

/-- A bound `ψ(y) ≤ c y` for `y > 0` extends to `y = 0`. -/
theorem psi_le_mul_of_nonneg {c y : ℝ} (hc : ∀ y, 0 < y → ψ y ≤ c * y)
    (hy : 0 ≤ y) : ψ y ≤ c * y := by
  rcases hy.eq_or_lt with rfl | hy
  · simp [psi_zero]
  · exact hc y hy

/-- A bound `θ(y) ≤ c y` for `y > 0` forces `c ≥ 0`, since `θ(2) = log 2 > 0`. -/
theorem nonneg_of_forall_theta_le {c : ℝ} (hc : ∀ y, 0 < y → θ y ≤ c * y) : 0 ≤ c := by
  have := hc 2 two_pos
  have := theta_pos (le_refl (2 : ℝ))
  linarith

/-- A bound `ψ(y) ≤ c y` for `y > 0` forces `c ≥ 0`, since `θ ≤ ψ`. -/
theorem nonneg_of_forall_psi_le {c : ℝ} (hc : ∀ y, 0 < y → ψ y ≤ c * y) : 0 ≤ c :=
  nonneg_of_forall_theta_le fun y hy ↦ (theta_le_psi y).trans (hc y hy)

/-- The terms with `k ≥ 3` of the decomposition: if `θ(y) ≤ c y` for every `y > 0`, then
`∑_{3 ≤ k ≤ N} θ(x^{1/k}) ≤ c ∑_{3 ≤ k ≤ N} x^{1/k}` for `x ≥ 0`. -/
theorem sum_theta_rpow_le_mul_sum_rpow {c x : ℝ} (hc : ∀ y, 0 < y → θ y ≤ c * y) (hx : 0 ≤ x)
    (N : ℕ) :
    ∑ k ∈ Icc 3 N, θ (x ^ ((1 : ℝ) / k)) ≤ c * ∑ k ∈ Icc 3 N, x ^ ((1 : ℝ) / k) := by
  rw [mul_sum]
  exact sum_le_sum fun k _ ↦ theta_le_mul_of_nonneg hc (rpow_nonneg hx _)

/-! ### Upper bounds for `ψ − θ` -/

/-- If `θ(y) ≤ c y` for every `y > 0`, then for `x ≥ 0`,
`ψ(x) − θ(x) ≤ c (√x + (log x / log 2 − 2)⁺ x^{1/3})`. -/
theorem psi_sub_theta_le_of_forall_theta_le {c x : ℝ} (hc : ∀ y, 0 < y → θ y ≤ c * y)
    (hx : 0 ≤ x) :
    ψ x - θ x ≤ c * (√x + max (log x / log 2 - 2) 0 * x ^ ((1 : ℝ) / 3)) := by
  have hc0 := nonneg_of_forall_theta_le hc
  have hsq := theta_le_mul_of_nonneg hc (sqrt_nonneg x)
  have hsum := (sum_theta_rpow_le_mul_sum_rpow hc hx ⌊log x / log 2⌋₊).trans
    (mul_le_mul_of_nonneg_left (sum_rpow_one_div_le hx) hc0)
  rw [psi_eq_theta_add_theta_sqrt_add_sum hx]
  linarith

/-- The unconditional bound
`0 ≤ ψ(x) − θ(x) ≤ (log 4) (√x + (log x / log 2 − 2)⁺ x^{1/3})` for `x ≥ 0`; the lower bound is
`Chebyshev.theta_le_psi`. -/
theorem psi_sub_theta_le_log_four_mul {x : ℝ} (hx : 0 ≤ x) :
    ψ x - θ x ≤ log 4 * (√x + max (log x / log 2 - 2) 0 * x ^ ((1 : ℝ) / 3)) :=
  psi_sub_theta_le_of_forall_theta_le (fun _ hy ↦ theta_le_log4_mul_x hy.le) hx

/-! ### Transfer of a bound for `θ` to `ψ − θ` -/

/-- Upper transfer: if `θ(y) ≤ c y` for every `y > 0` and `θ(y) ≤ (1 + ε) y` for every `y ≥ y₀`,
then `ψ(x) − θ(x) ≤ (1 + ε) √x + c (log x / log 2 − 2) x^{1/3}` for every `x ≥ max(4, y₀²)`. -/
theorem psi_sub_theta_le_one_add_mul_sqrt_add {c ε y₀ x : ℝ}
    (hc : ∀ y, 0 < y → θ y ≤ c * y) (hε : ∀ y, y₀ ≤ y → θ y ≤ (1 + ε) * y)
    (hx₀ : y₀ ^ 2 ≤ x) (hx : 4 ≤ x) :
    ψ x - θ x ≤ (1 + ε) * √x + c * (log x / log 2 - 2) * x ^ ((1 : ℝ) / 3) := by
  have hc0 := nonneg_of_forall_theta_le hc
  have hK : 0 ≤ log x / log 2 - 2 := by
    rw [sub_nonneg, le_div_iff₀ (log_pos one_lt_two), ← log_rpow two_pos]
    exact log_le_log (by positivity) (by rw [rpow_two]; linarith)
  have hsq : θ √x ≤ (1 + ε) * √x := hε _ ((le_abs_self y₀).trans (abs_le_sqrt hx₀))
  have hsum := (sum_theta_rpow_le_mul_sum_rpow hc (by linarith) ⌊log x / log 2⌋₊).trans
    (mul_le_mul_of_nonneg_left (sum_rpow_one_div_le (by linarith)) hc0)
  rw [max_eq_left hK] at hsum
  rw [psi_eq_theta_add_theta_sqrt_add_sum (by linarith)]
  linarith

/-- Lower transfer: if `(1 − ε) y ≤ θ(y)` for every `y ≥ y₀`, then
`(1 − ε) √x + θ(x^{1/3}) ≤ ψ(x) − θ(x)` for every `x ≥ y₀²`. -/
theorem one_sub_mul_sqrt_add_theta_rpow_le_psi_sub_theta {ε y₀ x : ℝ}
    (hε : ∀ y, y₀ ≤ y → (1 - ε) * y ≤ θ y) (hx₀ : y₀ ^ 2 ≤ x) :
    (1 - ε) * √x + θ (x ^ ((1 : ℝ) / 3)) ≤ ψ x - θ x := by
  have := hε _ ((le_abs_self y₀).trans (abs_le_sqrt hx₀))
  linarith [theta_sqrt_add_theta_rpow_le_psi_sub_theta ((sq_nonneg y₀).trans hx₀)]

/-! ### Conversions between bounds for `ψ` and for `θ` -/

/-- A bound for `|ψ(x) − x|` gives one for `|θ(x) − x|`: if `θ(y) ≤ c y` for every `y > 0`, then
`|θ(x) − x| ≤ |ψ(x) − x| + c (√x + (log x / log 2 − 2)⁺ x^{1/3})` for `x ≥ 0`. -/
theorem abs_theta_sub_le_abs_psi_sub_add {c x : ℝ} (hc : ∀ y, 0 < y → θ y ≤ c * y)
    (hx : 0 ≤ x) :
    |θ x - x| ≤ |ψ x - x| + c * (√x + max (log x / log 2 - 2) 0 * x ^ ((1 : ℝ) / 3)) := by
  have h1 := psi_sub_theta_le_of_forall_theta_le hc hx
  have h2 := theta_le_psi x
  rw [abs_le]
  constructor <;> linarith [neg_abs_le (ψ x - x), le_abs_self (ψ x - x)]

/-- A bound for `|θ(x) − x|` gives one for `|ψ(x) − x|`: if `θ(y) ≤ c y` for every `y > 0`, then
`|ψ(x) − x| ≤ |θ(x) − x| + c (√x + (log x / log 2 − 2)⁺ x^{1/3})` for `x ≥ 0`. -/
theorem abs_psi_sub_le_abs_theta_sub_add {c x : ℝ} (hc : ∀ y, 0 < y → θ y ≤ c * y)
    (hx : 0 ≤ x) :
    |ψ x - x| ≤ |θ x - x| + c * (√x + max (log x / log 2 - 2) 0 * x ^ ((1 : ℝ) / 3)) := by
  have h1 := psi_sub_theta_le_of_forall_theta_le hc hx
  have h2 := theta_le_psi x
  rw [abs_le]
  constructor <;> linarith [neg_abs_le (θ x - x), le_abs_self (θ x - x)]

/-- A global linear bound for `θ` from a bound for `ψ` beyond `x₁` and `θ(y) ≤ y` up to `x₁`:
if `0 ≤ ε`, `θ(y) ≤ y` for `0 < y ≤ x₁` and `ψ(y) ≤ (1 + ε) y` for `y ≥ x₁`, then
`θ(x) ≤ (1 + ε) x` for every `x > 0`. -/
theorem theta_le_one_add_mul_of_psi_le {ε x₁ x : ℝ} (hε : 0 ≤ ε)
    (hθ : ∀ y, 0 < y → y ≤ x₁ → θ y ≤ y) (hψ : ∀ y, x₁ ≤ y → ψ y ≤ (1 + ε) * y) (hx : 0 < x) :
    θ x ≤ (1 + ε) * x := by
  rcases le_total x x₁ with h | h
  · nlinarith [hθ x hx h]
  · exact (theta_le_psi x).trans (hψ x h)

/-- A linear upper bound for `ψ` gives a lower bound for `θ` through Costa Pereira's comparison
`ψ(x) − θ(x) ≤ ψ(x^{1/2}) + ψ(x^{1/3}) + ψ(x^{1/5})`: if `ψ(y) ≤ c₀ y` for every `y > 0`, then
`ψ(x) − c₀ (√x + x^{1/3} + x^{1/5}) ≤ θ(x)` for `x ≥ 0`. -/
theorem theta_ge_psi_sub_mul {c₀ x : ℝ} (hc₀ : ∀ y, 0 < y → ψ y ≤ c₀ * y) (hx : 0 ≤ x) :
    ψ x - c₀ * (√x + x ^ ((1 : ℝ) / 3) + x ^ ((1 : ℝ) / 5)) ≤ θ x := by
  have := psi_sub_theta_le_psi_add_psi_add_psi x
  rw [← one_div, ← one_div, ← one_div, ← sqrt_eq_rpow] at this
  have h2 := psi_le_mul_of_nonneg hc₀ (sqrt_nonneg x)
  have h3 := psi_le_mul_of_nonneg hc₀ (rpow_nonneg hx ((1 : ℝ) / 3))
  have h5 := psi_le_mul_of_nonneg hc₀ (rpow_nonneg hx ((1 : ℝ) / 5))
  linarith

/-- **Broadbent–Kadiri–Lumley–Ng–Wilk, Lemma 11.** If `ψ(y) ≤ c₀ y` for every `y > 0` and
`(1 − ε) x ≤ ψ(x)`, then `(1 − ε − c₀ (e^{−b/2} + e^{−2b/3} + e^{−4b/5})) x ≤ θ(x)` whenever
`x ≥ e^b`. -/
theorem theta_ge_of_psi_ge_of_exp_le {c₀ ε b x : ℝ} (hc₀ : ∀ y, 0 < y → ψ y ≤ c₀ * y)
    (hψ : (1 - ε) * x ≤ ψ x) (hx : exp b ≤ x) :
    (1 - ε - c₀ * (exp (-b / 2) + exp (-2 * b / 3) + exp (-4 * b / 5))) * x ≤ θ x := by
  have hx0 : 0 < x := (exp_pos b).trans_le hx
  have hc0 : 0 ≤ c₀ := nonneg_of_forall_psi_le hc₀
  -- `x^{1/k} = x^{−(1 − 1/k)} x ≤ e^{−(1 − 1/k) b} x`, as `log x ≥ b`.
  have hb : b ≤ log x := (le_log_iff_exp_le hx0).mpr hx
  have key (k : ℝ) (hk : 1 ≤ k) : x ^ (1 / k) ≤ exp (-((k - 1) / k) * b) * x := by
    have : 0 ≤ (k - 1) / k := div_nonneg (by linarith) (by linarith)
    rw [show 1 / k = -((k - 1) / k) + 1 by field_simp; ring, rpow_add_one hx0.ne',
      rpow_def_of_pos hx0]
    exact mul_le_mul_of_nonneg_right (exp_le_exp.mpr (by nlinarith)) hx0.le
  have h2 : √x ≤ exp (-b / 2) * x := by
    rw [sqrt_eq_rpow]
    convert key 2 one_le_two using 3
    ring
  have h3 : x ^ ((1 : ℝ) / 3) ≤ exp (-2 * b / 3) * x := by
    convert key 3 (by norm_num) using 3
    ring
  have h5 : x ^ ((1 : ℝ) / 5) ≤ exp (-4 * b / 5) * x := by
    convert key 5 (by norm_num) using 3
    ring
  have := theta_ge_psi_sub_mul hc₀ hx0.le
  nlinarith [mul_le_mul_of_nonneg_left (add_le_add (add_le_add h2 h3) h5) hc0]

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

end Chebyshev

end ChebyshevBounds

section TauCetiExtensions

open Finset Filter
open scoped Chebyshev Asymptotics

namespace TauCeti

/-! ### Exact `ψ - θ` decomposition and square-root lower bound -/

/-- For every `x ≥ 0`, `ψ x - θ x = ∑ k ∈ Icc 2 ⌊log x / log 2⌋₊, θ (x ^ (1 / k))`. -/
theorem psi_sub_theta_eq_sum_theta {x : ℝ} (hx : 0 ≤ x) :
    ψ x - θ x = ∑ k ∈ Icc 2 ⌊Real.log x / Real.log 2⌋₊, θ (x ^ ((1 : ℝ) / k)) := by
  rcases lt_or_ge x 2 with hx2 | hx2
  · rw [Chebyshev.psi_eq_zero_of_lt_two hx2, Chebyshev.theta_eq_zero_of_lt_two hx2, sub_zero]
    have hlt : ⌊Real.log x / Real.log 2⌋₊ < 1 :=
      (Real.natFloor_logb_lt_iff_lt_pow one_lt_two hx one_ne_zero).2 (by simpa using hx2)
    rw [Icc_eq_empty (by omega), sum_empty]
  · rw [Chebyshev.psi_eq_theta_add_sum_theta hx2, add_sub_cancel_left]

/-- Unconditional square-root lower bound: `θ √x ≤ ψ x - θ x` for every real `x`. -/
theorem theta_sqrt_le_psi_sub_theta (x : ℝ) : θ √x ≤ ψ x - θ x := by
  rcases le_or_gt 0 x with hx | hx
  · rw [Chebyshev.psi_eq_theta_add_theta_sqrt_add_sum hx, add_assoc, add_sub_cancel_left]
    exact le_add_of_nonneg_right (sum_nonneg fun _ _ ↦ Chebyshev.theta_nonneg _)
  · rw [Real.sqrt_eq_zero_of_nonpos hx.le, Chebyshev.theta_eq_zero_of_lt_two (by norm_num),
      Chebyshev.psi_eq_zero_of_lt_two (by linarith),
      Chebyshev.theta_eq_zero_of_lt_two (by linarith), sub_zero]

/-! ### The cube-root tail coefficient and its dyadic envelope -/

/-- The dimensionless coefficient `f(x) = ∑ k ∈ Icc 3 ⌊log x / log 2⌋₊, x ^ (1 / k - 1 / 3)`
controlling the cube-root tail `∑ k ≥ 3, θ (x ^ (1 / k))` of `ψ x - θ x` (Broadbent, Kadiri,
Lumley, Ng, and Wilk 2021). -/
noncomputable def psiSubThetaTailCoeff (x : ℝ) : ℝ :=
  ∑ k ∈ Icc 3 ⌊Real.log x / Real.log 2⌋₊, x ^ ((1 : ℝ) / k - 1 / 3)

/-- Definitional equation for `psiSubThetaTailCoeff`. -/
theorem psiSubThetaTailCoeff_def (x : ℝ) :
    psiSubThetaTailCoeff x =
      ∑ k ∈ Icc 3 ⌊Real.log x / Real.log 2⌋₊, x ^ ((1 : ℝ) / k - 1 / 3) :=
  (rfl)

/-- `psiSubThetaTailCoeff x = 0` for `0 ≤ x < 8`. -/
theorem psiSubThetaTailCoeff_eq_zero_of_lt_eight {x : ℝ} (hx0 : 0 ≤ x) (hx8 : x < 8) :
    psiSubThetaTailCoeff x = 0 := by
  rw [psiSubThetaTailCoeff_def]
  have hlt : ⌊Real.log x / Real.log 2⌋₊ < 3 :=
    (Real.natFloor_logb_lt_iff_lt_pow one_lt_two hx0 (by norm_num)).2 (by norm_num; exact hx8)
  rw [Icc_eq_empty (by omega), sum_empty]

/-- For `x ≥ 0`, `psiSubThetaTailCoeff x = 0` if and only if `x < 8`. -/
@[simp]
theorem psiSubThetaTailCoeff_eq_zero_iff {x : ℝ} (hx : 0 ≤ x) :
    psiSubThetaTailCoeff x = 0 ↔ x < 8 := by
  refine ⟨fun h0 ↦ ?_, psiSubThetaTailCoeff_eq_zero_of_lt_eight hx⟩
  by_contra! hx8
  have h3 : 3 ≤ ⌊Real.log x / Real.log 2⌋₊ :=
    (Real.le_natFloor_logb_iff_pow_le one_lt_two hx (by norm_num)).2 (by norm_num; exact hx8)
  have h1 : (1 : ℝ) ≤ psiSubThetaTailCoeff x := by
    rw [psiSubThetaTailCoeff_def]
    have hmem : (3 : ℕ) ∈ Icc 3 ⌊Real.log x / Real.log 2⌋₊ := mem_Icc.mpr ⟨le_rfl, h3⟩
    simpa using single_le_sum (f := fun k : ℕ ↦ x ^ ((1 : ℝ) / k - 1 / 3))
      (fun _ _ ↦ Real.rpow_nonneg hx _) hmem
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
theorem psiSubThetaTailCoeff_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ psiSubThetaTailCoeff x :=
  sum_nonneg fun _ _ ↦ Real.rpow_nonneg hx _

/-- Crude upper bound `psiSubThetaTailCoeff x ≤ max (log x / log 2 - 2) 0` for every `x ≥ 0`. -/
theorem psiSubThetaTailCoeff_le_max_sub_two {x : ℝ} (hx : 0 ≤ x) :
    psiSubThetaTailCoeff x ≤ max (Real.log x / Real.log 2 - 2) 0 := by
  rcases lt_or_ge x 8 with hx8 | hx8
  · rw [psiSubThetaTailCoeff_eq_zero_of_lt_eight hx hx8]
    exact le_max_right _ _
  · rw [psiSubThetaTailCoeff_def]
    have hx1 : 1 ≤ x := by linarith
    have h3 : 3 ≤ ⌊Real.log x / Real.log 2⌋₊ :=
      (Real.le_natFloor_logb_iff_pow_le one_lt_two hx (by norm_num)).2 (by norm_num; exact hx8)
    have hdiv : 0 ≤ Real.log x / Real.log 2 :=
      div_nonneg (Real.log_nonneg hx1) (Real.log_pos one_lt_two).le
    calc ∑ k ∈ Icc 3 ⌊Real.log x / Real.log 2⌋₊, x ^ ((1 : ℝ) / k - 1 / 3)
        ≤ ∑ _k ∈ Icc 3 ⌊Real.log x / Real.log 2⌋₊, (1 : ℝ) := by
          refine sum_le_sum fun k hk ↦ Real.rpow_le_one_of_one_le_of_nonpos hx1 ?_
          have hk3 : (3 : ℝ) ≤ k := Nat.cast_le.mpr (mem_Icc.mp hk).1
          have : (1 : ℝ) / k ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) hk3
          linarith
      _ = ((⌊Real.log x / Real.log 2⌋₊ + 1 - 3 : ℕ) : ℝ) := by simp
      _ = (⌊Real.log x / Real.log 2⌋₊ : ℝ) - 2 := by
          have : ⌊Real.log x / Real.log 2⌋₊ + 1 - 3 = ⌊Real.log x / Real.log 2⌋₊ - 2 := by omega
          rw [this, Nat.cast_sub (by omega), Nat.cast_ofNat]
      _ ≤ Real.log x / Real.log 2 - 2 := by linarith [Nat.floor_le hdiv]
      _ ≤ max (Real.log x / Real.log 2 - 2) 0 := le_max_left _ _

/-- Exponential evaluation of `psiSubThetaTailCoeff`:
`psiSubThetaTailCoeff (exp b) = ∑ k ∈ Icc 3 ⌊b / log 2⌋₊, exp (b * (1 / k - 1 / 3))`. -/
theorem psiSubThetaTailCoeff_exp (b : ℝ) :
    psiSubThetaTailCoeff (Real.exp b) =
      ∑ k ∈ Icc 3 ⌊b / Real.log 2⌋₊, Real.exp (b * ((1 : ℝ) / k - 1 / 3)) := by
  rw [psiSubThetaTailCoeff_def, Real.log_exp]
  refine sum_congr rfl fun k _ ↦ ?_
  rw [← Real.exp_mul]

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
    ∑ k ∈ Icc 3 ⌊Real.log x / Real.log 2⌋₊, θ (x ^ ((1 : ℝ) / k)) ≤
      c * psiSubThetaTailCoeff x * x ^ ((1 : ℝ) / 3) := by
  rw [psiSubThetaTailCoeff_def, mul_sum, sum_mul]
  refine sum_le_sum fun k hk ↦ ?_
  obtain ⟨hk3, hkf⟩ := mem_Icc.mp hk
  have h2k : (2 : ℝ) ^ k ≤ x :=
    (Real.le_natFloor_logb_iff_pow_le one_lt_two hx (by omega)).mp hkf
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity) h2k
  have h2le : 2 ≤ x ^ ((1 : ℝ) / k) := by
    have hkpos : (k : ℝ) ≠ 0 := by positivity
    calc (2 : ℝ) = ((2 : ℝ) ^ (k : ℝ)) ^ ((1 : ℝ) / k) := by
          rw [← Real.rpow_mul zero_le_two, mul_one_div_cancel hkpos, Real.rpow_one]
      _ ≤ x ^ ((1 : ℝ) / k) := by
          rw [Real.rpow_natCast]
          exact Real.rpow_le_rpow (by positivity) h2k (by positivity)
  calc θ (x ^ ((1 : ℝ) / k))
      ≤ c * x ^ ((1 : ℝ) / k) := hθ _ h2le
    _ = c * (x ^ ((1 : ℝ) / k - 1 / 3) * x ^ ((1 : ℝ) / 3)) := by
        rw [← Real.rpow_add hx0, sub_add_cancel]
    _ = c * x ^ ((1 : ℝ) / k - 1 / 3) * x ^ ((1 : ℝ) / 3) := by ring

/-- Exact value of `psiSubThetaTailCoeff` at powers of `2`: for `n ≥ 3`,
`psiSubThetaTailCoeff (2 ^ n) = 1 + ∑ k ∈ Icc 4 n, 2 ^ (n / k - n / 3)`. -/
theorem psiSubThetaTailCoeff_two_pow {n : ℕ} (hn : 3 ≤ n) :
    psiSubThetaTailCoeff ((2 : ℝ) ^ n) =
      1 + ∑ k ∈ Icc 4 n, (2 : ℝ) ^ ((n : ℝ) / k - (n : ℝ) / 3) := by
  have hmem : (2 : ℝ) ^ n ∈ Set.Ico ((2 : ℝ) ^ n) ((2 : ℝ) ^ (n + 1)) :=
    ⟨le_rfl, by rw [pow_succ]; linarith [pow_pos (zero_lt_two (α := ℝ)) n]⟩
  rw [psiSubThetaTailCoeff_eq_sum_of_mem_Ico hmem,
    ← add_sum_Ioc_eq_sum_Icc hn, ← Icc_add_one_left_eq_Ioc]
  congr 1
  · norm_num
  · refine sum_congr rfl fun k _ ↦ ?_
    rw [← Real.rpow_natCast, ← Real.rpow_mul zero_le_two]
    congr 1
    ring

/-- On every dyadic interval `[2 ^ n, 2 ^ (n + 1))`, `psiSubThetaTailCoeff` is antitone. -/
theorem antitoneOn_psiSubThetaTailCoeff_Ico_two_pow (n : ℕ) :
    AntitoneOn psiSubThetaTailCoeff (Set.Ico ((2 : ℝ) ^ n) ((2 : ℝ) ^ (n + 1))) := by
  intro x hx y hy hxy
  rw [psiSubThetaTailCoeff_eq_sum_of_mem_Ico hx, psiSubThetaTailCoeff_eq_sum_of_mem_Ico hy]
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx.1
  refine sum_le_sum fun k hk ↦ Real.rpow_le_rpow_of_nonpos hx0 hxy ?_
  have hk3 : (3 : ℝ) ≤ k := Nat.cast_le.mpr (mem_Icc.mp hk).1
  have : (1 : ℝ) / k ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) hk3
  linarith

/-- On every dyadic interval `[2 ^ n, 2 ^ (n + 1))` with `n ≥ 4`, `psiSubThetaTailCoeff` is
strictly decreasing. -/
theorem strictAntiOn_psiSubThetaTailCoeff_Ico_two_pow {n : ℕ} (hn : 4 ≤ n) :
    StrictAntiOn psiSubThetaTailCoeff (Set.Ico ((2 : ℝ) ^ n) ((2 : ℝ) ^ (n + 1))) := by
  intro x hx y hy hxy
  rw [psiSubThetaTailCoeff_eq_sum_of_mem_Ico hx, psiSubThetaTailCoeff_eq_sum_of_mem_Ico hy]
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx.1
  refine sum_lt_sum (fun k hk ↦ Real.rpow_le_rpow_of_nonpos hx0 hxy.le ?_)
    ⟨4, mem_Icc.mpr ⟨by omega, hn⟩, Real.rpow_lt_rpow_of_neg hx0 hxy (by norm_num)⟩
  have hk3 : (3 : ℝ) ≤ k := Nat.cast_le.mpr (mem_Icc.mp hk).1
  have : (1 : ℝ) / k ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) hk3
  linarith

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
    rw [mul_sub, mul_sub, mul_one, ← Real.rpow_add zero_lt_two, ← Real.rpow_add zero_lt_two,
      ← Real.rpow_add zero_lt_two]
    congr 1 <;> congr 1 <;> ring
  · rw [← Real.rpow_add zero_lt_two, add_sub_cancel, Real.rpow_one]

private lemma two_lt_sum_Icc_four_nine_term :
    (2 : ℝ) < ∑ k ∈ Icc (4 : ℕ) 9,
      (2 : ℝ) ^ ((10 : ℝ) / k) * ((2 : ℝ) ^ ((1 : ℝ) / 3 - 1 / k) - 1) := by
  let L : ℝ := 6931 / 10000
  have hL : L < Real.log 2 := by dsimp only [L]; linarith [Real.log_two_gt_d9]
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
          ≤ 2 * Real.exp (((10 : ℝ) / k - 1) * L) := by
            gcongr; exact Real.quadratic_le_exp_of_nonneg (by positivity)
        _ ≤ 2 * Real.exp (((10 : ℝ) / k - 1) * Real.log 2) := by gcongr
        _ = (2 : ℝ) ^ (1 : ℝ) * (2 : ℝ) ^ ((10 : ℝ) / k - 1) := by
            rw [Real.rpow_one, Real.rpow_def_of_pos zero_lt_two, mul_comm (Real.log 2)]
        _ = (2 : ℝ) ^ ((10 : ℝ) / k) := by rw [← Real.rpow_add zero_lt_two, add_sub_cancel]
    have h2 : ((1 : ℝ) / 3 - 1 / k) * L ≤ (2 : ℝ) ^ ((1 : ℝ) / 3 - 1 / k) - 1 := by
      have hexp := Real.add_one_le_exp (((1 : ℝ) / 3 - 1 / k) * Real.log 2)
      rw [Real.rpow_def_of_pos zero_lt_two, mul_comm (Real.log 2)]
      have hmul : ((1 : ℝ) / 3 - 1 / k) * L ≤ ((1 : ℝ) / 3 - 1 / k) * Real.log 2 := by gcongr
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
          have hk4 : (4 : ℝ) ≤ k := Nat.cast_le.mpr (mem_Icc.mp hk).1
          have hsub : 0 ≤ (1 : ℝ) / 3 - 1 / k :=
            sub_nonneg.mpr (one_div_le_one_div_of_le (by norm_num) (by linarith))
          have hfac : 0 ≤ (2 : ℝ) ^ ((1 : ℝ) / 3 - 1 / k) - 1 :=
            sub_nonneg.mpr (Real.one_le_rpow one_le_two hsub)
          have h10 : (10 : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast (by omega : 10 ≤ n + 1)
          gcongr
          exact one_le_two
      _ ≤ ∑ k ∈ Icc 4 n,
            (2 : ℝ) ^ (((n : ℝ) + 1) / k) * ((2 : ℝ) ^ ((1 : ℝ) / 3 - 1 / k) - 1) := by
          refine sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right hn) fun k hk _ ↦ ?_
          have hk4 : (4 : ℝ) ≤ k := Nat.cast_le.mpr (mem_Icc.mp hk).1
          have hsub : 0 ≤ (1 : ℝ) / 3 - 1 / k :=
            sub_nonneg.mpr (one_div_le_one_div_of_le (by norm_num) (by linarith))
          exact mul_nonneg (by positivity) (sub_nonneg.mpr (Real.one_le_rpow one_le_two hsub))
  linarith [two_lt_sum_Icc_four_nine_term]

/-- Monotonicity of `psiSubThetaTailCoeff` along powers of `2` for `9 ≤ m ≤ n`. -/
theorem psiSubThetaTailCoeff_two_pow_anti {m n : ℕ} (hm : 9 ≤ m) (hmn : m ≤ n) :
    psiSubThetaTailCoeff ((2 : ℝ) ^ n) ≤ psiSubThetaTailCoeff ((2 : ℝ) ^ m) := by
  induction hmn with
  | refl => exact le_rfl
  | @step k hmk ih => exact (psiSubThetaTailCoeff_two_pow_succ_lt (hm.trans hmk)).le.trans ih

private lemma two_rpow_neg_div_lt {p q : ℕ} {u : ℝ} (hq : q ≠ 0) (hu : 0 < u)
    (h : 1 < u ^ q * (2 : ℝ) ^ p) : (2 : ℝ) ^ (-(p : ℝ) / q) < u := by
  rw [← pow_lt_pow_iff_left₀ (by positivity) hu.le hq, ← Real.rpow_natCast,
    ← Real.rpow_mul zero_le_two, div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr hq),
    Real.rpow_neg zero_le_two, Real.rpow_natCast, ← one_div, div_lt_iff₀ (by positivity)]
  exact h

private lemma lt_two_rpow_neg_div {p q : ℕ} {l : ℝ} (hq : q ≠ 0) (hl : 0 ≤ l)
    (h : l ^ q * (2 : ℝ) ^ p < 1) : l < (2 : ℝ) ^ (-(p : ℝ) / q) := by
  rw [← pow_lt_pow_iff_left₀ hl (by positivity) hq,
    ← Real.rpow_natCast ((2 : ℝ) ^ (-(p : ℝ) / q)),
    ← Real.rpow_mul zero_le_two, div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr hq),
    Real.rpow_neg zero_le_two, Real.rpow_natCast, ← one_div, lt_div_iff₀ (by positivity)]
  exact h

/-- Sharpness of the threshold `n = 9` in `psiSubThetaTailCoeff_two_pow_succ_lt`:
at `n = 8`, `psiSubThetaTailCoeff (2 ^ 8) < psiSubThetaTailCoeff (2 ^ 9)`. -/
theorem psiSubThetaTailCoeff_two_pow_eight_lt_two_pow_nine :
    psiSubThetaTailCoeff ((2 : ℝ) ^ 8) < psiSubThetaTailCoeff ((2 : ℝ) ^ 9) := by
  have hIcc8 : Icc (4 : ℕ) 8 = {4, 5, 6, 7, 8} := by decide
  have hIcc9 : Icc (4 : ℕ) 9 = {4, 5, 6, 7, 8, 9} := by decide
  have h8 : psiSubThetaTailCoeff ((2 : ℝ) ^ 8) < 16 / 5 := by
    rw [psiSubThetaTailCoeff_two_pow (by norm_num), hIcc8]
    simp only [sum_insert (by decide : (4 : ℕ) ∉ ({5, 6, 7, 8} : Finset ℕ)),
      sum_insert (by decide : (5 : ℕ) ∉ ({6, 7, 8} : Finset ℕ)),
      sum_insert (by decide : (6 : ℕ) ∉ ({7, 8} : Finset ℕ)),
      sum_insert (by decide : (7 : ℕ) ∉ ({8} : Finset ℕ)),
      sum_singleton, Nat.cast_ofNat]
    have h4 : (2 : ℝ) ^ ((8 : ℝ) / 4 - 8 / 3) < 63 / 100 := by
      rw [show (8 : ℝ) / 4 - 8 / 3 = -((2 : ℕ) : ℝ) / 3 by norm_num]
      exact two_rpow_neg_div_lt (by norm_num) (by norm_num) (by norm_num)
    have h5 : (2 : ℝ) ^ ((8 : ℝ) / 5 - 8 / 3) < 48 / 100 := by
      rw [show (8 : ℝ) / 5 - 8 / 3 = -((16 : ℕ) : ℝ) / 15 by norm_num]
      exact two_rpow_neg_div_lt (by norm_num) (by norm_num) (by norm_num)
    have h6 : (2 : ℝ) ^ ((8 : ℝ) / 6 - 8 / 3) < 40 / 100 := by
      rw [show (8 : ℝ) / 6 - 8 / 3 = -((4 : ℕ) : ℝ) / 3 by norm_num]
      exact two_rpow_neg_div_lt (by norm_num) (by norm_num) (by norm_num)
    have h7 : (2 : ℝ) ^ ((8 : ℝ) / 7 - 8 / 3) < 36 / 100 := by
      have hle : (2 : ℝ) ^ ((8 : ℝ) / 7 - 8 / 3) ≤ (2 : ℝ) ^ (-((3 : ℕ) : ℝ) / 2) :=
        Real.rpow_le_rpow_of_exponent_le one_le_two (by norm_num)
      exact hle.trans_lt (two_rpow_neg_div_lt (by norm_num) (by norm_num) (by norm_num))
    have h8' : (2 : ℝ) ^ ((8 : ℝ) / 8 - 8 / 3) < 32 / 100 := by
      rw [show (8 : ℝ) / 8 - 8 / 3 = -((5 : ℕ) : ℝ) / 3 by norm_num]
      exact two_rpow_neg_div_lt (by norm_num) (by norm_num) (by norm_num)
    linarith
  have h9 : (16 : ℝ) / 5 < psiSubThetaTailCoeff ((2 : ℝ) ^ 9) := by
    rw [psiSubThetaTailCoeff_two_pow (by norm_num), hIcc9]
    simp only [sum_insert (by decide : (4 : ℕ) ∉ ({5, 6, 7, 8, 9} : Finset ℕ)),
      sum_insert (by decide : (5 : ℕ) ∉ ({6, 7, 8, 9} : Finset ℕ)),
      sum_insert (by decide : (6 : ℕ) ∉ ({7, 8, 9} : Finset ℕ)),
      sum_insert (by decide : (7 : ℕ) ∉ ({8, 9} : Finset ℕ)),
      sum_insert (by decide : (8 : ℕ) ∉ ({9} : Finset ℕ)),
      sum_singleton, Nat.cast_ofNat]
    have h4 : (19 : ℝ) / 32 < (2 : ℝ) ^ ((9 : ℝ) / 4 - 9 / 3) := by
      rw [show (9 : ℝ) / 4 - 9 / 3 = -((3 : ℕ) : ℝ) / 4 by norm_num]
      exact lt_two_rpow_neg_div (by norm_num) (by norm_num) (by norm_num)
    have h5 : (43 : ℝ) / 100 < (2 : ℝ) ^ ((9 : ℝ) / 5 - 9 / 3) := by
      rw [show (9 : ℝ) / 5 - 9 / 3 = -((6 : ℕ) : ℝ) / 5 by norm_num]
      exact lt_two_rpow_neg_div (by norm_num) (by norm_num) (by norm_num)
    have h6 : (353 : ℝ) / 1000 < (2 : ℝ) ^ ((9 : ℝ) / 6 - 9 / 3) := by
      rw [show (9 : ℝ) / 6 - 9 / 3 = -((3 : ℕ) : ℝ) / 2 by norm_num]
      exact lt_two_rpow_neg_div (by norm_num) (by norm_num) (by norm_num)
    have h7 : (304 : ℝ) / 1000 < (2 : ℝ) ^ ((9 : ℝ) / 7 - 9 / 3) := by
      rw [show (9 : ℝ) / 7 - 9 / 3 = -((12 : ℕ) : ℝ) / 7 by norm_num]
      exact lt_two_rpow_neg_div (by norm_num) (by norm_num) (by norm_num)
    have h8' : (27 : ℝ) / 100 < (2 : ℝ) ^ ((9 : ℝ) / 8 - 9 / 3) := by
      rw [show (9 : ℝ) / 8 - 9 / 3 = -((15 : ℕ) : ℝ) / 8 by norm_num]
      exact lt_two_rpow_neg_div (by norm_num) (by norm_num) (by norm_num)
    rw [show (2 : ℝ) ^ ((9 : ℝ) / 9 - 9 / 3) = 1 / 4 by
      rw [show (9 : ℝ) / 9 - 9 / 3 = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg zero_le_two,
        Real.rpow_natCast]
      norm_num]
    linarith
  exact h8.trans h9

/-- The uniform dyadic upper envelope
`F(X) = max (f X) (f (2 ^ (⌊log X / log 2⌋₊ + 1)))` bounding `psiSubThetaTailCoeff x`
for all `x ≥ X` once `X ≥ 2 ^ 8`. -/
noncomputable def psiSubThetaTailBound (X : ℝ) : ℝ :=
  max (psiSubThetaTailCoeff X) (psiSubThetaTailCoeff ((2 : ℝ) ^ (⌊Real.log X / Real.log 2⌋₊ + 1)))

/-- Definitional equation for `psiSubThetaTailBound`. -/
theorem psiSubThetaTailBound_def (X : ℝ) :
    psiSubThetaTailBound X =
      max (psiSubThetaTailCoeff X)
        (psiSubThetaTailCoeff ((2 : ℝ) ^ (⌊Real.log X / Real.log 2⌋₊ + 1))) :=
  (rfl)

/-- Upper-bound characterization of `psiSubThetaTailBound`. -/
@[simp]
theorem psiSubThetaTailBound_le_iff {X u : ℝ} :
    psiSubThetaTailBound X ≤ u ↔
      psiSubThetaTailCoeff X ≤ u ∧
        psiSubThetaTailCoeff ((2 : ℝ) ^ (⌊Real.log X / Real.log 2⌋₊ + 1)) ≤ u :=
  max_le_iff

/-- Exponential evaluation of `psiSubThetaTailBound`:
`psiSubThetaTailBound (exp b) = max (f (exp b)) (f (2 ^ (⌊b / log 2⌋₊ + 1)))`. -/
theorem psiSubThetaTailBound_exp (b : ℝ) :
    psiSubThetaTailBound (Real.exp b) =
      max (psiSubThetaTailCoeff (Real.exp b))
        (psiSubThetaTailCoeff ((2 : ℝ) ^ (⌊b / Real.log 2⌋₊ + 1))) := by
  rw [psiSubThetaTailBound_def, Real.log_exp]

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
  set m := ⌊Real.log X / Real.log 2⌋₊
  set n := ⌊Real.log x / Real.log 2⌋₊
  have hm8 : 8 ≤ m :=
    (Real.le_natFloor_logb_iff_pow_le one_lt_two (by positivity) (by norm_num)).2 hX
  have hX1 : 1 ≤ X := le_trans (one_le_pow₀ one_le_two) hX
  have hx1 : 1 ≤ x := hX1.trans hXx
  have hmn : m ≤ n := Nat.floor_mono
    (div_le_div_of_nonneg_right (Real.log_le_log (by linarith) hXx) (Real.log_pos one_lt_two).le)
  have hXmem : X ∈ Set.Ico ((2 : ℝ) ^ m) ((2 : ℝ) ^ (m + 1)) :=
    Real.mem_Ico_pow_natFloor_logb one_lt_two hX1
  have hxmem : x ∈ Set.Ico ((2 : ℝ) ^ n) ((2 : ℝ) ^ (n + 1)) :=
    Real.mem_Ico_pow_natFloor_logb one_lt_two hx1
  rw [psiSubThetaTailBound_def]
  rcases hmn.eq_or_lt with hEq | hLt
  · rw [← hEq] at hxmem
    exact le_max_of_le_left
      (antitoneOn_psiSubThetaTailCoeff_Ico_two_pow m hXmem hxmem hXx)
  · have h2n_mem : (2 : ℝ) ^ n ∈ Set.Ico ((2 : ℝ) ^ n) ((2 : ℝ) ^ (n + 1)) :=
      ⟨le_rfl, by rw [pow_succ]; linarith [pow_pos (zero_lt_two (α := ℝ)) n]⟩
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
  exact psiSubThetaTailBound_le_iff.mpr
    ⟨h X le_rfl, h _ (Real.lt_pow_natFloor_logb_add_one one_lt_two hXpos).le⟩

/-- The uniform envelope `psiSubThetaTailBound` is antitone on `[2 ^ 8, ∞)`. -/
theorem antitoneOn_psiSubThetaTailBound :
    AntitoneOn psiSubThetaTailBound (Set.Ici ((2 : ℝ) ^ 8)) :=
  fun _ hX₁ _ hX₂ hle ↦ (psiSubThetaTailBound_le_iff_forall hX₂).mpr fun _ hx ↦
    psiSubThetaTailCoeff_le_psiSubThetaTailBound hX₁ (hle.trans hx)

/-! ### General-input `ψ - θ` bounds and `ψ ↔ θ` error transfers -/

/-- Lower transfer from a `θ`-bound on `[y₀, ∞)`: if `y₀ ^ 2 ≤ x` and `a * y ≤ θ y` for `y ≥ y₀`,
then `a * √x ≤ ψ x - θ x`. -/
theorem mul_sqrt_le_psi_sub_theta {a y₀ x : ℝ} (hyx : y₀ ^ 2 ≤ x)
    (hθ : ∀ y, y₀ ≤ y → a * y ≤ θ y) :
    a * √x ≤ ψ x - θ x :=
  (hθ √x (Real.le_sqrt_of_sq_le hyx)).trans (theta_sqrt_le_psi_sub_theta x)

/-- Upper transfer from a global `θ`-bound `θ y ≤ c * y` on `[2, ∞)` and a bound
`θ y ≤ c' * y` on `[y₀, ∞)`: for `y₀ ^ 2 ≤ x`,
`ψ x - θ x ≤ c' * √x + c * max (log x / log 2 - 2) 0 * x ^ (1 / 3)`. -/
theorem psi_sub_theta_le_add_max_mul_cbrt {c c' y₀ x : ℝ} (hyx : y₀ ^ 2 ≤ x)
    (hθ : ∀ y, 2 ≤ y → θ y ≤ c * y) (hθ' : ∀ y, y₀ ≤ y → θ y ≤ c' * y) :
    ψ x - θ x ≤ c' * √x + c * max (Real.log x / Real.log 2 - 2) 0 * x ^ ((1 : ℝ) / 3) := by
  have hx : 0 ≤ x := le_trans (sq_nonneg y₀) hyx
  have hc : 0 < c := pos_of_theta_le hθ
  rw [Chebyshev.psi_eq_theta_add_theta_sqrt_add_sum hx, add_assoc, add_sub_cancel_left]
  have h1 : θ √x ≤ c' * √x := hθ' √x (Real.le_sqrt_of_sq_le hyx)
  have h2 : ∑ k ∈ Icc 3 ⌊Real.log x / Real.log 2⌋₊, θ (x ^ ((1 : ℝ) / k)) ≤
      c * max (Real.log x / Real.log 2 - 2) 0 * x ^ ((1 : ℝ) / 3) :=
    (sum_theta_rpow_le hx hθ).trans (by
      gcongr
      exact psiSubThetaTailCoeff_le_max_sub_two hx)
  linarith

/-- General upper bound for `ψ - θ`: if `θ y ≤ c * y` for all `y ≥ 2`, then for every `x ≥ 0`,
`ψ x - θ x ≤ c * (√x + max (log x / log 2 - 2) 0 * x ^ (1 / 3))`. -/
theorem psi_sub_theta_le_of_theta_le {c x : ℝ} (hx : 0 ≤ x)
    (hθ : ∀ y, 2 ≤ y → θ y ≤ c * y) :
    ψ x - θ x ≤ c * (√x + max (Real.log x / Real.log 2 - 2) 0 * x ^ ((1 : ℝ) / 3)) :=
  Chebyshev.psi_sub_theta_le_of_forall_theta_le (fun _ hy ↦ theta_le_mul_of_two_le hy.le hθ) hx

/-- Upper transfer from `θ`-bounds for `x ≥ max 4 (y₀ ^ 2)`:
`ψ x - θ x ≤ c' * √x + c * (log x / log 2 - 2) * x ^ (1 / 3)`. -/
theorem psi_sub_theta_le_add_mul_cbrt {c c' y₀ x : ℝ} (hx : 4 ≤ x) (hyx : y₀ ^ 2 ≤ x)
    (hθ : ∀ y, 2 ≤ y → θ y ≤ c * y) (hθ' : ∀ y, y₀ ≤ y → θ y ≤ c' * y) :
    ψ x - θ x ≤ c' * √x + c * (Real.log x / Real.log 2 - 2) * x ^ ((1 : ℝ) / 3) := by
  have h2 : (2 : ℝ) ≤ Real.log x / Real.log 2 := by
    rw [← Real.logb, Real.le_logb_iff_rpow_le one_lt_two (by linarith)]
    norm_num
    exact hx
  simpa only [max_eq_left (sub_nonneg.mpr h2)] using
    psi_sub_theta_le_add_max_mul_cbrt hyx hθ hθ'

/-- Relative-error form of `psi_sub_theta_le_of_theta_le`: if `θ y ≤ c * y` for all `y ≥ 2`, then
for every `x ≥ 0`,
`ψ x - θ x ≤ c * (x ^ (-1 / 2) + max (log x / log 2 - 2) 0 * x ^ (-2 / 3)) * x`. -/
theorem psi_sub_theta_le_mul_rpow_of_theta_le {c x : ℝ} (hx : 0 ≤ x)
    (hθ : ∀ y, 2 ≤ y → θ y ≤ c * y) :
    ψ x - θ x ≤
      c * (x ^ (-(1 : ℝ) / 2) +
        max (Real.log x / Real.log 2 - 2) 0 * x ^ (-(2 : ℝ) / 3)) * x := by
  rcases hx.eq_or_lt with rfl | hx0
  · simp [Chebyshev.psi_eq_zero_of_lt_two, Chebyshev.theta_eq_zero_of_lt_two]
  · have h1 : x ^ (-(1 : ℝ) / 2) * x = √x := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add_one hx0.ne']
      norm_num
    have h2 : x ^ (-(2 : ℝ) / 3) * x = x ^ ((1 : ℝ) / 3) := by
      rw [← Real.rpow_add_one hx0.ne']
      norm_num
    calc ψ x - θ x
        ≤ c * (√x + max (Real.log x / Real.log 2 - 2) 0 * x ^ ((1 : ℝ) / 3)) :=
          psi_sub_theta_le_of_theta_le hx hθ
      _ = c * (x ^ (-(1 : ℝ) / 2) * x +
            max (Real.log x / Real.log 2 - 2) 0 * (x ^ (-(2 : ℝ) / 3) * x)) := by rw [h1, h2]
      _ = _ := by ring

/-- Additive transfer from `|ψ x - x|` to `|θ x - x|` using a linear bound `θ y ≤ c * y`
on `[2, ∞)`. -/
theorem abs_theta_sub_self_le_of_theta_le {c x : ℝ} (hx : 0 ≤ x)
    (hθ : ∀ y, 2 ≤ y → θ y ≤ c * y) :
    |θ x - x| ≤
      |ψ x - x| + c * (√x + max (Real.log x / Real.log 2 - 2) 0 * x ^ ((1 : ℝ) / 3)) :=
  Chebyshev.abs_theta_sub_le_abs_psi_sub_add (fun _ hy ↦ theta_le_mul_of_two_le hy.le hθ) hx

/-- Additive transfer from `|θ x - x|` to `|ψ x - x|` using a linear bound `θ y ≤ c * y`
on `[2, ∞)`. -/
theorem abs_psi_sub_self_le_of_theta_le {c x : ℝ} (hx : 0 ≤ x)
    (hθ : ∀ y, 2 ≤ y → θ y ≤ c * y) :
    |ψ x - x| ≤
      |θ x - x| + c * (√x + max (Real.log x / Real.log 2 - 2) 0 * x ^ ((1 : ℝ) / 3)) :=
  Chebyshev.abs_psi_sub_le_abs_theta_sub_add (fun _ hy ↦ theta_le_mul_of_two_le hy.le hθ) hx

/-- Unconditional additive transfer from `|ψ x - x|` to `|θ x - x|`. -/
theorem abs_theta_sub_self_le_abs_psi_sub_self_add {x : ℝ} (hx : 0 ≤ x) :
    |θ x - x| ≤
      |ψ x - x| + Real.log 4 * (√x + max (Real.log x / Real.log 2 - 2) 0 * x ^ ((1 : ℝ) / 3)) :=
  abs_theta_sub_self_le_of_theta_le hx fun _ hy ↦ Chebyshev.theta_le_log4_mul_x (by linarith)

/-- Unconditional additive transfer from `|θ x - x|` to `|ψ x - x|`. -/
theorem abs_psi_sub_self_le_abs_theta_sub_self_add {x : ℝ} (hx : 0 ≤ x) :
    |ψ x - x| ≤
      |θ x - x| + Real.log 4 * (√x + max (Real.log x / Real.log 2 - 2) 0 * x ^ ((1 : ℝ) / 3)) :=
  abs_psi_sub_self_le_of_theta_le hx fun _ hy ↦ Chebyshev.theta_le_log4_mul_x (by linarith)

/-- Relative-error transfer from `|ψ x - x| ≤ ε * x` to `|θ x - x|` using `θ y ≤ c * y`
on `[2, ∞)`. -/
theorem abs_theta_sub_self_le_mul_of_theta_le_of_abs_psi_sub_self_le {c ε x : ℝ} (hx : 0 ≤ x)
    (hθ : ∀ y, 2 ≤ y → θ y ≤ c * y) (hψ : |ψ x - x| ≤ ε * x) :
    |θ x - x| ≤
      (ε + c * (x ^ (-(1 : ℝ) / 2) +
        max (Real.log x / Real.log 2 - 2) 0 * x ^ (-(2 : ℝ) / 3))) * x := by
  have hdiff : θ x - x = (ψ x - x) - (ψ x - θ x) := by ring
  have hnn : 0 ≤ ψ x - θ x := sub_nonneg.mpr (Chebyshev.theta_le_psi x)
  calc |θ x - x| ≤ |ψ x - x| + |ψ x - θ x| := by rw [hdiff]; exact abs_sub _ _
    _ = |ψ x - x| + (ψ x - θ x) := by rw [abs_of_nonneg hnn]
    _ ≤ ε * x + c * (x ^ (-(1 : ℝ) / 2) +
          max (Real.log x / Real.log 2 - 2) 0 * x ^ (-(2 : ℝ) / 3)) * x :=
        add_le_add hψ (psi_sub_theta_le_mul_rpow_of_theta_le hx hθ)
    _ = _ := by ring

/-- Unconditional relative-error transfer from `|ψ x - x| ≤ ε * x` to `|θ x - x|`. -/
theorem abs_theta_sub_self_le_mul_of_abs_psi_sub_self_le {ε x : ℝ} (hx : 0 ≤ x)
    (hψ : |ψ x - x| ≤ ε * x) :
    |θ x - x| ≤
      (ε + Real.log 4 * (x ^ (-(1 : ℝ) / 2) +
        max (Real.log x / Real.log 2 - 2) 0 * x ^ (-(2 : ℝ) / 3))) * x :=
  abs_theta_sub_self_le_mul_of_theta_le_of_abs_psi_sub_self_le hx
    (fun _ hy ↦ Chebyshev.theta_le_log4_mul_x (by linarith)) hψ

/-- Relative-error transfer from `|θ x - x| ≤ ε * x` to `|ψ x - x|` using `θ y ≤ c * y`
on `[2, ∞)`. -/
theorem abs_psi_sub_self_le_mul_of_theta_le_of_abs_theta_sub_self_le {c ε x : ℝ} (hx : 0 ≤ x)
    (hθ : ∀ y, 2 ≤ y → θ y ≤ c * y) (hθx : |θ x - x| ≤ ε * x) :
    |ψ x - x| ≤
      (ε + c * (x ^ (-(1 : ℝ) / 2) +
        max (Real.log x / Real.log 2 - 2) 0 * x ^ (-(2 : ℝ) / 3))) * x := by
  have hdiff : ψ x - x = (θ x - x) + (ψ x - θ x) := by ring
  have hnn : 0 ≤ ψ x - θ x := sub_nonneg.mpr (Chebyshev.theta_le_psi x)
  calc |ψ x - x| ≤ |θ x - x| + |ψ x - θ x| := by rw [hdiff]; exact abs_add_le _ _
    _ = |θ x - x| + (ψ x - θ x) := by rw [abs_of_nonneg hnn]
    _ ≤ ε * x + c * (x ^ (-(1 : ℝ) / 2) +
          max (Real.log x / Real.log 2 - 2) 0 * x ^ (-(2 : ℝ) / 3)) * x :=
        add_le_add hθx (psi_sub_theta_le_mul_rpow_of_theta_le hx hθ)
    _ = _ := by ring

/-- Unconditional relative-error transfer from `|θ x - x| ≤ ε * x` to `|ψ x - x|`. -/
theorem abs_psi_sub_self_le_mul_of_abs_theta_sub_self_le {ε x : ℝ} (hx : 0 ≤ x)
    (hθx : |θ x - x| ≤ ε * x) :
    |ψ x - x| ≤
      (ε + Real.log 4 * (x ^ (-(1 : ℝ) / 2) +
        max (Real.log x / Real.log 2 - 2) 0 * x ^ (-(2 : ℝ) / 3))) * x :=
  abs_psi_sub_self_le_mul_of_theta_le_of_abs_theta_sub_self_le hx
    (fun _ hy ↦ Chebyshev.theta_le_log4_mul_x (by linarith)) hθx

/-! ### General-input transfer bounds of Broadbent, Kadiri, Lumley, Ng, and Wilk -/

/-- Cube-root tail bound of Broadbent, Kadiri, Lumley, Ng, and Wilk (Proposition 3 / Corollary 3.1):
if `θ y ≤ c * y` for all `y ≥ 2`, then for every `X ≥ 2 ^ 8` and `x ≥ X`,
`ψ x - θ x - θ √x ≤ c * psiSubThetaTailBound X * x ^ (1 / 3)`. -/
theorem psi_sub_theta_sub_theta_sqrt_le {c X x : ℝ} (hX : (2 : ℝ) ^ 8 ≤ X) (hXx : X ≤ x)
    (hθ : ∀ y, 2 ≤ y → θ y ≤ c * y) :
    ψ x - θ x - θ √x ≤ c * psiSubThetaTailBound X * x ^ ((1 : ℝ) / 3) := by
  have hx : 0 ≤ x := le_trans (le_trans (by positivity) hX) hXx
  have hc : 0 < c := pos_of_theta_le hθ
  rw [Chebyshev.psi_eq_theta_add_theta_sqrt_add_sum hx, add_assoc, add_sub_cancel_left,
    add_sub_cancel_left]
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
  have h1 : θ √x ≤ c' * √x := hθ' √x (Real.sqrt_le_sqrt hXx)
  have h2 := psi_sub_theta_sub_theta_sqrt_le hX hXx hθ
  linarith

/-- General-input lower bound on `ψ - θ` (Broadbent, Kadiri, Lumley, Ng, and Wilk,
Proposition 4, lower half): if `a * y ≤ θ y` for `y ≥ √X`, then for every `x ≥ max 0 X`,
`a * √x + θ (x ^ (1 / 3)) ≤ ψ x - θ x`. -/
theorem mul_sqrt_add_theta_cbrt_le_psi_sub_theta {a X x : ℝ} (hx : 0 ≤ x) (hXx : X ≤ x)
    (hθ : ∀ y, √X ≤ y → a * y ≤ θ y) :
    a * √x + θ (x ^ ((1 : ℝ) / 3)) ≤ ψ x - θ x := by
  have h1 : a * √x ≤ θ √x := hθ √x (Real.sqrt_le_sqrt hXx)
  linarith [Chebyshev.theta_sqrt_add_theta_rpow_le_psi_sub_theta hx]

/-- Global linear upper bound on `θ` from a finite-range verification `θ y ≤ y` on `[2, x₁]`
and a `ψ`-bound `ψ y ≤ c * y` on `[x₁, ∞)` with `1 ≤ c` (Broadbent, Kadiri, Lumley, Ng, and Wilk,
Lemma 11, upper half). -/
theorem theta_le_of_theta_le_self_of_psi_le {c x₁ x : ℝ} (hc : 1 ≤ c) (hx : 0 ≤ x)
    (hθ : ∀ y, 2 ≤ y → y ≤ x₁ → θ y ≤ y) (hψ : ∀ y, x₁ ≤ y → ψ y ≤ c * y) :
    θ x ≤ c * x := by
  rcases le_or_gt x x₁ with hxx₁ | hx₁x
  · rcases lt_or_ge x 2 with hx2 | hx2
    · rw [Chebyshev.theta_eq_zero_of_lt_two hx2]
      exact mul_nonneg (by linarith) hx
    · exact (hθ x hx2 hxx₁).trans (by nlinarith)
  · exact (Chebyshev.theta_le_psi x).trans (hψ x hx₁x.le)

/-- General-input `ψ - θ` upper bound from a `ψ`-table and a finite verification `θ y ≤ y`
up to `x₁` (Broadbent, Kadiri, Lumley, Ng, and Wilk, Theorem 5): for `x₁ > 0`, `8 * log 2 ≤ b`
(in particular for every `b ≥ 6`), and `x ≥ exp b`,
`ψ x - θ x ≤ a₁ * √x + (1 + ε (log x₁)) * psiSubThetaTailBound (exp b) * x ^ (1 / 3)`
where `a₁ = 1 + ε (log x₁)` for `b ≤ 2 * log x₁` and `a₁ = 1 + ε (b / 2)` otherwise. -/
theorem psi_sub_theta_le_of_psi_le_exp {ε : ℝ → ℝ} {x₁ b x : ℝ}
    (hx₁ : 0 < x₁) (hb : 8 * Real.log 2 ≤ b) (hbx : Real.exp b ≤ x)
    (hε : 0 ≤ ε (Real.log x₁))
    (hθ : ∀ y, 2 ≤ y → y ≤ x₁ → θ y ≤ y)
    (hψ : ∀ b', Real.log x₁ ≤ b' → ∀ y, Real.exp b' ≤ y → ψ y ≤ (1 + ε b') * y) :
    ψ x - θ x ≤
      (if b ≤ 2 * Real.log x₁ then 1 + ε (Real.log x₁) else 1 + ε (b / 2)) * √x +
        (1 + ε (Real.log x₁)) * psiSubThetaTailBound (Real.exp b) * x ^ ((1 : ℝ) / 3) := by
  have hX : (2 : ℝ) ^ 8 ≤ Real.exp b := by
    calc (2 : ℝ) ^ 8
        = Real.exp (Real.log ((2 : ℝ) ^ (8 : ℕ))) := (Real.exp_log (by positivity)).symm
      _ = Real.exp (8 * Real.log 2) := by rw [Real.log_pow]; norm_num
      _ ≤ Real.exp b := Real.exp_le_exp.mpr hb
  have hθ_all : ∀ y, 2 ≤ y → θ y ≤ (1 + ε (Real.log x₁)) * y := fun y hy ↦
    theta_le_of_theta_le_self_of_psi_le (by linarith) (by linarith) hθ fun t ht ↦
      hψ (Real.log x₁) le_rfl t (by rwa [Real.exp_log hx₁])
  refine psi_sub_theta_le_add_psiSubThetaTailBound hX hbx hθ_all fun y hy ↦ ?_
  split_ifs with hble
  · exact theta_le_mul_of_two_le (le_trans (Real.sqrt_nonneg _) hy) hθ_all
  · rw [← Real.exp_half] at hy
    exact (Chebyshev.theta_le_psi y).trans (hψ (b / 2) (by linarith) y hy)

/-- Upper bound on `ψ x - θ x` from Costa Pereira's inequality
`Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi` and a global bound `ψ y ≤ c₀ * y` on `[2, ∞)`:
for `0 < X ≤ x`, `ψ x - θ x ≤ c₀ * (X ^ (-1 / 2) + X ^ (-2 / 3) + X ^ (-4 / 5)) * x`. -/
theorem psi_sub_theta_le_mul_rpow_sum {c₀ X x : ℝ} (hX : 0 < X) (hXx : X ≤ x)
    (hψ : ∀ y, 2 ≤ y → ψ y ≤ c₀ * y) :
    ψ x - θ x ≤
      c₀ * (X ^ (-(1 : ℝ) / 2) + X ^ (-(2 : ℝ) / 3) + X ^ (-(4 : ℝ) / 5)) * x := by
  have hx : 0 < x := lt_of_lt_of_le hX hXx
  have hc₀ : 0 < c₀ := pos_of_psi_le hψ
  have hrpow (r s : ℝ) (hrs : r = s + 1) (hs : s ≤ 0) : x ^ r ≤ X ^ s * x := by
    calc x ^ r = x ^ s * x := by rw [hrs, Real.rpow_add_one hx.ne']
      _ ≤ X ^ s * x := mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_nonpos hX hXx hs) hx.le
  have h2 : ψ (x ^ (2 : ℝ)⁻¹) ≤ c₀ * (X ^ (-(1 : ℝ) / 2) * x) :=
    (psi_le_mul_of_two_le (by positivity) hψ).trans
      (mul_le_mul_of_nonneg_left (hrpow _ _ (by norm_num) (by norm_num)) hc₀.le)
  have h3 : ψ (x ^ (3 : ℝ)⁻¹) ≤ c₀ * (X ^ (-(2 : ℝ) / 3) * x) :=
    (psi_le_mul_of_two_le (by positivity) hψ).trans
      (mul_le_mul_of_nonneg_left (hrpow _ _ (by norm_num) (by norm_num)) hc₀.le)
  have h5 : ψ (x ^ (5 : ℝ)⁻¹) ≤ c₀ * (X ^ (-(4 : ℝ) / 5) * x) :=
    (psi_le_mul_of_two_le (by positivity) hψ).trans
      (mul_le_mul_of_nonneg_left (hrpow _ _ (by norm_num) (by norm_num)) hc₀.le)
  linarith [Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi x]

/-- Exponential-cutoff form of `psi_sub_theta_le_mul_rpow_sum`: for `exp b ≤ x` and
`ψ y ≤ c₀ * y` on `[2, ∞)`,
`ψ x - θ x ≤ c₀ * (exp (-b / 2) + exp (-2 * b / 3) + exp (-4 * b / 5)) * x`. -/
theorem psi_sub_theta_le_mul_exp_sum {c₀ b x : ℝ} (hbx : Real.exp b ≤ x)
    (hψ : ∀ y, 2 ≤ y → ψ y ≤ c₀ * y) :
    ψ x - θ x ≤
      c₀ * (Real.exp (-b / 2) + Real.exp (-(2 * b) / 3) + Real.exp (-(4 * b) / 5)) * x := by
  have h := psi_sub_theta_le_mul_rpow_sum (Real.exp_pos b) hbx hψ
  have he1 : Real.exp b ^ (-(1 : ℝ) / 2) = Real.exp (-b / 2) := by
    rw [← Real.exp_mul]; congr 1; ring
  have he2 : Real.exp b ^ (-(2 : ℝ) / 3) = Real.exp (-(2 * b) / 3) := by
    rw [← Real.exp_mul]; congr 1; ring
  have he3 : Real.exp b ^ (-(4 : ℝ) / 5) = Real.exp (-(4 * b) / 5) := by
    rw [← Real.exp_mul]; congr 1; ring
  rwa [he1, he2, he3] at h

/-- Lower transfer from `ψ` to `θ` at a cutoff `X > 0`: from `a * x ≤ ψ x` and a global bound
`ψ y ≤ c₀ * y` on `[2, ∞)`,
`(a - c₀ * (X ^ (-1 / 2) + X ^ (-2 / 3) + X ^ (-4 / 5))) * x ≤ θ x` for `X ≤ x`. -/
theorem le_theta_of_le_psi_rpow {a c₀ X x : ℝ} (hX : 0 < X) (hXx : X ≤ x)
    (hψ : ∀ y, 2 ≤ y → ψ y ≤ c₀ * y) (hψx : a * x ≤ ψ x) :
    (a - c₀ * (X ^ (-(1 : ℝ) / 2) + X ^ (-(2 : ℝ) / 3) + X ^ (-(4 : ℝ) / 5))) * x ≤ θ x := by
  linarith [psi_sub_theta_le_mul_rpow_sum hX hXx hψ]

/-- Lower transfer from `ψ` to `θ` at an exponential cutoff `exp b` (Broadbent, Kadiri, Lumley,
Ng, and Wilk, Lemma 11, lower half): from `a * x ≤ ψ x` and `ψ y ≤ c₀ * y` on `[2, ∞)`,
`(a - c₀ * (exp (-b / 2) + exp (-2 * b / 3) + exp (-4 * b / 5))) * x ≤ θ x` for `exp b ≤ x`. -/
theorem le_theta_of_le_psi_exp {a c₀ b x : ℝ} (hbx : Real.exp b ≤ x)
    (hψ : ∀ y, 2 ≤ y → ψ y ≤ c₀ * y) (hψx : a * x ≤ ψ x) :
    (a - c₀ * (Real.exp (-b / 2) + Real.exp (-(2 * b) / 3) + Real.exp (-(4 * b) / 5))) * x ≤
      θ x := by
  linarith [psi_sub_theta_le_mul_exp_sum hbx hψ]

/-! ### Prime-power counts up to `N` and `O(x / log x)` estimates -/

/-- Natural-number form of the prime-power count bound: for every integer `N ≥ 2`,
`#{n ∈ Ioc 0 N | IsPrimePow n} ≤ 6 * N / log N`. -/
theorem card_filter_isPrimePow_Ioc_nat_le_six_mul_div_log {N : ℕ} (hN : 2 ≤ N) :
    (#{n ∈ Ioc 0 N | IsPrimePow n} : ℝ) ≤ 6 * N / Real.log N := by
  simpa only [Nat.floor_natCast] using
    Chebyshev.card_filter_isPrimePow_le_six_mul_div_log (by exact_mod_cast hN : (2 : ℝ) ≤ N)

/-- Asymptotic bound for the prime-power count on `ℝ`:
`#{n ∈ Ioc 0 ⌊x⌋₊ | IsPrimePow n} = O(x / log x)` as `x → ∞`. -/
theorem isBigO_card_filter_isPrimePow_Ioc_div_log :
    (fun x : ℝ ↦ (#{n ∈ Ioc 0 ⌊x⌋₊ | IsPrimePow n} : ℝ)) =O[atTop]
      (fun x : ℝ ↦ x / Real.log x) := by
  refine Asymptotics.IsBigO.of_bound 6 ?_
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (by positivity)]
  simpa only [mul_div_assoc] using Chebyshev.card_filter_isPrimePow_le_six_mul_div_log hx

/-- Asymptotic bound for the prime-power count on `ℕ`:
`#{n ∈ Ioc 0 N | IsPrimePow n} = O(N / log N)` as `N → ∞`. -/
theorem isBigO_card_filter_isPrimePow_Ioc_nat_div_log :
    (fun N : ℕ ↦ (#{n ∈ Ioc 0 N | IsPrimePow n} : ℝ)) =O[atTop]
      (fun N : ℕ ↦ (N : ℝ) / Real.log N) := by
  simpa only [Function.comp_def, Nat.floor_natCast] using
    isBigO_card_filter_isPrimePow_Ioc_div_log.comp_tendsto tendsto_natCast_atTop_atTop

end TauCeti

end TauCetiExtensions
