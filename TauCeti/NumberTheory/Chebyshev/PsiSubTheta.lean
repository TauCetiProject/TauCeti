/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds
import TauCeti.Algebra.Order.Floor.Semifield
import TauCeti.Analysis.SpecialFunctions.Log.Bounds
import TauCeti.NumberTheory.PrimeCounting

/-!
# Explicit bounds for the difference `ψ − θ`

For real `x ≥ 0`, Mathlib's `Chebyshev.psi_eq_sum_theta` writes `ψ(x) = ∑_{k ≥ 1} θ(x^{1/k})`, the
terms with `k > log x / log 2` vanishing. Splitting off `k = 1` and `k = 2`,

`ψ(x) − θ(x) = θ(√x) + ∑_{3 ≤ k ≤ log x / log 2} θ(x^{1/k})`,

and this file turns that decomposition into the explicit two-sided bounds for `ψ − θ` used to pass
between bounds for `ψ` and for `θ`:

* from any bound `θ(y) ≤ c y` on `y > 0`, `ψ(x) − θ(x) ≤ c (√x + (log x / log 2 − 2)⁺ x^{1/3})`;
  at `c = log 4` (`Chebyshev.theta_le_log4_mul_x`) this is unconditional;
* from relative bounds `(1 − ε) y ≤ θ(y) ≤ (1 + ε) y` for `y ≥ y₀`, the sharper
  `(1 − ε) √x + θ(x^{1/3}) ≤ ψ(x) − θ(x) ≤ (1 + ε) √x + c (log x / log 2 − 2) x^{1/3}`
  for `x ≥ y₀²` (and `x ≥ 4` on the right);
* conversely, a bound for `ψ` gives one for `θ` through Costa Pereira's comparison
  `ψ(x) − θ(x) ≤ ψ(x^{1/2}) + ψ(x^{1/3}) + ψ(x^{1/5})`.

It also counts the prime powers: the prime powers `m ≤ x` number `∑_{k ≥ 1} π(x^{1/k})`, which is at
most `π(x) + (log x / log 2 − 1) √x ≤ 6 x / log x` for `x ≥ 2`.

## Main results

* `Chebyshev.psi_eq_theta_add_theta_sqrt_add_sum`: the decomposition above.
* `Chebyshev.theta_sqrt_add_theta_rpow_le_psi_sub_theta`: `θ(√x) + θ(x^{1/3}) ≤ ψ(x) − θ(x)`.
* `Chebyshev.sum_rpow_one_div_le`:
  `∑_{3 ≤ k ≤ log x / log 2} x^{1/k} ≤ (log x / log 2 − 2)⁺ x^{1/3}`.
* `Chebyshev.theta_le_mul_of_nonneg`, `Chebyshev.psi_le_mul_of_nonneg`,
  `Chebyshev.nonneg_of_forall_theta_le`, `Chebyshev.nonneg_of_forall_psi_le`: a linear bound for
  `θ` or `ψ` on `y > 0` extends to `y = 0` and has a nonnegative constant.
* `Chebyshev.psi_sub_theta_le_of_forall_theta_le`, `Chebyshev.psi_sub_theta_le_log_four_mul`:
  the upper bound from a linear bound for `θ`, and its unconditional case.
* `Chebyshev.psi_sub_theta_le_one_add_mul_sqrt_add`,
  `Chebyshev.one_sub_mul_sqrt_add_theta_rpow_le_psi_sub_theta`: the transfer of a relative bound
  for `θ` to `ψ − θ`.
* `Chebyshev.abs_theta_sub_le_abs_psi_sub_add`, `Chebyshev.abs_psi_sub_le_abs_theta_sub_add`:
  the conversions between bounds for `|ψ(x) − x|` and `|θ(x) − x|`.
* `Chebyshev.theta_le_one_add_mul_of_psi_le`: a linear bound for `θ` on `x > 0` from a bound for
  `ψ` beyond `x₁` and `θ(y) ≤ y` below `x₁`.
* `Chebyshev.theta_ge_psi_sub_mul`, `Chebyshev.theta_ge_of_psi_ge_of_exp_le`: a lower bound for
  `θ` from a lower bound for `ψ` and a linear upper bound for `ψ`.
* `Chebyshev.card_filter_isPrimePow_eq_sum_primeCounting`,
  `Chebyshev.card_filter_isPrimePow_le_six_mul_div_log`,
  `Chebyshev.card_filter_range_isPrimePow_le_six_mul_div_log`: the number of prime powers up to
  `x`, and below an integer `N`.

## References

* L. Schoenfeld, *Sharper bounds for the Chebyshev functions θ(x) and ψ(x). II*, Math. Comp. 30
  (1976), 337–360, which displays the same decomposition of `ψ − θ`.
* S. Broadbent, H. Kadiri, A. Lumley, N. Ng, K. Wilk, *Sharper bounds for the Chebyshev function
  θ(x)*, Math. Comp. 90 (2021), 2281–2315: (2.4), Propositions 3–4 and Lemma 11.
-/

public section

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
