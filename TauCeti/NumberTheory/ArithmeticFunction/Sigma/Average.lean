/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import TauCeti.NumberTheory.ArithmeticFunction.Sigma.Basic
public import TauCeti.NumberTheory.Harmonic.Remainder
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import TauCeti.Analysis.Real.Sqrt
import TauCeti.Analysis.SpecialFunctions.Log.Bounds
import TauCeti.NumberTheory.Harmonic.FloorSum

/-!
# The average order of the divisor function

Write `τ(n) = σ₀(n)` for the number of divisors of `n`. This file proves Dirichlet's theorem that
`τ(n)` is `log n` on average, in the form

  `∑_{n ≤ x} τ(n) = x log x + (2γ - 1) x + O(√x)`,

where `γ` is the Euler–Mascheroni constant, with the explicit error `6 √x` for every real
`x ≥ 0`.

The proof is Dirichlet's hyperbola method. The sum counts the pairs `(a, b)` of positive integers
with `a b ≤ N`, and such a pair has `a ≤ M` or `b ≤ M` for `M = ⌊√N⌋`. Counting the pairs with
`a ≤ M`, those with `b ≤ M`, and the `M²` pairs with both, gives the exact identity
`∑_{n ≤ N} τ(n) + M² = 2 ∑_{a ≤ M} ⌊N / a⌋`. Replacing `⌊N / a⌋` by `x / a` costs at most `M`, and
the harmonic sum `∑_{a ≤ M} 1 / a` is `log M + γ` up to `1 / (2M)`
(`TauCeti.harmonic_sub_log_sub_eulerMascheroniConstant_le`).

## Main results

* `TauCeti.sum_Ioc_sigma_zero_natFloor_add_sq`: the hyperbola identity
  `∑_{n ≤ x} τ(n) + ⌊√x⌋² = 2 ∑_{a ≤ √x} ⌊x / a⌋` with a real cutoff; the natural-number form
  `TauCeti.sum_Ioc_sigma_zero_add_sqrt_sq` is in `Sigma/Basic.lean`.
* `TauCeti.abs_sum_Ioc_sigma_zero_sub_le`:
  `|∑_{n ≤ x} τ(n) - (x log x + (2γ - 1) x)| ≤ 6 √x` for `x ≥ 0`.
* `TauCeti.isBigO_sum_Ioc_sigma_zero_sub`: the error is `O(√x)` as `x → ∞`.

## References

* D. Koukoulopoulos, *The Distribution of Prime Numbers*, Graduate Studies in Mathematics 203,
  AMS (2019), Theorem 3.3.
-/

public section

open Finset Real
open scoped ArithmeticFunction.sigma

namespace TauCeti

/-! ### The average order -/

/-- **Dirichlet's hyperbola identity** for the divisor function, with a real cutoff:
`∑_{n ≤ x} τ(n) + ⌊√x⌋² = 2 ∑_{a ≤ √x} ⌊x / a⌋`. -/
theorem sum_Ioc_sigma_zero_natFloor_add_sq (x : ℝ) :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, σ 0 n + ⌊√x⌋₊ ^ 2 = 2 * ∑ a ∈ Ioc 0 ⌊√x⌋₊, ⌊x / a⌋₊ := by
  simp only [nat_floor_real_sqrt_eq_nat_sqrt_floor, Nat.floor_div_natCast]
  exact sum_Ioc_sigma_zero_add_sqrt_sq _

/-- For `0 ≤ x < 1` the main term `x log x + (2γ - 1) x` is at most `6 √x` in absolute value. -/
private theorem abs_mul_log_add_le_of_lt_one {x : ℝ} (hx : 0 ≤ x) (hx1 : x < 1) :
    |x * log x + (2 * eulerMascheroniConstant - 1) * x| ≤ 6 * √x := by
  rcases hx.eq_or_lt with rfl | hx0
  · simp
  have hs : 0 < √x := sqrt_pos.2 hx0
  have hs1 : √x < 1 := (sqrt_lt' zero_lt_one).2 (by simpa using hx1)
  have hxs : x = √x * √x := (mul_self_sqrt hx).symm
  have hlog : log x = 2 * log √x := by rw [log_sqrt hx]; ring
  have hlog_le : log √x ≤ 0 := log_nonpos hs.le hs1.le
  have hlog_ge : √x - 1 ≤ √x * log √x := self_sub_one_le_mul_log (sqrt_nonneg x)
  have hγ₁ := one_half_lt_eulerMascheroniConstant
  have hγ₂ := eulerMascheroniConstant_lt_two_thirds
  have hprod : x * log x = 2 * √x * (√x * log √x) := by rw [hlog]; nlinarith [hxs]
  rw [hprod, abs_le]
  constructor <;> nlinarith [mul_nonneg hs.le hs.le, mul_nonpos_of_nonneg_of_nonpos hs.le hlog_le]

/-- **Dirichlet's theorem on the average order of the divisor function**, with an explicit error:
`|∑_{n ≤ x} τ(n) - (x log x + (2γ - 1) x)| ≤ 6 √x` for every real `x ≥ 0`, where `γ` is the
Euler–Mascheroni constant. -/
theorem abs_sum_Ioc_sigma_zero_sub_le {x : ℝ} (hx : 0 ≤ x) :
    |∑ n ∈ Ioc 0 ⌊x⌋₊, (σ 0 n : ℝ) - (x * log x + (2 * eulerMascheroniConstant - 1) * x)| ≤
      6 * √x := by
  rcases lt_or_ge x 1 with hx1 | hx1
  · rw [Nat.floor_eq_zero.2 hx1, Ioc_self, sum_empty, zero_sub, abs_neg]
    exact abs_mul_log_add_le_of_lt_one hx hx1
  -- Notation: `N = ⌊x⌋₊`, `M = ⌊√N⌋`, and `H` the `M`-th harmonic number.
  have hM : 0 < ⌊x⌋₊.sqrt := Nat.sqrt_pos.2 (Nat.floor_pos.2 hx1)
  have hM1 : (1 : ℝ) ≤ (⌊x⌋₊.sqrt : ℕ) := by exact_mod_cast hM
  have hMs := nat_sqrt_floor_le_real_sqrt x
  have hsM := real_sqrt_lt_nat_sqrt_floor_add_one x
  have hxs : x = √x * √x := (mul_self_sqrt hx).symm
  -- The hyperbola identity, with the terms `⌊N / a⌋` compared with `x / a`.
  have hid : ∑ n ∈ Ioc 0 ⌊x⌋₊, (σ 0 n : ℝ) + (⌊x⌋₊.sqrt : ℕ) ^ 2 =
      2 * ∑ a ∈ Ioc 0 ⌊x⌋₊.sqrt, ((⌊x⌋₊ / a : ℕ) : ℝ) := by
    exact_mod_cast sum_Ioc_sigma_zero_add_sqrt_sq ⌊x⌋₊
  have hup := sum_Ioc_natFloor_div_le_mul_harmonic hx ⌊x⌋₊.sqrt
  have hlo := mul_harmonic_sub_le_sum_Ioc_natFloor_div x ⌊x⌋₊.sqrt
  -- The harmonic number and the logarithm of `M`.
  have hh_up := harmonic_sub_log_sub_eulerMascheroniConstant_le ⌊x⌋₊.sqrt
  have hh_lo : 0 ≤ (harmonic ⌊x⌋₊.sqrt : ℝ) - log (⌊x⌋₊.sqrt : ℕ) - eulerMascheroniConstant :=
    le_trans (by positivity)
      (one_div_two_mul_add_le_harmonic_sub_log_sub_eulerMascheroniConstant hM.ne')
  have hlogx : log x = 2 * log √x := by rw [log_sqrt hx]; ring
  have hL_up : log (⌊x⌋₊.sqrt : ℕ) ≤ log √x := log_le_log (by linarith) hMs
  have hL_lo := log_sub_one_div_le_log (sqrt_nonneg x) (Nat.cast_nonneg ⌊x⌋₊.sqrt) hsM.le
  -- The sizes of `x / M` and `x - M²`.
  have hxM : x / (⌊x⌋₊.sqrt : ℕ) ≤ 2 * √x := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [sqrt_nonneg x]
  have hsub_up : x - (⌊x⌋₊.sqrt : ℕ) ^ 2 ≤ 2 * √x := by nlinarith [sqrt_nonneg x]
  have hsub_lo : 0 ≤ x - (⌊x⌋₊.sqrt : ℕ) ^ 2 := by nlinarith [sqrt_nonneg x]
  have hxh_up : x * ((harmonic ⌊x⌋₊.sqrt : ℝ) - log (⌊x⌋₊.sqrt : ℕ) - eulerMascheroniConstant) ≤
      x / (⌊x⌋₊.sqrt : ℕ) / 2 := by
    refine (mul_le_mul_of_nonneg_left hh_up hx).trans (le_of_eq ?_)
    field_simp
  have hxh_lo := mul_nonneg hx hh_lo
  have hxL_up := mul_le_mul_of_nonneg_left hL_up hx
  have hxL_lo := mul_le_mul_of_nonneg_left hL_lo hx
  rw [mul_sub, mul_one_div] at hxL_lo
  rw [hlogx, abs_le]
  constructor <;> nlinarith [sqrt_nonneg x]

/-- **Dirichlet's theorem on the average order of the divisor function**:
`∑_{n ≤ x} τ(n) = x log x + (2γ - 1) x + O(√x)` as `x → ∞`. -/
theorem isBigO_sum_Ioc_sigma_zero_sub :
    (fun x : ℝ ↦ ∑ n ∈ Ioc 0 ⌊x⌋₊, (σ 0 n : ℝ) -
      (x * log x + (2 * eulerMascheroniConstant - 1) * x)) =O[Filter.atTop] fun x ↦ √x :=
  Asymptotics.IsBigO.of_bound 6 <| (Filter.eventually_ge_atTop 0).mono fun x hx ↦ by
    rw [norm_eq_abs, norm_eq_abs, abs_of_nonneg (sqrt_nonneg x)]
    exact abs_sum_Ioc_sigma_zero_sub_le hx

end TauCeti
