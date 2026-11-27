/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

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
  -- `2 √x (√x - 1) ≤ x log x ≤ 0`, by scaling `√x - 1 ≤ √x log √x ≤ 0` by `2 √x`.
  have hA_up : 2 * √x * (√x * log √x) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) (mul_nonpos_of_nonneg_of_nonpos hs.le hlog_le)
  have hA_lo : 2 * √x * (√x - 1) ≤ 2 * √x * (√x * log √x) :=
    mul_le_mul_of_nonneg_left hlog_ge (by positivity)
  -- `0 ≤ (2γ - 1) x ≤ x ≤ √x`.
  have hB_lo : 0 ≤ (2 * eulerMascheroniConstant - 1) * x := mul_nonneg (by linarith) hx
  have hB_up : (2 * eulerMascheroniConstant - 1) * x ≤ x := mul_le_of_le_one_left hx (by linarith)
  have hxle : x ≤ √x := hxs.le.trans (mul_le_of_le_one_right hs.le hs1.le)
  rw [hprod, abs_le]
  constructor
  · linarith [hA_lo, hB_lo, mul_nonneg hs.le hs.le]
  · linarith [hA_up, hB_up, hxle]

/-- The sum of the hyperbola method: for `x ≥ 1` and `M = ⌊√⌊x⌋⌋`,
`∑_{a ≤ M} ⌊x / a⌋ = x (log √x + γ) + E` with `-3 √x ≤ E ≤ √x`. The error `E` collects three
terms: `⌊x / a⌋` against `x / a` (between `-M` and `0` in total), the harmonic number `H_M` against
`log M + γ` (between `0` and `1 / (2 M)`), and `log M` against `log √x` (between `-1 / M` and
`0`). -/
private theorem sum_Ioc_natFloor_div_sub_mem {x : ℝ} (hx1 : 1 ≤ x) :
    -(3 * √x) ≤ ∑ a ∈ Ioc 0 ⌊x⌋₊.sqrt, ((⌊x⌋₊ / a : ℕ) : ℝ) -
        x * (log √x + eulerMascheroniConstant) ∧
      ∑ a ∈ Ioc 0 ⌊x⌋₊.sqrt, ((⌊x⌋₊ / a : ℕ) : ℝ) -
        x * (log √x + eulerMascheroniConstant) ≤ √x := by
  have hx : 0 ≤ x := zero_le_one.trans hx1
  have hM : 0 < ⌊x⌋₊.sqrt := Nat.sqrt_pos.2 (Nat.floor_pos.2 hx1)
  have hM1 : (1 : ℝ) ≤ (⌊x⌋₊.sqrt : ℕ) := by exact_mod_cast hM
  have hMs := nat_sqrt_floor_le_real_sqrt x
  have hsM := real_sqrt_lt_nat_sqrt_floor_add_one x
  have hxs : x = √x * √x := (mul_self_sqrt hx).symm
  have hxM : x / (⌊x⌋₊.sqrt : ℕ) ≤ 2 * √x := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [sqrt_nonneg x]
  -- The floor sum against `x H_M`.
  have he₁_up := sum_Ioc_natFloor_div_le_mul_harmonic hx ⌊x⌋₊.sqrt
  have he₁_lo := mul_harmonic_sub_le_sum_Ioc_natFloor_div x ⌊x⌋₊.sqrt
  -- The harmonic number against `log M + γ`, scaled by `x`.
  have he₂_lo : 0 ≤ x * ((harmonic ⌊x⌋₊.sqrt : ℝ) - log (⌊x⌋₊.sqrt : ℕ) -
      eulerMascheroniConstant) :=
    mul_nonneg hx (le_trans (by positivity)
      (one_div_two_mul_add_le_harmonic_sub_log_sub_eulerMascheroniConstant hM.ne'))
  have he₂_up : x * ((harmonic ⌊x⌋₊.sqrt : ℝ) - log (⌊x⌋₊.sqrt : ℕ) -
      eulerMascheroniConstant) ≤ √x := by
    have h := mul_le_mul_of_nonneg_left
      (harmonic_sub_log_sub_eulerMascheroniConstant_le ⌊x⌋₊.sqrt) hx
    rw [mul_one_div, div_mul_eq_div_div_swap] at h
    linarith [h, hxM]
  -- `log M` against `log √x`, scaled by `x`.
  have he₃_up : x * (log (⌊x⌋₊.sqrt : ℕ) - log √x) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hx (sub_nonpos.2 (log_le_log (by linarith) hMs))
  have he₃_lo : -(2 * √x) ≤ x * (log (⌊x⌋₊.sqrt : ℕ) - log √x) := by
    have hL := log_sub_one_div_le_log (sqrt_nonneg x) (Nat.cast_nonneg ⌊x⌋₊.sqrt) hsM.le
    have h := mul_le_mul_of_nonneg_left
      (by linarith [hL] : -(1 / ((⌊x⌋₊.sqrt : ℕ) : ℝ)) ≤ log (⌊x⌋₊.sqrt : ℕ) - log √x) hx
    rw [mul_neg, mul_one_div] at h
    linarith [h, hxM]
  have hdecomp : ∑ a ∈ Ioc 0 ⌊x⌋₊.sqrt, ((⌊x⌋₊ / a : ℕ) : ℝ) -
      x * (log √x + eulerMascheroniConstant) =
      (∑ a ∈ Ioc 0 ⌊x⌋₊.sqrt, ((⌊x⌋₊ / a : ℕ) : ℝ) - x * harmonic ⌊x⌋₊.sqrt) +
        x * ((harmonic ⌊x⌋₊.sqrt : ℝ) - log (⌊x⌋₊.sqrt : ℕ) - eulerMascheroniConstant) +
        x * (log (⌊x⌋₊.sqrt : ℕ) - log √x) := by
    ring
  rw [hdecomp]
  constructor
  · linarith [he₁_lo, he₂_lo, he₃_lo, hMs]
  · linarith [he₁_up, he₂_up, he₃_up]

/-- **Dirichlet's theorem on the average order of the divisor function**, with an explicit error:
`|∑_{n ≤ x} τ(n) - (x log x + (2γ - 1) x)| ≤ 6 √x` for every real `x ≥ 0`, where `γ` is the
Euler–Mascheroni constant. -/
theorem abs_sum_Ioc_sigma_zero_sub_le {x : ℝ} (hx : 0 ≤ x) :
    |∑ n ∈ Ioc 0 ⌊x⌋₊, (σ 0 n : ℝ) - (x * log x + (2 * eulerMascheroniConstant - 1) * x)| ≤
      6 * √x := by
  rcases lt_or_ge x 1 with hx1 | hx1
  · rw [Nat.floor_eq_zero.2 hx1, Ioc_self, sum_empty, zero_sub, abs_neg]
    exact abs_mul_log_add_le_of_lt_one hx hx1
  have hMs := nat_sqrt_floor_le_real_sqrt x
  have hsM := real_sqrt_lt_nat_sqrt_floor_add_one x
  have hxs : x = √x * √x := (mul_self_sqrt hx).symm
  -- The hyperbola identity, and the square cutoff `0 ≤ x - M² ≤ 2 √x`.
  have hid : ∑ n ∈ Ioc 0 ⌊x⌋₊, (σ 0 n : ℝ) + (⌊x⌋₊.sqrt : ℕ) ^ 2 =
      2 * ∑ a ∈ Ioc 0 ⌊x⌋₊.sqrt, ((⌊x⌋₊ / a : ℕ) : ℝ) := by
    exact_mod_cast sum_Ioc_sigma_zero_add_sqrt_sq ⌊x⌋₊
  have hsub_up : x - (⌊x⌋₊.sqrt : ℕ) ^ 2 ≤ 2 * √x := by nlinarith [sqrt_nonneg x]
  have hsub_lo : 0 ≤ x - (⌊x⌋₊.sqrt : ℕ) ^ 2 := by nlinarith [sqrt_nonneg x]
  obtain ⟨hF_lo, hF_up⟩ := sum_Ioc_natFloor_div_sub_mem hx1
  have hlogx : log x = 2 * log √x := by rw [log_sqrt hx]; ring
  -- The difference is twice the error of the hyperbola sum plus `x - M²`.
  have hdecomp : ∑ n ∈ Ioc 0 ⌊x⌋₊, (σ 0 n : ℝ) -
      (x * (2 * log √x) + (2 * eulerMascheroniConstant - 1) * x) =
      2 * (∑ a ∈ Ioc 0 ⌊x⌋₊.sqrt, ((⌊x⌋₊ / a : ℕ) : ℝ) -
        x * (log √x + eulerMascheroniConstant)) + (x - ((⌊x⌋₊.sqrt : ℕ) : ℝ) ^ 2) := by
    linear_combination hid
  rw [hlogx, abs_le, hdecomp]
  constructor
  · linarith [hF_lo, hsub_lo]
  · linarith [hF_up, hsub_up]

/-- **Dirichlet's theorem on the average order of the divisor function**:
`∑_{n ≤ x} τ(n) = x log x + (2γ - 1) x + O(√x)` as `x → ∞`. -/
theorem isBigO_sum_Ioc_sigma_zero_sub :
    (fun x : ℝ ↦ ∑ n ∈ Ioc 0 ⌊x⌋₊, (σ 0 n : ℝ) -
      (x * log x + (2 * eulerMascheroniConstant - 1) * x)) =O[Filter.atTop] fun x ↦ √x :=
  Asymptotics.IsBigO.of_bound 6 <| (Filter.eventually_ge_atTop 0).mono fun x hx ↦ by
    rw [norm_eq_abs, norm_eq_abs, abs_of_nonneg (sqrt_nonneg x)]
    exact abs_sum_Ioc_sigma_zero_sub_le hx

end TauCeti
