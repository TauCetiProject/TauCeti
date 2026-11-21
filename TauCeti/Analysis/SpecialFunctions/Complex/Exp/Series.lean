/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exponential
import TauCeti.Analysis.Normed.Algebra.Exponential

/-!
# The exponential series without its constant term

In any complete normed algebra, dropping the constant term `1` of the exponential series gives the
series of `exp x - 1`, re-indexed from `0` (`NormedSpace.hasSum_exp_sub_one`). This file records
its complex form, with `Complex.exp` and multiplication: `exp z - 1 = ∑ₙ z ^ (n + 1) / (n + 1)!`.

Dropping the linear term too gives the remainder `exp z - 1 - z = ∑ₙ bₙ z ^ (n + 1)`, with
`b₀ = 0` and `bₙ = 1 / (n + 1)!` for `n ≥ 1` (`Complex.expRemainderCoeff`). Its majorant series
`∑ₙ ‖bₙ‖ xⁿ` at `x ≥ 0` is at most `x exp x`, which bounds the remainder quadratically.

## Main results

* `Complex.hasSum_exp_sub_one`: `exp z - 1 = ∑ₙ z ^ (n + 1) / (n + 1)!` for every complex `z`.
* `Complex.hasSum_expRemainderCoeff`: `exp z - 1 - z = ∑ₙ bₙ z ^ (n + 1)`.
* `Complex.summable_and_tsum_norm_expRemainderCoeff_le`: the majorant `∑ₙ ‖bₙ‖ xⁿ` is at most
  `x exp x` for `x ≥ 0`.
-/

public section

open scoped Nat

namespace Complex

/-- The exponential series without its constant term: `exp z - 1 = ∑ₙ z ^ (n + 1) / (n + 1)!`. -/
theorem hasSum_exp_sub_one (z : ℂ) :
    HasSum (fun n : ℕ ↦ (((n + 1)! : ℂ))⁻¹ * z ^ (n + 1)) (exp z - 1) := by
  simpa only [smul_eq_mul, ← exp_eq_exp_ℂ] using NormedSpace.hasSum_exp_sub_one ℂ z

/-- The coefficients of `exp z - 1 - z = ∑ₙ bₙ z ^ (n + 1)`: the exponential series without its
terms of degree `0` and `1`, so `b₀ = 0` and `bₙ = 1 / (n + 1)!` for `n ≥ 1`. -/
noncomputable def expRemainderCoeff (n : ℕ) : ℂ := (((n + 1)! : ℂ))⁻¹ - if n = 0 then 1 else 0

/-- The remainder series has no term of degree `1`: `b₀ = 0`. -/
@[simp]
theorem expRemainderCoeff_zero : expRemainderCoeff 0 = 0 := by simp [expRemainderCoeff]

/-- The coefficient of `z ^ (n + 2)` in `exp z - 1 - z` is `1 / (n + 2)!`. -/
@[simp]
theorem expRemainderCoeff_succ (n : ℕ) : expRemainderCoeff (n + 1) = (((n + 2)! : ℂ))⁻¹ := by
  simp [expRemainderCoeff]

/-- The exponential series without its constant and linear terms:
`exp z - 1 - z = ∑ₙ bₙ z ^ (n + 1)`. -/
theorem hasSum_expRemainderCoeff (z : ℂ) :
    HasSum (fun n ↦ expRemainderCoeff n * z ^ (n + 1)) (exp z - 1 - z) := by
  have h := (hasSum_exp_sub_one z).sub (hasSum_ite_eq 0 z)
  refine h.congr_fun fun n ↦ ?_
  rcases n with _ | n <;> simp

/-- The majorant series `∑ₙ ‖bₙ‖ xⁿ` of `expRemainderCoeff` at `x ≥ 0` converges, with sum at most
`x exp x`. -/
theorem summable_and_tsum_norm_expRemainderCoeff_le {x : ℝ} (hx : 0 ≤ x) :
    Summable (fun n ↦ ‖expRemainderCoeff n‖ * x ^ n) ∧
      ∑' n, ‖expRemainderCoeff n‖ * x ^ n ≤ x * Real.exp x := by
  -- After the vanishing term `n = 0`, the terms are `x ^ (n + 1) / (n + 2)! ≤ x · xⁿ / n!`.
  have hle (n : ℕ) : ‖expRemainderCoeff (n + 1)‖ * x ^ (n + 1) ≤ x * (x ^ n / n !) := by
    have h₂ : (n ! : ℝ) ≤ (n + 2)! :=
      Nat.cast_le.2 (Nat.factorial_le (by omega))
    simp only [expRemainderCoeff_succ, norm_inv, Complex.norm_natCast, pow_succ, div_eq_mul_inv]
    calc ((n + 2)! : ℝ)⁻¹ * (x ^ n * x) ≤ (n ! : ℝ)⁻¹ * (x ^ n * x) := by
          gcongr
      _ = x * (x ^ n * (n ! : ℝ)⁻¹) := by ring
  have hexp := (Real.summable_pow_div_factorial x).mul_left x
  have hsum : Summable fun n ↦ ‖expRemainderCoeff (n + 1)‖ * x ^ (n + 1) :=
    hexp.of_nonneg_of_le (fun n ↦ by positivity) hle
  have hsum' : Summable fun n ↦ ‖expRemainderCoeff n‖ * x ^ n := (summable_nat_add_iff 1).1 hsum
  refine ⟨hsum', ?_⟩
  rw [hsum'.tsum_eq_zero_add, expRemainderCoeff_zero, norm_zero, zero_mul, zero_add,
    Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div, ← tsum_mul_left]
  exact hsum.tsum_le_tsum hle hexp

end Complex
