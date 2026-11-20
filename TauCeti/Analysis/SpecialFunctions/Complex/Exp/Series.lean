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
Dropping the linear term as well gives the series `exp z - 1 - z = ∑ₙ aₙ z ^ (n + 1)` of the
quadratic remainder, whose coefficients `aₙ` (`Complex.expRemainderCoeff`) vanish at `n = 0` and
are bounded by `1 / n!`.

## Main definitions

* `Complex.expRemainderCoeff`: the coefficients of the series of `exp z - 1 - z`.

## Main results

* `Complex.hasSum_exp_sub_one`: `exp z - 1 = ∑ₙ z ^ (n + 1) / (n + 1)!` for every complex `z`.
* `Complex.hasSum_expRemainderCoeff`: `exp z - 1 - z = ∑ₙ aₙ z ^ (n + 1)` for every complex `z`.
-/

public section

open scoped Nat

namespace Complex

/-- The exponential series without its constant term: `exp z - 1 = ∑ₙ z ^ (n + 1) / (n + 1)!`. -/
theorem hasSum_exp_sub_one (z : ℂ) :
    HasSum (fun n : ℕ ↦ (((n + 1)! : ℂ))⁻¹ * z ^ (n + 1)) (exp z - 1) := by
  simpa only [smul_eq_mul, ← exp_eq_exp_ℂ] using NormedSpace.hasSum_exp_sub_one ℂ z

/-- The coefficients of the series `exp z - 1 - z = ∑ₙ aₙ z ^ (n + 1)`
(`Complex.hasSum_expRemainderCoeff`): `a₀ = 0` and `aₙ = 1 / (n + 1)!` for `n ≥ 1`. -/
noncomputable def expRemainderCoeff (n : ℕ) : ℂ := (((n + 1)! : ℂ))⁻¹ - if n = 0 then 1 else 0

/-- The remainder series has no term of degree `1`: `a₀ = 0`. -/
@[simp]
theorem expRemainderCoeff_zero : expRemainderCoeff 0 = 0 := by
  simp [expRemainderCoeff]

/-- The coefficients of the series of `exp z - 1 - z` are bounded by `‖aₙ‖ ≤ 1 / n!`. -/
theorem norm_expRemainderCoeff_le (n : ℕ) : ‖expRemainderCoeff n‖ ≤ ((n ! : ℝ))⁻¹ := by
  rcases n with _ | n
  · simp
  · have han : expRemainderCoeff (n + 1) = (((n + 1 + 1)! : ℂ))⁻¹ := by
      simp [expRemainderCoeff]
    rw [han, norm_inv, norm_natCast]
    gcongr
    exact Nat.le_succ n

/-- The series of the quadratic remainder of the exponential:
`exp z - 1 - z = ∑ₙ aₙ z ^ (n + 1)`, with `aₙ = Complex.expRemainderCoeff n`. -/
theorem hasSum_expRemainderCoeff (z : ℂ) :
    HasSum (fun n ↦ expRemainderCoeff n * z ^ (n + 1)) (exp z - 1 - z) := by
  have hite : HasSum (fun n : ℕ ↦ (if n = 0 then 1 else 0 : ℂ) * z ^ (n + 1)) z := by
    convert hasSum_ite_eq 0 z using 1
    ext n
    split_ifs <;> simp_all
  convert (hasSum_exp_sub_one z).sub hite using 1
  ext n
  simp only [expRemainderCoeff, sub_mul]

end Complex
