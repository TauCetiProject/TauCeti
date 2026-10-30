/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.FieldSimp

/-!
# Sums of inverse factorials

The alternating convolution of inverse factorials is zero in every positive degree and one in
degree zero, by the binomial theorem. This is the coefficient identity expressing that the
formal exponential series of `-X` and `X` are inverses.
-/

public section

open Finset

namespace Nat

/-- The coefficients of the product of the exponential series of `-X` and of `X`: the coefficient
of `Xⁿ` is `(1 - 1)ⁿ / n!`. -/
theorem sum_antidiagonal_neg_one_pow_mul_inv_factorial (n : ℕ) :
    ∑ p ∈ antidiagonal n, (-1 : ℚ) ^ p.1 * ((p.1.factorial : ℚ)⁻¹ * (p.2.factorial : ℚ)⁻¹) =
      if n = 0 then 1 else 0 := by
  have hterm : ∀ m ∈ range (n + 1), (-1 : ℚ) ^ m * ((m.factorial : ℚ)⁻¹ *
      ((n - m).factorial : ℚ)⁻¹) = (n.factorial : ℚ)⁻¹ * ((-1) ^ m * 1 ^ (n - m) * n.choose m) := by
    intro m hm
    have hmn : m ≤ n := Nat.lt_succ_iff.1 (mem_range.1 hm)
    have hfac : (n.choose m : ℚ) * m.factorial * (n - m).factorial = n.factorial := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial hmn
    have hc : (n.choose m : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hmn).ne'
    rw [one_pow, mul_one, ← hfac]
    field_simp
  rw [Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j ↦ (-1 : ℚ) ^ i * ((i.factorial : ℚ)⁻¹ * (j.factorial : ℚ)⁻¹)) n,
    sum_congr rfl hterm, ← mul_sum, ← add_pow, neg_add_cancel]
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · simp [hn]

end Nat
