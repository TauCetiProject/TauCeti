/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# Small complex logarithms of `1` and `-1`

The solutions of `exp ν = 1` are the points of `2π i ℤ` (`Complex.exp_eq_one_iff`), and those of
`exp ν = -1` are the points of `π i (2 ℤ + 1)`. Measuring them by their norm: the only solution of
`exp ν = 1` with `‖ν‖ < 2π` is `ν = 0`, and every solution of `exp ν = -1` has `π ≤ ‖ν‖`. These
are the bounds that keep the eigenvalues `1` and `-1` away from the exponential of a small matrix.
In the other direction, `-1` has roots `exp (t * I)` of some order `k` with `t` arbitrarily
small, namely `t = π / k`.

## Main results

* `Complex.eq_zero_of_exp_eq_one_of_norm_lt`: `exp ν = 1` and `‖ν‖ < 2π` imply `ν = 0`.
* `Complex.pi_le_norm_of_exp_eq_neg_one`: `exp ν = -1` implies `π ≤ ‖ν‖`.
* `Complex.exists_abs_lt_and_exp_mul_I_pow_eq_neg_one`: for every `ε > 0` there are `|t| < ε`
  and `k` with `exp (t * I) ^ k = -1`.
-/

public section

namespace Complex

/-- A logarithm `ν` of `1` with `‖ν‖ < 2π` is `0`, since `ν ∈ 2π i ℤ`. -/
theorem eq_zero_of_exp_eq_one_of_norm_lt {ν : ℂ} (hν : exp ν = 1)
    (hν2π : ‖ν‖ < 2 * Real.pi) : ν = 0 := by
  obtain ⟨k, rfl⟩ := exp_eq_one_iff.1 hν
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  have h1 : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast Int.one_le_abs hk
  have hnorm : ‖(k : ℂ) * (2 * Real.pi * I)‖ = |(k : ℝ)| * (2 * Real.pi) := by
    simp [abs_of_pos Real.pi_pos]
  nlinarith [Real.pi_pos]

/-- A logarithm `ν` of `-1` has `π ≤ ‖ν‖`, since `ν ∈ π i (2 ℤ + 1)`. -/
theorem pi_le_norm_of_exp_eq_neg_one {ν : ℂ} (hν : exp ν = -1) : Real.pi ≤ ‖ν‖ := by
  obtain ⟨k, hk⟩ := exp_eq_one_iff.1 (show exp (ν - Real.pi * I) = 1 by
    rw [exp_sub, hν, exp_pi_mul_I, neg_div_neg_eq, div_one])
  have hν' : ν = ((2 * k + 1 : ℤ) : ℂ) * (Real.pi * I) := by
    rw [sub_eq_iff_eq_add] at hk
    rw [hk]
    push_cast
    ring
  have h1 : (1 : ℝ) ≤ |((2 * k + 1 : ℤ) : ℝ)| := by
    exact_mod_cast Int.one_le_abs (by omega)
  have hnorm : ‖ν‖ = |((2 * k + 1 : ℤ) : ℝ)| * Real.pi := by
    rw [hν', norm_mul, norm_intCast]
    simp [abs_of_pos Real.pi_pos]
  nlinarith [Real.pi_pos]

/-- **Small roots of `-1` on the unit circle**: for every `ε > 0` there are a real `t` with
`|t| < ε` and a natural number `k` with `exp (t * I) ^ k = -1`, namely `t = π / k` for
`k > π / ε`. -/
theorem exists_abs_lt_and_exp_mul_I_pow_eq_neg_one {ε : ℝ} (hε : 0 < ε) :
    ∃ (k : ℕ) (t : ℝ), |t| < ε ∧ exp (t * I) ^ k = -1 := by
  obtain ⟨k, hk⟩ := exists_nat_gt (Real.pi / ε)
  have hk0 : (0 : ℝ) < k := (div_pos Real.pi_pos hε).trans hk
  refine ⟨k, Real.pi / k, ?_, ?_⟩
  · rw [abs_of_pos (div_pos Real.pi_pos hk0), div_lt_iff₀ hk0, mul_comm]
    exact (div_lt_iff₀ hε).1 hk
  · have h : (k : ℂ) * (↑(Real.pi / k) * I) = Real.pi * I := by
      have hk0' : (k : ℂ) ≠ 0 := by exact_mod_cast hk0.ne'
      push_cast
      field_simp
    rw [← exp_natCast_mul, h, exp_pi_mul_I]

end Complex
