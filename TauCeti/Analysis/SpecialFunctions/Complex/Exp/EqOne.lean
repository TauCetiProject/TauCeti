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

## Main results

* `Complex.eq_zero_of_exp_eq_one_of_norm_lt`: `exp ν = 1` and `‖ν‖ < 2π` imply `ν = 0`.
* `Complex.pi_le_norm_of_exp_eq_neg_one`: `exp ν = -1` implies `π ≤ ‖ν‖`.
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

end Complex
