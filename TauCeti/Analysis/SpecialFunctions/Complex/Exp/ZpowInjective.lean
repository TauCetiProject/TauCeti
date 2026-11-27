/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.Real.Pi.Irrational

/-!
# The integer powers of `e^{i}` are pairwise distinct

An equality `e^{i m} = e^{i n}` of integer powers of `e^{i}` says that `m - n` is an integer
multiple of `2π`. Since `π` is irrational, this forces `m = n`
(`Complex.exp_I_zpow_injective`). So `e^{i}` is not a root of unity, and it separates any family
of characters `z ↦ z ^ n`, `n ∈ ℤ`, of the circle at once.

## Main results

* `Complex.exp_I_zpow_injective`: the integer powers of `e^{i}` are pairwise distinct.
-/

public section

namespace Complex

/-- **The integer powers of `e^{i}` are pairwise distinct**, since `π` is irrational. -/
theorem exp_I_zpow_injective : Function.Injective fun n : ℤ ↦ exp I ^ n := by
  intro m n h
  simp only [← exp_intCast_mul] at h
  obtain ⟨k, hk⟩ := exp_eq_exp_iff_exists_int.1 h
  have hre : (m : ℝ) = n + k * (2 * Real.pi) := by simpa using congrArg im hk
  rcases eq_or_ne k 0 with rfl | hk0
  · exact_mod_cast (by simpa using hre : (m : ℝ) = n)
  · refine (irrational_pi ⟨(m - n) / (2 * k), ?_⟩).elim
    have : (k : ℝ) ≠ 0 := by exact_mod_cast hk0
    push_cast
    field_simp
    linarith

end Complex
