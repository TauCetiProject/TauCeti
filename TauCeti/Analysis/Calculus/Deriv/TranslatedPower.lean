/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Data.Nat.Factorial.Cast

/-!
# Derivatives of a translated power at the origin

The first two derivatives of `(1 + t) ^ m` at zero are `m` and `m(m - 1)`.
-/

public section

namespace Nat

/-- The first derivative of `(1+t)^m` at the origin is `m`. -/
theorem hasDerivAt_one_add_pow_zero (m : ℕ) :
    HasDerivAt (fun t : ℝ ↦ (1 + t) ^ m) m 0 := by
  convert (((hasDerivAt_id (0 : ℝ)).const_add 1).pow m) using 1
  · funext t
    rfl
  · simp

/-- The second derivative of `(1+t)^m` at the origin is `m(m-1)`. -/
theorem deriv_deriv_one_add_pow_zero (m : ℕ) :
    deriv (deriv (fun t : ℝ ↦ (1 + t) ^ m)) 0 = (m : ℝ) * ((m : ℝ) - 1) := by
  have h : iteratedDeriv 2 (fun t : ℝ ↦ (1 + t) ^ m) =
      deriv (deriv (fun t : ℝ ↦ (1 + t) ^ m)) := by
    rw [show (2 : ℕ) = 1 + 1 by decide, iteratedDeriv_succ,
      show (1 : ℕ) = 0 + 1 by decide, iteratedDeriv_succ, iteratedDeriv_zero]
  rw [← h]
  change iteratedDeriv 2 (fun t : ℝ ↦ (fun z : ℝ ↦ z ^ m) (1 + t)) 0 = _
  rw [iteratedDeriv_comp_const_add 2 (fun z : ℝ ↦ z ^ m) 1]
  simp only [add_zero, iteratedDeriv_pow, one_pow, mul_one]
  exact Nat.cast_descFactorial_two ℝ m

end Nat
