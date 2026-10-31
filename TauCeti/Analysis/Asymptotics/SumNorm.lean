/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Order.Interval.Finset.Nat

/-!
# Partial sums of norms from mean-square bounds

Cauchy–Schwarz turns a bound `∑_{j=1}^n ‖f j‖² = O(n^r)` into
`∑_{j=1}^n ‖f j‖ = O(n^((r+1)/2))`. This is the partial-sum estimate used to obtain
absolute convergence of Dirichlet series from mean-square bounds on their coefficients.
The coefficient space can be any seminormed additive group, and the exponent can be any real
number.
-/

public section

open Asymptotics Filter Finset

namespace TauCeti

/-- A mean-square bound with exponent `r` gives a bound with exponent `(r+1)/2` for the
partial sums of norms. -/
theorem isBigO_sum_norm_Icc_of_sum_norm_sq {E : Type*} [SeminormedAddCommGroup E]
    {f : ℕ → E} {r : ℝ}
    (h : (fun n ↦ ∑ j ∈ Icc 1 n, ‖f j‖ ^ 2) =O[atTop] fun n ↦ (n : ℝ) ^ r) :
    (fun n ↦ ∑ j ∈ Icc 1 n, ‖f j‖) =O[atTop] fun n ↦ (n : ℝ) ^ ((r + 1) / 2) := by
  have hsq : (fun n ↦ (∑ j ∈ Icc 1 n, ‖f j‖) ^ 2) =O[atTop]
      fun n ↦ (n : ℝ) * (n : ℝ) ^ r := by
    refine (isBigO_of_le _ fun n ↦ ?_).trans ((isBigO_refl (fun n : ℕ ↦ (n : ℝ)) atTop).mul h)
    have hsum : 0 ≤ ∑ j ∈ Icc 1 n, ‖f j‖ ^ 2 := sum_nonneg fun _ _ ↦ sq_nonneg _
    simpa [abs_of_nonneg hsum, mul_comm] using
      (sum_mul_sq_le_sq_mul_sq (Icc 1 n) (fun _ ↦ (1 : ℝ)) (fun j ↦ ‖f j‖))
  have hsqrt := hsq.sqrt (Eventually.of_forall fun n ↦ by positivity)
  refine hsqrt.congr' (Eventually.of_forall fun n ↦
    Real.sqrt_sq (sum_nonneg fun _ _ ↦ norm_nonneg _)) ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  rw [Real.sqrt_eq_rpow]
  nth_rw 1 [← Real.rpow_one (n : ℝ)]
  rw [← Real.rpow_add hn', ← Real.rpow_mul hn'.le]
  congr 1
  ring

end TauCeti
