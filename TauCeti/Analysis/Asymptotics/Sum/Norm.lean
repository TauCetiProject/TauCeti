/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
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

/-- A power-growth bound on range sums of nonnegative terms also bounds their partial sums
from one through `n`, with the same real exponent. -/
theorem isBigO_sum_Icc_of_sum_range {f : ℕ → ℝ} (hf : 0 ≤ f) {r : ℝ}
    (h : (fun n ↦ ∑ j ∈ range n, f j) =O[atTop] fun n ↦ (n : ℝ) ^ r) :
    (fun n ↦ ∑ j ∈ Icc 1 n, f j) =O[atTop] fun n ↦ (n : ℝ) ^ r := by
  have hshift : (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ) ^ r) =O[atTop]
      fun n ↦ (n : ℝ) ^ r := by
    have heq : (fun n : ℕ ↦ (n : ℝ) + 1) ~[atTop] fun n ↦ (n : ℝ) :=
      IsEquivalent.refl.add_const_of_norm_tendsto_atTop
        (tendsto_norm_atTop_atTop.comp tendsto_natCast_atTop_atTop)
    simpa only [Nat.cast_add, Nat.cast_one, Pi.pow_def] using
      (heq.rpow (fun n ↦ Nat.cast_nonneg n) (r := r)).isBigO
  refine (isBigO_of_le _ fun n ↦ ?_).trans
    ((h.comp_tendsto (tendsto_add_atTop_nat 1)).trans hshift)
  simp only [Function.comp_apply, Real.norm_of_nonneg (sum_nonneg fun j _ ↦ hf j)]
  exact sum_le_sum_of_subset_of_nonneg
    (fun j hj ↦ mem_range.mpr (by have := (mem_Icc.mp hj).2; omega))
    (fun j _ _ ↦ hf j)

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
      (sq_sum_le_card_mul_sum_sq (s := Icc 1 n) (f := fun j ↦ ‖f j‖))
  have hsqrt := hsq.sqrt (Eventually.of_forall fun n ↦ by positivity)
  refine hsqrt.congr' (Eventually.of_forall fun n ↦
    Real.sqrt_sq (sum_nonneg fun _ _ ↦ norm_nonneg _)) ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  rw [Real.sqrt_eq_rpow, mul_comm, ← Real.rpow_add_one hn'.ne',
    ← Real.rpow_mul hn'.le]
  congr 1
  ring

end TauCeti
