/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Algebra.BigOperators.Module

/-!
# Norm bounds by summation by parts

`Finset.norm_sum_range_smul_le_of_antitoneOn` uses Mathlib's `Finset.sum_range_by_parts` to
bound a weighted sum by its first weight times a bound on the unweighted partial sums.
-/

public section

namespace Finset

/-- Abel's inequality for finite sums in a real seminormed space. If the weights on
`range N` decrease and are nonnegative, the norm of the weighted sum is at most the first
weight times a uniform bound on the norms of the unweighted partial sums up to `N`. -/
theorem norm_sum_range_smul_le_of_antitoneOn {E : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℝ E] {a : ℕ → E} {w : ℕ → ℝ} {B : ℝ} {N : ℕ}
    (hw : AntitoneOn w (Set.Iio N)) (hw₀ : 0 ≤ w (N - 1))
    (ha : ∀ n ≤ N, ‖∑ i ∈ range n, a i‖ ≤ B) :
    ‖∑ i ∈ range N, w i • a i‖ ≤ w 0 * B := by
  cases N with
  | zero =>
    simpa using mul_nonneg hw₀ ((norm_nonneg _).trans (ha 0 le_rfl))
  | succ N =>
    simp only [Nat.add_sub_cancel] at hw₀
    have hdiff (i : ℕ) (hi : i < N) : w (i + 1) ≤ w i :=
      hw (Set.mem_Iio.mpr (Nat.lt_succ_of_lt hi))
        (Set.mem_Iio.mpr (Nat.succ_lt_succ hi)) (Nat.le_succ i)
    have hvar :
        ‖∑ i ∈ range N, (w (i + 1) - w i) • ∑ j ∈ range (i + 1), a j‖ ≤
          (w 0 - w N) * B := by
      calc
        _ ≤ ∑ i ∈ range N, (w i - w (i + 1)) * B := by
          refine (norm_sum_le _ _).trans (sum_le_sum fun i hi ↦ ?_)
          have hi' := mem_range.mp hi
          have hstep := hdiff i hi'
          rw [norm_smul, Real.norm_of_nonpos (sub_nonpos.mpr hstep), neg_sub]
          exact mul_le_mul_of_nonneg_left (ha _ (Nat.succ_le_succ hi'.le)) (sub_nonneg.mpr hstep)
        _ = _ := by rw [← sum_mul, sum_range_sub']
    rw [sum_range_by_parts, Nat.add_sub_cancel]
    calc
      _ ≤ w N * B + (w 0 - w N) * B := by
        refine norm_sub_le_of_le ?_ hvar
        rw [norm_smul, Real.norm_of_nonneg hw₀]
        exact mul_le_mul_of_nonneg_left (ha _ le_rfl) hw₀
      _ = _ := by rw [← add_mul, add_sub_cancel]

end Finset
