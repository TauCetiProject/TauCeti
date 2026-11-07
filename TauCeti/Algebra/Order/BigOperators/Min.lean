/-
Copyright (c) 2026 Ralf Stephan and The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan, The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Order.Monotone.Basic
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.SplitIfs

/-!
# Product bounds for minima of finite sequences

For a positive increasing sequence, a product of pairwise minima is bounded by the product
of the first entries. If all first indices lie above a cut and some second index lies below
it, the bound gains the ratio across the cut. This retains a jump between consecutive minima
when estimating permutation products in exterior-power determinants.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry* (2006), §7.5.30.
* Adapted from Ralf Stephan's `DiophantineApproximation/WedgeDomain.lean` in
  `rwst/Subspace-Theorems`, commit `09835cb23557ae5ae0cf55a9c4ab9055f5d60338` (Apache 2.0).
-/

public section

open Finset

namespace TauCeti

/-- A product of pairwise minima gains the ratio across the first `k` indices when every
first index is above the cut and some second index is below it. The proposition `P` controls
whether the stronger bound is used. -/
theorem prod_min_le_jump_mul_prod {N k p : ℕ} {μ : ℕ → ℝ}
    (hμm : MonotoneOn μ (Set.Iio N)) (hμp : ∀ j < N, 0 < μ j)
    {i j : Fin p → ℕ} (hi : ∀ b, i b < N) (hj : ∀ b, j b < N)
    (hk : ∃ b, j b < k) (P : Prop) [Decidable P] (hP : P → ∀ b, k ≤ i b) :
    ∏ b, min (μ (i b)) (μ (j b)) ≤
      (if P then μ (k - 1) / μ k else 1) * ∏ b, μ (i b) := by
  have hm0 (b) : 0 ≤ min (μ (i b)) (μ (j b)) :=
    le_min (hμp _ (hi b)).le (hμp _ (hj b)).le
  split_ifs with hPt
  · obtain ⟨b₀, hb₀⟩ := hk
    have hkN : k < N := (hP hPt b₀).trans_lt (hi b₀)
    have hk0 : 0 < μ k := hμp k hkN
    have hr : 0 ≤ μ (k - 1) / μ k := div_nonneg (hμp _ (by omega)).le hk0.le
    rw [← mul_prod_erase _ _ (mem_univ b₀),
      ← mul_prod_erase _ (fun b ↦ μ (i b)) (mem_univ b₀), ← mul_assoc]
    refine mul_le_mul ?_ (prod_le_prod₀ (fun b _ ↦ hm0 b) fun b _ ↦ min_le_left _ _)
      (prod_nonneg fun b _ ↦ hm0 b) (mul_nonneg hr (hμp _ (hi b₀)).le)
    calc
      min (μ (i b₀)) (μ (j b₀)) ≤ μ (j b₀) := min_le_right _ _
      _ ≤ μ (k - 1) := hμm (hj b₀) (by simp only [Set.mem_Iio]; omega) (by omega)
      _ = μ (k - 1) / μ k * μ k := (div_mul_cancel₀ _ hk0.ne').symm
      _ ≤ μ (k - 1) / μ k * μ (i b₀) :=
        mul_le_mul_of_nonneg_left (hμm hkN (hi b₀) (hP hPt b₀)) hr
  · rw [one_mul]
    exact prod_le_prod₀ (fun b _ ↦ hm0 b) fun b _ ↦ min_le_left _ _

end TauCeti
