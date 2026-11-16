/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Normed.Module.Basic

import Mathlib.Algebra.Order.Floor.Semiring
import TauCeti.Algebra.BigOperators.Finset.Periodic

/-!
# Norm bounds and zero-mean criterion for periodic partial sums

For a sequence `a : ℕ → M` that is `N`-periodic on positive indices (`a (k + N) = a k` for all
`1 ≤ k`), vanishing of the period sum `∑ j ∈ Icc 1 N, a j` makes the partial sums
`m ↦ ∑ j ∈ Icc 1 m, a j` periodic on all of `ℕ` (`Finset.periodic_sum_Icc_of_sum_eq_zero`), hence
uniformly bounded in norm by `∑ j ∈ Icc 1 N, ‖a j‖` whenever `N ≠ 0`. Conversely, in any normed
vector space over `ℝ`, if `a` is `N`-periodic on `k ≥ 1` and its partial sums are `O(1)`, then the
full-period sums `m • ∑ j ∈ Icc 1 N, a j` remain bounded as `m → ∞`, forcing the period sum to
vanish.

## Main results

* `Finset.norm_sum_Icc_le_of_sum_eq_zero`: if `N ≠ 0`, `a (k + N) = a k` for `k ≥ 1`, and
  `∑ j ∈ Icc 1 N, a j = 0`, then `‖∑ j ∈ Icc 1 m, a j‖ ≤ ∑ j ∈ Icc 1 N, ‖a j‖` for all `m : ℕ`.
* `TauCeti.sum_Icc_eq_zero_of_periodic_of_isBigO_one`: conversely, if `a : ℕ → E` in a real normed
  space is `N`-periodic on `k ≥ 1` and `m ↦ ∑ k ∈ Icc 1 m, a k` is `O(1)`, then
  `∑ k ∈ Icc 1 N, a k = 0`.
-/

public section

namespace Finset

/-- **Uniform partial-sum bound for a zero-mean periodic sequence.** If `N ≠ 0`, `a (k + N) = a k`
for all `1 ≤ k`, and `∑ j ∈ Icc 1 N, a j = 0`, every partial sum `∑ j ∈ Icc 1 m, a j` has norm at
most `∑ j ∈ Icc 1 N, ‖a j‖`. -/
theorem norm_sum_Icc_le_of_sum_eq_zero {M : Type*} [SeminormedAddCommGroup M] {a : ℕ → M} {N : ℕ}
    (hN : N ≠ 0) (hper : ∀ k, 1 ≤ k → a (k + N) = a k)
    (hsum : ∑ j ∈ Icc 1 N, a j = 0) (m : ℕ) :
    ‖∑ j ∈ Icc 1 m, a j‖ ≤ ∑ j ∈ Icc 1 N, ‖a j‖ := by
  rw [sum_Icc_eq_sum_Icc_mod_of_sum_eq_zero hper hsum m]
  have hlt : m % N ≤ N := (Nat.mod_lt m (Nat.pos_of_ne_zero hN)).le
  exact (norm_sum_le _ _).trans
    (sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right hlt) fun _ _ _ ↦ norm_nonneg _)

end Finset

namespace TauCeti

open Asymptotics Filter

/-- **Bounded partial sums of a periodic sequence force vanishing period sum.** If `a : ℕ → E` in a
real normed space satisfies `a (k + N) = a k` for all `k ≥ 1` and its partial sums are `O(1)`, then
`∑ k ∈ Icc 1 N, a k = 0`. -/
theorem sum_Icc_eq_zero_of_periodic_of_isBigO_one {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {a : ℕ → E} {N : ℕ} (hper : ∀ k, 1 ≤ k → a (k + N) = a k)
    (hbdd : (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, a k) =O[atTop] (1 : ℕ → ℝ)) :
    ∑ k ∈ Finset.Icc 1 N, a k = 0 := by
  rcases eq_or_ne N 0 with rfl | hN
  · simp
  · by_contra hS
    have hSpos : 0 < ‖∑ k ∈ Finset.Icc 1 N, a k‖ := norm_pos_iff.mpr hS
    obtain ⟨c, hc⟩ := hbdd.bound
    obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp hc
    let m : ℕ := max n₀ (⌊max c 0 / ‖∑ k ∈ Finset.Icc 1 N, a k‖⌋₊ + 1)
    have hmN : n₀ ≤ m * N :=
      (le_max_left _ _).trans (Nat.le_mul_of_pos_right m (Nat.pos_of_ne_zero hN))
    have hle := hn₀ (m * N) hmN
    rw [Finset.sum_Icc_mul_eq_nsmul_of_periodic hper m, ← Nat.cast_smul_eq_nsmul ℝ, norm_smul,
      Real.norm_natCast, Pi.one_apply, norm_one, mul_one] at hle
    have hlt : max c 0 < (m : ℝ) * ‖∑ k ∈ Finset.Icc 1 N, a k‖ :=
      (div_lt_iff₀ hSpos).mp
        ((Nat.lt_floor_add_one _).trans_le (by exact_mod_cast le_max_right n₀ _))
    linarith [le_max_left c 0]

end TauCeti
