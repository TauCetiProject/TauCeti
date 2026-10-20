/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Positive weights taming a double sequence geometrically

Given nonnegative numbers `a m k`, there are positive weights `η n` with
`a m k * η (m + k) ≤ (1 / 2) ^ k` for all `m` and `k`: the weight at level `n` only has to beat
the finitely many `a m (n - m)` with `m ≤ n`. In a gliding-hump argument `a m k` bounds how much
the `k`-th hump after level `m` can grow, and the weights are admissible sizes for the humps.

## Main declarations

* `TauCeti.exists_pos_mul_le_half_pow`: the weights exist.
-/

public section

namespace TauCeti

/-- Given nonnegative numbers `a m k`, there are positive weights `η n` such that
`a m k * η (m + k) ≤ (1 / 2) ^ k` for all `m` and `k`. -/
theorem exists_pos_mul_le_half_pow (a : ℕ → ℕ → ℝ) (ha : ∀ m k, 0 ≤ a m k) :
    ∃ η : ℕ → ℝ, (∀ n, 0 < η n) ∧ ∀ m k, a m k * η (m + k) ≤ (1 / 2) ^ k := by
  set D : ℕ → ℝ := fun n ↦ 1 + ∑ m ∈ Finset.range (n + 1), a m (n - m)
  have hD : ∀ n, 0 < D n := fun n ↦
    add_pos_of_pos_of_nonneg one_pos (Finset.sum_nonneg fun m _ ↦ ha m _)
  refine ⟨fun n ↦ (1 / 2) ^ n / D n, fun n ↦ div_pos (by positivity) (hD n), fun m k ↦ ?_⟩
  have hle : a m k ≤ D (m + k) := by
    have := Finset.single_le_sum (f := fun i ↦ a i (m + k - i)) (fun i _ ↦ ha i _)
      (Finset.mem_range.2 (by omega : m < m + k + 1))
    simp only [Nat.add_sub_cancel_left] at this
    linarith
  calc a m k * ((1 / 2) ^ (m + k) / D (m + k))
      = (1 / 2) ^ (m + k) * (a m k / D (m + k)) := by ring
    _ ≤ (1 / 2) ^ (m + k) * 1 := by
        gcongr
        exact div_le_one_of_le₀ hle (hD _).le
    _ ≤ (1 / 2) ^ k := by
        rw [mul_one, pow_add]
        exact mul_le_of_le_one_left (by positivity) (pow_le_one₀ (by norm_num) (by norm_num))

end TauCeti
