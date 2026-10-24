/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.Ring.Defs

/-!
# Sums of rapidly decreasing finite sequences

A nonnegative finite sequence in which every term is at most half of the previous one sums to at
most twice its first term. In Roth's lemma this bounds the sum of the weights `rᵢ` by `2 r₀`.

## Main results

* `Fin.sum_le_two_mul_of_two_mul_succ_le`: if `0 ≤ rᵢ` and `2 rᵢ₊₁ ≤ rᵢ`, then
  `∑ᵢ rᵢ ≤ 2 r₀`.
-/

public section

namespace Fin

/-- A nonnegative sequence whose terms at least halve at each step sums to at most twice its
first term. -/
theorem sum_le_two_mul_of_two_mul_succ_le {R : Type*} [Semiring R] [PartialOrder R]
    [IsOrderedRing R] {n : ℕ} {r : Fin (n + 1) → R} (hr : ∀ i, 0 ≤ r i)
    (h : ∀ i : Fin n, 2 * r i.succ ≤ r i.castSucc) : ∑ i, r i ≤ 2 * r 0 := by
  induction n with
  | zero =>
    rw [sum_univ_one, two_mul]
    exact le_add_of_nonneg_right (hr 0)
  | succ n ih =>
    have hs := ih (r := fun i ↦ r i.succ) (fun i ↦ hr _) fun i ↦ by
      rw [succ_castSucc]
      exact h i.succ
    have h0 := h 0
    rw [castSucc_zero] at h0
    rw [sum_univ_succ, two_mul]
    gcongr
    exact hs.trans h0

end Fin
