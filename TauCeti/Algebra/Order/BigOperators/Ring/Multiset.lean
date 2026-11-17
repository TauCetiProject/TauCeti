/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Sums of squares over a multiset

This file expands `∑_{x ∈ s} (a x - b)²` (`Multiset.sum_map_mul_sub_sq`) and proves the equality
case of the inequality `(∑ s)² ≤ card s · ∑_{x ∈ s} x²` of Mathlib's
`Multiset.sq_sum_le_card_mul_sum_sq`: equality holds only when all elements of `s` are equal
(`Multiset.eq_of_sq_sum_eq_card_mul_sum_sq`).
-/

public section

namespace Multiset

section CommRing

variable {R : Type*} [CommRing R]

/-- Expanding `∑_{x ∈ s} (a x - b)²`. -/
theorem sum_map_mul_sub_sq (s : Multiset R) (a b : R) :
    (s.map fun x ↦ (a * x - b) ^ 2).sum =
      a ^ 2 * (s.map (· ^ 2)).sum - 2 * a * b * s.sum + Multiset.card s * b ^ 2 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons x s ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons, ih]
    push_cast
    ring

end CommRing

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The equality case of `Multiset.sq_sum_le_card_mul_sum_sq`: if `(∑ s)² = card s · ∑_{x ∈ s} x²`,
then all elements of `s` are equal. -/
theorem eq_of_sq_sum_eq_card_mul_sum_sq (s : Multiset K)
    (h : s.sum ^ 2 = Multiset.card s * (s.map (· ^ 2)).sum) :
    ∀ x ∈ s, ∀ y ∈ s, x = y := by
  have hsum := sum_map_mul_sub_sq s (Multiset.card s) s.sum
  have hzero : (s.map fun x ↦ ((Multiset.card s : K) * x - s.sum) ^ 2).sum = 0 := by
    rw [hsum]
    linear_combination (-(Multiset.card s : K)) * h
  have hx : ∀ x ∈ s, (Multiset.card s : K) * x = s.sum := fun x hx ↦ by
    have := Multiset.single_le_sum (fun y hy ↦ by
      obtain ⟨x, -, rfl⟩ := Multiset.mem_map.mp hy
      positivity) _ (Multiset.mem_map_of_mem (fun x ↦ ((Multiset.card s : K) * x - s.sum) ^ 2) hx)
    rw [hzero] at this
    nlinarith [sq_nonneg ((Multiset.card s : K) * x - s.sum)]
  intro x hx' y hy'
  have hn : (Multiset.card s : K) ≠ 0 := by
    exact_mod_cast (Multiset.card_pos_iff_exists_mem.mpr ⟨x, hx'⟩).ne'
  exact mul_left_cancel₀ hn ((hx x hx').trans (hx y hy').symm)

end Multiset
