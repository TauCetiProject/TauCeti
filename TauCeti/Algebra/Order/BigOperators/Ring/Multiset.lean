/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.Ring.Multiset
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Tactic.Linarith

/-!
# Products of `1 - t` over a multiset of elements of `[0, 1]`

For a multiset `s` of elements of `[0, 1]` in a linearly ordered commutative ring:

* `Multiset.prod_map_one_sub_le_one`: `∏ (1 - t) ≤ 1`;
* `Multiset.one_sub_prod_map_one_sub_le_sum`: the Weierstrass product inequality
  `1 - ∏ (1 - t) ≤ ∑ t`;
* `Multiset.sum_map_sq_le_card_mul_one_sub_prod_map_one_sub`:
  `∑ t² ≤ card s · (1 - ∏ (1 - t))`.

Nonnegativity of `∏ (1 - t)` is `Multiset.prod_map_nonneg`.
-/

public section

namespace Multiset

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] {s : Multiset R}

/-- For `t ∈ [0, 1]`, the product `∏ (1 - t)` is at most `1`. -/
theorem prod_map_one_sub_le_one (h₀ : ∀ t ∈ s, 0 ≤ t) (h₁ : ∀ t ∈ s, t ≤ 1) :
    (s.map fun t ↦ 1 - t).prod ≤ 1 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons t₀ s ih =>
    rw [map_cons, prod_cons]
    have h₀' : ∀ t ∈ s, 0 ≤ t := fun t ht ↦ h₀ t (mem_cons_of_mem ht)
    have h₁' : ∀ t ∈ s, t ≤ 1 := fun t ht ↦ h₁ t (mem_cons_of_mem ht)
    have hP₀ := prod_map_nonneg (f := fun t ↦ 1 - t) fun t ht ↦ sub_nonneg.2 (h₁' t ht)
    nlinarith [h₀ t₀ (mem_cons_self _ _), ih h₀' h₁']

/-- **Weierstrass product inequality.** For `t ∈ [0, 1]`, `1 - ∏ (1 - t) ≤ ∑ t`. -/
theorem one_sub_prod_map_one_sub_le_sum (h₀ : ∀ t ∈ s, 0 ≤ t) (h₁ : ∀ t ∈ s, t ≤ 1) :
    1 - (s.map fun t ↦ 1 - t).prod ≤ s.sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons t₀ s ih =>
    have h₀' : ∀ t ∈ s, 0 ≤ t := fun t ht ↦ h₀ t (mem_cons_of_mem ht)
    have h₁' : ∀ t ∈ s, t ≤ 1 := fun t ht ↦ h₁ t (mem_cons_of_mem ht)
    have hP₁ := prod_map_one_sub_le_one h₀' h₁'
    rw [map_cons, prod_cons, sum_cons]
    nlinarith [ih h₀' h₁', mul_le_of_le_one_right (h₀ t₀ (mem_cons_self _ _)) hP₁]

/-- For `t ∈ [0, 1]`, `∑ t² ≤ card s · (1 - ∏ (1 - t))`. -/
theorem sum_map_sq_le_card_mul_one_sub_prod_map_one_sub (h₀ : ∀ t ∈ s, 0 ≤ t)
    (h₁ : ∀ t ∈ s, t ≤ 1) :
    (s.map fun t ↦ t ^ 2).sum ≤ (card s : R) * (1 - (s.map fun t ↦ 1 - t).prod) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons t₀ s ih =>
    have h₀' : ∀ t ∈ s, 0 ≤ t := fun t ht ↦ h₀ t (mem_cons_of_mem ht)
    have h₁' : ∀ t ∈ s, t ≤ 1 := fun t ht ↦ h₁ t (mem_cons_of_mem ht)
    have ht₀ := h₀ t₀ (mem_cons_self _ _)
    have ht₁ := h₁ t₀ (mem_cons_self _ _)
    have hP₀ := prod_map_nonneg (f := fun t ↦ 1 - t) fun t ht ↦ sub_nonneg.2 (h₁' t ht)
    have hP₁ := prod_map_one_sub_le_one h₀' h₁'
    have hk : (0 : R) ≤ card s := Nat.cast_nonneg _
    simp only [map_cons, prod_cons, sum_cons, card_cons, Nat.cast_succ]
    nlinarith [ih h₀' h₁', mul_nonneg (sub_nonneg.2 hP₁) (sub_nonneg.2 ht₁),
      mul_nonneg hk (mul_nonneg ht₀ hP₀), mul_le_of_le_one_left ht₀ ht₁]

end Multiset
