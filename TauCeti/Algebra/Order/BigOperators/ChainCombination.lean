/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Basic.Real.Basic

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import TauCeti.Algebra.BigOperators.Finset.Erase
import TauCeti.Algebra.Order.BigOperators.Sum.Erase
import TauCeti.Algebra.Order.BigOperators.Sum.NatSub
import TauCeti.Order.Chain

/-!
# Combinations of chains of counting vectors

Let the vectors `C a`, for `a` in a finite set `A`, of natural numbers be distinct and pairwise
comparable, with each coordinate differing by at most one between any two of them. A combination
of them with real coefficients `v` summing to zero then has `ℓ¹` norm at least half the `ℓ¹` norm
of `v`. This is the counting estimate behind the uniform fatness of edgewise subdivisions.

## Main results

* `TauCeti.sum_abs_le_two_mul_sum_abs_sum_mul`: `∑ a, |v a| ≤ 2 * ∑ i, |∑ a, v a * C a i|`.
-/

public section

open Finset

namespace TauCeti

/-- Coordinatewise, the vector of the maximum `t` exceeds that of the second largest `t'` by `0`
or `1`. -/
private theorem eq_or_eq_add_one_of_comparable {α β : Type*} {C : α → β → ℕ} {t t' : α}
    (hle : C t' ≤ C t) (hc : (C t ≤ C t' ∧ C t' ≤ C t + 1) ∨ (C t' ≤ C t ∧ C t ≤ C t' + 1))
    (i : β) : C t i = C t' i ∨ C t i = C t' i + 1 := by
  have h₁ : C t' i ≤ C t i := hle i
  rcases hc with h | h
  · have h₂ : C t i ≤ C t' i := h.1 i
    omega
  · have h₂ : C t i ≤ C t' i + 1 := h.2 i
    omega

/-- Where the maximum `t` exceeds the second largest `t'`, all other vectors agree with `t'`. -/
private theorem forall_erase_eq_of_lt {α β : Type*} [DecidableEq α] {C : α → β → ℕ}
    {A : Finset α} {t t' : α}
    (hC : ∀ a ∈ A, ∀ b ∈ A, (C a ≤ C b ∧ C b ≤ C a + 1) ∨ (C b ≤ C a ∧ C a ≤ C b + 1))
    (htA : t ∈ A) (ht' : ∀ a ∈ A.erase t, C a ≤ C t') {i : β} (h : C t i = C t' i + 1) :
    ∀ a ∈ A.erase t, C a i = C t' i := by
  intro a ha
  refine le_antisymm (ht' a ha i) ?_
  rcases hC a (mem_of_mem_erase ha) t htA with h' | h'
  · have h₂ : C t i ≤ C a i + 1 := h'.2 i
    omega
  · have h₂ : C t i ≤ C a i := h'.1 i
    omega

/-- Removing the maximum `t` and merging its coefficient into that of `t'` decreases the absolute
value of the `i`-th coordinate of the combination by `|v t|` times the gap between the `i`-th
coordinates of `t` and `t'`. -/
private theorem abs_sum_mul_eq {α β : Type*} [DecidableEq α] {C : α → β → ℕ} {A : Finset α}
    {t t' : α}
    (hC : ∀ a ∈ A, ∀ b ∈ A, (C a ≤ C b ∧ C b ≤ C a + 1) ∨ (C b ≤ C a ∧ C a ≤ C b + 1))
    (htA : t ∈ A) (ht'A' : t' ∈ A.erase t) (ht : ∀ a ∈ A, C a ≤ C t)
    (ht' : ∀ a ∈ A.erase t, C a ≤ C t') {v : α → ℝ} (hv : ∑ a ∈ A, v a = 0) (i : β) :
    |∑ a ∈ A, v a * C a i| =
      |∑ a ∈ A.erase t, (v a + if a = t' then v t else 0) * C a i| +
        |v t| * ((C t i : ℝ) - C t' i) := by
  have ht'A : t' ∈ A := mem_of_mem_erase ht'A'
  rw [sum_erase_merge_mul ht'A' v fun a => (C a i : ℝ), ← add_sum_erase A _ htA]
  rcases eq_or_eq_add_one_of_comparable (ht t' ht'A) (hC t htA t' ht'A) i with h | h
  · rw [h, sub_self, mul_zero, add_zero, add_comm]
  · have hagree := forall_erase_eq_of_lt hC htA ht' h
    have hrest : ∑ a ∈ A.erase t, v a * C a i + v t * C t' i = 0 := by
      rw [← sum_erase_merge_mul ht'A' v fun a => (C a i : ℝ),
        sum_congr rfl fun a ha => by rw [hagree a ha], ← Finset.sum_mul,
        (sum_erase_merge ht'A' htA v).trans hv, zero_mul]
    rw [h, Nat.cast_add, Nat.cast_one, add_sub_cancel_left, mul_one, hrest, abs_zero, zero_add]
    congr 1
    linarith

/-- Let the vectors `C a`, for `a ∈ A`, of natural numbers be distinct and pairwise comparable,
with each coordinate differing by at most one between any two of them. Then a combination of them
with coefficients `v` summing to zero satisfies `∑ a, |v a| ≤ 2 * ∑ i, |∑ a, v a * C a i|`. -/
theorem sum_abs_le_two_mul_sum_abs_sum_mul {α β : Type*} [Fintype β]
    (C : α → β → ℕ) (A : Finset α)
    (hC : ∀ a ∈ A, ∀ b ∈ A, (C a ≤ C b ∧ C b ≤ C a + 1) ∨ (C b ≤ C a ∧ C a ≤ C b + 1))
    (hinj : ∀ a ∈ A, ∀ b ∈ A, C a = C b → a = b) (v : α → ℝ) (hv : ∑ a ∈ A, v a = 0) :
    ∑ a ∈ A, |v a| ≤ 2 * ∑ i, |∑ a ∈ A, v a * C a i| := by
  classical
  -- Remove the largest vector `t`. Where it exceeds the second largest `t'`, all the other
  -- vectors agree with `t'`, so there the combination only sees the coefficient of `t`. Merge
  -- that coefficient into the one of `t'` and induct.
  induction A using Finset.strongInduction generalizing v with
  | H A ih =>
  rcases A.eq_empty_or_nonempty with rfl | hne
  · simp
  -- Every nonempty part of `A` has a vector dominating all the others in it.
  have hmax : ∀ B ⊆ A, B.Nonempty → ∃ t ∈ B, ∀ a ∈ B, C a ≤ C t := fun B hBA hB =>
    Finset.exists_forall_le_of_forall_comparable C
      (fun a ha b hb => (hC a (hBA ha) b (hBA hb)).imp And.left And.left) hB
  obtain ⟨t, htA, ht⟩ := hmax A subset_rfl hne
  rcases (A.erase t).eq_empty_or_nonempty with hA' | hA'
  · -- Then `A = {t}`, and `v t = 0`.
    obtain rfl : A = {t} := (erase_eq_empty_iff A t).mp hA' |>.resolve_left hne.ne_empty
    simp only [sum_singleton] at hv
    simp [hv]
  obtain ⟨t', ht'A', ht'⟩ := hmax (A.erase t) (erase_subset t A) hA'
  -- Merge the coefficient of `t` into that of `t'`, and apply the induction hypothesis.
  have hIH := ih (A.erase t) (erase_ssubset htA)
    (fun a ha b hb => hC a (mem_of_mem_erase ha) b (mem_of_mem_erase hb))
    (fun a ha b hb => hinj a (mem_of_mem_erase ha) b (mem_of_mem_erase hb))
    (fun a => v a + if a = t' then v t else 0) ((sum_erase_merge ht'A' htA v).trans hv)
  -- The vectors of `t` and `t'` differ somewhere, so `t` exceeds `t'` by at least `1` in total.
  have hgap := Finset.one_le_sum_sub_of_lt (R := ℝ) <|
    lt_of_le_of_ne (ht t' (mem_of_mem_erase ht'A'))
    fun h => (ne_of_mem_erase ht'A') (hinj t' (mem_of_mem_erase ht'A') t htA h)
  -- Removing `t` costs `|v t|` once on the left and at least `|v t|` on the right.
  have hright : ∑ i, |∑ a ∈ A, v a * C a i| =
      ∑ i, |∑ a ∈ A.erase t, (v a + if a = t' then v t else 0) * C a i| +
        |v t| * ∑ i, ((C t i : ℝ) - C t' i) := by
    simp only [abs_sum_mul_eq hC htA ht'A' ht ht' hv, Finset.sum_add_distrib, Finset.mul_sum]
  have hleft := sum_abs_erase_le ht'A' v
  rw [← add_sum_erase A _ htA, hright]
  nlinarith [abs_nonneg (v t)]

end TauCeti
