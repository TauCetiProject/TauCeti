/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Multiset
public import Mathlib.Data.Multiset.Count
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Multisets of natural numbers compared through their initial counts

A multiset `s` of natural numbers is determined by its *initial counts*
`countP (· ≤ n) s`, the numbers of its elements of size at most `n`
(`Multiset.ext_countP_le`). Its sum is read off the complementary counts:
`s.sum = ∑_{k < B} countP (k < ·) s` for every bound `B` on the elements of `s`
(`Multiset.sum_eq_sum_range_countP_lt`), each element `x` being counted once for every `k < x`.

Suppose that `s` and `t` have the same cardinality and that, for every `n`, `t` has at least as many
elements of size at most `n` as `s` does. Then `t` is pointwise smaller than `s` after sorting, so
`t.sum ≤ s.sum`, and equality of the sums forces `s = t`
(`Multiset.eq_of_forall_countP_le_le_of_sum_le`).

This is the combinatorial step in comparing the degrees of homogeneous generators of two graded
polynomial algebras `A ⊆ B` of the same dimension: algebraic independence bounds the number of
generators of `A` of degree at most `n` by the corresponding number for `B`, and an independent
computation of the sums of the degrees then shows that the two multisets of degrees coincide.
-/

public section

namespace Multiset

/-- The number of elements of size at most `a` is the multiplicity of `a` plus the number of
elements smaller than `a`. -/
theorem countP_le_eq_count_add_countP_lt (s : Multiset ℕ) (a : ℕ) :
    s.countP (· ≤ a) = s.count a + s.countP (· < a) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons b s ih =>
    simp only [countP_cons, count_cons, ih]
    split_ifs <;> omega

/-- **A multiset of natural numbers is determined by its initial counts.** If, for every `n`, the
multisets `s` and `t` have the same number of elements of size at most `n`, then `s = t`. -/
theorem ext_countP_le {s t : Multiset ℕ}
    (h : ∀ n, s.countP (· ≤ n) = t.countP (· ≤ n)) : s = t := by
  have hlt : ∀ a, s.countP (· < a) = t.countP (· < a) := by
    rintro (_ | a)
    · simp
    · simpa only [Nat.lt_succ_iff] using h a
  ext a
  have := h a
  rw [countP_le_eq_count_add_countP_lt, countP_le_eq_count_add_countP_lt, hlt] at this
  omega

/-- **The sum of a multiset of natural numbers from its counts.** If every element of `s` is at
most `B`, then `s.sum` is the sum over `k < B` of the number of elements of `s` larger than `k`. -/
theorem sum_eq_sum_range_countP_lt {s : Multiset ℕ} {B : ℕ} (hs : ∀ x ∈ s, x ≤ B) :
    s.sum = ∑ k ∈ Finset.range B, s.countP (k < ·) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    have ha : a ≤ B := hs a (mem_cons_self a s)
    rw [sum_cons, ih fun x hx ↦ hs x (mem_cons_of_mem hx)]
    simp only [countP_cons, Finset.sum_add_distrib, Finset.sum_boole, Nat.cast_id]
    have : (Finset.range B).filter (· < a) = Finset.range a := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_range]
      omega
    rw [this, Finset.card_range, add_comm]

/-- **Equal sums and dominated initial counts force equality.** Let `s` and `t` be multisets of
natural numbers of the same cardinality such that, for every `n`, `t` has at least as many
elements of size at most `n` as `s`. If `s.sum ≤ t.sum`, then `s = t`. -/
theorem eq_of_forall_countP_le_le_of_sum_le {s t : Multiset ℕ} (hcard : card s = card t)
    (h : ∀ n, s.countP (· ≤ n) ≤ t.countP (· ≤ n)) (hsum : s.sum ≤ t.sum) : s = t := by
  -- The number of elements larger than `k` is the cardinality minus the initial count.
  have hcompl (u : Multiset ℕ) (k : ℕ) : u.countP (k < ·) + u.countP (· ≤ k) = card u := by
    rw [card_eq_countP_add_countP (· ≤ k) u, add_comm]
    simp only [not_le]
  set B := s.sum + t.sum
  have hsB : ∀ x ∈ s, x ≤ B := fun x hx ↦ (le_sum_of_mem hx).trans (Nat.le_add_right _ _)
  have htB : ∀ x ∈ t, x ≤ B := fun x hx ↦ (le_sum_of_mem hx).trans (Nat.le_add_left _ _)
  have hle : ∀ k ∈ Finset.range B, t.countP (k < ·) ≤ s.countP (k < ·) := fun k _ ↦ by
    have := h k
    have := hcompl s k
    have := hcompl t k
    omega
  have heq : ∀ k ∈ Finset.range B, t.countP (k < ·) = s.countP (k < ·) :=
    (Finset.sum_eq_sum_iff_of_le hle).1 <| le_antisymm (Finset.sum_le_sum hle) <| by
      rw [← sum_eq_sum_range_countP_lt hsB, ← sum_eq_sum_range_countP_lt htB]
      exact hsum
  refine ext_countP_le fun k ↦ ?_
  rcases lt_or_ge k B with hk | hk
  · have := heq k (Finset.mem_range.2 hk)
    have := hcompl s k
    have := hcompl t k
    omega
  · rw [countP_eq_card.2 fun x hx ↦ (hsB x hx).trans hk,
      countP_eq_card.2 fun x hx ↦ (htB x hx).trans hk, hcard]

end Multiset
