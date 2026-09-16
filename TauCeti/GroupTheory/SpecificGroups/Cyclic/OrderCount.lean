/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Counting the elements of a cyclic group by a condition on their order

In a finite cyclic group, the number of elements whose order satisfies a predicate `p` is the sum
of `φ d` over the divisors `d` of the group order that satisfy `p`.

Mathlib counts elements of an *exact* order: `IsCyclic.card_orderOf_eq_totient` says there are
`φ d` of them for each `d` dividing the group order. Summing that over the divisors selected by
`p` is the whole content here.

The point of stating it for a predicate is that it turns a count defined by a condition on orders
into an arithmetic sum over divisors, where the group has disappeared. Whatever `p` is, the answer
is a totient sum over `{d ∣ #α | p d}`, so it can then be evaluated or estimated by number theory
alone.

## Main results

* `IsCyclic.card_filter_orderOf_eq_sum_totient`, and its additive counterpart: the count of
  elements whose order satisfies `p` is `∑ φ d` over the divisors `d` of the group order with
  `p d`.
* `IsCyclic.card_filter_dvd_orderOf_eq_sum_totient`: the case `p = (f ∣ ·)`.
-/

public section

open Finset Nat

variable {α : Type*} [Group α] [Fintype α] [IsCyclic α]

/-- **The elements of a cyclic group whose order satisfies `p`, counted by order.**
Each divisor `d` of the group order contributes its `φ d` elements of order exactly `d`, and the
condition `p (orderOf τ)` keeps precisely the divisors satisfying `p`. -/
@[to_additive
/-- **The elements of a finite additive cyclic group whose order satisfies `p`, counted by
order.** Each divisor `d` of the group order contributes its `φ d` elements of `addOrderOf`
exactly `d`, and the condition `p (addOrderOf τ)` keeps precisely the divisors satisfying
`p`. -/]
theorem IsCyclic.card_filter_orderOf_eq_sum_totient (p : ℕ → Prop) [DecidablePred p] :
    #{τ : α | p (orderOf τ)} =
      ∑ d ∈ {d ∈ (Fintype.card α).divisors | p d}, φ d := by
  classical
  calc #{τ : α | p (orderOf τ)}
      -- Every element's order divides the group order, so selecting by `p` and selecting by
      -- membership in the `p`-divisors keep the same elements.
      = #{τ ∈ (Finset.univ : Finset α) | orderOf τ ∈ {d ∈ (Fintype.card α).divisors | p d}} := by
        refine congrArg Finset.card (filter_congr fun τ _ ↦ ?_)
        simp only [mem_filter, Nat.mem_divisors]
        exact ⟨fun h ↦ ⟨⟨orderOf_dvd_card, Fintype.card_ne_zero⟩, h⟩, fun h ↦ h.2⟩
    _ = ∑ d ∈ {d ∈ (Fintype.card α).divisors | p d},
          #{τ ∈ (Finset.univ : Finset α) | orderOf τ = d} :=
        (Finset.sum_card_fiberwise_eq_card_filter _ _ _).symm
    _ = ∑ d ∈ {d ∈ (Fintype.card α).divisors | p d}, φ d := by
        refine sum_congr rfl fun d hd ↦ ?_
        rw [mem_filter, Nat.mem_divisors] at hd
        exact IsCyclic.card_orderOf_eq_totient hd.1.1

/-- **The elements of a cyclic group whose order is a multiple of `f`, counted by order.**
The divisibility case of `IsCyclic.card_filter_orderOf_eq_sum_totient`. -/
@[to_additive
/-- **The elements of a finite additive cyclic group whose order is a multiple of `f`, counted by
order.** The divisibility case of
`IsAddCyclic.card_filter_addOrderOf_eq_sum_totient`. -/]
theorem IsCyclic.card_filter_dvd_orderOf_eq_sum_totient (f : ℕ) :
    #{τ : α | f ∣ orderOf τ} =
      ∑ d ∈ {d ∈ (Fintype.card α).divisors | f ∣ d}, φ d :=
  IsCyclic.card_filter_orderOf_eq_sum_totient (f ∣ ·)
