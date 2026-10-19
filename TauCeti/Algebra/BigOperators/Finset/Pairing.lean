/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Finite sums with injectively indexed partners

A source finset together with an embedding of its elements into the ambient type determines
a family of sources and partners. When partners lie outside the source finset, every pair is
counted once. A sum over this family vanishes if the two contributions in every pair sum to zero.

## Main results

* `Finset.withPartners`: the union of a source finset and its injectively indexed partners.
* `Finset.mem_withPartners`: membership as a source or a partner.
* `Finset.sum_withPartners_eq_zero`: cancellation of pairwise zero contributions.
-/

public section

namespace Finset

variable {α M : Type*} [DecidableEq α]

/-- A source finset together with its injectively indexed partners. -/
def withPartners (s : Finset α) (e : {a // a ∈ s} ↪ α) : Finset α :=
  s ∪ s.attach.map e

/-- Membership in the paired family is membership as a source or as an indexed partner. -/
@[simp]
theorem mem_withPartners (s : Finset α) (e : {a // a ∈ s} ↪ α) (a : α) :
    a ∈ s.withPartners e ↔ a ∈ s ∨ ∃ b : {b // b ∈ s}, e b = a := by
  simp only [withPartners, mem_union, mem_map, mem_attach, true_and]

/-- A sum over sources and their partners vanishes when partners lie outside the sources
and each pair contributes zero. Only an additive commutative monoid is required. -/
theorem sum_withPartners_eq_zero [AddCommMonoid M] (s : Finset α)
    (e : {a // a ∈ s} ↪ α) (f : α → M) (hdisjoint : ∀ a, e a ∉ s)
    (hzero : ∀ a, f a.val + f (e a) = 0) :
    ∑ a ∈ s.withPartners e, f a = 0 := by
  have hd : Disjoint s (s.attach.map e) := by
    rw [disjoint_right]
    intro a ha
    obtain ⟨b, _, rfl⟩ := mem_map.mp ha
    exact hdisjoint b
  rw [withPartners, sum_union hd, sum_map, ← sum_attach s f, ← sum_add_distrib]
  exact sum_eq_zero fun a _ => hzero a

end Finset
