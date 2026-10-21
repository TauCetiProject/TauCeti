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

Partners may also be specified by a relation between two finsets rather than by an embedding.
If every source has a related partner with the same contribution, distinct sources never share
a partner, each source has at most one partner, and every partner is related to some source,
then the two finsets have the same product.

## Main results

* `Finset.withPartners`: the union of a source finset and its injectively indexed partners.
* `Finset.mem_withPartners`: membership as a source or a partner.
* `Finset.sum_withPartners_eq_zero`: cancellation of pairwise zero contributions.
* `Finset.prod_bij_of_rel`, `Finset.sum_bij_of_rel`: equality of products or sums over two
  finsets matched one-to-one by a relation.
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

omit [DecidableEq α] in
/-- A relational form of `Finset.prod_bij`: two finsets have equal products when a relation
`r` matches each element of `s` with exactly one element of `t` carrying the same factor,
distinct elements of `s` are never matched with the same element of `t`, and every element
of `t` is matched. -/
@[to_additive /-- A relational form of `Finset.sum_bij`: two finsets have equal sums when a
relation `r` matches each element of `s` with exactly one element of `t` carrying the same term,
distinct elements of `s` are never matched with the same element of `t`, and every element
of `t` is matched. -/]
theorem prod_bij_of_rel {κ : Type*} [CommMonoid M] {s : Finset α} {t : Finset κ}
    {f : α → M} {g : κ → M} (r : α → κ → Prop)
    (hex : ∀ a ∈ s, ∃ b ∈ t, r a b ∧ f a = g b)
    (hleft : ∀ a ∈ s, ∀ a' ∈ s, ∀ b ∈ t, r a b → r a' b → a = a')
    (hright : ∀ a ∈ s, ∀ b ∈ t, ∀ b' ∈ t, r a b → r a b' → b = b')
    (hsurj : ∀ b ∈ t, ∃ a ∈ s, r a b) :
    ∏ a ∈ s, f a = ∏ b ∈ t, g b := by
  refine prod_bij (fun a ha => (hex a ha).choose) (fun a ha => (hex a ha).choose_spec.1)
    (fun a ha a' ha' h => ?_) (fun b hb => ?_) (fun a ha => (hex a ha).choose_spec.2.2)
  · exact hleft a ha a' ha' _ (hex a ha).choose_spec.1 (hex a ha).choose_spec.2.1
      (h ▸ (hex a' ha').choose_spec.2.1)
  · obtain ⟨a, ha, hab⟩ := hsurj b hb
    exact ⟨a, ha, hright a ha _ (hex a ha).choose_spec.1 b hb (hex a ha).choose_spec.2.1 hab⟩

end Finset
