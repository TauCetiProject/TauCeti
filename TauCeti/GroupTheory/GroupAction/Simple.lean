/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.Primitive
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.Subgroup.Simple

/-!
# Simplicity from primitive actions

Suppose a nontrivial group acts faithfully and primitively on a nonempty set whose
cardinality is divisible by a prime `p`, with `p²` not dividing the group order.
If an element whose `p`th power is one normally generates the group, then the group
is simple. A faithful transitive action of prime degree is a special case.

A nontrivial normal subgroup must act transitively, so its order is divisible by `p`.
Its index is therefore coprime to `p`, forcing the chosen element into that subgroup.
Normal generation then forces the subgroup to be the whole group.

This criterion supports the presented-group simplicity work in CFSG basic properties P0.
-/

public section

namespace TauCeti

open MulAction

/-- In a faithful primitive action, a prime divisor of the degree that occurs only once
in the group order forces simplicity when an element of that prime order normally generates. -/
theorem isSimpleGroup_of_prime_divisor_degree_action
    {G X : Type*} [Group G] [Nontrivial G] [Nonempty X]
    [MulAction G X] [FaithfulSMul G X] [IsPreprimitive G X]
    {p : ℕ} (hp : p.Prime) (hdegree : p ∣ Nat.card X) (hcard : ¬ p ^ 2 ∣ Nat.card G)
    (a : G) (ha : a ^ p = 1)
    (hgen : Subgroup.normalClosure ({a} : Set G) = ⊤) : IsSimpleGroup G := by
  refine ⟨fun N _ ↦ ?_⟩
  by_cases hN : N = ⊥
  · exact Or.inl hN
  right
  have hfixed : fixedPoints N X ≠ Set.univ := by
    intro h
    apply hN
    apply bot_unique
    intro n hn
    change n = 1
    apply FaithfulSMul.eq_of_smul_eq_smul (α := X)
    intro x
    have hx : x ∈ fixedPoints N X := by rw [h]; trivial
    simpa only [one_smul, subgroup_smul_def] using (mem_fixedPoints.mp hx ⟨n, hn⟩)
  have : IsPretransitive N X := IsQuasiPreprimitive.isPretransitive_of_normal hfixed
  let x : X := Classical.choice inferInstance
  have hdiv : p ∣ Nat.card N := by
    apply hdegree.trans
    rw [← index_stabilizer_of_transitive N x]
    exact (stabilizer N x).index_dvd_card
  have hindex : ¬ p ∣ N.index := by
    intro hi
    apply hcard
    rw [← N.card_mul_index, pow_two]
    exact Nat.mul_dvd_mul hdiv hi
  have hpow : (QuotientGroup.mk' N a) ^ p = 1 := by
    rw [← map_pow, ha, map_one]
  have horder : orderOf (QuotientGroup.mk' N a) = 1 := by
    rcases hp.eq_one_or_self_of_dvd _ (orderOf_dvd_of_pow_eq_one hpow) with h | h
    · exact h
    · exact False.elim (hindex (by
        rw [N.index_eq_card, ← h]
        exact orderOf_dvd_natCard _))
  have hmem : a ∈ N := (QuotientGroup.eq_one_iff a).mp (orderOf_eq_one_iff.mp horder)
  apply top_unique
  rw [← hgen]
  exact Subgroup.normalClosure_le_normal (Set.singleton_subset_iff.mpr hmem)

/-- A normal generator of order dividing the prime degree forces simplicity when that
prime occurs only once in the group order. -/
theorem isSimpleGroup_of_prime_degree_action
    {G X : Type*} [Group G] [Nontrivial G]
    [MulAction G X] [FaithfulSMul G X] [IsPretransitive G X]
    (hp : (Nat.card X).Prime) (hcard : ¬ Nat.card X ^ 2 ∣ Nat.card G)
    (a : G) (ha : a ^ Nat.card X = 1)
    (hgen : Subgroup.normalClosure ({a} : Set G) = ⊤) : IsSimpleGroup G := by
  have : IsPreprimitive G X := IsPreprimitive.of_prime_card hp
  have : Nonempty X := (Nat.card_ne_zero.mp hp.ne_zero).1
  exact isSimpleGroup_of_prime_divisor_degree_action hp (dvd_refl _) hcard a ha hgen

end TauCeti
