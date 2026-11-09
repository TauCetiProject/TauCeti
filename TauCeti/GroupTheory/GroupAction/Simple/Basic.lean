/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.Subgroup.Simple
public import TauCeti.GroupTheory.GroupAction.Primitive
public import TauCeti.GroupTheory.GroupAction.Transitive

/-!
# Simplicity from primitive actions

Suppose a nontrivial group acts faithfully and quasi-primitively on a set whose cardinality is
divisible by a prime `p`, with `p²` not dividing the group order. If an element whose `p`th power
is one normally generates the group, then the group is simple. A faithful transitive action of
prime degree is a special case.

A nontrivial normal subgroup must act transitively, so its order is divisible by `p`. Its index
is therefore coprime to `p`, forcing the chosen element into that subgroup. Normal generation
then forces the subgroup to be the whole group.
-/

public section

namespace TauCeti

open _root_.MulAction TauCeti.MulAction

/-- In a faithful quasi-primitive action, a prime divisor of the degree that occurs only once in
the group order forces simplicity when an element of that prime order normally generates. -/
theorem isSimpleGroup_of_normalClosure_eq_top_of_prime_dvd_card
    {G X : Type*} [Group G] [Nontrivial G]
    [MulAction G X] [FaithfulSMul G X] [IsQuasiPreprimitive G X]
    {p : ℕ} (hp : p.Prime) (hdegree : p ∣ Nat.card X) (hcard : ¬ p ^ 2 ∣ Nat.card G)
    (a : G) (ha : a ^ p = 1)
    (hgen : Subgroup.normalClosure ({a} : Set G) = ⊤) : IsSimpleGroup G := by
  refine ⟨fun N _ ↦ ?_⟩
  by_cases hN : N = ⊥
  · exact Or.inl hN
  right
  have : IsPretransitive N X := IsQuasiPreprimitive.isPretransitive_of_normal_of_ne_bot N hN
  have : Nontrivial X := nontrivial_of_fixedPoints_ne_univ (fixedPoints_ne_univ_of_ne_bot hN)
  have hdiv : p ∣ Nat.card N := hdegree.trans (natCard_dvd_natCard_of_isPretransitive N)
  have hindex : ¬ p ∣ N.index := by
    intro hi
    apply hcard
    rw [← N.card_mul_index, pow_two]
    exact Nat.mul_dvd_mul hdiv hi
  have hpow : (a : G ⧸ N) ^ p = 1 := by
    rw [← QuotientGroup.mk_pow, ha, QuotientGroup.mk_one]
  have horder : orderOf (a : G ⧸ N) = 1 := by
    rcases hp.eq_one_or_self_of_dvd _ (orderOf_dvd_of_pow_eq_one hpow) with h | h
    · exact h
    · exact (hindex (by rw [N.index_eq_card, ← h]; exact orderOf_dvd_natCard _)).elim
  have hmem : a ∈ N := (QuotientGroup.eq_one_iff a).mp (orderOf_eq_one_iff.mp horder)
  apply top_unique
  rw [← hgen]
  exact Subgroup.normalClosure_le_normal (Set.singleton_subset_iff.mpr hmem)

/-- If `G` acts faithfully and transitively on a set of prime size `p` with `p ^ 2` not dividing
`|G|`, and an element `a` with `a ^ p = 1` normally generates `G`, then `G` is simple. -/
theorem isSimpleGroup_of_normalClosure_eq_top_of_prime_card
    {G X : Type*} [Group G] [MulAction G X] [FaithfulSMul G X] [IsPretransitive G X]
    (hp : (Nat.card X).Prime) (hcard : ¬ Nat.card X ^ 2 ∣ Nat.card G)
    (a : G) (ha : a ^ Nat.card X = 1)
    (hgen : Subgroup.normalClosure ({a} : Set G) = ⊤) : IsSimpleGroup G := by
  have : IsPreprimitive G X := IsPreprimitive.of_prime_card hp
  -- Two points of the prime-degree set are moved onto each other by a nonidentity element.
  have : Finite X := Nat.finite_of_card_ne_zero hp.ne_zero
  have : Nontrivial X := Finite.one_lt_card_iff_nontrivial.mp hp.one_lt
  obtain ⟨x, y, hxy⟩ := exists_pair_ne X
  obtain ⟨g, rfl⟩ := exists_smul_eq G x y
  have : Nontrivial G := ⟨⟨g, 1, fun h ↦ hxy (by rw [h, one_smul])⟩⟩
  exact isSimpleGroup_of_normalClosure_eq_top_of_prime_dvd_card hp (dvd_refl _) hcard a ha hgen

end TauCeti
