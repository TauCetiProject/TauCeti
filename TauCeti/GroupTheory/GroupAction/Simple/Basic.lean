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
public import TauCeti.GroupTheory.Subgroup.Simple

/-!
# Simplicity from primitive actions

Suppose a nontrivial group acts faithfully and quasi-primitively on a set whose cardinality is
divisible by a prime `p`, with `p²` not dividing the group order. If an element whose `p`th power
is one normally generates the group, then the group is simple. A faithful transitive action of
prime degree is a special case.

A nontrivial normal subgroup must act transitively, so its order is divisible by `p`. The
group-theoretic criterion
`TauCeti.isSimpleGroup_of_normalClosure_eq_top_of_forall_prime_dvd_natCard` then applies: the
index of such a subgroup is coprime to `p`, forcing the chosen element into it, and normal
generation forces the subgroup to be the whole group.
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
  -- A nontrivial normal subgroup acts transitively, so its order is divisible by `p`.
  refine isSimpleGroup_of_normalClosure_eq_top_of_forall_prime_dvd_natCard hp hcard
    (fun N _ hN ↦ ?_) a ha hgen
  have : IsPretransitive N X := IsQuasiPreprimitive.isPretransitive_of_normal_of_ne_bot N hN
  have : Nontrivial X := nontrivial_of_fixedPoints_ne_univ (fixedPoints_ne_univ_of_ne_bot hN)
  exact hdegree.trans (natCard_dvd_natCard_of_isPretransitive N)

/-- If `G` acts faithfully and transitively on a set of prime size `p` with `p ^ 2` not dividing
`|G|`, and an element `a` with `a ^ p = 1` normally generates `G`, then `G` is simple. -/
theorem isSimpleGroup_of_normalClosure_eq_top_of_prime_card
    {G X : Type*} [Group G] [MulAction G X] [FaithfulSMul G X] [IsPretransitive G X]
    (hp : (Nat.card X).Prime) (hcard : ¬ Nat.card X ^ 2 ∣ Nat.card G)
    (a : G) (ha : a ^ Nat.card X = 1)
    (hgen : Subgroup.normalClosure ({a} : Set G) = ⊤) : IsSimpleGroup G := by
  have : IsPreprimitive G X := IsPreprimitive.of_prime_card hp
  -- The group maps onto the prime-degree set, which has more than one point.
  have : Finite X := Nat.finite_of_card_ne_zero hp.ne_zero
  have : Nontrivial X := Finite.one_lt_card_iff_nontrivial.mp hp.one_lt
  have : Nontrivial G := (surjective_smul G (Classical.arbitrary X)).nontrivial
  exact isSimpleGroup_of_normalClosure_eq_top_of_prime_dvd_card hp (dvd_refl _) hcard a ha hgen

end TauCeti
