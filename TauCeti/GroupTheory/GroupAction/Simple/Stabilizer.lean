/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Subgroup.Simple
public import TauCeti.GroupTheory.Automorphism.PrimeOrder
public import TauCeti.GroupTheory.GroupAction.ConjAct
public import TauCeti.GroupTheory.GroupAction.Primitive

/-!
# Simplicity from simple point stabilizers

In a faithful quasi-primitive action with a simple point stabilizer, a nontrivial normal
subgroup either contains the stabilizer, and is then the whole group, or meets it trivially and
acts regularly. Ruling out regular normal subgroups is therefore a simplicity criterion.

For degree `p + 1` with `p` prime, an element of order `p` in the stabilizer rules out a regular
normal subgroup whenever two distinct primes divide the degree: the stabilizer acts faithfully by
conjugation on such a subgroup, and the prime-order automorphism bound
`MulAut.orderOf_ne_prime_of_card_eq_succ` applies.
-/

public section

namespace TauCeti

open _root_.MulAction TauCeti.MulAction
open scoped Pointwise

/-- A group acting faithfully and quasi-primitively with a simple point stabilizer is simple if
no normal subgroup acts regularly: every transitive normal subgroup has a nontrivial point
stabilizer. -/
theorem isSimpleGroup_of_isSimpleGroup_stabilizer_of_forall_stabilizer_ne_bot
    {G X : Type*} [Group G] [MulAction G X] [FaithfulSMul G X] [IsQuasiPreprimitive G X]
    (x : X) [IsSimpleGroup (stabilizer G x)]
    (hreg : ∀ (N : Subgroup G) [N.Normal] [IsPretransitive N X], stabilizer N x ≠ ⊥) :
    IsSimpleGroup G := by
  have : Nontrivial G := (stabilizer G x).subtype_injective.nontrivial
  refine ⟨fun N _ ↦ ?_⟩
  by_cases hN : N = ⊥
  · exact Or.inl hN
  right
  have : IsPretransitive N X := IsQuasiPreprimitive.isPretransitive_of_normal_of_ne_bot N hN
  -- `N` meets the simple stabilizer in a normal subgroup, which is trivial or everything.
  rcases Subgroup.Normal.eq_bot_or_eq_top (N.subgroupOf (stabilizer G x)) with hi | hi
  · -- Trivial intersection: `N` acts regularly, which `hreg` forbids.
    have hstab : stabilizer N x = ⊥ := by
      rw [← stabilizer_subgroupOf, Subgroup.subgroupOf_eq_bot]
      exact (Subgroup.subgroupOf_eq_bot.mp hi).symm
    exact (hreg N hstab).elim
  · -- The stabilizer lies in the transitive subgroup `N`, so `N` is everything.
    exact (stabilizer_orbit_eq (Subgroup.subgroupOf_eq_top.mp hi)).symm.trans
      (by rw [orbit_eq_univ, stabilizer_univ])

/-- A group acting faithfully and quasi-primitively with degree `p + 1` for a prime `p` is simple
if a point stabilizer is simple and contains an element of order `p`, and two distinct primes
divide the degree: the stabilizer cannot act faithfully on a regular normal subgroup. -/
theorem isSimpleGroup_of_isSimpleGroup_stabilizer_of_card_eq_succ
    {G X : Type*} [Group G] [MulAction G X] [FaithfulSMul G X] [IsQuasiPreprimitive G X]
    (x : X) [IsSimpleGroup (stabilizer G x)]
    {p q r : ℕ} (hp : p.Prime) (hcard : Nat.card X = p + 1)
    (hq : q.Prime) (hr : r.Prime) (hqr : q ≠ r)
    (hqdvd : q ∣ Nat.card X) (hrdvd : r ∣ Nat.card X)
    (a : stabilizer G x) (ha : orderOf a = p) : IsSimpleGroup G := by
  refine isSimpleGroup_of_isSimpleGroup_stabilizer_of_forall_stabilizer_ne_bot x
    fun N _ _ hN ↦ ?_
  have hcardN : Nat.card N = Nat.card X := by
    rw [← Subgroup.index_bot, ← hN, index_stabilizer_of_transitive]
  let f := (MulAut.conjNormal (H := N)).comp (stabilizer G x).subtype
  have hf : orderOf (f a) = p :=
    (orderOf_injective f (N.stabilizer_conjNormal_injective x) a).trans ha
  exact MulAut.orderOf_ne_prime_of_card_eq_succ (f a) hp (hcardN.trans hcard)
    hq hr hqr (hcardN ▸ hqdvd) (hcardN ▸ hrdvd) hf

end TauCeti
