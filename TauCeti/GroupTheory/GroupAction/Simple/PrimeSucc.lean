/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.PGroup
public import TauCeti.Data.Nat.Factorial.Prime
public import TauCeti.GroupTheory.GroupAction.MultipleTransitivity
public import TauCeti.GroupTheory.GroupAction.Simple.Stabilizer
public import TauCeti.GroupTheory.GroupAction.SubMulAction
public import TauCeti.GroupTheory.GroupAction.Transitive
public import TauCeti.GroupTheory.Subgroup.Simple

/-!
# Simplicity of transitive groups of degree `p + 1`

Let a group `G` act faithfully and transitively on `p + 1` points, where `p` is a prime and
`p + 1` is not a prime power, and let `a` be an element of order `p`. This file proves that the
order of every nontrivial normal subgroup of `G` is divisible by `p`, and deduces that `G` is
simple as soon as `a` normally generates it. The criterion needs no knowledge of a point
stabilizer beyond the element `a`, and no order computation: `p ^ 2` cannot divide the order of a
group of permutations of `p + 1` points.

The element `a` fixes exactly one point `x` and permutes the other `p` points transitively. So the
stabilizer of `x` is transitive, hence primitive, on these `p` points, and `G` is doubly
transitive, by `TauCeti.is_two_pretransitive_of_card_eq_succ_of_smul_ne`, hence primitive. A
nontrivial normal subgroup `N` is therefore transitive. Its intersection with the stabilizer of
`x` is normal in that stabilizer, so it is trivial or transitive on the other `p` points. In the
second case `p` divides `|N|`. In the first case `N` acts regularly, which
`TauCeti.stabilizer_ne_bot_of_card_eq_succ` excludes: an automorphism of order `p` of a group of
order `p + 1` forces `p + 1` to be a prime power.

Finally, since `p` divides the order of every nontrivial normal subgroup and `p ^ 2` does not
divide `|G|`, the criterion
`TauCeti.isSimpleGroup_of_normalClosure_eq_top_of_forall_prime_dvd_natCard` applies: the index of
`N` is prime to `p`, so `N` contains `a`, and with it the normal closure of `a`.

The hypothesis on `p + 1` cannot be dropped: the affine group of the line over the field with
eight elements acts faithfully and doubly transitively on `7 + 1` points and is normally generated
by an element of order `7`, but its translations form a proper normal subgroup.

## Main results

* `TauCeti.prime_dvd_natCard_of_normal_of_card_eq_succ`: in a faithful transitive action on
  `p + 1` points of a group containing an element of order `p`, the order of every nontrivial
  normal subgroup is divisible by `p`, if two distinct primes divide `p + 1`.
* `TauCeti.isSimpleGroup_of_normalClosure_eq_top_of_card_eq_succ`: such a group is simple if an
  element with `p`-th power `1` normally generates it.

## References

* J. D. Dixon and B. Mortimer, *Permutation Groups*, Graduate Texts in Mathematics 163, Springer,
  1996, §1.6, for normal subgroups of primitive permutation groups.
-/

public section

namespace TauCeti

open _root_.MulAction TauCeti.MulAction

/-- **Normal subgroups in degree `p + 1`.** Let a group `G` act faithfully and transitively on
`p + 1` points, `p` prime, with two distinct primes dividing `p + 1`, and let `G` contain an
element of order `p`. Then `p` divides the order of every nontrivial normal subgroup of `G`. -/
theorem prime_dvd_natCard_of_normal_of_card_eq_succ
    {G X : Type*} [Group G] [MulAction G X] [FaithfulSMul G X] [IsPretransitive G X]
    {p q r : ℕ} (hp : p.Prime) (hcard : Nat.card X = p + 1)
    (hq : q.Prime) (hr : r.Prime) (hqr : q ≠ r)
    (hqdvd : q ∣ Nat.card X) (hrdvd : r ∣ Nat.card X)
    {a : G} (ha : orderOf a = p) (N : Subgroup G) [N.Normal] (hN : N ≠ ⊥) :
    p ∣ Nat.card N := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite X := Nat.finite_of_card_ne_zero (by omega)
  -- The element `a` of order `p` fixes a point `x` and moves a point `y`.
  obtain ⟨x, hx⟩ := (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ha, pow_one])
    : IsPGroup p (Subgroup.zpowers a)).nonempty_fixed_point_of_prime_not_dvd_card X fun h ↦
      hp.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right dvd_rfl).mp (hcard ▸ h)))
  replace hx : a • x = x := by
    simpa only [subgroup_smul_def] using mem_fixedPoints.mp hx ⟨a, Subgroup.mem_zpowers a⟩
  obtain ⟨y, hy⟩ : ∃ y : X, a • y ≠ y := by
    by_contra! h
    exact hp.ne_one (ha ▸ orderOf_eq_one_iff.mpr (eq_of_smul_eq_smul fun y ↦ by rw [h y, one_smul]))
  have hax : a ∈ stabilizer G x := mem_stabilizer_iff.mpr hx
  -- So the action of `G` is doubly transitive, hence primitive, and the stabilizer of `x` is
  -- transitive, hence primitive, on the other `p` points.
  have h2 : IsMultiplyPretransitive G X 2 := is_two_pretransitive_of_card_eq_succ_of_smul_ne hp
    hcard hx (by rw [← ha, pow_orderOf_eq_one, one_smul]) hy
  have : IsPreprimitive G X := isPreprimitive_of_is_two_pretransitive h2
  have hY : Nat.card (SubMulAction.ofStabilizer G x) = p := by
    rw [SubMulAction.nat_card_ofStabilizer_eq, hcard, Nat.add_sub_cancel]
  have : IsPretransitive (stabilizer G x) (SubMulAction.ofStabilizer G x) :=
    is_one_pretransitive_iff.mp (SubMulAction.ofStabilizer.isMultiplyPretransitive.mp h2)
  have : IsPreprimitive (stabilizer G x) (SubMulAction.ofStabilizer G x) :=
    IsPreprimitive.of_prime_card (hY ▸ hp)
  have : IsPretransitive N X := IsQuasiPreprimitive.isPretransitive_of_normal_of_ne_bot N hN
  -- If `p` does not divide `|N|`, then `N` meets the stabilizer of `x` trivially, since a
  -- nontrivial intersection would be transitive on the other `p` points; so `N` acts regularly.
  by_contra hdiv
  refine stabilizer_ne_bot_of_card_eq_succ x hp hcard hq hr hqr hqdvd hrdvd ⟨a, hax⟩
    (by rw [Subgroup.orderOf_mk, ha]) N ?_
  rw [← stabilizer_subgroupOf, Subgroup.subgroupOf_eq_bot, disjoint_comm,
    ← Subgroup.subgroupOf_eq_bot]
  by_contra hne
  have : IsPretransitive (N.subgroupOf (stabilizer G x)) (SubMulAction.ofStabilizer G x) :=
    IsQuasiPreprimitive.isPretransitive_of_normal_of_ne_bot _ hne
  have : Nonempty (SubMulAction.ofStabilizer G x) :=
    ⟨⟨y, (SubMulAction.mem_ofStabilizer_iff G x).mpr fun h ↦ hy (h ▸ hx)⟩⟩
  refine hdiv (dvd_trans ?_ (Subgroup.card_dvd_of_le (inf_le_left : N ⊓ stabilizer G x ≤ N)))
  rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv,
    Subgroup.inf_subgroupOf_right, ← hY]
  exact natCard_dvd_natCard_of_isPretransitive _

/-- **Simplicity in degree `p + 1`.** A group acting faithfully and transitively on `p + 1`
points, `p` prime, with two distinct primes dividing `p + 1`, is simple if it is normally generated
by an element `a` with `a ^ p = 1`. -/
theorem isSimpleGroup_of_normalClosure_eq_top_of_card_eq_succ
    {G X : Type*} [Group G] [MulAction G X] [FaithfulSMul G X] [IsPretransitive G X]
    {p q r : ℕ} (hp : p.Prime) (hcard : Nat.card X = p + 1)
    (hq : q.Prime) (hr : r.Prime) (hqr : q ≠ r)
    (hqdvd : q ∣ Nat.card X) (hrdvd : r ∣ Nat.card X)
    (a : G) (ha : a ^ p = 1)
    (hgen : Subgroup.normalClosure ({a} : Set G) = ⊤) : IsSimpleGroup G := by
  have : Fact p.Prime := ⟨hp⟩
  have hp2 := hp.two_le
  have : Finite X := Nat.finite_of_card_ne_zero (by omega)
  have : Nontrivial X := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  have : Nontrivial G := (surjective_smul G (Classical.arbitrary X)).nontrivial
  -- The normal generator `a` is not `1`, so it has order `p`.
  have ha1 : a ≠ 1 := by
    rintro rfl
    exact top_ne_bot (hgen.symm.trans (Subgroup.normalClosure_eq_bot_iff.mpr (by simp)))
  -- The group embeds in the permutations of `p + 1` points, so `p ^ 2` does not divide `|G|`.
  have hsq : ¬ p ^ 2 ∣ Nat.card G := fun h ↦ by
    have := hp.sq_dvd_factorial_iff.mp (h.trans ((Subgroup.card_dvd_of_injective
      (toPermHom G X) toPerm_injective).trans (by rw [Nat.card_perm, hcard])))
    omega
  -- The order of every nontrivial normal subgroup is divisible by `p`, which occurs only once in
  -- the order of `G`.
  exact isSimpleGroup_of_normalClosure_eq_top_of_forall_prime_dvd_natCard hp hsq
    (fun N _ hN ↦ prime_dvd_natCard_of_normal_of_card_eq_succ hp hcard hq hr hqr hqdvd hrdvd
      (orderOf_eq_prime ha ha1) N hN) a ha hgen

end TauCeti
