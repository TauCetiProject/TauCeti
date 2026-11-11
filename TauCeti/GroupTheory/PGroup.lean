/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.PGroup

/-!
# Results about `p`-groups

Mathlib's `IsPGroup.to_quotient` says that every quotient of a `p`-group is again a `p`-group.
This file records the complementary behaviour, in which the group is fixed and the normal
subgroup varies: how the property `IsPGroup p (G ⧸ N)` of *the quotient* behaves under
intersection of normal subgroups and under preimage along a group homomorphism. It also records
closure of `p`-groups under binary and finite products and under extensions, and their
disjointness from subgroups of order prime to `p`.

The two quotient statements are group-theoretic, with no topology. They are what makes the family of
normal subgroups with `p`-group quotient usable: `IsPGroup.quotient_inf` says the family is
closed under binary intersection, hence downward directed, and `IsPGroup.quotient_comap` says
it is contravariantly functorial. The profinite development uses the first to run a compactness
argument on the family of open normal subgroups with `p`-group quotient, and the second to see
that a homomorphism into a pro-`p` group kills their intersection.

## Main results

* `IsPGroup.exists_pow_pow_eq_one_map`: every element in the image of a `p`-group under a monoid
  homomorphism has `p`-power order.
* `IsPGroup.prod`: a product of two `p`-groups is a `p`-group.
* `IsPGroup.pi`: a finite product of `p`-groups is a `p`-group.
* `IsPGroup.of_subgroup_of_quotient`: an extension of a `p`-group by a `p`-group is a
  `p`-group.
* `TauCeti.disjoint_of_not_dvd_natCard_of_isPGroup`: a `p`-group meets a subgroup of order prime
  to `p` trivially.
* `IsPGroup.subsingleton_of_coprime`, `IsPGroup.subsingleton_of_ne`: a group that is a `p`-group
  and a `q`-group for coprime `p`, `q`, in particular for distinct primes, is trivial.
* `IsPGroup.smul_zmod_eq_self`: a `p`-group acts trivially on the additive group `ZMod p`.
* `MonoidHom.apply_eq_self_of_iterate_pow_eq_self`: an endomorphism of a group of order `p`
  with a `p`-power iterate equal to the identity is the identity.
* `IsPGroup.le_total_of_isCyclic`: the subgroups of a finite cyclic `p`-group form a chain.
* `TauCeti.exists_isPGroup_quotient_notMem_of_pow_pow_eq_one`: in a finite commutative
  group, an element of `p`-power order survives in some `p`-group quotient.
* `IsPGroup.exists_mem_center_orderOf_eq_prime`: a nontrivial finite `p`-group has a central
  element of order `p`.
* `IsPGroup.exists_ne_one_le_centralizer`: a nontrivial finite `p`-subgroup lies in the
  centralizer of one of its nontrivial elements.
* `IsPGroup.quotient_inf`: if `G ⧸ M` and `G ⧸ N` are `p`-groups, so is `G ⧸ (M ⊓ N)`.
* `IsPGroup.quotient_comap`: if `H ⧸ N` is a `p`-group and `f : G →* H`, then `G ⧸ N.comap f`
  is a `p`-group.
-/

public section

namespace TauCeti

variable {p : ℕ} {G : Type*} [Group G] {H : Type*} [Group H]

/-- **Every element in the image of a `p`-group under a monoid homomorphism has `p`-power order.**
This supplies the power-order hypothesis for a representation of a `p`-group. -/
theorem _root_.IsPGroup.exists_pow_pow_eq_one_map {M : Type*} [Monoid M] (hG : IsPGroup p G)
    (f : G →* M) (g : G) : ∃ n : ℕ, f g ^ p ^ n = 1 :=
  (hG g).elim fun n hn => ⟨n, by rw [← map_pow, hn, map_one]⟩

/-- A product of two `p`-groups is a `p`-group. -/
theorem _root_.IsPGroup.prod (hG : IsPGroup p G) (hH : IsPGroup p H) :
    IsPGroup p (G × H) := by
  rintro ⟨g, h⟩
  obtain ⟨m, hm⟩ := hG g
  obtain ⟨n, hn⟩ := hH h
  exact ⟨m + n, Prod.ext (by simp [pow_add, pow_mul, hm]) (by simp [pow_add, pow_mul', hn])⟩

/-- A product of finitely many `p`-groups is a `p`-group. -/
theorem _root_.IsPGroup.pi {ι : Type*} [Finite ι] {G : ι → Type*} [∀ i, Group (G i)]
    (hG : ∀ i, IsPGroup p (G i)) : IsPGroup p (∀ i, G i) := by
  cases nonempty_fintype ι
  intro g
  choose n hn using fun i ↦ hG i (g i)
  refine ⟨∑ i, n i, funext fun i ↦ ?_⟩
  obtain ⟨k, hk⟩ := pow_dvd_pow p (Finset.single_le_sum (fun j _ ↦ Nat.zero_le (n j))
    (Finset.mem_univ i))
  rw [Pi.pow_apply, hk, pow_mul, hn, one_pow, Pi.one_apply]

/-- An extension of a `p`-group by a `p`-group is a `p`-group: if a normal subgroup `N` of `G`
and the quotient `G ⧸ N` are both `p`-groups, then so is `G`. This is the converse of
`IsPGroup.to_subgroup` and `IsPGroup.to_quotient` taken together. -/
theorem _root_.IsPGroup.of_subgroup_of_quotient {N : Subgroup G} [N.Normal]
    (hN : IsPGroup p N) (hQ : IsPGroup p (G ⧸ N)) : IsPGroup p G := by
  have := (hQ.to_subgroup ⊤).comap_of_ker_isPGroup (QuotientGroup.mk' N)
    (by rwa [QuotientGroup.ker_mk'])
  rw [Subgroup.comap_top] at this
  exact this.of_equiv Subgroup.topEquiv

/-- A `p`-group meets a subgroup of order prime to `p` trivially. -/
theorem disjoint_of_not_dvd_natCard_of_isPGroup [Fact p.Prime] {C Q : Subgroup G}
    (hC : ¬ p ∣ Nat.card C) (hQ : IsPGroup p Q) : Disjoint C Q :=
  (hQ.disjoint_of_coprime (IsPGroup.card (G := C))
    ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hC)).symm

/-- A group that is a `p`-group and a `q`-group for coprime `p` and `q` is trivial. -/
theorem _root_.IsPGroup.subsingleton_of_coprime {q : ℕ} (hp : IsPGroup p G) (hq : IsPGroup q G)
    (hpq : p.Coprime q) : Subsingleton G :=
  Subgroup.subsingleton_iff.mp <| subsingleton_of_bot_eq_top
    (disjoint_self.mp ((hp.to_subgroup ⊤).disjoint_of_coprime (hq.to_subgroup ⊤) hpq)).symm

/-- **A group that is a `p`-group and a `q`-group for two distinct primes is trivial.** -/
theorem _root_.IsPGroup.subsingleton_of_ne {q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hp : IsPGroup p G) (hq : IsPGroup q G) (hpq : p ≠ q) : Subsingleton G :=
  hp.subsingleton_of_coprime hq ((Nat.coprime_primes Fact.out Fact.out).mpr hpq)

/-- A `p`-group acts trivially on the additive group `ZMod p`, for `p` prime. -/
theorem _root_.IsPGroup.smul_zmod_eq_self [Fact p.Prime] (hG : IsPGroup p G)
    [DistribMulAction G (ZMod p)] (g : G) (m : ZMod p) : g • m = m := by
  -- The action of `g` on `ZMod p` is multiplication by `g • 1`.
  have hlin : (g • · : ZMod p → ZMod p) = (g • (1 : ZMod p) * ·) := funext fun m ↦
    calc g • m = g • (m.val • (1 : ZMod p)) := by rw [nsmul_one, ZMod.natCast_zmod_val]
      _ = m.val • (g • (1 : ZMod p)) := smul_comm _ _ _
      _ = g • (1 : ZMod p) * m := by rw [nsmul_eq_mul, ZMod.natCast_zmod_val, mul_comm]
  obtain ⟨k, hk⟩ := hG g
  -- Iterating `g • ·` `p ^ k` times is the identity, and `(g • 1) ^ p ^ k = g • 1`.
  have hu := congrFun (smul_iterate g (p ^ k)) (1 : ZMod p)
  rw [hk, one_smul, hlin, mul_left_iterate_apply, ZMod.pow_card_pow, mul_one] at hu
  rw [congrFun hlin m, hu, one_mul]

/-- An endomorphism of a group of prime order `p` some `p`-power iterate of which is the identity
is itself the identity. This is the form in which a `p`-group acts trivially on a group of order
`p`. -/
theorem _root_.MonoidHom.apply_eq_self_of_iterate_pow_eq_self [Fact p.Prime] {A : Type*}
    [Group A] (f : A →* A) (hA : Nat.card A = p) {k : ℕ} (hf : ∀ a, f^[p ^ k] a = a) (a : A) :
    f a = a := by
  -- `f` is a power map `a ↦ a ^ m` of the cyclic group `A`, and `m ^ (p ^ k) ≡ m` modulo `p`.
  have : IsCyclic A := isCyclic_of_prime_card (p := p) hA
  obtain ⟨m, hm⟩ := f.map_cyclic
  have hiter (n : ℕ) (b : A) : f^[n] b = b ^ (m ^ n) := by
    induction n with
    | zero => simp
    | succ n ih => rw [Function.iterate_succ_apply', ih, hm, ← zpow_mul, pow_succ]
  have hmod : m ^ p ^ k ≡ m [ZMOD orderOf a] := by
    refine Int.ModEq.of_dvd (Int.natCast_dvd_natCast.2 (hA ▸ orderOf_dvd_natCard a)) ?_
    rw [← ZMod.intCast_eq_intCast_iff]
    push_cast
    exact ZMod.pow_card_pow (p := p) _
  calc f a = a ^ m := hm a
    _ = a ^ (m ^ p ^ k) := zpow_eq_zpow_iff_modEq.2 hmod.symm
    _ = a := (hiter _ a).symm.trans (hf a)

/-- The subgroups of a cyclic `p`-group are totally ordered by inclusion: such a group is finite,
in a cyclic group one subgroup contains another exactly when its order is divisible by the other's,
and here every order is a power of `p`. -/
theorem _root_.IsPGroup.le_total_of_isCyclic [Fact p.Prime] [IsCyclic G]
    (hG : IsPGroup p G) (H K : Subgroup G) : H ≤ K ∨ K ≤ H := by
  -- a generator has finite order, since it is killed by a power of `p`
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  have hfin : Finite (Subgroup.zpowers g) :=
    (hG.isOfFinOrder (Fact.out : p.Prime).ne_zero g).finite_zpowers
  have : Finite G := Finite.of_surjective (fun x : Subgroup.zpowers g ↦ (x : G))
    fun x ↦ ⟨⟨x, hg x⟩, rfl⟩
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.1 (hG.to_subgroup H)
  obtain ⟨b, hb⟩ := IsPGroup.iff_card.1 (hG.to_subgroup K)
  simp only [IsCyclic.subgroup_le_iff_card_dvd, ha, hb]
  exact (le_total a b).imp (pow_dvd_pow p) (pow_dvd_pow p)

open scoped IsMulCommutative in
/-- In a finite commutative group, a nontrivial element of `p`-power order survives in some
`p`-group quotient: there is a subgroup `N` with `A ⧸ N` a `p`-group and `a ∉ N`. The subgroup
is the kernel of raising to the power `ordCompl[p] (Nat.card A)`, the part of the group order
prime to `p`. -/
theorem exists_isPGroup_quotient_notMem_of_pow_pow_eq_one {A : Type*} [Group A]
    [IsMulCommutative A] [Finite A] [hp : Fact p.Prime] {a : A} {k : ℕ} (ha : a ^ p ^ k = 1)
    (ha1 : a ≠ 1) : ∃ N : Subgroup A, IsPGroup p (A ⧸ N) ∧ a ∉ N := by
  let f : A →* A := powMonoidHom (ordCompl[p] (Nat.card A))
  refine ⟨f.ker, ?_, fun h ↦ ha1 ?_⟩
  · -- The quotient by the kernel is the range, whose elements are killed by `ordProj[p]`.
    refine IsPGroup.of_equiv ?_ (QuotientGroup.quotientKerEquivRange f).symm
    rintro ⟨_, b, rfl⟩
    refine ⟨(Nat.card A).factorization p, ?_⟩
    rw [Subtype.ext_iff, Subgroup.coe_pow, OneMemClass.coe_one]
    simp only [f, powMonoidHom_apply]
    rw [← pow_mul, mul_comm, Nat.ordProj_mul_ordCompl_eq_self, pow_card_eq_one']
  · -- An element of `p`-power order killed by a power prime to `p` is trivial.
    rw [MonoidHom.mem_ker] at h
    simp only [f, powMonoidHom_apply] at h
    exact orderOf_eq_one_iff.mp <| Nat.eq_one_of_dvd_coprimes
      ((Nat.coprime_ordCompl hp.out Nat.card_pos.ne').pow_left k)
      (orderOf_dvd_of_pow_eq_one ha) (orderOf_dvd_of_pow_eq_one h)

/-- A nontrivial finite `p`-group has an element in its centre of order `p`. -/
theorem _root_.IsPGroup.exists_mem_center_orderOf_eq_prime [Fact p.Prime] [Finite G]
    [Nontrivial G] (hG : IsPGroup p G) : ∃ z ∈ Subgroup.center G, orderOf z = p := by
  have := hG.center_nontrivial
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center G) p
    ((hG.to_subgroup _).card_eq_or_dvd.resolve_left Finite.one_lt_card.ne')
  exact ⟨z, z.2, (Subgroup.orderOf_coe z).trans hz⟩

/-- A nontrivial finite `p`-subgroup `P` of `G` lies in the centralizer of one of its nontrivial
elements, namely of any nontrivial element of the centre of `P`. -/
theorem _root_.IsPGroup.exists_ne_one_le_centralizer [Fact p.Prime] {P : Subgroup G} [Finite P]
    (hP : IsPGroup p P) (hne : P ≠ ⊥) : ∃ g ∈ P, g ≠ 1 ∧ P ≤ Subgroup.centralizer {g} := by
  have : Nontrivial P := (Subgroup.nontrivial_iff_ne_bot P).2 hne
  obtain ⟨z, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hP.bot_lt_center.ne'
  refine ⟨z.1, z.1.2, fun h ↦ hz1 (Subtype.ext (Subtype.ext h)), fun y hy ↦ ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact congrArg Subtype.val (Subgroup.mem_center_iff.1 z.2 ⟨y, hy⟩)

/-- The normal subgroups of `G` with `p`-group quotient are closed under binary intersection. -/
theorem _root_.IsPGroup.quotient_inf {M N : Subgroup G} [M.Normal] [N.Normal]
    (hM : IsPGroup p (G ⧸ M)) (hN : IsPGroup p (G ⧸ N)) : IsPGroup p (G ⧸ M ⊓ N) := by
  -- `G ⧸ (M ⊓ N)` embeds in `(G ⧸ M) × (G ⧸ N)`.
  have hker : ((QuotientGroup.mk' M).prod (QuotientGroup.mk' N)).ker = M ⊓ N := by
    rw [MonoidHom.ker_prod, QuotientGroup.ker_mk', QuotientGroup.ker_mk']
  exact ((hM.prod hN).of_injective _ (QuotientGroup.kerLift_injective _)).of_equiv
    (QuotientGroup.quotientMulEquivOfEq hker)

/-- The preimage of a normal subgroup with `p`-group quotient also has `p`-group quotient. -/
theorem _root_.IsPGroup.quotient_comap {N : Subgroup H} [N.Normal] (hN : IsPGroup p (H ⧸ N))
    (f : G →* H) : IsPGroup p (G ⧸ N.comap f) := by
  -- `G ⧸ N.comap f` embeds in `H ⧸ N`.
  have hker : ((QuotientGroup.mk' N).comp f).ker = N.comap f := by
    simpa using (MonoidHom.comap_ker (QuotientGroup.mk' N) f).symm
  exact (hN.of_injective _ (QuotientGroup.kerLift_injective _)).of_equiv
    (QuotientGroup.quotientMulEquivOfEq hker)

end TauCeti
