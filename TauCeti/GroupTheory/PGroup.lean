/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.GroupTheory.Nilpotent
public import Mathlib.GroupTheory.PGroup

/-!
# Normal subgroups with `p`-group quotient

Mathlib's `IsPGroup.to_quotient` says that every quotient of a `p`-group is again a `p`-group.
This file records the complementary behaviour, in which the group is fixed and the normal
subgroup varies: how the property `IsPGroup p (G ⧸ N)` of *the quotient* behaves under
intersection of normal subgroups and under preimage along a group homomorphism. It also records
closure of `p`-groups under binary and finite products.

The two quotient statements are group-theoretic, with no topology. They are what makes the family of
normal subgroups with `p`-group quotient usable: `IsPGroup.quotient_inf` says the family is
closed under binary intersection, hence downward directed, and `IsPGroup.quotient_comap` says
it is contravariantly functorial. The profinite development uses the first to run a compactness
argument on the family of open normal subgroups with `p`-group quotient, and the second to see
that a homomorphism into a pro-`p` group kills their intersection.

## Main results

* `IsPGroup.prod`: a product of two `p`-groups is a `p`-group.
* `IsPGroup.pi`: a finite product of `p`-groups is a `p`-group.
* `IsPGroup.index_eq_prime_of_isCoatom`: a maximal subgroup of a finite `p`-group has index
  `p`.
* `IsPGroup.quotient_inf`: if `G ⧸ M` and `G ⧸ N` are `p`-groups, so is `G ⧸ (M ⊓ N)`.
* `IsPGroup.quotient_comap`: if `H ⧸ N` is a `p`-group and `f : G →* H`, then `G ⧸ N.comap f`
  is a `p`-group.
-/

public section

namespace TauCeti

variable {p : ℕ} {G : Type*} [Group G] {H : Type*} [Group H]

/-- A product of two `p`-groups is a `p`-group. -/
theorem _root_.IsPGroup.prod (hG : IsPGroup p G) (hH : IsPGroup p H) :
    IsPGroup p (G × H) := by
  rintro ⟨g, h⟩
  obtain ⟨m, hm⟩ := hG g
  obtain ⟨n, hn⟩ := hH h
  refine ⟨m + n, ?_⟩
  rw [Prod.pow_mk, Prod.mk_eq_one, pow_add, pow_mul, hm, one_pow, mul_comm, pow_mul, hn, one_pow]
  exact ⟨rfl, rfl⟩

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

/-- A maximal subgroup of a finite `p`-group has index `p`. -/
theorem _root_.IsPGroup.index_eq_prime_of_isCoatom [Finite G] [hp : Fact p.Prime]
    (hG : IsPGroup p G) {H : Subgroup G} (hH : IsCoatom H) : H.index = p := by
  let _ : Group.IsNilpotent G := hG.isNilpotent
  let _ : H.Normal :=
    Subgroup.NormalizerCondition.normal_of_coatom
      H (Group.normalizerCondition_of_isNilpotent (G := G)) hH
  let Q := G ⧸ H
  let _ : Nontrivial Q := QuotientGroup.nontrivial_iff.mpr hH.ne_top
  have hQ : IsPGroup p Q := hG.to_quotient H
  have hp_dvd : p ∣ Nat.card Q := hQ.card_eq_or_dvd.resolve_left Finite.one_lt_card.ne'
  let _ : Group.IsNilpotent Q := hQ.isNilpotent
  obtain ⟨K, hKindex, hKnormal⟩ :=
    Group.IsNilpotent.exists_normal_index_eq_of_dvd_card hp_dvd
  let _ : K.Normal := hKnormal
  let q : G →* Q := QuotientGroup.mk' H
  have hHK : H ≤ K.comap q := by
    intro x hx
    rw [Subgroup.mem_comap]
    have hxq : q x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
    rw [hxq]
    exact K.one_mem
  have hKbot : K = ⊥ := by
    rcases hH.le_iff.mp hHK with htop | hH'
    · have hKtop : K = ⊤ := Subgroup.comap_injective (QuotientGroup.mk'_surjective H) htop
      rw [hKtop, Subgroup.index_top] at hKindex
      exact (hp.out.ne_one hKindex.symm).elim
    · apply Subgroup.comap_injective (QuotientGroup.mk'_surjective H)
      rw [hH', MonoidHom.comap_bot]
      exact (QuotientGroup.ker_mk' H).symm
  rw [hKbot, Subgroup.index_eq_card] at hKindex
  exact (Subgroup.index_eq_card (H := H)).trans <|
    (Nat.card_congr QuotientGroup.quotientBot.toEquiv).symm.trans hKindex

/-- The normal subgroups of `G` with `p`-group quotient are closed under binary intersection. -/
theorem _root_.IsPGroup.quotient_inf {M N : Subgroup G} [M.Normal] [N.Normal]
    (hM : IsPGroup p (G ⧸ M)) (hN : IsPGroup p (G ⧸ N)) : IsPGroup p (G ⧸ M ⊓ N) := by
  intro x
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (M ⊓ N) x
  obtain ⟨m, hm⟩ := hM (QuotientGroup.mk' M g)
  obtain ⟨n, hn⟩ := hN (QuotientGroup.mk' N g)
  rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hm hn
  refine ⟨m + n, ?_⟩
  rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_inf]
  refine ⟨?_, ?_⟩
  · rw [pow_add, pow_mul]
    exact Subgroup.pow_mem M hm _
  · rw [pow_add, mul_comm, pow_mul]
    exact Subgroup.pow_mem N hn _

/-- The preimage of a normal subgroup with `p`-group quotient also has `p`-group quotient. -/
theorem _root_.IsPGroup.quotient_comap {N : Subgroup H} [N.Normal] (hN : IsPGroup p (H ⧸ N))
    (f : G →* H) : IsPGroup p (G ⧸ N.comap f) := by
  let φ := (QuotientGroup.mk' N).comp f
  have hφ : N.comap f = φ.ker := by
    simpa [φ] using MonoidHom.comap_ker (g := QuotientGroup.mk' N) (f := f)
  exact (hN.of_injective (QuotientGroup.kerLift φ)
    (QuotientGroup.kerLift_injective φ)).of_equiv
      (QuotientGroup.quotientMulEquivOfEq hφ.symm)

end TauCeti
