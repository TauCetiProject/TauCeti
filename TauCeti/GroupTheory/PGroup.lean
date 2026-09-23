/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.GroupTheory.Nilpotent
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

* `IsPGroup.prod`: a product of two `p`-groups is a `p`-group.
* `IsPGroup.pi`: a finite product of `p`-groups is a `p`-group.
* `IsPGroup.of_subgroup_of_quotient`: an extension of a `p`-group by a `p`-group is a
  `p`-group.
* `TauCeti.disjoint_of_not_dvd_natCard_of_isPGroup`: a `p`-group meets a subgroup of order prime
  to `p` trivially.
* `IsPGroup.index_eq_prime_of_isCoatom`: a maximal subgroup of a finite `p`-group has index
  `p`.
* `IsPGroup.exists_normal_ne_bot_le_inf_centralizer`: a nontrivial finite normal `p`-subgroup `N`
  contains a nontrivial normal subgroup of exponent dividing `p` that centralizes `N`.
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

/-- An extension of a `p`-group by a `p`-group is a `p`-group: if a normal subgroup `N` of `G`
and the quotient `G ⧸ N` are both `p`-groups, then so is `G`. This is the converse of
`IsPGroup.to_subgroup` and `IsPGroup.to_quotient` taken together. -/
theorem _root_.IsPGroup.of_subgroup_of_quotient {N : Subgroup G} [N.Normal]
    (hN : IsPGroup p N) (hQ : IsPGroup p (G ⧸ N)) : IsPGroup p G := by
  intro g
  obtain ⟨k, hk⟩ := hQ (QuotientGroup.mk' N g)
  rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hk
  obtain ⟨m, hm⟩ := hN ⟨g ^ p ^ k, hk⟩
  refine ⟨k + m, ?_⟩
  rw [pow_add, pow_mul]
  simpa using congrArg Subtype.val hm

/-- A `p`-group meets a subgroup of order prime to `p` trivially. -/
theorem disjoint_of_not_dvd_natCard_of_isPGroup [Fact p.Prime] {C Q : Subgroup G}
    (hC : ¬ p ∣ Nat.card C) (hQ : IsPGroup p Q) : Disjoint C Q := by
  rw [Subgroup.disjoint_def]
  intro g hg hgQ
  by_contra hg1
  refine hC ((?_ : p ∣ orderOf g).trans ?_)
  · simpa [Subgroup.orderOf_mk] using hQ.dvd_orderOf (g := (⟨g, hgQ⟩ : Q)) (by simpa using hg1)
  · simpa [Subgroup.orderOf_mk] using orderOf_dvd_natCard (⟨g, hg⟩ : C)

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

/-- A nontrivial finite normal `p`-subgroup `N` of `G` contains a nontrivial subgroup `A`, normal
in `G`, which centralizes `N` and all of whose elements satisfy `x ^ p = 1`. In particular `A` is
an elementary abelian `p`-group on which `N` acts trivially by conjugation. -/
theorem _root_.IsPGroup.exists_normal_ne_bot_le_inf_centralizer [hp : Fact p.Prime]
    {N : Subgroup G} [hNn : N.Normal] [Finite N] (hN : IsPGroup p N) (hN' : N ≠ ⊥) :
    ∃ A : Subgroup G, A.Normal ∧ A ≠ ⊥ ∧ A ≤ N ⊓ Subgroup.centralizer N ∧
      ∀ x ∈ A, x ^ p = 1 := by
  -- `A` is the set of elements of the centre of `N` whose `p`-th power is `1`. It is normal in `G`
  -- because conjugation by `G` preserves `N`, and nontrivial by Cauchy's theorem applied to the
  -- centre of `N`, which is nontrivial because `N` is a nontrivial finite `p`-group.
  let A : Subgroup G :=
    { carrier := {x | x ∈ N ⊓ Subgroup.centralizer N ∧ x ^ p = 1}
      mul_mem' := by
        rintro x y ⟨hx, hxp⟩ ⟨hy, hyp⟩
        have hxy : Commute x y :=
          (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hx).2 y
            (Subgroup.mem_inf.mp hy).1).symm
        exact ⟨mul_mem hx hy, by rw [hxy.mul_pow, hxp, hyp, one_mul]⟩
      one_mem' := ⟨one_mem _, one_pow p⟩
      inv_mem' := by
        rintro x ⟨hx, hxp⟩
        exact ⟨inv_mem hx, by rw [inv_pow, hxp, inv_one]⟩ }
  refine ⟨A, ⟨fun x hx g ↦ ⟨Subgroup.mem_inf.mpr ⟨hNn.conj_mem x (Subgroup.mem_inf.mp hx.1).1 g,
    Subgroup.mem_centralizer_iff.mpr fun y hy ↦ ?_⟩,
    by rw [conj_pow, hx.2, mul_one, mul_inv_cancel]⟩⟩, ?_, fun x hx ↦ hx.1, fun x hx ↦ hx.2⟩
  · -- `x` commutes with `g⁻¹ * y * g ∈ N`, so its conjugate `g * x * g⁻¹` commutes with `y`.
    have hy' : g⁻¹ * y * g ∈ N := by simpa using hNn.conj_mem y hy g⁻¹
    have hc := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hx.1).2 _ hy'
    calc y * (g * x * g⁻¹) = g * ((g⁻¹ * y * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * y * g)) * g⁻¹ := by rw [hc]
      _ = g * x * g⁻¹ * y := by group
  · have : Nontrivial N := (Subgroup.nontrivial_iff_ne_bot N).mpr hN'
    have := hN.center_nontrivial
    have hdvd : p ∣ Nat.card (Subgroup.center N) :=
      (hN.to_subgroup _).card_eq_or_dvd.resolve_left Finite.one_lt_card.ne'
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p hdvd
    have hz1 : ((z : N) : G) ≠ 1 := by
      intro h
      rw [show z = 1 from Subtype.ext (Subtype.ext h), orderOf_one] at hz
      exact hp.out.ne_one hz.symm
    refine (Subgroup.ne_bot_iff_exists_ne_one).mpr ⟨⟨(z : N), ?_, ?_⟩, ?_⟩
    · refine Subgroup.mem_inf.mpr ⟨(z : N).2, Subgroup.mem_centralizer_iff.mpr fun y hy ↦ ?_⟩
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp z.2 ⟨y, hy⟩)
    · have := congrArg (fun w : Subgroup.center N ↦ ((w : N) : G)) (hz ▸ pow_orderOf_eq_one z)
      simpa using this
    · exact fun h ↦ hz1 (congrArg Subtype.val h)

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
