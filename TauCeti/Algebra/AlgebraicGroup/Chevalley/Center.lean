/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Bruhat.Decomposition
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.SimplyConnected
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Torus.Center
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Bruhat.Basic
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Torus.Normalizer
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Weyl.Quotient
import TauCeti.Algebra.Group.AddChar.Equiv
import TauCeti.GroupTheory.Subgroup.Centralizer
import TauCeti.LinearAlgebra.RootSystem.Inversions.StrongExchange
import TauCeti.LinearAlgebra.RootSystem.LongestElement
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Reduced

/-!
# Normalizer and centralizer of the torus and the centre of a Chevalley group

Using the Bruhat decomposition, the opposite-unipotent intersection theorems, and the longest
Weyl-element action on the positive unipotent subgroup, we determine:

* over any infinite field `K`, the normalizer/centralizer quotient of the actual torus `T(K)` inside
  `D.extendedElementarySubgroup K`
  (`ChevalleyDatum.normalizerTorusQuotientMulEquiv : N_E / C_E ≃* W`);
* over every field `K` (including finite fields such as `𝔽₂`), the full centre of any
  intermediate subgroup `D.elementarySubgroup K ≤ H ≤ D.extendedElementarySubgroup K`, and in
  particular of `D.extendedElementarySubgroup K`, `D.elementarySubgroup K`, and
  `(t.scChevalleyDatum ht).elementarySubgroup K`.

## Main definitions

* `ChevalleyDatum.normalizerTorusQuotientMulEquiv`: over any infinite field `K`,
  `N_{E_D(K)}(T(K)) / C_{E_D(K)}(T(K)) ≃* W`.
* `ChevalleyDatum.centerEquivOfLe`: over every field `K`, for any intermediate subgroup
  `D.elementarySubgroup K ≤ H ≤ D.extendedElementarySubgroup K` containing the toral centralizer,
  `AddChar (Λ(D) / Q) Kˣ ≃* Subgroup.center H`.
* `ChevalleyDatum.centerExtendedElementarySubgroupEquiv`: over every field `K` and for every
  Chevalley datum `D`, the centre of `D.extendedElementarySubgroup K` is canonically
  isomorphic to `AddChar (Λ(D) / Q) Kˣ`.
* `ChevalleyDatum.centerElementarySubgroupEquivOfLe`: specialization of `centerEquivOfLe` to
  `D.elementarySubgroup K` when it contains the toral centralizer.
* `DynkinType.scChevalleyDatumCenterElementarySubgroupEquiv`: for the simply connected datum
  over every field `K`, the extended and elementary subgroups coincide and the centre of
  `(t.scChevalleyDatum ht).elementarySubgroup K` is canonically isomorphic to
  `AddChar (P / Q) Kˣ`.

## Main results

* `ChevalleyDatum.positivePoints_inf_normalizer_range_torusPoints_le_centralizer`: over any
  commutative ring, any positive point normalizing `T(A)` centralizes it.
* `ChevalleyDatum.normalizer_range_torusPoints_subgroupOf_extendedElementarySubgroup` and
  `ChevalleyDatum.centralizer_range_torusPoints_subgroupOf_extendedElementarySubgroup`:
  subgroup-inside-`E_D(K)` normalizer and centralizer identifications over infinite fields.
* `ChevalleyDatum.mem_borelSubgroup_of_mem_extendedElementarySubgroup_of_commute_simpleRoot`,
  `ChevalleyDatum.mem_range_torusPoints_of_mem_borelSubgroup_of_commute_weylElement`, and
  `ChevalleyDatum.mem_range_torusPoints_of_mem_extendedElementarySubgroup_of_commute`:
  commutation with `x_{αᵢ}(1)` and `n_{αᵢ}(1)` forces membership in `B(K)` and `T(K)`.
* `ChevalleyDatum.extendedElementarySubgroup_inf_centralizer_elementarySubgroup`: over every
  field `K`, every element of `D.extendedElementarySubgroup K` centralizing
  `D.elementarySubgroup K` lies in the actual torus `T(K)` and centralizes
  `D.rootTorusSubgroup K`.
* `ChevalleyDatum.center_eq_subgroupOf_of_le`, `ChevalleyDatum.mem_center_iff_of_le`, and
  `ChevalleyDatum.center_eq_bot_of_le`: centre restriction, membership criterion, and
  trivial-centre criterion for any intermediate subgroup `E(K) ≤ H ≤ E_D(K)`.
* `ChevalleyDatum.mem_center_extendedElementarySubgroup_iff`,
  `ChevalleyDatum.mem_center_elementarySubgroup_iff`,
  `ChevalleyDatum.torusPoints_mem_center_extendedElementarySubgroup_iff`, and
  `ChevalleyDatum.torusPoints_mem_center_elementarySubgroup_iff`: centre membership criteria for
  arbitrary points and `@[simp]` criteria for torus points in terms of coordinate root characters.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 28 and Corollary 1 to
  Theorem 4′.
* R. W. Carter, *Simple Groups of Lie Type*, §§7.1–7.2 and §8.4.
-/

public section

open Multiplicative TauCeti.UniversalEnvelopingAlgebra

namespace TauCeti.DynkinType

noncomputable section

universe v

variable {t : DynkinType} {ht : t.Valid}

namespace ChevalleyDatum

variable (D : ChevalleyDatum t ht)

/-! ### Normalizer and centralizer of the torus -/

/-- Over any commutative ring, any positive point normalizing the actual torus `T_D(A)`
centralizes it. -/
theorem positivePoints_inf_normalizer_range_torusPoints_le_centralizer
    (A : Type v) [CommRing A] :
    D.positivePoints A ⊓ Subgroup.normalizer (D.torusPoints A).range ≤
      Subgroup.centralizer (Set.range (D.torusPoints A)) := by
  rintro u ⟨hu, hu_norm⟩
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨s, rfl⟩
  let t₀ := D.torusPoints A s
  have hT : u * t₀ * u⁻¹ * t₀⁻¹ ∈ (D.torusPoints A).range :=
    mul_mem ((Subgroup.mem_normalizer_iff.mp hu_norm t₀).mp ⟨s, rfl⟩) (inv_mem ⟨s, rfl⟩)
  have hU : u * t₀ * u⁻¹ * t₀⁻¹ ∈ D.positivePoints A := by
    have ht_pos : t₀ * u⁻¹ * t₀⁻¹ ∈ D.positivePoints A :=
      (Subgroup.mem_normalizer_iff.mp
        (D.range_torusPoints_le_normalizer_positivePoints A ⟨s, rfl⟩) u⁻¹).mp (inv_mem hu)
    rw [mul_assoc u, mul_assoc u]
    exact mul_mem hu ht_pos
  have hbot : u * t₀ * u⁻¹ * t₀⁻¹ = 1 := by
    rw [← Subgroup.mem_bot, ← D.positivePoints_inf_range_torusPoints_eq_bot A]
    exact ⟨hU, hT⟩
  exact (mul_inv_eq_one.mp (by simpa only [mul_inv_rev, mul_assoc] using hbot)).symm

section InfiniteField

variable (K : Type v) [Field K] [Infinite K]

local notation "T_E" =>
  Subgroup.subgroupOf (MonoidHom.range (D.torusPoints K)) (D.extendedElementarySubgroup K)
local notation "N_E" =>
  Subgroup.normalizer
    ((T_E : Subgroup (D.extendedElementarySubgroup K)) : Set (D.extendedElementarySubgroup K))
local notation "C_E" =>
  Subgroup.centralizer
    ((T_E : Subgroup (D.extendedElementarySubgroup K)) : Set (D.extendedElementarySubgroup K))

/-- Over an infinite field, the normalizer of the actual torus inside the extended elementary
group `D.extendedElementarySubgroup K` is `D.weylSubgroup K`. -/
@[simp]
theorem normalizer_range_torusPoints_subgroupOf_extendedElementarySubgroup :
    N_E = (D.weylSubgroup K).subgroupOf (D.extendedElementarySubgroup K) := by
  rw [← Subgroup.subgroupOf_normalizer_eq (D.range_torusPoints_le_extendedElementarySubgroup K)]
  ext ⟨x, hx⟩
  have h := SetLike.ext_iff.mp (D.extendedElementarySubgroup_inf_normalizer_range_torusPoints K) x
  simp only [Subgroup.mem_inf, hx, true_and] at h
  simpa only [Subgroup.mem_subgroupOf, MonoidHom.coe_range] using h

/-- Over an infinite field, the actual torus is self-centralizing inside
`D.extendedElementarySubgroup K`. -/
@[simp]
theorem centralizer_range_torusPoints_subgroupOf_extendedElementarySubgroup :
    C_E = T_E := by
  ext ⟨g, hgE⟩
  simp only [Subgroup.mem_centralizer_iff, SetLike.mem_coe, Subgroup.mem_subgroupOf,
    MonoidHom.mem_range]
  constructor
  · intro hc
    have hgc : g ∈ Subgroup.centralizer (Set.range (D.torusPoints K)) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨s, rfl⟩
      exact congrArg Subtype.val
        (hc ⟨D.torusPoints K s, D.torusPoints_mem_extendedElementarySubgroup K s⟩ ⟨s, rfl⟩)
    have hmem : g ∈ D.extendedElementarySubgroup K ⊓
        Subgroup.centralizer (Set.range (D.torusPoints K)) :=
      Subgroup.mem_inf.mpr ⟨hgE, hgc⟩
    rwa [D.extendedElementarySubgroup_inf_centralizer_range_torusPoints K] at hmem
  · rintro ⟨s, hs⟩ ⟨x, hxE⟩ ⟨r, hr⟩
    dsimp only at hr
    exact Subtype.ext (by
      simpa [← hr, ← hs] using ((Commute.all r s).map (D.torusPoints K)).eq)

private noncomputable def normalizerEquivWeylSubgroup :
    N_E ≃* D.weylSubgroup K :=
  (MulEquiv.subgroupCongr
    (D.normalizer_range_torusPoints_subgroupOf_extendedElementarySubgroup K)).trans
    (Subgroup.subgroupOfEquivOfLe (D.weylSubgroup_le_extendedElementarySubgroup K))

@[local simp]
private theorem normalizerEquivWeylSubgroup_apply (n : N_E) :
    D.normalizerEquivWeylSubgroup K n =
      ⟨(n : D.extendedElementarySubgroup K),
        (D.normalizer_range_torusPoints_subgroupOf_extendedElementarySubgroup K).le n.property⟩ :=
  rfl

private theorem map_range_torusPoints_subgroupOf_normalizerEquiv :
    (Subgroup.subgroupOf T_E N_E).map ((D.normalizerEquivWeylSubgroup K : _ ≃* _) : _ →* _) =
      ((D.torusPoints K).range).subgroupOf (D.weylSubgroup K) := by
  ext n
  rw [← MulEquiv.toMonoidHom_eq_coe, Subgroup.mem_map_equiv]
  simp [Subgroup.mem_subgroupOf, normalizerEquivWeylSubgroup, MulEquiv.subgroupCongr_symm_apply]

/-- Over an infinite field, the normalizer of `T_D(K)` inside `E_D(K)` modulo its centralizer is
canonically isomorphic to the root datum's Weyl group. -/
noncomputable def normalizerTorusQuotientMulEquiv :
    (N_E : Subgroup (D.extendedElementarySubgroup K)) ⧸ (Subgroup.subgroupOf C_E N_E) ≃*
      (t.simplyConnectedRootDatum ht).weylGroup :=
  (QuotientGroup.quotientMulEquivOfEq (by
    rw [D.centralizer_range_torusPoints_subgroupOf_extendedElementarySubgroup K])).trans
    ((QuotientGroup.congr (Subgroup.subgroupOf T_E N_E)
        (((D.torusPoints K).range).subgroupOf (D.weylSubgroup K))
        (D.normalizerEquivWeylSubgroup K)
        (D.map_range_torusPoints_subgroupOf_normalizerEquiv K)).trans
      (D.weylSubgroupQuotientMulEquiv K))

/-- Evaluating `normalizerTorusQuotientMulEquiv` on the class of a normalizer element returns its
Weyl projection. -/
@[simp]
theorem normalizerTorusQuotientMulEquiv_mk (n : N_E) :
    D.normalizerTorusQuotientMulEquiv K (QuotientGroup.mk n) =
      D.weylProjection K
        ⟨(n : D.extendedElementarySubgroup K),
          (D.normalizer_range_torusPoints_subgroupOf_extendedElementarySubgroup K).le
            n.property⟩ := by
  simp [normalizerTorusQuotientMulEquiv]

end InfiniteField

/-! ### The centre over an arbitrary field -/

variable (K : Type v) [Field K]

/-- Over any field, an element of `D.extendedElementarySubgroup K` that commutes with each simple
root element `x_{αᵢ}(1)` belongs to `D.borelSubgroup K`. -/
theorem mem_borelSubgroup_of_mem_extendedElementarySubgroup_of_commute_simpleRoot
    {g : D.points K} (hg : g ∈ D.extendedElementarySubgroup K)
    (hcomm : ∀ i : Fin t.rank,
      Commute g (D.rootSubgroupPoints (t.simpleIndex ht i) K (ofAdd 1))) :
    g ∈ D.borelSubgroup K := by
  let _ := t.isReduced_simplyConnectedRootDatum ht
  obtain ⟨n, u, b, hu, hb, hprod⟩ := D.exists_bruhatNormalForm K hg
  have hw : D.weylProjection K n = 1 := by
    by_contra hwne
    obtain ⟨α, hαsupp, hαinv⟩ := exists_mem_support_mem_inversions_of_ne_one
      (P := t.simplyConnectedRootDatum ht) (b := t.simplyConnectedBase ht) (inv_ne_one.mpr hwne)
    obtain ⟨i, rfl⟩ := exists_simpleIndex_eq_of_mem_support (by rwa [support_rationalBase])
    let x := D.rootSubgroupPoints (t.simpleIndex ht i) K (ofAdd 1)
    have hx_inv : x ∈ D.inversionPoints K (D.weylProjection K n) :=
      D.rootSubgroupPoints_mem_inversionPoints K hαinv (ofAdd 1)
    have hx_B : x ∈ D.borelSubgroup K :=
      D.positivePoints_le_borelSubgroup K
        (D.rootSubgroupPoints_mem_positivePoints K (simpleIndex_mem_posRoots i) (ofAdd 1))
    have hmul : (x * u) * (n : D.points K) * b = u * (n : D.points K) * (b * x) := by
      calc
        (x * u) * (n : D.points K) * b = x * (u * (n : D.points K) * b) := by group
        _ = x * g := by rw [hprod]
        _ = g * x := (hcomm i).symm.eq
        _ = u * (n : D.points K) * (b * x) := by rw [← hprod]; group
    have hle := D.inversionPoints_le_map_negativePoints_conj K n
    have hxu_eq := (D.eq_and_eq_of_mem_map_negativePoints_conj_of_mul_eq K
      (hle (mul_mem hx_inv hu)) (hle hu) hb (mul_mem hb hx_B) hmul).1
    exact D.rootSubgroupPoints_ofAdd_one_ne_one K (t.simpleIndex ht i)
      (mul_right_cancel (by simpa only [one_mul] using hxu_eq))
  rw [hw, D.inversionPoints_one K, Subgroup.mem_bot] at hu
  have hnT : (n : D.points K) ∈ (D.torusPoints K).range :=
    (D.weylProjection_eq_one_iff_mem_range_torusPoints K n).mp hw
  rw [← hprod, hu, one_mul]
  exact mul_mem (D.range_torusPoints_le_borelSubgroup K hnT) hb

/-- Over any field, an element of `D.borelSubgroup K` that commutes with each pinned simple Weyl
representative `n_{αᵢ}(1)` lies in the actual torus `(D.torusPoints K).range`. -/
theorem mem_range_torusPoints_of_mem_borelSubgroup_of_commute_weylElement
    {g : D.points K} (hg : g ∈ D.borelSubgroup K)
    (hcomm : ∀ i : Fin t.rank, Commute g (D.weylElement (t.simpleIndex ht i) K 1)) :
    g ∈ (D.torusPoints K).range := by
  let _ := t.isReduced_simplyConnectedRootDatum ht
  obtain ⟨u, hu, s, rfl⟩ := (D.mem_borelSubgroup_iff K).mp hg
  let w₀ := longestElement (t.simplyConnectedRootDatum ht) (t.simplyConnectedBase ht)
  obtain ⟨l, hl⟩ := t.simplyConnectedWeylWordProd_surjective ht w₀
  let n₀ : D.weylSubgroup K :=
    ⟨(l.map fun i => D.weylElement (t.simpleIndex ht i) K 1).prod,
      D.list_prod_map_weylElement_mem_weylSubgroup K l⟩
  have hn₀_proj : D.weylProjection K n₀ = w₀ := by
    rw [D.weylProjection_list_prod K l, hl]
  have hcomm_n₀ : Commute (u * D.torusPoints K s) (n₀ : D.points K) :=
    Commute.list_prod_right _ _ fun x hx => by
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
      exact hcomm i
  have hu_neg : (n₀ : D.points K) * u * (n₀ : D.points K)⁻¹ ∈ D.negativePoints K := by
    rw [← D.map_positivePoints_conj_eq_negativePoints K n₀
      (by rw [hn₀_proj, inversions_longestElement])]
    exact ⟨u, hu, rfl⟩
  obtain ⟨s', hs'⟩ := (Subgroup.mem_normalizer_iff.mp
    (D.weylSubgroup_le_normalizer_range_torusPoints K n₀.property) (D.torusPoints K s)).mp
    ⟨s, rfl⟩
  have hu_eq : u =
      ((n₀ : D.points K) * u * (n₀ : D.points K)⁻¹) *
        (D.torusPoints K s' * (D.torusPoints K s)⁻¹) := by
    rw [hs']
    calc
      u = (u * D.torusPoints K s) * (D.torusPoints K s)⁻¹ := by group
      _ = ((n₀ : D.points K) * (u * D.torusPoints K s) * (n₀ : D.points K)⁻¹) *
            (D.torusPoints K s)⁻¹ := by rw [hcomm_n₀.symm.eq]; group
      _ = _ := by group
  have hu_in_opp : u ∈ D.negativePoints K ⊔ (D.torusPoints K).range := by
    rw [hu_eq]
    exact mul_mem (Subgroup.mem_sup_left hu_neg)
      (Subgroup.mem_sup_right (mul_mem ⟨s', rfl⟩ (inv_mem ⟨s, rfl⟩)))
  have hu1 : u = 1 := by
    rw [← Subgroup.mem_bot, ← D.positivePoints_inf_negativePoints_sup_range_torusPoints_eq_bot K]
    exact ⟨hu, hu_in_opp⟩
  rw [hu1, one_mul]
  exact ⟨s, rfl⟩

/-- Over any field, an element of `D.extendedElementarySubgroup K` commuting with the simple root
elements `x_{αᵢ}(1)` and simple Weyl elements `n_{αᵢ}(1)` belongs to the actual torus
`T_D(K)`. -/
theorem mem_range_torusPoints_of_mem_extendedElementarySubgroup_of_commute
    {g : D.points K} (hg : g ∈ D.extendedElementarySubgroup K)
    (hroot : ∀ i : Fin t.rank,
      Commute g (D.rootSubgroupPoints (t.simpleIndex ht i) K (ofAdd 1)))
    (hweyl : ∀ i : Fin t.rank, Commute g (D.weylElement (t.simpleIndex ht i) K 1)) :
    g ∈ (D.torusPoints K).range :=
  D.mem_range_torusPoints_of_mem_borelSubgroup_of_commute_weylElement K
    (D.mem_borelSubgroup_of_mem_extendedElementarySubgroup_of_commute_simpleRoot K hg hroot) hweyl

/-- Over every field `K`, every element of `D.extendedElementarySubgroup K` centralizing
`D.elementarySubgroup K` lies in the actual character-lattice torus and centralizes the full
root-and-torus subgroup. -/
theorem extendedElementarySubgroup_inf_centralizer_elementarySubgroup :
    D.extendedElementarySubgroup K ⊓
        Subgroup.centralizer (D.elementarySubgroup K : Set (D.points K)) =
      (D.torusPoints K).range ⊓
        Subgroup.centralizer (D.rootTorusSubgroup K : Set (D.points K)) := by
  let _ := t.isReduced_simplyConnectedRootDatum ht
  apply le_antisymm
  · rintro g ⟨hgE, hgC⟩
    have hle : D.positivePoints K ≤ D.elementarySubgroup K :=
      D.positivePoints_le_iff.mpr fun _ _ u => D.rootSubgroupPoints_mem_elementarySubgroup K _ u
    have hgN : g ∈ Subgroup.normalizer (D.positivePoints K : Set (D.points K)) :=
      Subgroup.centralizer_le_normalizer _ (Subgroup.centralizer_le hle hgC)
    have hgB : g ∈ D.borelSubgroup K :=
      (D.extendedElementarySubgroup_inf_normalizer_positivePoints K).le ⟨hgE, hgN⟩
    let w₀ := longestElement (t.simplyConnectedRootDatum ht) (t.simplyConnectedBase ht)
    obtain ⟨n₀, hn₀E, hn₀w⟩ := D.exists_mem_elementarySubgroup_weylProjection_eq K w₀
    have hcomm : Commute (n₀ : D.points K) g :=
      Subgroup.mem_centralizer_iff.mp hgC n₀ hn₀E
    have hgConj : g ∈ (D.borelSubgroup K).map (MulAut.conj (n₀ : D.points K)).toMonoidHom :=
      ⟨g, hgB, by simp [MulAut.conj_apply, mul_inv_eq_iff_eq_mul.mpr hcomm.eq]⟩
    obtain ⟨s, rfl⟩ :=
      (D.borelSubgroup_inf_map_borelSubgroup_conj_eq_range_torusPoints K n₀
        (hn₀w ▸ inversions_longestElement _ _)).le ⟨hgB, hgConj⟩
    refine ⟨⟨s, rfl⟩, ?_⟩
    rw [← D.extendedElementarySubgroup_eq_rootTorusSubgroup K, D.extendedElementarySubgroup_def K,
      Subgroup.sup_eq_closure, Subgroup.centralizer_closure]
    exact (Set.centralizer_union
      (S := (D.elementarySubgroup K : Set (D.points K)))
      (T := ((D.torusPoints K).range : Set (D.points K)))).ge
      ⟨hgC, Subgroup.le_centralizer _ ⟨s, rfl⟩⟩
  · refine le_inf (inf_le_left.trans ?_) (inf_le_right.trans (Subgroup.centralizer_le ?_))
    · rintro _ ⟨s, rfl⟩
      exact D.torusPoints_mem_extendedElementarySubgroup K s
    · rw [← D.extendedElementarySubgroup_eq_rootTorusSubgroup K]
      exact D.elementarySubgroup_le_extendedElementarySubgroup K

/-- Over any field, every element of `D.extendedElementarySubgroup K` centralizing the elementary
subgroup `D.elementarySubgroup K` lies in the actual torus `(D.torusPoints K).range`. -/
theorem extendedElementarySubgroup_inf_centralizer_elementarySubgroup_le_range_torusPoints :
    D.extendedElementarySubgroup K ⊓
        Subgroup.centralizer (D.elementarySubgroup K : Set (D.points K)) ≤
      (D.torusPoints K).range :=
  (D.extendedElementarySubgroup_inf_centralizer_elementarySubgroup K).le.trans inf_le_left

/-- Over any field, for any intermediate subgroup `D.elementarySubgroup K ≤ H ≤ E_D(K)`, the
centralizer of `H` in itself equals its intersection with the toral centralizer of
`D.rootTorusSubgroup K`. -/
theorem inf_centralizer_of_le {H : Subgroup (D.points K)}
    (hEH : D.elementarySubgroup K ≤ H) (hHE : H ≤ D.extendedElementarySubgroup K) :
    H ⊓ Subgroup.centralizer (H : Set (D.points K)) =
      H ⊓ ((D.torusPoints K).range ⊓
        Subgroup.centralizer (D.rootTorusSubgroup K : Set (D.points K))) := by
  apply le_antisymm
  · rw [← D.extendedElementarySubgroup_inf_centralizer_elementarySubgroup K]
    exact le_inf inf_le_left (inf_le_inf hHE (Subgroup.centralizer_le hEH))
  · refine inf_le_inf_left H (inf_le_right.trans (Subgroup.centralizer_le ?_))
    rw [← D.extendedElementarySubgroup_eq_rootTorusSubgroup K]
    exact SetLike.coe_subset_coe.mpr hHE

/-- Over any field, for any intermediate subgroup `D.elementarySubgroup K ≤ H ≤ E_D(K)`, the
centre of `H` (viewed inside `D.points K`) is the part of the toral centralizer of
`D.rootTorusSubgroup K` lying in `H`. -/
theorem map_center_subtype_of_le {H : Subgroup (D.points K)}
    (hEH : D.elementarySubgroup K ≤ H) (hHE : H ≤ D.extendedElementarySubgroup K) :
    (Subgroup.center H).map H.subtype =
      H ⊓ ((D.torusPoints K).range ⊓
        Subgroup.centralizer (D.rootTorusSubgroup K : Set (D.points K))) := by
  rw [Subgroup.map_center_subtype, D.inf_centralizer_of_le K hEH hHE]

/-- Over any field, for any intermediate subgroup `D.elementarySubgroup K ≤ H ≤ E_D(K)`,
`Subgroup.center H` is the restriction of the toral centralizer of `D.rootTorusSubgroup K` to
`H`. -/
theorem center_eq_subgroupOf_of_le {H : Subgroup (D.points K)}
    (hEH : D.elementarySubgroup K ≤ H) (hHE : H ≤ D.extendedElementarySubgroup K) :
    Subgroup.center H =
      ((D.torusPoints K).range ⊓
        Subgroup.centralizer (D.rootTorusSubgroup K : Set (D.points K))).subgroupOf H := by
  apply Subgroup.map_injective H.subtype_injective
  rw [D.map_center_subtype_of_le K hEH hHE, Subgroup.subgroupOf_map_subtype, inf_comm]

/-- Over every field `K`, the centre of `D.extendedElementarySubgroup K` embeds into `D.points K`
as the toral centralizer `T(K) ∩ C(D.rootTorusSubgroup K)`. -/
theorem map_center_extendedElementarySubgroup :
    (Subgroup.center (D.extendedElementarySubgroup K)).map
        (D.extendedElementarySubgroup K).subtype =
      (D.torusPoints K).range ⊓
        Subgroup.centralizer (D.rootTorusSubgroup K : Set (D.points K)) := by
  rw [D.map_center_subtype_of_le K (D.elementarySubgroup_le_extendedElementarySubgroup K) le_rfl,
    inf_eq_right]
  exact inf_le_left.trans (D.range_torusPoints_le_extendedElementarySubgroup K)

/-- Over any field, `Subgroup.center (D.extendedElementarySubgroup K)` is the restriction of the
toral centralizer of `D.rootTorusSubgroup K`. -/
theorem center_extendedElementarySubgroup_eq_subgroupOf :
    Subgroup.center (D.extendedElementarySubgroup K) =
      ((D.torusPoints K).range ⊓
        Subgroup.centralizer (D.rootTorusSubgroup K : Set (D.points K))).subgroupOf
        (D.extendedElementarySubgroup K) :=
  D.center_eq_subgroupOf_of_le K (D.elementarySubgroup_le_extendedElementarySubgroup K) le_rfl

/-- Over every field `K`, the centre of `D.elementarySubgroup K` consists of the elementary
points lying in the toral centralizer `T(K) ∩ C(D.rootTorusSubgroup K)`. -/
theorem map_center_elementarySubgroup :
    (Subgroup.center (D.elementarySubgroup K)).map (D.elementarySubgroup K).subtype =
      D.elementarySubgroup K ⊓
        ((D.torusPoints K).range ⊓
          Subgroup.centralizer (D.rootTorusSubgroup K : Set (D.points K))) :=
  D.map_center_subtype_of_le K le_rfl (D.elementarySubgroup_le_extendedElementarySubgroup K)

/-- Over any field, `Subgroup.center (D.elementarySubgroup K)` is the restriction of the toral
centralizer of `D.rootTorusSubgroup K` to `D.elementarySubgroup K`. -/
theorem center_elementarySubgroup_eq_subgroupOf :
    Subgroup.center (D.elementarySubgroup K) =
      ((D.torusPoints K).range ⊓
        Subgroup.centralizer (D.rootTorusSubgroup K : Set (D.points K))).subgroupOf
        (D.elementarySubgroup K) :=
  D.center_eq_subgroupOf_of_le K le_rfl (D.elementarySubgroup_le_extendedElementarySubgroup K)

/-- Over any field, an element of an intermediate subgroup `D.elementarySubgroup K ≤ H ≤ E_D(K)`
belongs to `Subgroup.center H` if and only if it is a torus point on which every root character is
trivial. -/
theorem mem_center_iff_of_le {H : Subgroup (D.points K)}
    (hEH : D.elementarySubgroup K ≤ H) (hHE : H ≤ D.extendedElementarySubgroup K) (g : H) :
    g ∈ Subgroup.center H ↔
      ∃ s : Fin t.rank → Kˣ, (g : D.points K) = D.torusPoints K s ∧
        ∀ γ, torusCharacter s (D.coordinateRoot γ) = 1 := by
  rw [D.center_eq_subgroupOf_of_le K hEH hHE, Subgroup.mem_subgroupOf]
  exact D.mem_range_torusPoints_inf_centralizer_rootTorusSubgroup_iff _

/-- Over every field `K`, an arbitrary point of `D.extendedElementarySubgroup K` lies in the
centre if and only if its ambient point is `D.torusPoints K s` for some parameter `s` on which
every coordinate root character vanishes. -/
theorem mem_center_extendedElementarySubgroup_iff (g : D.extendedElementarySubgroup K) :
    g ∈ Subgroup.center (D.extendedElementarySubgroup K) ↔
      ∃ s : Fin t.rank → Kˣ,
        (g : D.points K) = D.torusPoints K s ∧
          ∀ γ, torusCharacter s (D.coordinateRoot γ) = 1 :=
  D.mem_center_iff_of_le K (D.elementarySubgroup_le_extendedElementarySubgroup K) le_rfl g

/-- Over every field `K`, an arbitrary point of `D.elementarySubgroup K` lies in the centre if and
only if its ambient point is `D.torusPoints K s` for some parameter `s` on which every coordinate
root character vanishes. -/
theorem mem_center_elementarySubgroup_iff (g : D.elementarySubgroup K) :
    g ∈ Subgroup.center (D.elementarySubgroup K) ↔
      ∃ s : Fin t.rank → Kˣ,
        (g : D.points K) = D.torusPoints K s ∧
          ∀ γ, torusCharacter s (D.coordinateRoot γ) = 1 :=
  D.mem_center_iff_of_le K le_rfl (D.elementarySubgroup_le_extendedElementarySubgroup K) g

/-- Over every field `K`, a torus point of `D.extendedElementarySubgroup K` lies in the centre
if and only if every coordinate root character vanishes on it. -/
@[simp]
theorem torusPoints_mem_center_extendedElementarySubgroup_iff (s : Fin t.rank → Kˣ) :
    (⟨D.torusPoints K s, D.torusPoints_mem_extendedElementarySubgroup K s⟩ :
        D.extendedElementarySubgroup K) ∈
      Subgroup.center (D.extendedElementarySubgroup K) ↔
    ∀ γ, torusCharacter s (D.coordinateRoot γ) = 1 := by
  rw [D.mem_center_extendedElementarySubgroup_iff K]
  simp only [(D.torusPoints_injective K).eq_iff, exists_eq_left']

/-- Over every field `K`, a torus point lying in `D.elementarySubgroup K` lies in the centre of
`D.elementarySubgroup K` if and only if every coordinate root character vanishes on it. -/
@[simp]
theorem torusPoints_mem_center_elementarySubgroup_iff (s : Fin t.rank → Kˣ)
    (hs : D.torusPoints K s ∈ D.elementarySubgroup K) :
    (⟨D.torusPoints K s, hs⟩ : D.elementarySubgroup K) ∈
      Subgroup.center (D.elementarySubgroup K) ↔
    ∀ γ, torusCharacter s (D.coordinateRoot γ) = 1 := by
  rw [D.mem_center_elementarySubgroup_iff K]
  simp only [(D.torusPoints_injective K).eq_iff, exists_eq_left']

private theorem map_center_subtype_eq_of_le {H : Subgroup (D.points K)}
    (hEH : D.elementarySubgroup K ≤ H) (hHE : H ≤ D.extendedElementarySubgroup K)
    (hZ : (D.torusPoints K).range ⊓
        Subgroup.centralizer (D.rootTorusSubgroup K : Set (D.points K)) ≤ H) :
    (Subgroup.center H).map H.subtype =
      (D.torusPoints K).range ⊓
        Subgroup.centralizer (D.rootTorusSubgroup K : Set (D.points K)) := by
  rw [D.map_center_subtype_of_le K hEH hHE, inf_eq_right.mpr hZ]

/-- Over any field, for any intermediate subgroup `D.elementarySubgroup K ≤ H ≤ E_D(K)`
containing the toral centralizer of `D.rootTorusSubgroup K`, `AddChar (Λ(D) / Q) Kˣ` identifies
with `Subgroup.center H`. -/
def centerEquivOfLe {H : Subgroup (D.points K)}
    (hEH : D.elementarySubgroup K ≤ H) (hHE : H ≤ D.extendedElementarySubgroup K)
    (hZ : (D.torusPoints K).range ⊓
        Subgroup.centralizer (D.rootTorusSubgroup K : Set (D.points K)) ≤ H) :
    AddChar (D.weightLattice ⧸
        ((t.simplyConnectedRootDatum ht).rootSpan ℤ).comap D.weightLattice.subtype) Kˣ ≃*
      Subgroup.center H :=
  (AddChar.congrLeft D.weightLatticeQuotientEquiv.symm.toAddEquiv).trans
    ((D.torusInfCentralizerRootTorusSubgroupEquiv K).trans
      (Subgroup.centerEquivOfMapSubtypeEq (D.map_center_subtype_eq_of_le K hEH hHE hZ)))

/-- Evaluating `centerEquivOfLe` recovers the corresponding torus point inside `H`. -/
@[simp]
theorem coe_centerEquivOfLe {H : Subgroup (D.points K)}
    (hEH : D.elementarySubgroup K ≤ H) (hHE : H ≤ D.extendedElementarySubgroup K)
    (hZ : (D.torusPoints K).range ⊓
        Subgroup.centralizer (D.rootTorusSubgroup K : Set (D.points K)) ≤ H)
    (χ : AddChar (D.weightLattice ⧸
        ((t.simplyConnectedRootDatum ht).rootSpan ℤ).comap D.weightLattice.subtype) Kˣ) :
    ((D.centerEquivOfLe K hEH hHE hZ χ : H) : D.points K) =
      D.torusPoints K (fun i => χ (Submodule.Quotient.mk (D.weightLatticeBasis i))) := by
  simp only [centerEquivOfLe, MulEquiv.trans_apply, LinearEquiv.coe_toAddEquiv,
    Subgroup.coe_centerEquivOfMapSubtypeEq, D.coe_torusInfCentralizerRootTorusSubgroupEquiv K]
  refine congrArg (D.torusPoints K) (funext fun i => ?_)
  have hsingle : D.weightLatticeBasis.equivFun.symm (Pi.single i 1) = D.weightLatticeBasis i := by
    rw [LinearEquiv.symm_apply_eq]
    ext j
    simp [Pi.single_apply, eq_comm]
  simp [quotientCharTorusPoint_apply, hsingle]

/-- The inverse equivalence `centerEquivOfLe` evaluates a quotient class on the torus parameter of
the given central element. -/
@[simp]
theorem centerEquivOfLe_symm_apply_mk {H : Subgroup (D.points K)}
    (hEH : D.elementarySubgroup K ≤ H) (hHE : H ≤ D.extendedElementarySubgroup K)
    (hZ : (D.torusPoints K).range ⊓
        Subgroup.centralizer (D.rootTorusSubgroup K : Set (D.points K)) ≤ H)
    (s : Fin t.rank → Kˣ) (hsH : D.torusPoints K s ∈ H)
    (hg : (⟨D.torusPoints K s, hsH⟩ : H) ∈ Subgroup.center H) (μ : D.weightLattice) :
    (D.centerEquivOfLe K hEH hHE hZ).symm ⟨⟨D.torusPoints K s, hsH⟩, hg⟩
        (Submodule.Quotient.mk μ) =
      torusCharacter s (D.weightLatticeBasis.repr μ) := by
  simp [centerEquivOfLe]

/-- **Centre of an extended elementary Chevalley group.** Over every field `K` and for every
Chevalley datum `D`, unit-valued characters of `Λ(D) / Q` canonically identify with
`Subgroup.center (D.extendedElementarySubgroup K)`. -/
def centerExtendedElementarySubgroupEquiv :
    AddChar (D.weightLattice ⧸
        ((t.simplyConnectedRootDatum ht).rootSpan ℤ).comap D.weightLattice.subtype) Kˣ ≃*
      Subgroup.center (D.extendedElementarySubgroup K) :=
  D.centerEquivOfLe K (D.elementarySubgroup_le_extendedElementarySubgroup K) le_rfl
    (inf_le_left.trans (D.range_torusPoints_le_extendedElementarySubgroup K))

/-- The forward equivalence sends a character of `Λ(D) / Q` to the torus point whose
coordinates in `D.weightLatticeBasis` are its values on the basis classes. -/
@[simp]
theorem coe_centerExtendedElementarySubgroupEquiv
    (χ : AddChar (D.weightLattice ⧸
        ((t.simplyConnectedRootDatum ht).rootSpan ℤ).comap D.weightLattice.subtype) Kˣ) :
    ((D.centerExtendedElementarySubgroupEquiv K χ : D.extendedElementarySubgroup K) :
        D.points K) =
      D.torusPoints K (fun i => χ (Submodule.Quotient.mk (D.weightLatticeBasis i))) :=
  D.coe_centerEquivOfLe K (D.elementarySubgroup_le_extendedElementarySubgroup K) le_rfl
    (inf_le_left.trans (D.range_torusPoints_le_extendedElementarySubgroup K)) χ

/-- The inverse equivalence recovers the character on a quotient class in `Λ(D) / Q` by
evaluating the torus parameter in the chosen basis. -/
@[simp]
theorem centerExtendedElementarySubgroupEquiv_symm_apply_mk
    (s : Fin t.rank → Kˣ)
    (hg : (⟨D.torusPoints K s, D.torusPoints_mem_extendedElementarySubgroup K s⟩ :
        D.extendedElementarySubgroup K) ∈ Subgroup.center (D.extendedElementarySubgroup K))
    (μ : D.weightLattice) :
    (D.centerExtendedElementarySubgroupEquiv K).symm
      ⟨⟨D.torusPoints K s, D.torusPoints_mem_extendedElementarySubgroup K s⟩, hg⟩
      (Submodule.Quotient.mk μ) = torusCharacter s (D.weightLatticeBasis.repr μ) :=
  D.centerEquivOfLe_symm_apply_mk K (D.elementarySubgroup_le_extendedElementarySubgroup K) le_rfl
    (inf_le_left.trans (D.range_torusPoints_le_extendedElementarySubgroup K)) s
    (D.torusPoints_mem_extendedElementarySubgroup K s) hg μ

/-- Over any field, when the toral centralizer of `D.rootTorusSubgroup K` lies inside
`D.elementarySubgroup K`, `AddChar (Λ(D) / Q) Kˣ` identifies with
`Subgroup.center (D.elementarySubgroup K)`. -/
def centerElementarySubgroupEquivOfLe
    (hZ : (D.torusPoints K).range ⊓
        Subgroup.centralizer (D.rootTorusSubgroup K : Set (D.points K)) ≤
      D.elementarySubgroup K) :
    AddChar (D.weightLattice ⧸
        ((t.simplyConnectedRootDatum ht).rootSpan ℤ).comap D.weightLattice.subtype) Kˣ ≃*
      Subgroup.center (D.elementarySubgroup K) :=
  D.centerEquivOfLe K le_rfl (D.elementarySubgroup_le_extendedElementarySubgroup K) hZ

/-- Evaluating `centerElementarySubgroupEquivOfLe` recovers the same torus coordinates. -/
@[simp]
theorem coe_centerElementarySubgroupEquivOfLe
    (hZ : (D.torusPoints K).range ⊓
        Subgroup.centralizer (D.rootTorusSubgroup K : Set (D.points K)) ≤
      D.elementarySubgroup K)
    (χ : AddChar (D.weightLattice ⧸
        ((t.simplyConnectedRootDatum ht).rootSpan ℤ).comap D.weightLattice.subtype) Kˣ) :
    ((D.centerElementarySubgroupEquivOfLe K hZ χ : D.elementarySubgroup K) : D.points K) =
      D.torusPoints K (fun i => χ (Submodule.Quotient.mk (D.weightLatticeBasis i))) :=
  D.coe_centerEquivOfLe K le_rfl (D.elementarySubgroup_le_extendedElementarySubgroup K) hZ χ

/-- The inverse equivalence `centerElementarySubgroupEquivOfLe` evaluates a quotient class on the
torus parameter of the given central element. -/
@[simp]
theorem centerElementarySubgroupEquivOfLe_symm_apply_mk
    (hZ : (D.torusPoints K).range ⊓
        Subgroup.centralizer (D.rootTorusSubgroup K : Set (D.points K)) ≤
      D.elementarySubgroup K)
    (s : Fin t.rank → Kˣ)
    (hsE : D.torusPoints K s ∈ D.elementarySubgroup K)
    (hg : (⟨D.torusPoints K s, hsE⟩ : D.elementarySubgroup K) ∈
        Subgroup.center (D.elementarySubgroup K))
    (μ : D.weightLattice) :
    (D.centerElementarySubgroupEquivOfLe K hZ).symm
        ⟨⟨D.torusPoints K s, hsE⟩, hg⟩
        (Submodule.Quotient.mk μ) =
      torusCharacter s (D.weightLatticeBasis.repr μ) :=
  D.centerEquivOfLe_symm_apply_mk K le_rfl (D.elementarySubgroup_le_extendedElementarySubgroup K)
    hZ s hsE hg μ

/-- Over any field, if the coordinate roots span `Fin t.rank → ℤ` (for instance, for an adjoint
Chevalley datum), any intermediate subgroup `D.elementarySubgroup K ≤ H ≤ E_D(K)` has trivial
centre. -/
theorem center_eq_bot_of_le {H : Subgroup (D.points K)}
    (hEH : D.elementarySubgroup K ≤ H) (hHE : H ≤ D.extendedElementarySubgroup K)
    (hspan : Submodule.span ℤ (Set.range D.coordinateRoot) = ⊤) :
    Subgroup.center H = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [D.mem_center_iff_of_le K hEH hHE] at hg
  obtain ⟨s, hgs, hroot⟩ := hg
  have hs_ann : s ∈ torusAnnihilator (R := K) (Submodule.span ℤ (Set.range D.coordinateRoot)) :=
    (mem_torusAnnihilator_span_iff D.coordinateRoot s).mpr hroot
  rw [hspan] at hs_ann
  have hs1 : s = 1 := by
    funext i
    simpa only [torusCharacter_single, zpow_one, Pi.one_apply] using
      (mem_torusAnnihilator ⊤ s).mp hs_ann (Pi.single i 1) trivial
  apply Subgroup.mem_bot.mpr
  apply Subtype.ext
  rw [hgs, hs1, map_one, Subgroup.coe_one]

/-- Over any field, if the coordinate roots span `Fin t.rank → ℤ` (for instance, for an adjoint
Chevalley datum), `D.extendedElementarySubgroup K` has trivial centre. -/
theorem center_extendedElementarySubgroup_eq_bot
    (hspan : Submodule.span ℤ (Set.range D.coordinateRoot) = ⊤) :
    Subgroup.center (D.extendedElementarySubgroup K) = ⊥ :=
  D.center_eq_bot_of_le K (D.elementarySubgroup_le_extendedElementarySubgroup K) le_rfl hspan

end ChevalleyDatum

/-! ### Simply connected Chevalley groups -/

section SimplyConnected

variable (t ht)

section InfiniteField

variable (K : Type v) [Field K] [Infinite K]

/-- Over an infinite field, the normalizer of the torus inside the simply connected elementary
Chevalley group is its Weyl subgroup. -/
theorem scChevalleyDatum_elementarySubgroup_inf_normalizer_range_torusPoints :
    (t.scChevalleyDatum ht).elementarySubgroup K ⊓
        Subgroup.normalizer (Set.range ((t.scChevalleyDatum ht).torusPoints K)) =
      (t.scChevalleyDatum ht).weylSubgroup K := by
  rw [← t.scChevalleyDatum_extendedElementarySubgroup ht K]
  exact (t.scChevalleyDatum ht).extendedElementarySubgroup_inf_normalizer_range_torusPoints K

/-- Over an infinite field, the torus of the simply connected Chevalley group is self-centralizing
inside its elementary group. -/
theorem scChevalleyDatum_elementarySubgroup_inf_centralizer_range_torusPoints :
    (t.scChevalleyDatum ht).elementarySubgroup K ⊓
        Subgroup.centralizer (Set.range ((t.scChevalleyDatum ht).torusPoints K)) =
      ((t.scChevalleyDatum ht).torusPoints K).range := by
  rw [← t.scChevalleyDatum_extendedElementarySubgroup ht K]
  exact (t.scChevalleyDatum ht).extendedElementarySubgroup_inf_centralizer_range_torusPoints K

end InfiniteField

section Field

variable (K : Type v) [Field K]

/-- Over any field, the centralizer of the simply connected elementary Chevalley group inside
itself, viewed as a subgroup of `(t.scChevalleyDatum ht).points K`, is the toral centralizer of
`(t.scChevalleyDatum ht).rootTorusSubgroup K`. -/
theorem scChevalleyDatum_elementarySubgroup_inf_centralizer_elementarySubgroup :
    (t.scChevalleyDatum ht).elementarySubgroup K ⊓
        Subgroup.centralizer
          ((t.scChevalleyDatum ht).elementarySubgroup K :
            Set ((t.scChevalleyDatum ht).points K)) =
      ((t.scChevalleyDatum ht).torusPoints K).range ⊓
        Subgroup.centralizer
          ((t.scChevalleyDatum ht).rootTorusSubgroup K :
            Set ((t.scChevalleyDatum ht).points K)) := by
  nth_rw 1 [← t.scChevalleyDatum_extendedElementarySubgroup ht K]
  exact (t.scChevalleyDatum ht).extendedElementarySubgroup_inf_centralizer_elementarySubgroup K

/-- Over any field, a simply connected torus point belongs to the centre of the simply connected
elementary Chevalley group if and only if every root character evaluates to `1` on it. -/
theorem scChevalleyDatum_torusPoints_mem_center_elementarySubgroup_iff (s : Fin t.rank → Kˣ) :
    (⟨(t.scChevalleyDatum ht).torusPoints K s,
        t.scChevalleyDatum_torusPoints_mem_elementarySubgroup ht K s⟩ :
        (t.scChevalleyDatum ht).elementarySubgroup K) ∈
      Subgroup.center ((t.scChevalleyDatum ht).elementarySubgroup K) ↔
    ∀ γ, torusCharacter s ((t.simplyConnectedRootDatum ht).root γ) = 1 := by
  simpa only [scChevalleyDatum_coordinateRoot] using
    (t.scChevalleyDatum ht).torusPoints_mem_center_elementarySubgroup_iff K s
      (t.scChevalleyDatum_torusPoints_mem_elementarySubgroup ht K s)

/-- Over any field, an element of `(t.scChevalleyDatum ht).elementarySubgroup K` belongs to the
centre if and only if it is a torus point on which every root character is trivial. -/
theorem mem_center_scChevalleyDatum_elementarySubgroup_iff
    (g : (t.scChevalleyDatum ht).elementarySubgroup K) :
    g ∈ Subgroup.center ((t.scChevalleyDatum ht).elementarySubgroup K) ↔
      ∃ s : Fin t.rank → Kˣ, (g : (t.scChevalleyDatum ht).points K) =
          (t.scChevalleyDatum ht).torusPoints K s ∧
        ∀ γ, torusCharacter s ((t.simplyConnectedRootDatum ht).root γ) = 1 := by
  simpa only [scChevalleyDatum_coordinateRoot] using
    (t.scChevalleyDatum ht).mem_center_elementarySubgroup_iff K g

/-- Over every field `K`, the centre of the simply connected elementary Chevalley group embeds
into the ambient points as the toral centralizer. -/
theorem map_center_scChevalleyDatum_elementarySubgroup :
    (Subgroup.center ((t.scChevalleyDatum ht).elementarySubgroup K)).map
        ((t.scChevalleyDatum ht).elementarySubgroup K).subtype =
      ((t.scChevalleyDatum ht).torusPoints K).range ⊓
        Subgroup.centralizer ((t.scChevalleyDatum ht).rootTorusSubgroup K :
          Set ((t.scChevalleyDatum ht).points K)) := by
  rw [← t.scChevalleyDatum_extendedElementarySubgroup ht K]
  exact (t.scChevalleyDatum ht).map_center_extendedElementarySubgroup K

/-- **Centre of the simply connected Chevalley group.** Over every field `K`, unit-valued
characters of `P / Q` canonically identify with the centre of
`(t.scChevalleyDatum ht).elementarySubgroup K`. -/
def scChevalleyDatumCenterElementarySubgroupEquiv :
    AddChar ((Fin t.rank → ℤ) ⧸ (t.simplyConnectedRootDatum ht).rootSpan ℤ) Kˣ ≃*
      Subgroup.center ((t.scChevalleyDatum ht).elementarySubgroup K) :=
  let e := Submodule.quotEquivOfEq _ _ (t.span_range_scChevalleyDatum_coordinateRoot_eq_rootSpan ht)
  (AddChar.congrLeft e.toAddEquiv).trans
    (((t.scChevalleyDatum ht).torusInfCentralizerRootTorusSubgroupEquiv K).trans
      (Subgroup.centerEquivOfMapSubtypeEq (t.map_center_scChevalleyDatum_elementarySubgroup ht K)))

/-- The simply connected centre equivalence sends a character of `P / Q` to the corresponding
torus point. -/
@[simp]
theorem coe_scChevalleyDatumCenterElementarySubgroupEquiv
    (χ : AddChar ((Fin t.rank → ℤ) ⧸ (t.simplyConnectedRootDatum ht).rootSpan ℤ) Kˣ) :
    ((t.scChevalleyDatumCenterElementarySubgroupEquiv ht K χ :
        (t.scChevalleyDatum ht).elementarySubgroup K) : (t.scChevalleyDatum ht).points K) =
      (t.scChevalleyDatum ht).torusPoints K (quotientCharTorusPoint _ χ) := by
  simp only [scChevalleyDatumCenterElementarySubgroupEquiv, MulEquiv.trans_apply,
    LinearEquiv.coe_toAddEquiv, Subgroup.coe_centerEquivOfMapSubtypeEq,
    ChevalleyDatum.coe_torusInfCentralizerRootTorusSubgroupEquiv]
  refine congrArg ((t.scChevalleyDatum ht).torusPoints K) (funext fun i => ?_)
  simp [quotientCharTorusPoint_apply]

/-- The inverse simply connected centre equivalence evaluates a weight class by the character
of the given torus parameter. -/
@[simp]
theorem scChevalleyDatumCenterElementarySubgroupEquiv_symm_apply_mk
    (s : Fin t.rank → Kˣ)
    (hg : (⟨(t.scChevalleyDatum ht).torusPoints K s,
        t.scChevalleyDatum_torusPoints_mem_elementarySubgroup ht K s⟩ :
        (t.scChevalleyDatum ht).elementarySubgroup K) ∈
      Subgroup.center ((t.scChevalleyDatum ht).elementarySubgroup K))
    (μ : Fin t.rank → ℤ) :
    (t.scChevalleyDatumCenterElementarySubgroupEquiv ht K).symm
      ⟨⟨(t.scChevalleyDatum ht).torusPoints K s,
        t.scChevalleyDatum_torusPoints_mem_elementarySubgroup ht K s⟩, hg⟩
      (Submodule.Quotient.mk μ) = torusCharacter s μ := by
  have hmk : (Submodule.quotEquivOfEq _ _
      (t.span_range_scChevalleyDatum_coordinateRoot_eq_rootSpan ht)).symm
      (Submodule.Quotient.mk μ) = Submodule.Quotient.mk μ := by
    rw [LinearEquiv.symm_apply_eq, Submodule.quotEquivOfEq_mk]
  simp [scChevalleyDatumCenterElementarySubgroupEquiv, hmk]

end Field

end SimplyConnected

end

end TauCeti.DynkinType
