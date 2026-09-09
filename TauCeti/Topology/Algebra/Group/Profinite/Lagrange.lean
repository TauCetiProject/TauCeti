/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.Index
public import TauCeti.Topology.Algebra.Group.Profinite.Order

/-!
# Lagrange's theorem for profinite groups

For a closed subgroup `H` of a profinite group `G`, the supernatural order of `G` is the
product of the supernatural order of `H` and its supernatural index in `G`. The proof first
shows that the finite images of `H` in the quotients of `G` are cofinal among all finite
continuous quotients of `H`. Finite Lagrange's theorem then applies in every ambient quotient,
and directedness of the open normal subgroups lets the two suprema be combined.

## Main results

* `Subgroup.profiniteOrder_eq_iSup_image`: a closed subgroup's supernatural order is the
  supremum of the orders of its images in the ambient finite quotients.
* `Subgroup.profiniteOrder_apply_eq_iSup_image`: the primewise form of this description.
* `Subgroup.profiniteOrder_apply_eq_add_profiniteIndex`: the primewise profinite Lagrange
  formula.
* `Subgroup.profiniteOrder_mul_profiniteIndex`: the supernatural-number form of profinite
  Lagrange's theorem.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Section 2.3, Proposition 2.3.2.
-/

public section

namespace TauCeti

open scoped ENat

variable {G : Type*} [Group G] [TopologicalSpace G]

private theorem index_comap_eq_card_map (H : Subgroup G) (N : OpenNormalSubgroup G) :
    (N.toSubgroup.comap H.subtype).index =
      Nat.card (H.map (QuotientGroup.mk' N.toSubgroup)) := by
  let f : H →* G ⧸ N.toSubgroup :=
    (QuotientGroup.mk' N.toSubgroup).comp H.subtype
  have hker : f.ker = N.toSubgroup.comap H.subtype := by
    ext x
    simp [f, Subgroup.mem_subgroupOf]
  have hrange : f.range = H.map (QuotientGroup.mk' N.toSubgroup) := by
    ext x
    simp [f]
  rw [← hker, Subgroup.index_ker, hrange]

private theorem index_map_mk_eq_index_sup (H : Subgroup G) (N : OpenNormalSubgroup G) :
    (H.map (QuotientGroup.mk' N.toSubgroup)).index =
      (H ⊔ N.toSubgroup).index := by
  rw [H.index_map, QuotientGroup.ker_mk',
    (QuotientGroup.mk' N.toSubgroup).range_eq_top_of_surjective
      (QuotientGroup.mk'_surjective N.toSubgroup), Subgroup.index_top, mul_one]

private theorem padicValNat_mono_of_dvd (p : Nat.Primes) {m n : ℕ} (hm : m ≠ 0)
    (hn : n ≠ 0) (h : m ∣ n) :
    (padicValNat p m : ℕ∞) ≤ (padicValNat p n : ℕ∞) := by
  have : Fact (p : ℕ).Prime := ⟨p.prop⟩
  obtain ⟨k, rfl⟩ := h
  have hk : k ≠ 0 := fun hk ↦ hn (by simp [hk])
  rw [padicValNat.mul hm hk, Nat.cast_add]
  exact le_add_right le_rfl

section Profinite

variable [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]

private theorem exists_openNormalSubgroup_comap_le (H : Subgroup G)
    (V : OpenNormalSubgroup H) :
    ∃ N : OpenNormalSubgroup G, N.toSubgroup.comap H.subtype ≤ V.toSubgroup := by
  obtain ⟨s, hs, hpre⟩ := isOpen_induced_iff.mp V.toOpenSubgroup.isOpen
  have h_one : (1 : G) ∈ s := by
    have : (1 : H) ∈ V := V.toSubgroup.one_mem
    exact hpre.symm.subset this
  obtain ⟨N, hN⟩ :=
    ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hs h_one
  refine ⟨N, fun x hx ↦ ?_⟩
  have : (x : G) ∈ s := hN hx
  exact hpre.subset this

/-- The supernatural order of a closed subgroup is the supremum of the orders of its images
in the ambient finite continuous quotients. -/
theorem _root_.Subgroup.profiniteOrder_eq_iSup_image (H : Subgroup G)
    (hH : IsClosed (H : Set G)) :
    profiniteOrder H = ⨆ N : OpenNormalSubgroup G,
      Supernatural.ofNat
        (⟨Nat.card (H.map (QuotientGroup.mk' N.toSubgroup)), Nat.card_pos⟩ : ℕ+) := by
  let : CompactSpace H := isCompact_iff_compactSpace.mp hH.isCompact
  rw [profiniteOrder_eq_iSup_ofNat]
  apply le_antisymm
  · refine iSup_le fun V ↦ ?_
    obtain ⟨N, hNV⟩ := exists_openNormalSubgroup_comap_le H V
    refine le_trans ?_ (le_iSup (fun N : OpenNormalSubgroup G ↦
      Supernatural.ofNat
        (⟨Nat.card (H.map (QuotientGroup.mk' N.toSubgroup)), Nat.card_pos⟩ : ℕ+)) N)
    apply Supernatural.ofNat_le_ofNat_iff.mpr
    apply PNat.dvd_iff.mpr
    have hdvd : Nat.card (H ⧸ V.toSubgroup) ∣
        Nat.card (H.map (QuotientGroup.mk' N.toSubgroup)) := by
      rw [← V.toSubgroup.index_eq_card, ← index_comap_eq_card_map H N]
      exact Subgroup.index_dvd_of_le hNV
    exact hdvd
  · refine iSup_le fun N ↦ ?_
    let V := OpenNormalSubgroup.comap N H.subtype continuous_subtype_val
    refine le_iSup_of_le V ?_
    apply le_of_eq
    apply congrArg Supernatural.ofNat
    apply Subtype.ext
    have hcard : Nat.card (H ⧸ V.toSubgroup) =
        Nat.card (H.map (QuotientGroup.mk' N.toSubgroup)) := by
      rw [← V.toSubgroup.index_eq_card]
      have hV : V.toSubgroup = N.toSubgroup.comap H.subtype :=
        OpenNormalSubgroup.toSubgroup_comap N H.subtype continuous_subtype_val
      rw [hV]
      exact index_comap_eq_card_map H N
    exact hcard.symm

/-- Primewise form of `Subgroup.profiniteOrder_eq_iSup_image`. -/
theorem _root_.Subgroup.profiniteOrder_apply_eq_iSup_image (H : Subgroup G)
    (hH : IsClosed (H : Set G)) (ℓ : Nat.Primes) :
    profiniteOrder H ℓ = ⨆ N : OpenNormalSubgroup G,
      (padicValNat ℓ (Nat.card (H.map (QuotientGroup.mk' N.toSubgroup))) : ℕ∞) := by
  rw [H.profiniteOrder_eq_iSup_image hH, Supernatural.iSup_apply]
  congr 1
  funext N
  exact Supernatural.ofNat_apply _ _

/-- Primewise Lagrange formula for a closed subgroup of a profinite group: the exponent in
the ambient order is the exponent in the subgroup order plus the exponent in the index. -/
theorem _root_.Subgroup.profiniteOrder_apply_eq_add_profiniteIndex (H : Subgroup G)
    (hH : IsClosed (H : Set G)) (ℓ : Nat.Primes) :
    profiniteOrder G ℓ = profiniteOrder H ℓ + H.profiniteIndex ℓ := by
  have : Fact (ℓ : ℕ).Prime := ⟨ℓ.prop⟩
  rw [profiniteOrder_apply, H.profiniteOrder_apply_eq_iSup_image hH,
    Subgroup.profiniteIndex_apply]
  calc
    (⨆ N : OpenNormalSubgroup G,
        (padicValNat ℓ (Nat.card (G ⧸ N.toSubgroup)) : ℕ∞)) =
        ⨆ N : OpenNormalSubgroup G,
          (padicValNat ℓ
              (Nat.card (H.map (QuotientGroup.mk' N.toSubgroup))) : ℕ∞) +
            (padicValNat ℓ
              (H.map (QuotientGroup.mk' N.toSubgroup)).index : ℕ∞) := by
      congr 1
      funext N
      have hcard := (H.map (QuotientGroup.mk' N.toSubgroup)).card_mul_index
      rw [← hcard, padicValNat.mul Nat.card_pos.ne'
        Subgroup.index_ne_zero_of_finite, Nat.cast_add]
    _ = (⨆ N : OpenNormalSubgroup G,
          (padicValNat ℓ
            (Nat.card (H.map (QuotientGroup.mk' N.toSubgroup))) : ℕ∞)) +
        ⨆ N : OpenNormalSubgroup G,
          (padicValNat ℓ
            (H.map (QuotientGroup.mk' N.toSubgroup)).index : ℕ∞) := by
      symm
      apply ENat.iSup_add_iSup
      intro N M
      let K : OpenNormalSubgroup G := N ⊓ M
      refine ⟨K, add_le_add ?_ ?_⟩
      · apply padicValNat_mono_of_dvd ℓ Nat.card_pos.ne' Nat.card_pos.ne'
        rw [← index_comap_eq_card_map H N, ← index_comap_eq_card_map H K]
        apply Subgroup.index_dvd_of_le
        apply Subgroup.comap_mono
        exact inf_le_left
      · apply padicValNat_mono_of_dvd ℓ Subgroup.index_ne_zero_of_finite
          Subgroup.index_ne_zero_of_finite
        rw [index_map_mk_eq_index_sup H M, index_map_mk_eq_index_sup H K]
        apply Subgroup.index_dvd_of_le
        exact sup_le_sup_left inf_le_right H

/-- **Lagrange's theorem for profinite groups**: the supernatural order of a closed subgroup,
times its supernatural index, is the supernatural order of the ambient group. -/
theorem _root_.Subgroup.profiniteOrder_mul_profiniteIndex (H : Subgroup G)
    (hH : IsClosed (H : Set G)) :
    profiniteOrder H * H.profiniteIndex = profiniteOrder G := by
  ext ℓ
  rw [Supernatural.mul_apply]
  exact (H.profiniteOrder_apply_eq_add_profiniteIndex hH ℓ).symm

end Profinite

end TauCeti
