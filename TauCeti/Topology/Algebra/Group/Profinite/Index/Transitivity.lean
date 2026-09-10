/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.Index.Basic

/-!
# Transitivity of profinite index

This file proves that supernatural index is multiplicative in a subgroup tower whose
intermediate subgroup is closed, allowing profinite indices to be decomposed through a closed
intermediate subgroup.

## Main results

* `Subgroup.profiniteIndex_mul_profiniteIndex`: multiplicativity of supernatural index in a
  subgroup tower.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Section 2.3.
-/

public section

namespace TauCeti

open scoped ENat

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]

omit [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] in
private theorem index_at_level_mul_index_at_level {H K : Subgroup G} (hHK : H ≤ K)
    (N : OpenNormalSubgroup G) (N' : OpenNormalSubgroup K)
    (hN' : N'.toSubgroup = N.toSubgroup.comap K.subtype) :
    ((H.comap K.subtype).map
        (QuotientGroup.mk' N'.toSubgroup)).index *
      (K.map (QuotientGroup.mk' N.toSubgroup)).index =
        (H.map (QuotientGroup.mk' N.toSubgroup)).index := by
  let q : G →* G ⧸ N.toSubgroup := QuotientGroup.mk' N.toSubgroup
  let f : K →* G ⧸ N.toSubgroup := q.comp K.subtype
  have himage : H.map q ≤ K.map q := Subgroup.map_mono hHK
  rw [← (H.map q).relIndex_mul_index himage]
  congr 1
  have hker : f.ker = N'.toSubgroup := by
    ext x
    simp only [MonoidHom.mem_ker]
    rw [show f x = q (x : G) by exact MonoidHom.comp_apply q K.subtype x]
    rw [show q (x : G) = 1 ↔ (x : G) ∈ N.toSubgroup by
      exact QuotientGroup.eq_one_iff (x : G)]
    rw [hN', Subgroup.mem_comap]
    simp only [Subgroup.coe_subtype]
  have hmapH : (H.comap K.subtype).map f = H.map q := by
    ext y
    constructor
    · intro hy
      obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy
      exact Subgroup.mem_map.mpr ⟨x, Subgroup.mem_comap.mp hx, by
        simpa only [f, MonoidHom.comp_apply, Subgroup.coe_subtype] using hxy⟩
    · intro hy
      obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy
      exact Subgroup.mem_map.mpr ⟨⟨x, hHK hx⟩, Subgroup.mem_comap.mpr hx, by
        simpa only [f, MonoidHom.comp_apply, Subgroup.coe_subtype] using hxy⟩
  have hmapK : (⊤ : Subgroup K).map f = K.map q := by
    ext y
    constructor
    · intro hy
      obtain ⟨x, _, hxy⟩ := Subgroup.mem_map.mp hy
      exact Subgroup.mem_map.mpr ⟨x, x.property, by
        simpa only [f, MonoidHom.comp_apply, Subgroup.coe_subtype] using hxy⟩
    · intro hy
      obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy
      exact Subgroup.mem_map.mpr ⟨⟨x, hx⟩, Subgroup.mem_top _, by
        simpa only [f, MonoidHom.comp_apply, Subgroup.coe_subtype] using hxy⟩
  calc
    ((H.comap K.subtype).map (QuotientGroup.mk' N'.toSubgroup)).index =
        (H.comap K.subtype ⊔ N'.toSubgroup).index :=
      (H.comap K.subtype).index_map_mk'_eq_index_sup _
    _ = (H.comap K.subtype ⊔ f.ker).relIndex ((⊤ : Subgroup K) ⊔ f.ker) := by
      rw [hker, top_sup_eq, Subgroup.relIndex_top_right]
    _ = ((H.comap K.subtype).map f).relIndex ((⊤ : Subgroup K).map f) :=
      (Subgroup.relIndex_map_map f (H.comap K.subtype) ⊤).symm
    _ = (H.map q).relIndex (K.map q) := by rw [hmapH, hmapK]

/-- Supernatural index is multiplicative in a subgroup tower with closed intermediate subgroup.
No closedness assumption on `H` is needed because supernatural index depends only on closure. -/
theorem _root_.Subgroup.profiniteIndex_mul_profiniteIndex {H K : Subgroup G} (hHK : H ≤ K)
    (hK : IsClosed (K : Set G)) :
    (H.subgroupOf K).profiniteIndex * K.profiniteIndex = H.profiniteIndex := by
  let _ : CompactSpace K := isCompact_iff_compactSpace.mp hK.isCompact
  let _ : Nonempty (OpenNormalSubgroup G) :=
    ⟨{ toOpenSubgroup := ⊤, isNormal' := Subgroup.normal_top }⟩
  let _ : Nonempty (OpenNormalSubgroup K) :=
    ⟨{ toOpenSubgroup := ⊤, isNormal' := Subgroup.normal_top }⟩
  ext ℓ
  let _ : Fact (ℓ : ℕ).Prime := ⟨ℓ.prop⟩
  rw [Supernatural.mul_apply, Subgroup.profiniteIndex_apply,
    Subgroup.profiniteIndex_apply, Subgroup.profiniteIndex_apply]
  apply le_antisymm
  · apply ENat.iSup_add_iSup_le
    intro M N
    obtain ⟨L₀, hL₀⟩ := K.exists_openNormalSubgroup_comap_le M
    let L : OpenNormalSubgroup G := L₀ ⊓ N
    let L' : OpenNormalSubgroup K :=
      OpenNormalSubgroup.comap L K.subtype continuous_subtype_val
    have hL' : L'.toSubgroup = L.toSubgroup.comap K.subtype :=
      OpenNormalSubgroup.toSubgroup_comap L K.subtype continuous_subtype_val
    have hLM : L'.toSubgroup ≤ M.toSubgroup := by
      rw [hL']
      exact (Subgroup.comap_mono inf_le_left).trans hL₀
    have hLN : L.toSubgroup ≤ N.toSubgroup := inf_le_right
    calc
      (padicValNat ℓ
            ((H.comap K.subtype).map (QuotientGroup.mk' M.toSubgroup)).index : ℕ∞) +
          (padicValNat ℓ (K.map (QuotientGroup.mk' N.toSubgroup)).index : ℕ∞) ≤
          (padicValNat ℓ
            ((H.comap K.subtype).map
              (QuotientGroup.mk' L'.toSubgroup)).index : ℕ∞) +
          (padicValNat ℓ (K.map (QuotientGroup.mk' L.toSubgroup)).index : ℕ∞) := by
        apply add_le_add
        · rw [padicValNat_eq_emultiplicity Subgroup.index_ne_zero_of_finite,
            padicValNat_eq_emultiplicity Subgroup.index_ne_zero_of_finite]
          apply emultiplicity_le_emultiplicity_of_dvd_right
          rw [(H.comap K.subtype).index_map_mk'_eq_index_sup M.toSubgroup,
            (H.comap K.subtype).index_map_mk'_eq_index_sup L'.toSubgroup]
          exact Subgroup.index_dvd_of_le (sup_le_sup_left hLM _)
        · rw [padicValNat_eq_emultiplicity Subgroup.index_ne_zero_of_finite,
            padicValNat_eq_emultiplicity Subgroup.index_ne_zero_of_finite]
          apply emultiplicity_le_emultiplicity_of_dvd_right
          rw [K.index_map_mk'_eq_index_sup N.toSubgroup,
            K.index_map_mk'_eq_index_sup L.toSubgroup]
          exact Subgroup.index_dvd_of_le (sup_le_sup_left hLN _)
      _ = (padicValNat ℓ (H.map (QuotientGroup.mk' L.toSubgroup)).index : ℕ∞) := by
        rw [← Nat.cast_add, ← padicValNat.mul Subgroup.index_ne_zero_of_finite
          Subgroup.index_ne_zero_of_finite,
          index_at_level_mul_index_at_level hHK L L' hL']
      _ ≤ ⨆ L : OpenNormalSubgroup G,
          (padicValNat ℓ (H.map (QuotientGroup.mk' L.toSubgroup)).index : ℕ∞) :=
        le_iSup (fun L : OpenNormalSubgroup G ↦
          (padicValNat ℓ (H.map (QuotientGroup.mk' L.toSubgroup)).index : ℕ∞)) L
  · refine iSup_le fun N ↦ ?_
    let N' : OpenNormalSubgroup K :=
      OpenNormalSubgroup.comap N K.subtype continuous_subtype_val
    have hN' : N'.toSubgroup = N.toSubgroup.comap K.subtype :=
      OpenNormalSubgroup.toSubgroup_comap N K.subtype continuous_subtype_val
    calc
      (padicValNat ℓ (H.map (QuotientGroup.mk' N.toSubgroup)).index : ℕ∞) =
          (padicValNat ℓ
            ((H.comap K.subtype).map
              (QuotientGroup.mk' N'.toSubgroup)).index : ℕ∞) +
          (padicValNat ℓ (K.map (QuotientGroup.mk' N.toSubgroup)).index : ℕ∞) := by
        rw [← Nat.cast_add, ← padicValNat.mul Subgroup.index_ne_zero_of_finite
          Subgroup.index_ne_zero_of_finite,
          index_at_level_mul_index_at_level hHK N N' hN']
      _ ≤ (⨆ M : OpenNormalSubgroup K,
            (padicValNat ℓ
              ((H.comap K.subtype).map (QuotientGroup.mk' M.toSubgroup)).index : ℕ∞)) +
          ⨆ L : OpenNormalSubgroup G,
            (padicValNat ℓ (K.map (QuotientGroup.mk' L.toSubgroup)).index : ℕ∞) :=
        add_le_add
          (le_iSup (fun M : OpenNormalSubgroup K ↦
            (padicValNat ℓ
              ((H.comap K.subtype).map (QuotientGroup.mk' M.toSubgroup)).index : ℕ∞)) <|
                N')
          (le_iSup (fun L : OpenNormalSubgroup G ↦
            (padicValNat ℓ (K.map (QuotientGroup.mk' L.toSubgroup)).index : ℕ∞)) N)

end TauCeti
