/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.Index.Basic

/-!
# Profinite index in a subgroup tower

This file proves multiplicativity of supernatural index in a tower `H ≤ K ≤ G`, where `K` is a
closed subgroup of a profinite group. The relative factor is the profinite index of `H`, regarded
as a subgroup of `K`. The subgroup `H` need not be closed because profinite index only sees its
topological closure.

The primewise proof compares the finite images of both subgroups in a common finite quotient of
`G`.  Closedness of `K` makes it a profinite group in its own right, while cofinality of ambient
open normal subgroups identifies the relative indices of these finite images with the profinite
index computed inside `K`.

## Main results

* `Subgroup.profiniteIndex_subgroupOf_apply_eq_iSup_relIndex`: computes the relative factor from
  the finite images of a pair of subgroups when the larger one is closed.
* `Subgroup.profiniteIndex_subgroupOf_add_profiniteIndex`: primewise index multiplicativity.
* `Subgroup.profiniteIndex_subgroupOf_mul_profiniteIndex`: supernatural index multiplicativity.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Section 2.3.
-/

public section

namespace TauCeti

open scoped ENat

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]

variable (H K : Subgroup G) (hHK : H ≤ K)

omit [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] in
private lemma relIndex_map_quotient_eq_index_sup_comap (hHK : H ≤ K)
    (N : OpenNormalSubgroup G) :
    (H.map (QuotientGroup.mk' N.toSubgroup)).relIndex
        (K.map (QuotientGroup.mk' N.toSubgroup)) =
      ((H.subgroupOf K) ⊔ N.toSubgroup.comap K.subtype).index := by
  let q : G →* G ⧸ N.toSubgroup := QuotientGroup.mk' N.toSubgroup
  let qK : K →* G ⧸ N.toSubgroup := q.comp K.subtype
  have hHmap : (H.subgroupOf K).map qK = H.map q := by
    change (H.subgroupOf K).map (q.comp K.subtype) = H.map q
    rw [← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hHK]
  have hKmap : (⊤ : Subgroup K).map qK = K.map q := by
    change (⊤ : Subgroup K).map (q.comp K.subtype) = K.map q
    rw [← Subgroup.map_map, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  rw [← hHmap, ← hKmap, Subgroup.relIndex_map_map, top_sup_eq,
    Subgroup.relIndex_top_right]
  congr 2
  ext x
  change ((x : G) : G ⧸ N.toSubgroup) = 1 ↔ (x : G) ∈ N.toSubgroup
  rw [QuotientGroup.eq_one_iff (x : G)]

omit [CompactSpace G] [TotallyDisconnectedSpace G] in
private lemma index_subgroupOf_sup_comap_ne_zero [CompactSpace K]
    (N : OpenNormalSubgroup G) :
    ((H.subgroupOf K) ⊔ N.toSubgroup.comap K.subtype).index ≠ 0 := by
  have hcomap_ne : (N.toSubgroup.comap K.subtype).index ≠ 0 := by
    let _ : Finite (K ⧸ N.toSubgroup.comap K.subtype) :=
      Subgroup.quotient_finite_of_isOpen _
        (N.toOpenSubgroup.isOpen.preimage continuous_subtype_val)
    exact Subgroup.index_ne_zero_of_finite
  exact ne_zero_of_dvd_ne_zero hcomap_ne (Subgroup.index_dvd_of_le le_sup_right)

/-- The relative supernatural index in `K` is the supremum of the relative indices of the
images of `H` and `K` in the finite quotients of `G`.

This is the relative-index counterpart of `Subgroup.profiniteOrder_apply_eq_iSup_image` and is
the comparison that lets all three terms of the tower formula use the same ambient quotients. -/
theorem _root_.Subgroup.profiniteIndex_subgroupOf_apply_eq_iSup_relIndex
    (hHK : H ≤ K) (hK : IsClosed (K : Set G))
    (ell : Nat.Primes) :
    (H.subgroupOf K).profiniteIndex ell =
      ⨆ N : OpenNormalSubgroup G,
        (padicValNat ell
          ((H.map (QuotientGroup.mk' N.toSubgroup)).relIndex
            (K.map (QuotientGroup.mk' N.toSubgroup))) : ℕ∞) := by
  let _ : CompactSpace K := isCompact_iff_compactSpace.mp hK.isCompact
  have : Fact (ell : ℕ).Prime := ⟨ell.prop⟩
  rw [Subgroup.profiniteIndex_apply]
  apply le_antisymm
  · refine iSup_le fun V ↦ ?_
    obtain ⟨N, hNV⟩ := K.exists_openNormalSubgroup_comap_le V
    refine le_trans ?_ (le_iSup (fun N : OpenNormalSubgroup G ↦
      (padicValNat ell
        ((H.map (QuotientGroup.mk' N.toSubgroup)).relIndex
          (K.map (QuotientGroup.mk' N.toSubgroup))) : ℕ∞)) N)
    have hVne : ((H.subgroupOf K) ⊔ V.toSubgroup).index ≠ 0 := by
      apply ne_zero_of_dvd_ne_zero
        (Subgroup.index_ne_zero_of_finite : V.toSubgroup.index ≠ 0)
      exact Subgroup.index_dvd_of_le le_sup_right
    rw [Subgroup.index_map_mk'_eq_index_sup,
      relIndex_map_quotient_eq_index_sup_comap H K hHK N,
      padicValNat_eq_emultiplicity hVne,
      padicValNat_eq_emultiplicity (index_subgroupOf_sup_comap_ne_zero H K N)]
    apply emultiplicity_le_emultiplicity_of_dvd_right
    exact Subgroup.index_dvd_of_le (sup_le_sup_left hNV (H.subgroupOf K))
  · refine iSup_le fun N ↦ ?_
    let V := OpenNormalSubgroup.comap N K.subtype continuous_subtype_val
    refine le_iSup_of_le V ?_
    rw [relIndex_map_quotient_eq_index_sup_comap H K hHK N,
      Subgroup.index_map_mk'_eq_index_sup]
    rw [show V.toSubgroup = N.toSubgroup.comap K.subtype from
      OpenNormalSubgroup.toSubgroup_comap N K.subtype continuous_subtype_val]

/-- Primewise multiplicativity of profinite index through a closed intermediate subgroup. -/
theorem _root_.Subgroup.profiniteIndex_subgroupOf_add_profiniteIndex
    (hHK : H ≤ K) (hK : IsClosed (K : Set G)) (ell : Nat.Primes) :
    (H.subgroupOf K).profiniteIndex ell + K.profiniteIndex ell = H.profiniteIndex ell := by
  let _ : CompactSpace K := isCompact_iff_compactSpace.mp hK.isCompact
  have : Fact (ell : ℕ).Prime := ⟨ell.prop⟩
  rw [H.profiniteIndex_subgroupOf_apply_eq_iSup_relIndex K hHK hK,
    Subgroup.profiniteIndex_apply, Subgroup.profiniteIndex_apply]
  calc
    (⨆ N : OpenNormalSubgroup G,
        (padicValNat ell
          ((H.map (QuotientGroup.mk' N.toSubgroup)).relIndex
            (K.map (QuotientGroup.mk' N.toSubgroup))) : ℕ∞)) +
        ⨆ N : OpenNormalSubgroup G,
          (padicValNat ell
            (K.map (QuotientGroup.mk' N.toSubgroup)).index : ℕ∞) =
      ⨆ N : OpenNormalSubgroup G,
        (padicValNat ell
          ((H.map (QuotientGroup.mk' N.toSubgroup)).relIndex
            (K.map (QuotientGroup.mk' N.toSubgroup))) : ℕ∞) +
          (padicValNat ell
            (K.map (QuotientGroup.mk' N.toSubgroup)).index : ℕ∞) := by
      apply ENat.iSup_add_iSup
      intro N M
      let P : OpenNormalSubgroup G := N ⊓ M
      refine ⟨P, add_le_add ?_ ?_⟩
      · rw [relIndex_map_quotient_eq_index_sup_comap H K hHK N,
          relIndex_map_quotient_eq_index_sup_comap H K hHK P,
          padicValNat_eq_emultiplicity (index_subgroupOf_sup_comap_ne_zero H K N),
          padicValNat_eq_emultiplicity (index_subgroupOf_sup_comap_ne_zero H K P)]
        apply emultiplicity_le_emultiplicity_of_dvd_right
        apply Subgroup.index_dvd_of_le
        exact sup_le_sup_left (Subgroup.comap_mono inf_le_left) (H.subgroupOf K)
      · rw [padicValNat_eq_emultiplicity Subgroup.index_ne_zero_of_finite,
          padicValNat_eq_emultiplicity Subgroup.index_ne_zero_of_finite]
        apply emultiplicity_le_emultiplicity_of_dvd_right
        rw [K.index_map_mk'_eq_index_sup M.toSubgroup,
          K.index_map_mk'_eq_index_sup P.toSubgroup]
        exact Subgroup.index_dvd_of_le (sup_le_sup_left inf_le_right K)
    _ = ⨆ N : OpenNormalSubgroup G,
        (padicValNat ell (H.map (QuotientGroup.mk' N.toSubgroup)).index : ℕ∞) := by
      congr 1
      funext N
      have hrelne :
          (H.map (QuotientGroup.mk' N.toSubgroup)).relIndex
              (K.map (QuotientGroup.mk' N.toSubgroup)) ≠ 0 := by
        intro hzero
        have htower :=
          (H.map (QuotientGroup.mk' N.toSubgroup)).relIndex_mul_index
            (Subgroup.map_mono hHK)
        rw [hzero, zero_mul] at htower
        exact Subgroup.index_ne_zero_of_finite htower.symm
      rw [← (H.map (QuotientGroup.mk' N.toSubgroup)).relIndex_mul_index
          (Subgroup.map_mono hHK),
        padicValNat.mul hrelne
          Subgroup.index_ne_zero_of_finite,
        Nat.cast_add]

/-- **Multiplicativity of profinite index through a closed subgroup.** If `H ≤ K ≤ G` and `K`
is closed, then `[G : H] = [K : H] [G : K]` as supernatural numbers. -/
theorem _root_.Subgroup.profiniteIndex_subgroupOf_mul_profiniteIndex
    (hHK : H ≤ K) (hK : IsClosed (K : Set G)) :
    (H.subgroupOf K).profiniteIndex * K.profiniteIndex = H.profiniteIndex := by
  ext ell
  rw [Supernatural.mul_apply]
  exact H.profiniteIndex_subgroupOf_add_profiniteIndex K hHK hK ell

end TauCeti
