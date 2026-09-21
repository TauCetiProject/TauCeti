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
  have hHmap : (H.subgroupOf K).map ((QuotientGroup.mk' N.toSubgroup).comp K.subtype) =
      H.map (QuotientGroup.mk' N.toSubgroup) := by
    rw [← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hHK]
  have hKmap : (⊤ : Subgroup K).map ((QuotientGroup.mk' N.toSubgroup).comp K.subtype) =
      K.map (QuotientGroup.mk' N.toSubgroup) := by
    rw [← Subgroup.map_map, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have hker : ((QuotientGroup.mk' N.toSubgroup).comp K.subtype).ker =
      N.toSubgroup.comap K.subtype := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
  rw [← hHmap, ← hKmap, Subgroup.relIndex_map_map, top_sup_eq,
    Subgroup.relIndex_top_right, hker]

omit [CompactSpace G] [TotallyDisconnectedSpace G] in
private lemma index_subgroupOf_sup_comap_ne_zero [CompactSpace K]
    (N : OpenNormalSubgroup G) :
    ((H.subgroupOf K) ⊔ N.toSubgroup.comap K.subtype).index ≠ 0 := by
  have : Finite (K ⧸ N.toSubgroup.comap K.subtype) :=
    Subgroup.quotient_finite_of_isOpen _
      (N.toOpenSubgroup.isOpen.preimage continuous_subtype_val)
  have : (N.toSubgroup.comap K.subtype).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  exact (Subgroup.finiteIndex_of_le le_sup_right).index_ne_zero

/-- The exponent of `ell` in the relative supernatural index of `H` in `K` is the supremum of
the `ell`-adic valuations of the relative indices of the images of `H` and `K` in the finite
quotients of `G`.

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
      have : V.toSubgroup.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
      exact (Subgroup.finiteIndex_of_le le_sup_right).index_ne_zero
    rw [Subgroup.index_map_mk'_eq_index_sup,
      relIndex_map_quotient_eq_index_sup_comap H K hHK N,
      padicValNat_eq_emultiplicity hVne,
      padicValNat_eq_emultiplicity (index_subgroupOf_sup_comap_ne_zero H K N)]
    apply emultiplicity_le_emultiplicity_of_dvd_right
    exact Subgroup.index_dvd_of_le (sup_le_sup_left hNV (H.subgroupOf K))
  · refine iSup_le fun N ↦ ?_
    refine le_iSup_of_le (OpenNormalSubgroup.comap N K.subtype continuous_subtype_val) ?_
    have hV : (OpenNormalSubgroup.comap N K.subtype continuous_subtype_val).toSubgroup =
        N.toSubgroup.comap K.subtype :=
      OpenNormalSubgroup.toSubgroup_comap N K.subtype continuous_subtype_val
    rw [relIndex_map_quotient_eq_index_sup_comap H K hHK N,
      Subgroup.index_map_mk'_eq_index_sup, hV]

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
        have : (H.map (QuotientGroup.mk' N.toSubgroup)).FiniteIndex :=
          Subgroup.finiteIndex_of_finite_quotient
        have : (H.map (QuotientGroup.mk' N.toSubgroup)).IsFiniteRelIndex
            (K.map (QuotientGroup.mk' N.toSubgroup)) :=
          Subgroup.isFiniteRelIndex_of_finiteIndex
        exact Subgroup.relIndex_ne_zero
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
