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
product of the supernatural order of `H` and its supernatural index in `G`. The order of `H`
is represented by its finite images in the quotients of `G`, and finite Lagrange formulas in
these quotients relate their orders to the corresponding finite indices. This yields both the
primewise additive formula and the multiplicative supernatural-number formula.

## Main results

* `Subgroup.profiniteOrder_apply_eq_add_profiniteIndex`: the primewise profinite Lagrange
  formula.
* `Subgroup.profiniteOrder_eq_mul_profiniteIndex`: the supernatural-number form of profinite
  Lagrange's theorem.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Section 2.3, Proposition 2.3.2.
-/

public section

namespace TauCeti

open scoped ENat

variable {G : Type*} [Group G] [TopologicalSpace G]

section Profinite

variable [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]

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
      · rw [padicValNat_eq_emultiplicity Nat.card_pos.ne',
          padicValNat_eq_emultiplicity Nat.card_pos.ne']
        apply emultiplicity_le_emultiplicity_of_dvd_right
        rw [← Subgroup.relIndex_ker H (QuotientGroup.mk' N.toSubgroup),
          ← Subgroup.relIndex_ker H (QuotientGroup.mk' K.toSubgroup),
          QuotientGroup.ker_mk', QuotientGroup.ker_mk']
        exact Subgroup.relIndex_dvd_of_le_left _ inf_le_left
      · rw [padicValNat_eq_emultiplicity Subgroup.index_ne_zero_of_finite,
          padicValNat_eq_emultiplicity Subgroup.index_ne_zero_of_finite]
        apply emultiplicity_le_emultiplicity_of_dvd_right
        rw [H.index_map_mk'_eq_index_sup M.toSubgroup,
          H.index_map_mk'_eq_index_sup K.toSubgroup]
        apply Subgroup.index_dvd_of_le
        exact sup_le_sup_left inf_le_right H

/-- **Lagrange's theorem for profinite groups**: the supernatural order of the ambient group
is the order of a closed subgroup times its supernatural index. -/
theorem _root_.Subgroup.profiniteOrder_eq_mul_profiniteIndex (H : Subgroup G)
    (hH : IsClosed (H : Set G)) :
    profiniteOrder G = profiniteOrder H * H.profiniteIndex := by
  ext ℓ
  rw [Supernatural.mul_apply]
  exact H.profiniteOrder_apply_eq_add_profiniteIndex hH ℓ

end Profinite

end TauCeti
