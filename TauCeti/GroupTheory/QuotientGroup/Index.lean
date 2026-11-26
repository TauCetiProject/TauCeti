/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.OrderOfElement
public import TauCeti.GroupTheory.QuotientGroup.ThirdIso
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Indices in quotient groups

This file records how the index of the image of a subgroup in a quotient group is computed in
the original group. It is the `Nat.card` shadow of the coset-space bijection
`QuotientGroup.quotientQuotientEquivQuotientSup`, and is read off it.

## Main results

* `Subgroup.index_map_mk'_eq_index_sup`: the index of the image of `H` in `G ⧸ N` is the
  index of `H ⊔ N` in `G`.
* `Subgroup.index_comap_subtype_eq_card_map`: the index of the preimage of `N` in `H` is the order
  of the image of `H` in `G ⧸ N`.
* `Subgroup.orderOf_mk_eq_index_of_index_prime_of_notMem`, `Subgroup.quotientPrimeEquiv`: an element
  outside a normal subgroup `H` of prime index generates `G ⧸ H`, of order `H.index`, giving an
  equivalence between `G ⧸ H` and `Fin H.index`.
-/

public section

namespace Subgroup

variable {G : Type*} [Group G]

/-- The index of the image of a subgroup in a quotient is the index of its join with the
quotienting subgroup: the two coset spaces are in bijection, by
`QuotientGroup.quotientQuotientEquivQuotientSup`. -/
@[to_additive (attr := simp), simp]
theorem index_map_mk'_eq_index_sup (H N : Subgroup G) [N.Normal] :
    (H.map (QuotientGroup.mk' N)).index = (H ⊔ N).index :=
  Nat.card_congr (QuotientGroup.quotientQuotientEquivQuotientSup H N)

/-- The index of the preimage of a normal subgroup `N` in a subgroup `H` is the order of the image
of `H` in the quotient by `N`. -/
@[to_additive]
theorem index_comap_subtype_eq_card_map (H N : Subgroup G) [N.Normal] :
    (N.comap H.subtype).index = Nat.card (H.map (QuotientGroup.mk' N)) := by
  rw [← Subgroup.relIndex_ker H (QuotientGroup.mk' N), QuotientGroup.ker_mk', Subgroup.relIndex,
    ← Subgroup.comap_subtype]

/-- In the quotient `G ⧸ H` by a normal subgroup of prime index `l`, every element `x ∉ H`
generates the quotient. -/
theorem zpowers_mk_eq_top_of_index_prime {G : Type*} [Group G] (H : Subgroup G) [H.Normal]
    {l : ℕ} (hl : l.Prime) (hH : H.index = l) {x : G} (hx : x ∉ H) :
    zpowers (QuotientGroup.mk x : G ⧸ H) = ⊤ :=
  have : Fact l.Prime := ⟨hl⟩
  zpowers_eq_top_of_prime_card (hH ▸ H.index_eq_card.symm)
    fun h ↦ hx ((QuotientGroup.eq_one_iff x).mp h)

/-- In the quotient `G ⧸ H` by a normal subgroup of prime index `l`, every element `x ∉ H`
projects to an element of order `l`. -/
theorem orderOf_mk_eq_index_of_index_prime_of_notMem {G : Type*} [Group G] (H : Subgroup G)
    [H.Normal] {l : ℕ} (hl : l.Prime) (hH : H.index = l) {x : G} (hx : x ∉ H) :
    orderOf (QuotientGroup.mk x : G ⧸ H) = l := by
  rw [orderOf_eq_card_of_zpowers_eq_top (zpowers_mk_eq_top_of_index_prime H hl hH hx),
    ← H.index_eq_card, hH]

/-- For a normal subgroup `H ≤ G` of prime index `l` and `x ∉ H`, the map
`i ↦ (x : G ⧸ H)⁻¹ ^ (i : ℕ)` is a bijection `Fin l ≃ G ⧸ H`: the powers of the generator
`(x : G ⧸ H)⁻¹` below its order enumerate `G ⧸ H` (`finEquivZPowers`). -/
noncomputable def quotientPrimeEquiv {G : Type*} [Group G] (H : Subgroup G) [H.Normal]
    {l : ℕ} (hl : l.Prime) (hH : H.index = l) {x : G} (hx : x ∉ H) : Fin l ≃ G ⧸ H :=
  have hq : orderOf (QuotientGroup.mk x : G ⧸ H)⁻¹ = l := by
    rw [orderOf_inv, orderOf_mk_eq_index_of_index_prime_of_notMem H hl hH hx]
  have htop : zpowers (QuotientGroup.mk x : G ⧸ H)⁻¹ = ⊤ := by
    rw [zpowers_inv, zpowers_mk_eq_top_of_index_prime H hl hH hx]
  (finCongr hq.symm).trans <| (finEquivZPowers (orderOf_pos_iff.mp (hq ▸ hl.pos))).trans <|
    (MulEquiv.subgroupCongr htop).toEquiv.trans topEquiv.toEquiv

/-- Explicit formula for `Subgroup.quotientPrimeEquiv`. -/
@[simp]
theorem quotientPrimeEquiv_apply {G : Type*} [Group G] (H : Subgroup G) [H.Normal]
    {l : ℕ} (hl : l.Prime) (hH : H.index = l) {x : G} (hx : x ∉ H) (i : Fin l) :
    quotientPrimeEquiv H hl hH hx i = QuotientGroup.mk ((x ^ (i : ℕ))⁻¹) := by
  have hdef : quotientPrimeEquiv H hl hH hx i = (QuotientGroup.mk x : G ⧸ H)⁻¹ ^ (i : ℕ) := by
    simp [quotientPrimeEquiv, finEquivZPowers_apply]
  rw [hdef, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_pow, inv_pow]

end Subgroup
