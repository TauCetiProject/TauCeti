/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.FixedSubgroup
public import TauCeti.GroupTheory.QuotientGroup.Map
import TauCeti.GroupTheory.FixedSubgroup.Lang

/-!
# Fixed points on coset spaces

Let `F : G →* G` be an endomorphism of a group `G` and `J ≤ G` an `F`-invariant subgroup
(`J ≤ J.comap F`), not necessarily normal. Then `F` induces a map `F.quotientMap hJF` on the
left-coset space `G ⧸ J`, and a coset `gJ` is fixed by `F.quotientMap hJF` if and only if the
Lang defect `g⁻¹ * F g` lies in `J` (`MonoidHom.quotientMap_mk_eq_self_iff`).

The canonical map `G^F ⧸ J^F ↪ (G ⧸ J)^F` is injective
(`MonoidHom.fixedSubgroupQuotientEmbedding`), and surjectivity of the Lang map `z ↦ z⁻¹ * F z`
on `J` upgrades it to a bijection `G^F ⧸ J^F ≃ (G ⧸ J)^F`
(`MonoidHom.fixedSubgroupQuotientEquiv`), via `MonoidHom.exists_fixed_mul_of_surjective_inv_mul`.

## Main definitions

* `MonoidHom.fixedSubgroupQuotientEmbedding`: the canonical injection `G^F ⧸ J^F ↪ (G ⧸ J)^F`.
* `MonoidHom.fixedSubgroupQuotientEquiv`: the bijection `G^F ⧸ J^F ≃ (G ⧸ J)^F` when the Lang
  map on `J` is surjective.

## Main statements

* `MonoidHom.quotientMap_mk_eq_self_iff` and `MonoidHom.mem_fixedPoints_quotientMap_mk_iff`: a
  left coset `gJ` is fixed by `F.quotientMap hJF` if and only if `g⁻¹ * F g ∈ J`.
* `MonoidHom.coe_fixedSubgroupQuotientEmbedding_mk`,
  `MonoidHom.fixedSubgroupQuotientEmbedding_surjective`, and
  `MonoidHom.coe_fixedSubgroupQuotientEquiv_mk`: evaluation and surjectivity of the fixed-coset
  maps.
-/

public section

namespace MonoidHom

variable {G : Type*} [Group G]

/-- A left coset `gJ` is fixed by the induced endomorphism `F.quotientMap hJF` on `G ⧸ J` if and
only if the Lang defect `g⁻¹ * F g` lies in `J`. -/
theorem quotientMap_mk_eq_self_iff (F : G →* G) {J : Subgroup G} (hJF : J ≤ J.comap F) (g : G) :
    F.quotientMap hJF (QuotientGroup.mk g) = QuotientGroup.mk g ↔ g⁻¹ * F g ∈ J := by
  rw [quotientMap_mk, eq_comm, QuotientGroup.eq]

/-- Membership of a left coset `gJ` in the fixed points of `F.quotientMap hJF` is equivalent to
`g⁻¹ * F g ∈ J`. -/
theorem mem_fixedPoints_quotientMap_mk_iff (F : G →* G) {J : Subgroup G} (hJF : J ≤ J.comap F)
    (g : G) :
    QuotientGroup.mk g ∈ Function.fixedPoints (F.quotientMap hJF) ↔ g⁻¹ * F g ∈ J :=
  F.quotientMap_mk_eq_self_iff hJF g

/-- The canonical injection `G^F ⧸ J^F ↪ (G ⧸ J)^F` sending the coset of a fixed element `g ∈ G^F`
modulo `J.subgroupOf G^F` to the `F`-fixed coset `gJ ∈ (G ⧸ J)^F`. -/
def fixedSubgroupQuotientEmbedding (F : G →* G) {J : Subgroup G} (hJF : J ≤ J.comap F) :
    ↥(TauCeti.fixedSubgroup F) ⧸ J.subgroupOf (TauCeti.fixedSubgroup F) ↪
      Function.fixedPoints (F.quotientMap hJF) where
  toFun := Quotient.lift
    (fun g : TauCeti.fixedSubgroup F =>
      ⟨QuotientGroup.mk (g : G), by
        rw [Function.mem_fixedPoints_iff, quotientMap_mk, TauCeti.mem_fixedSubgroup.mp g.property]⟩)
    (fun a b hab => Subtype.ext <| by
      have hab' : (a : G)⁻¹ * (b : G) ∈ J :=
        Subgroup.mem_subgroupOf.mp (QuotientGroup.leftRel_apply.mp hab)
      exact Quotient.sound (QuotientGroup.leftRel_apply.mpr hab'))
  inj' := Quotient.ind₂' fun a b h => by
    have h' : QuotientGroup.mk (a : G) = QuotientGroup.mk (b : G) := congrArg Subtype.val h
    rw [QuotientGroup.eq] at h'
    exact Quotient.sound (QuotientGroup.leftRel_apply.mpr (Subgroup.mem_subgroupOf.mpr h'))

/-- `fixedSubgroupQuotientEmbedding` sends the coset of `g ∈ G^F` to the coset `gJ`. -/
@[simp]
theorem coe_fixedSubgroupQuotientEmbedding_mk (F : G →* G) {J : Subgroup G} (hJF : J ≤ J.comap F)
    (g : TauCeti.fixedSubgroup F) :
    (F.fixedSubgroupQuotientEmbedding hJF (QuotientGroup.mk g) : G ⧸ J) =
      QuotientGroup.mk (g : G) := by
  rfl

/-- If the Lang map `z ↦ z⁻¹ * F z` is surjective on an `F`-invariant subgroup `J ≤ G`, then
every `F`-fixed left coset in `G ⧸ J` has a fixed representative, so `G^F ⧸ J^F ↪ (G ⧸ J)^F` is
surjective. -/
theorem fixedSubgroupQuotientEmbedding_surjective (F : G →* G) {J : Subgroup G}
    (hJF : J ≤ J.comap F) (hJ : ∀ d ∈ J, ∃ z ∈ J, z⁻¹ * F z = d) :
    Function.Surjective (F.fixedSubgroupQuotientEmbedding hJF) := by
  rintro ⟨q, hq⟩
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective q
  have hh : h⁻¹ * F h ∈ J := (F.mem_fixedPoints_quotientMap_mk_iff hJF h).mp hq
  obtain ⟨z, hzJ, hfix⟩ := F.exists_fixed_mul_of_surjective_inv_mul J hJ hh
  refine ⟨QuotientGroup.mk ⟨h * z, TauCeti.mem_fixedSubgroup.mpr hfix⟩, Subtype.ext ?_⟩
  rw [coe_fixedSubgroupQuotientEmbedding_mk, QuotientGroup.eq]
  simpa only [mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one] using J.inv_mem hzJ

/-- **Non-normal fixed-coset bijection**: if `J ≤ G` is an `F`-invariant subgroup (not necessarily
normal) on which `z ↦ z⁻¹ * F z` is surjective, then `G^F ⧸ J^F ≃ (G ⧸ J)^F`. -/
noncomputable def fixedSubgroupQuotientEquiv (F : G →* G) {J : Subgroup G}
    (hJF : J ≤ J.comap F) (hJ : ∀ d ∈ J, ∃ z ∈ J, z⁻¹ * F z = d) :
    ↥(TauCeti.fixedSubgroup F) ⧸ J.subgroupOf (TauCeti.fixedSubgroup F) ≃
      Function.fixedPoints (F.quotientMap hJF) :=
  Equiv.ofBijective _ ⟨(F.fixedSubgroupQuotientEmbedding hJF).injective,
    F.fixedSubgroupQuotientEmbedding_surjective hJF hJ⟩

/-- `fixedSubgroupQuotientEquiv` sends the coset of `g ∈ G^F` to the coset `gJ`. -/
@[simp]
theorem coe_fixedSubgroupQuotientEquiv_mk (F : G →* G) {J : Subgroup G} (hJF : J ≤ J.comap F)
    (hJ : ∀ d ∈ J, ∃ z ∈ J, z⁻¹ * F z = d) (g : TauCeti.fixedSubgroup F) :
    (F.fixedSubgroupQuotientEquiv hJF hJ (QuotientGroup.mk g) : G ⧸ J) =
      QuotientGroup.mk (g : G) := by
  rfl

end MonoidHom
