/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.GroupAlgebra.DefectGroup.Basic

/-!
# Defect groups under group isomorphisms

A group isomorphism `σ : G ≃* G'` induces the algebra isomorphism
`MonoidAlgebra.domCongr R R σ : R[G] ≃ₐ[R] R[G']`, which carries block idempotents to block
idempotents (`TauCeti.IsBlockIdempotent.domCongr`). It also carries defect groups to defect
groups: the Brauer projection of `σ x` at `σ(P)` vanishes exactly when that of `x` at `P` does
(`TauCeti.brauerProjection_map_domCongr_eq_zero_iff`), and `σ` preserves `p`-subgroups and
inclusions of subgroups.

## Main results

* `TauCeti.IsDefectGroup.domCongr_map`: a defect group of `x` is carried to a defect group of
  `σ x`.
* `TauCeti.isDefectGroup_domCongr_map_iff`: transport of defect groups.
-/

public section

namespace TauCeti

open MonoidAlgebra

variable {R G G' : Type*} [CommSemiring R] [Group G] [Group G']

/-- A defect group of `x` is carried by a group isomorphism `σ` to a defect group of `σ x`. -/
theorem IsDefectGroup.domCongr_map (σ : G ≃* G') {p : ℕ} {x : MonoidAlgebra R G}
    {P : Subgroup G} (h : IsDefectGroup R p x P) :
    IsDefectGroup R p (domCongr R R σ x) (P.map σ.toMonoidHom) := by
  obtain ⟨hP, hPx, hmax⟩ := isDefectGroup_iff.1 h
  refine isDefectGroup_iff.2 ⟨hP.map _, (brauerProjection_map_domCongr_eq_zero_iff σ).not.2 hPx,
    fun Q hQ hQx hPQ ↦ ?_⟩
  -- pull `Q` back to `G`
  have hQ' : (Q.comap σ.toMonoidHom).map σ.toMonoidHom = Q :=
    Subgroup.map_comap_eq_self_of_surjective σ.surjective Q
  rw [← hQ'] at hQx hPQ ⊢
  rw [hmax _ (hQ.comap_of_injective _ σ.injective)
    ((brauerProjection_map_domCongr_eq_zero_iff σ).not.1 hQx)
    ((Subgroup.map_le_map_iff_of_injective σ.injective).1 hPQ)]

/-- **Transport of defect groups.** `σ(P)` is a defect group of `σ x` exactly when `P` is a
defect group of `x`. -/
theorem isDefectGroup_domCongr_map_iff (σ : G ≃* G') {p : ℕ} {x : MonoidAlgebra R G}
    {P : Subgroup G} :
    IsDefectGroup R p (domCongr R R σ x) (P.map σ.toMonoidHom) ↔ IsDefectGroup R p x P := by
  refine ⟨fun h ↦ ?_, IsDefectGroup.domCongr_map σ⟩
  have h' := h.domCongr_map σ.symm
  rwa [← domCongr_symm, AlgEquiv.symm_apply_apply, Subgroup.map_equiv_eq_comap_symm',
    MulEquiv.symm_symm, Subgroup.comap_map_eq_self_of_injective σ.injective] at h'

end TauCeti
