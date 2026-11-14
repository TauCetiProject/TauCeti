/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Induction.Clifford.Obstruction.Basic
public import TauCeti.RepresentationTheory.Induction.Clifford.Extension.Naturality
public import TauCeti.RepresentationTheory.Homological.GroupCohomology.Functoriality

/-!
# Isomorphism invariance of the Clifford obstruction

An isomorphism of normal-subgroup representations identifies their inertia groups
and inertia quotients. Conjugating the operators of a compatible projective extension
and pulling back its factor set gives a compatible extension of the source representation.
Consequently the induced pullback on second cohomology carries the Clifford obstruction
of the target to that of the source. The obstruction therefore depends only on the
isomorphism class of the normal-subgroup representation.

The comparison uses the canonical quotient identification
`CategoryTheory.Iso.cliffordExtensionQuotientEquiv`. It works over arbitrary fields,
with the scalar-endomorphism hypothesis explicit and without finiteness of the group.

## References

* I. M. Isaacs, *Character Theory of Finite Groups* (1976), Chapter 11.
* G. Karpilovsky, *Projective Representations of Finite Groups* (1985).
-/

public noncomputable section

open CategoryTheory

namespace TauCeti.IsProjectiveInertiaExtension

variable {k G : Type*} [CommRing k] [Group G] {N : Subgroup G} [N.Normal]
  {A B : FDRep k N}
  {ρ : inertia B → B ≃ₗ[k] B}
  {β : inertia B ⧸ N.subgroupOf (inertia B) → inertia B ⧸ N.subgroupOf (inertia B) → kˣ}

/-- Conjugating a compatible projective extension along a representation isomorphism
pulls back its quotient factor set along the canonical inertia-quotient equivalence. -/
theorem of_iso (h : IsProjectiveInertiaExtension B ρ β) (e : A ≅ B) :
    IsProjectiveInertiaExtension A
      (fun t ↦ (FDRep.isoToLinearEquiv e).trans
        ((ρ (MulEquiv.subgroupCongr (inertia_congr e) t)).trans
          (FDRep.isoToLinearEquiv e).symm))
      (fun q r ↦ β (e.cliffordExtensionQuotientEquiv q)
        (e.cliffordExtensionQuotientEquiv r)) where
  isProjectiveRep := {
    isFactorSet := by
      have := h.isProjectiveRep.isFactorSet
      simpa only [MulEquiv.coe_toMonoidHom, e.cliffordExtensionQuotientEquiv_mk] using
        IsFactorSet.comp (MulEquiv.subgroupCongr (inertia_congr e)).toMonoidHom
          (fun s t : inertia B ↦ β s t)
    map_one := by
      ext x
      simp [h.isProjectiveRep.map_one]
    mul_apply s t x := by
      simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
      rw [h.isProjectiveRep.mul_apply, map_smul]
      simp only [map_mul, e.cliffordExtensionQuotientEquiv_mk]
  }
  apply_inclusion n x := by
    have hn : MulEquiv.subgroupCongr (inertia_congr e)
        (Subgroup.inclusion (le_inertia A) n) = Subgroup.inclusion (le_inertia B) n :=
      Subtype.ext rfl
    simp only [LinearEquiv.trans_apply, hn, h.apply_inclusion]
    simp [FDRep.Iso.conj_ρ e, LinearEquiv.conj_apply]

section Cohomology

attribute [local instance] trivialMulDistribMulAction

variable {k G : Type} [CommRing k] [Group G] {N : Subgroup G} [N.Normal]
  {A B : FDRep k N}
  {ρ : inertia B → B ≃ₗ[k] B}
  {β : inertia B ⧸ N.subgroupOf (inertia B) → inertia B ⧸ N.subgroupOf (inertia B) → kˣ}

/-- Pulling back the class of a compatible extension along the canonical quotient
identification gives the class of its transported extension. No scalar-Schur or
nonzero hypothesis is needed for this comparison of supplied factor sets. -/
theorem map_cohomologyClass_factorSet_of_iso (h : IsProjectiveInertiaExtension B ρ β)
    (e : A ≅ B) :
    groupCohomology.map e.cliffordExtensionQuotientEquiv.toMonoidHom (𝟙 _) 2
      h.factorSet.cohomologyClass = (h.of_iso e).factorSet.cohomologyClass := by
  rw [FactorSet.cohomologyClass_def, FactorSet.cohomologyClass_def,
    groupCohomology.H2π_comp_map_apply]
  apply congrArg (groupCohomology.H2π _)
  ext q r
  rw [TauCeti.groupCohomology.mapCocycles₂_apply]
  simp only [Rep.hom_id, Representation.IntertwiningMap.id_apply]
  -- Restriction views the same coefficient carrier as a different representation.
  -- Use the cocycle evaluation equations across these two carrier presentations.
  erw [congrFun h.factorSet.coe_toCocycles₂ _,
    congrFun (h.of_iso e).factorSet.coe_toCocycles₂ _]
  simp only [factorSet_apply, MulEquiv.coe_toMonoidHom]
  rfl

end Cohomology

end TauCeti.IsProjectiveInertiaExtension

namespace CategoryTheory.Iso

open TauCeti

attribute [local instance] trivialMulDistribMulAction

variable {k G : Type} [Field k] [Group G] {N : Subgroup G} [N.Normal]
  {A B : FDRep k N} [Nontrivial A] [Nontrivial B]

/-- The pullback along the canonical inertia-quotient identification carries the
Clifford obstruction of an isomorphic representation to the original obstruction. -/
theorem map_cliffordObstruction (e : A ≅ B)
    (hA : ∀ f : A ⟶ A, ∃ c : k, c • 𝟙 A = f)
    (hB : ∀ f : B ⟶ B, ∃ c : k, c • 𝟙 B = f) :
    groupCohomology.map e.cliffordExtensionQuotientEquiv.toMonoidHom (𝟙 _) 2
      (cliffordObstruction B hB) = cliffordObstruction A hA := by
  obtain ⟨ρ, β, h⟩ := exists_isProjectiveInertiaExtension B hB
  rw [← h.cohomologyClass_factorSet_eq_cliffordObstruction hB,
    h.map_cohomologyClass_factorSet_of_iso e,
    (h.of_iso e).cohomologyClass_factorSet_eq_cliffordObstruction hA]

end CategoryTheory.Iso
