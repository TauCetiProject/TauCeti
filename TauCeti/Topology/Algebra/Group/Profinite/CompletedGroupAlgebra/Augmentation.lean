/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.MonoidAlgebra.Augmentation
public import TauCeti.Topology.Algebra.Group.Profinite.CompletedGroupAlgebra.Basic

/-!
# The augmentation of a completed group algebra

The augmentation `R[[Γ]] → R` of the completed group algebra is the common coefficient sum of the
projections to the group algebras `R[Γ ⧸ U]`: these agree, because the transition maps
`R[Γ ⧸ U] → R[Γ ⧸ V]` preserve coefficient sums. It sends every group element to `1` and is a
retraction of the structure map `R → R[[Γ]]`.

## Main definitions

* `TauCeti.completedGroupAlgebra.augmentation R Γ`: the augmentation `R[[Γ]] → R`.

## Main results

* `TauCeti.completedGroupAlgebra.augmentation_proj`: the augmentation is the coefficient sum of
  the projection to any level.
* `TauCeti.completedGroupAlgebra.augmentation_of`,
  `TauCeti.completedGroupAlgebra.augmentation_algebraMap`: its values on group elements and
  scalars.
* `TauCeti.completedGroupAlgebra.augmentation_surjective`: it is surjective.
-/

public section

namespace TauCeti

namespace completedGroupAlgebra

universe u v

variable (R : Type u) [CommRing R] (Γ : Type v) [Group Γ] [TopologicalSpace Γ]

/-- The **augmentation** `R[[Γ]] → R`: the coefficient sum of the projection to any finite level
`R[Γ ⧸ U]` (`augmentation_proj`), taken at the top level `Γ ⧸ Γ`. It sends every group element
to `1`. -/
noncomputable def augmentation : completedGroupAlgebra R Γ →+* R :=
  (MonoidAlgebra.augmentation R (Γ ⧸ (⊤ : OpenNormalSubgroup Γ).toSubgroup)).comp
    (proj R Γ ⊤).toRingHom

variable {R Γ}

/-- The augmentation of `R[[Γ]]` is the coefficient sum of the projection to any level. -/
@[simp]
theorem augmentation_proj (U : OpenNormalSubgroup Γ) (x : completedGroupAlgebra R Γ) :
    MonoidAlgebra.augmentation R (Γ ⧸ U.toSubgroup) (proj R Γ U x) = augmentation R Γ x := by
  rw [augmentation, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    ← mapDomain_mapOfLE_proj (le_top : U ≤ ⊤) x]
  exact (RingHom.congr_fun (MonoidAlgebra.augmentation_comp_mapDomainRingHom R
    (QuotientGroup.mapOfLE (le_top : U ≤ ⊤))) (proj R Γ U x)).symm

/-- The augmentation of the element with a prescribed compatible family of projections is the
coefficient sum of the member of the family at the top level `Γ ⧸ Γ`; by `augmentation_proj`
it is also that of the member at any other level. -/
@[simp]
theorem augmentation_mk (x : ∀ U : OpenNormalSubgroup Γ, MonoidAlgebra R (Γ ⧸ U.toSubgroup))
    (hx : ∀ ⦃U V : OpenNormalSubgroup Γ⦄ (hUV : U ≤ V),
      MonoidAlgebra.mapDomain (QuotientGroup.mapOfLE hUV) (x U) = x V) :
    augmentation R Γ (mk R Γ x hx) =
      MonoidAlgebra.augmentation R (Γ ⧸ (⊤ : OpenNormalSubgroup Γ).toSubgroup) (x ⊤) := by
  rw [← augmentation_proj ⊤, proj_mk]

/-- The augmentation sends every group element to `1`. -/
@[simp]
theorem augmentation_of (γ : Γ) : augmentation R Γ (of R Γ γ) = 1 := by
  rw [← augmentation_proj ⊤, proj_of, MonoidAlgebra.augmentation_single]

/-- The augmentation is a retraction of the structure map `R → R[[Γ]]`. -/
@[simp]
theorem augmentation_algebraMap (r : R) :
    augmentation R Γ (algebraMap R (completedGroupAlgebra R Γ) r) = r := by
  rw [← augmentation_proj ⊤, AlgHom.commutes, MonoidAlgebra.coe_algebraMap, Function.comp_apply,
    MonoidAlgebra.augmentation_single, Algebra.algebraMap_self, RingHom.id_apply]

/-- The augmentation is surjective. -/
theorem augmentation_surjective : Function.Surjective (augmentation R Γ) :=
  fun r ↦ ⟨algebraMap R _ r, augmentation_algebraMap r⟩

end completedGroupAlgebra

end TauCeti
