/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.RelativeSpec.Basic

/-!
# Relative spectra of trivial algebras

If the unit `𝒪_X ⟶ A` of a quasi-coherent commutative `𝒪_X`-algebra `A` is an isomorphism, the
structure morphism `Spec_X A ⟶ X` of its relative spectrum is an isomorphism
(`CategoryTheory.CommMon.isIso_relativeSpecToBase_of_isIso_one`): over every affine open `U` of
`X`, the relative spectrum is `Spec Γ(A, U)`, and the structure map `Γ(X, U) ⟶ Γ(A, U)` is the
unit on sections over `U`, hence bijective.

## Main declarations

* `CategoryTheory.CommMon.isIso_relativeSpecToBase_of_isIso_one`: a quasi-coherent algebra whose
  unit is an isomorphism has relative spectrum isomorphic to the base.
-/

public section

open CategoryTheory Limits Opposite AlgebraicGeometry MonObj

universe u

noncomputable section

namespace CategoryTheory.CommMon

variable {X : Scheme.{u}} (A : CommMon X.Modules)

/-- If the unit `𝒪_X ⟶ A` is an isomorphism, the structure map `Γ(X, U) ⟶ Γ(A, U)` is bijective
on every open `U`: it is the unit on sections over `U`. -/
theorem bijective_algebraMap_of_isIso_one [IsIso η[A.X]] (U : X.Opens) :
    Function.Bijective (algebraMap Γ(X, U) Γ(A.X, U)) := by
  rw [show (algebraMap Γ(X, U) Γ(A.X, U) : Γ(X, U) → Γ(A.X, U)) = (η[A.X]).app U from
    funext fun r ↦ (A.one_app_eq_algebraMap U r).symm]
  exact ConcreteCategory.bijective_of_isIso _

/-- **The relative spectrum of a trivial algebra is the base.** If the unit `𝒪_X ⟶ A` of a
quasi-coherent commutative `𝒪_X`-algebra is an isomorphism, the structure morphism
`Spec_X A ⟶ X` is an isomorphism: over an affine open `U`, it is `Spec` of the structure map
`Γ(X, U) ⟶ Γ(A, U)`, which is bijective. -/
theorem isIso_relativeSpecToBase_of_isIso_one [A.X.IsQuasicoherent] [IsIso η[A.X]] :
    IsIso A.relativeSpecToBase := by
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme)
    _ (iSup_affineOpens_eq_top X) fun U ↦ ?_
  let V : X.AffineZariskiSite := ⟨U.val, U.property⟩
  have hφ : IsIso (A.toSectionsPresheaf.app (op V.val)) := by
    rw [CommMon.toSectionsPresheaf_app]
    exact (ConcreteCategory.isIso_iff_bijective _).2 (A.bijective_algebraMap_of_isIso_one V.val)
  have hpb := A.isPullback_relativeSpecCover V
  have hpb' := isPullback_morphismRestrict A.relativeSpecToBase V.val
  have he : A.relativeSpecToBase ∣_ V.val = (hpb.isoIsPullback _ _ hpb').inv ≫
      Spec.map (A.toSectionsPresheaf.app (op V.val)) ≫ V.property.isoSpec.inv :=
    (Iso.eq_inv_comp _).2 (hpb.isoIsPullback_hom_fst _ _ hpb')
  refine (MorphismProperty.isomorphisms.iff _).mpr ?_
  rw [he]
  infer_instance

end CategoryTheory.CommMon
