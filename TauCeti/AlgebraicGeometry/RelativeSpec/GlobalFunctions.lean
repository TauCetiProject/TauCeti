/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.RelativeSpec.Affine
public import TauCeti.AlgebraicGeometry.Modules.Algebra.RegularFunctions

/-!
# Global functions on relative spectra over affine schemes

For a quasicoherent algebra on an affine scheme, the global functions on its relative
spectrum recover the global sections of the algebra, compatibly with the algebra structure
over the base. This is the affine normalization of the algebra-side unit in the
relative-Spec equivalence.

## References

* The Stacks Project, Tag 01LL (relative spectrum).
-/

public section

open CategoryTheory Opposite AlgebraicGeometry

namespace CategoryTheory.CommMon

universe u

noncomputable section

variable {X : Scheme.{u}} [IsAffine X] (A : CommMon X.Modules) [A.X.IsQuasicoherent]

-- The underlying ring map is the composite of global functions along the affine
-- normalization and the usual global-functions isomorphism for `Spec`.
private def relativeSpecGlobalSectionsRingEquiv :
    Γ(A.relativeSpecToBase.pushforwardStructureAlgebra.X, ⊤) ≃+* Γ(A.X, ⊤) := by
  haveI : IsIso A.relativeSpecIsoSpec.inv.appTop :=
    inferInstanceAs (IsIso (A.relativeSpecIsoSpec.inv.app ⊤))
  exact (A.relativeSpecToBase.pushforwardStructureAlgebraSectionsRingEquiv ⊤).trans
    ((asIso A.relativeSpecIsoSpec.inv.appTop).commRingCatIsoToRingEquiv.trans
      (Scheme.ΓSpecIso (CommRingCat.of Γ(A.X, ⊤))).commRingCatIsoToRingEquiv)

private theorem relativeSpecGlobalSectionsRingEquiv_apply
    (s : Γ(A.relativeSpecToBase.pushforwardStructureAlgebra.X, ⊤)) :
    A.relativeSpecGlobalSectionsRingEquiv s =
      (Scheme.ΓSpecIso (CommRingCat.of Γ(A.X, ⊤))).hom
        (A.relativeSpecIsoSpec.inv.appTop
          (A.relativeSpecToBase.pushforwardStructureAlgebraSectionsRingEquiv ⊤ s)) := by
  simp only [relativeSpecGlobalSectionsRingEquiv]
  rfl

-- Normalize the structure morphism on global sections once, including the
-- section-presheaf object wrapper, so ΓSpec naturality applies to the algebra map.
private theorem relativeSpecGlobalSections_baseMap :
    A.relativeSpecToBase.appTop ≫ A.relativeSpecIsoSpec.inv.appTop =
      X.isoSpec.inv.appTop ≫
        (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, ⊤) Γ(A.X, ⊤)))).appTop := by
  have h := congrArg Scheme.Hom.appTop A.relativeSpecIsoSpec_inv_relativeSpecToBase
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop] at h
  -- The two presentations carry definitionally equal section-ring instances;
  -- record that identification here rather than repeating it in the main proof.
  convert h using 1
  all_goals simp only [CommMon.toSectionsPresheaf_app]
  all_goals rfl

/-- The affine global-function comparison respects the algebra structures over the
global functions on the base. -/
def relativeSpecGlobalSectionsAlgEquiv :
    Γ(A.relativeSpecToBase.pushforwardStructureAlgebra.X, ⊤) ≃ₐ[Γ(X, ⊤)] Γ(A.X, ⊤) :=
  AlgEquiv.ofRingEquiv (f := A.relativeSpecGlobalSectionsRingEquiv) (by
    intro r
    have hx : X.isoSpec.inv.appTop ≫ (Scheme.ΓSpecIso Γ(X, ⊤)).hom = 𝟙 _ := by
      have hx' := congrArg Scheme.Hom.appTop X.isoSpec.hom_inv_id
      rw [Scheme.Hom.comp_appTop] at hx'
      simpa only [Scheme.isoSpec, asIso_hom, Scheme.toSpecΓ_appTop,
        Scheme.Hom.id_appTop] using hx'
    have h'' := congrArg (· ≫
      (Scheme.ΓSpecIso (CommRingCat.of Γ(A.X, ⊤))).hom) A.relativeSpecGlobalSections_baseMap
    simp only [Category.assoc] at h''
    rw [Scheme.ΓSpecIso_naturality (R := Γ(X, ⊤))
      (CommRingCat.ofHom (algebraMap Γ(X, ⊤) Γ(A.X, ⊤)))] at h''
    simp only [← Category.assoc] at h''
    rw [hx, Category.id_comp] at h''
    rw [relativeSpecGlobalSectionsRingEquiv_apply,
      Scheme.Hom.pushforwardStructureAlgebraSectionsRingEquiv_apply,
      Scheme.Hom.pushforwardStructureAlgebra_algebraMap]
    exact congrArg (fun f : Γ(X, ⊤) ⟶ CommRingCat.of Γ(A.X, ⊤) => f r) h'')

/-- The affine comparison evaluates a global function through the normalization
`Spec_X A ≅ Spec Γ(A)` and the global-functions isomorphism for `Spec`. -/
@[simp]
theorem relativeSpecGlobalSectionsAlgEquiv_apply
    (s : Γ(A.relativeSpecToBase.pushforwardStructureAlgebra.X, ⊤)) :
    A.relativeSpecGlobalSectionsAlgEquiv s =
      (Scheme.ΓSpecIso (CommRingCat.of Γ(A.X, ⊤))).hom
        (A.relativeSpecIsoSpec.inv.appTop
          (A.relativeSpecToBase.pushforwardStructureAlgebraSectionsRingEquiv ⊤ s)) := by
  exact A.relativeSpecGlobalSectionsRingEquiv_apply s

end

end CategoryTheory.CommMon

end
