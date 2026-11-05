/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.RelativeSpec.Unit

/-!
# Global functions on relative spectra

For a quasi-coherent algebra `A` on a scheme `X`, the global functions on its relative spectrum
are the global sections of `A`, as algebras over the global functions on the base: this is the
global component `CategoryTheory.CommMon.sectionsAlgEquiv A.relativeSpecPushforwardIso ⊤` of the
algebra-side unit `CategoryTheory.CommMon.relativeSpecPushforwardIso`. Over an affine base, this
file identifies it with the normalization `Spec_X A ≅ Spec Γ(A)` followed by the global-functions
isomorphism for `Spec`.

## References

* The Stacks Project, Tag 01LL (relative spectrum).
-/

public section

open CategoryTheory Opposite AlgebraicGeometry

namespace CategoryTheory.CommMon

universe u

variable {X : Scheme.{u}} (A : CommMon X.Modules) [A.X.IsQuasicoherent]

/-- Over an affine base, the global component of the isomorphism `p_* 𝒪 ≅ A` evaluates a global
function through the normalization `Spec_X A ≅ Spec Γ(A)` and the global-functions isomorphism
for `Spec`. -/
-- Not a simp lemma: `CommMon.sectionsAlgEquiv_apply` already rewrites its left-hand side.
theorem sectionsAlgEquiv_relativeSpecPushforwardIso_top_apply [IsAffine X]
    (s : Γ(A.relativeSpecToBase.pushforwardStructureAlgebra.X, ⊤)) :
    CommMon.sectionsAlgEquiv A.relativeSpecPushforwardIso ⊤ s =
      (Scheme.ΓSpecIso (CommRingCat.of Γ(A.X, ⊤))).hom
        (A.relativeSpecIsoSpec.inv.appTop
          (A.relativeSpecToBase.pushforwardStructureAlgebraSectionsRingEquiv ⊤ s)) := by
  rw [CommMon.sectionsAlgEquiv_apply]
  refine (A.sectionsAlgHom_relativeSpecPushforwardIso_hom_apply ⟨⊤, isAffineOpen_top X⟩ s).trans
    ((A.relativeSpecCoverFunctionAlgebraSectionsRingEquiv_apply ⟨⊤, isAffineOpen_top X⟩ s).trans
      ?_)
  have h : (A.relativeSpecCover.f ⟨⊤, isAffineOpen_top X⟩).appLE _ ⊤
      (A.top_le_preimage_relativeSpecToBase ⟨⊤, isAffineOpen_top X⟩) =
      (A.relativeSpecCover.f ⟨⊤, isAffineOpen_top X⟩).appTop :=
    Scheme.Hom.appLE_eq_app _
  rw [relativeSpecIsoSpec_inv]
  exact congrArg _ (ConcreteCategory.congr_hom h _)

end CategoryTheory.CommMon

end
