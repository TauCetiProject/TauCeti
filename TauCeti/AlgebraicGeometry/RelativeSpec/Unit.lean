/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.RelativeSpec.AffineFunctions
public import TauCeti.AlgebraicGeometry.RelativeSpec.Affine

/-!
# Relative Spec recovers its algebra on affine charts

For a quasi-coherent algebra, the functions on the relative spectrum above an affine open
recover the sections of the original algebra on that open. This is the local comparison needed
for the algebra-side unit of the relative-Spec anti-equivalence.

The comparison is assembled from the pushforward description of regular functions, the affine
chart in the relative-Spec gluing, and `Scheme.ΓSpecIso`.

## References

* The Stacks Project, Tag 01LL (relative spectrum).
* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique II*, §1.3.
-/

public section

open CategoryTheory Opposite AlgebraicGeometry

namespace CategoryTheory.CommMon

universe u

noncomputable section

variable {X : Scheme.{u}} (A : CommMon X.Modules) [A.X.IsQuasicoherent]

/-- Sections of the function algebra of `Spec_X A` above an affine open are the sections of `A`.

The isomorphism is induced by identifying the inverse image of the affine open with the range
of its relative-Spec chart, then using the ordinary affine identification of global functions. -/
def relativeSpecCoverFunctionAlgebraSectionsRingEquiv (U : X.AffineZariskiSite) :
    Γ(A.relativeSpecToBase.pushforwardStructureAlgebra.X, U.1) ≃+* Γ(A.X, U.1) := by
  let ι := A.relativeSpecCover.f U
  have hpre : A.relativeSpecToBase ⁻¹ᵁ U.1 = ι ''ᵁ ⊤ := by
    rw [A.relativeSpecToBase_preimage, Scheme.Hom.image_top_eq_opensRange]
  exact (A.relativeSpecToBase.pushforwardStructureAlgebraSectionsRingEquiv U.1).trans
    (((A.relativeSpec.presheaf.mapIso (eqToIso hpre).op).symm ≪≫
      ι.appIso ⊤).commRingCatIsoToRingEquiv.trans
        (Scheme.ΓSpecIso (CommRingCat.of Γ(A.X, U.1))).commRingCatIsoToRingEquiv)

end

end CategoryTheory.CommMon

end
