/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Differentials.Restriction
public import TauCeti.AlgebraicGeometry.Modules.Differentials.Spec
public import Mathlib.CategoryTheory.Sites.Spaces

/-!
# Quasi-coherence of relative differentials

The relative differentials of any scheme over a commutative ring are quasi-coherent. On an
affine open, the restriction comparison identifies them with the sheaf associated to the module
of Kähler differentials of its coordinate ring. The resulting local presentations give
quasi-coherence on the whole scheme.

## References

* The Stacks Project, Section 29.33, Lemmas 29.33.3 and 29.33.5 (Tag 01UM).
* R. Hartshorne, *Algebraic Geometry*, Section II.8.
-/

public section

open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace

namespace TauCeti.AlgebraicGeometry

universe u

noncomputable section

variable (R : Type u) [CommRing R] (X : Scheme.{u}) [X.Over (Spec (.of R))]

private def affinePresentation (U : X.affineOpens) :
    ((X.relativeDifferentials R).over U.val).Presentation := by
  letI : Algebra R Γ(X, U) :=
    ((X.baseRingToStructurePresheaf R).app (op U.val)).hom.toAlgebra
  letI : U.property.fromSpec.IsOver (Spec (.of R)) := isOver_fromSpec R X U
  letI : IsOpenImmersion U.property.fromSpec :=
    IsAffineOpen.isOpenImmersion_fromSpec U.property
  let e := relativeDifferentialsRestrictIso R U.property.fromSpec ≪≫
    relativeDifferentialsSpecIso R Γ(X, U)
  let P := presentationTilde (ModuleCat.of Γ(X, U) Ω[Γ(X, U)⁄R])
    .univ (by simp) _ (Submodule.span_eq _)
  -- Supplying the isomorphism witnesses explicitly avoids instance search across the two
  -- presentations of the scheme's sheaf of rings (`TopCat.Sheaf` and `Sheaf`).
  let Q := @SheafOfModules.Presentation.ofIsIso.{u, u, u}
    _ _ _ _ _ _ _ _ e.inv e.isIso_inv P
  let Q' := Scheme.Modules.presentationRestrict U.property.isoSpec.hom Q
  let e' := ((Scheme.Modules.restrictFunctorComp U.property.isoSpec.hom
    U.property.fromSpec).app (X.relativeDifferentials R)).symm ≪≫
      (Scheme.Modules.restrictFunctorCongr U.property.isoSpec_hom_fromSpec).app
        (X.relativeDifferentials R)
  let Q'' := @SheafOfModules.Presentation.ofIsIso.{u, u, u}
    _ _ _ _ _ _ _ _ e'.hom e'.isIso_hom Q'
  let F := Scheme.Modules.overEquiv U.val
  let η := U.val.sheafOfModulesEquivOverInverseUnit X.ringCatSheaf
  let Q''' := @SheafOfModules.Presentation.map
    _ _ _ _ _ _ _ _ _ _ _ _ _ Q'' F.inverse
      F.symm.toAdjunction.leftAdjoint_preservesColimits η.symm
  let e'' := F.inverse.mapIso ((Scheme.Modules.overFunctorEquiv U.val).app
    (X.relativeDifferentials R)).symm ≪≫
      (F.unitIso.app ((X.relativeDifferentials R).over U.val)).symm
  exact SheafOfModules.Presentation.ofIsIso.{u, u, u} e''.hom Q'''

/-- The sheaf of relative differentials of a scheme over `Spec R` is quasi-coherent. -/
instance isQuasicoherent_relativeDifferentials : (X.relativeDifferentials R).IsQuasicoherent :=
  SheafOfModules.QuasicoherentData.isQuasicoherent (M := X.relativeDifferentials R)
    { I := X.affineOpens
      X := fun U ↦ U.val
      coversTop := (Opens.coversTop_iff X (fun U : X.affineOpens ↦ U.val)).mpr
        (iSup_affineOpens_eq_top X)
      presentation := affinePresentation R X }

end

end TauCeti.AlgebraicGeometry
