/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Differentials.Restriction
public import TauCeti.AlgebraicGeometry.Modules.Differentials.Spec
public import TauCeti.AlgebraicGeometry.Modules.Localization
public import TauCeti.AlgebraicGeometry.Modules.Tilde.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import Mathlib.CategoryTheory.Sites.Spaces

/-!
# Quasi-coherence and finite presentation of relative differentials

The relative differentials of any scheme over a commutative ring are quasi-coherent. On an
affine open, the restriction comparison identifies them with the sheaf associated to the module
of Kähler differentials of its coordinate ring. The resulting local presentations give
quasi-coherence on the whole scheme. If the structure morphism is locally of finite
presentation, the same comparisons give finite presentation of the differential sheaf. No
Noetherian, properness, or smoothness assumption is needed.

On global sections over an affine open `U`, the same comparisons identify `Γ(Ω_{X/R}, U)` with
the module of Kähler differentials `Ω[Γ(X, U)⁄R]`, matching `d a` with `D a`. In particular, if
`X` is locally of finite type over `Spec R`, these modules of sections are finitely generated,
which is the finiteness needed to form the Fitting ideal sheaves of `Ω_{X/R}`.

## Main declarations

* `TauCeti.AlgebraicGeometry.isQuasicoherent_relativeDifferentials`: `Ω_{X/R}` is
  quasi-coherent;
* `TauCeti.AlgebraicGeometry.isFinitePresentation_relativeDifferentials`: `Ω_{X/R}` is finitely
  presented when `X` is locally of finite presentation over `Spec R`;
* `TauCeti.AlgebraicGeometry.relativeDifferentialsSectionsEquiv`: over an affine open `U`,
  `Ω[Γ(X, U)⁄R] ≃ Γ(Ω_{X/R}, U)`, characterized by
  `TauCeti.AlgebraicGeometry.relativeDifferentialsSectionsEquiv_D`;
* `TauCeti.AlgebraicGeometry.finite_relativeDifferentials_sections`: these modules of sections
  are finitely generated when `X` is locally of finite type over `Spec R`.

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

private def affinePresentation (U : X.affineOpens)
    (P : letI : Algebra R Γ(X, U) :=
      ((X.baseRingToStructurePresheaf R).app (op U.val)).hom.toAlgebra
      (tilde (ModuleCat.of Γ(X, U) Ω[Γ(X, U)⁄R])).Presentation) :
    ((X.relativeDifferentials R).over U.val).Presentation := by
  letI : Algebra R Γ(X, U) :=
    ((X.baseRingToStructurePresheaf R).app (op U.val)).hom.toAlgebra
  letI : U.property.fromSpec.IsOver (Spec (.of R)) := isOver_fromSpec R X U
  letI : IsOpenImmersion U.property.fromSpec :=
    IsAffineOpen.isOpenImmersion_fromSpec U.property
  let e := relativeDifferentialsRestrictIso R U.property.fromSpec ≪≫
    relativeDifferentialsSpecIso R Γ(X, U)
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
      presentation U :=
        letI : Algebra R Γ(X, U) :=
          ((X.baseRingToStructurePresheaf R).app (op U.val)).hom.toAlgebra
        affinePresentation R X U (presentationTilde (ModuleCat.of Γ(X, U) Ω[Γ(X, U)⁄R])
          .univ (by simp) _ (Submodule.span_eq _)) }

private theorem isFinite_affinePresentation (U : X.affineOpens)
    (P : letI : Algebra R Γ(X, U) :=
      ((X.baseRingToStructurePresheaf R).app (op U.val)).hom.toAlgebra
      (tilde (ModuleCat.of Γ(X, U) Ω[Γ(X, U)⁄R])).Presentation) [P.IsFinite] :
    (affinePresentation R X U P).IsFinite := by
  dsimp only [affinePresentation]
  apply +allowSynthFailures SheafOfModules.instIsFiniteOfIsIso
  apply +allowSynthFailures SheafOfModules.Presentation.isFinite_map
  apply +allowSynthFailures SheafOfModules.instIsFiniteOfIsIso
  unfold Scheme.Modules.presentationRestrict
  apply +allowSynthFailures SheafOfModules.Presentation.isFinite_map
  apply +allowSynthFailures SheafOfModules.instIsFiniteOfIsIso

private theorem exists_finiteAffinePresentation
    [LocallyOfFinitePresentation (X ↘ Spec (.of R))] (U : X.affineOpens) :
    ∃ P : ((X.relativeDifferentials R).over U.val).Presentation, P.IsFinite := by
  let : Algebra R Γ(X, U) :=
    ((X.baseRingToStructurePresheaf R).app (op U.val)).hom.toAlgebra
  let : U.property.fromSpec.IsOver (Spec (.of R)) := isOver_fromSpec R X U
  let : IsOpenImmersion U.property.fromSpec :=
    IsAffineOpen.isOpenImmersion_fromSpec U.property
  have hfp : LocallyOfFinitePresentation
      (Spec.map (CommRingCat.ofHom (algebraMap R Γ(X, U)))) := by
    have hc : LocallyOfFinitePresentation (U.property.fromSpec ≫ X ↘ Spec (.of R)) :=
      inferInstance
    rw [HomIsOver.comp_over (f := U.property.fromSpec) (S := Spec (.of R))] at hc
    exact hc
  have : Algebra.FinitePresentation R Γ(X, U) :=
    RingHom.finitePresentation_algebraMap.mp
      ((LocallyOfFinitePresentation.SpecMap_iff _).mp hfp)
  obtain ⟨s, hs, t, ht⟩ := Module.FinitePresentation.out
    (R := Γ(X, U)) (M := Ω[Γ(X, U)⁄R])
  let P := presentationTilde (ModuleCat.of Γ(X, U) Ω[Γ(X, U)⁄R]) s hs t ht
  have : P.IsFinite := isFinite_presentationTilde _ _ hs _ ht
  exact ⟨affinePresentation R X U P, isFinite_affinePresentation R X U P⟩

/-- Relative differentials of a scheme locally of finite presentation over `Spec R` are
finitely presented as a sheaf of modules. -/
instance isFinitePresentation_relativeDifferentials
    [LocallyOfFinitePresentation (X ↘ Spec (.of R))] :
    (X.relativeDifferentials R).IsFinitePresentation := by
  let q : (X.relativeDifferentials R).QuasicoherentData :=
    { I := X.affineOpens
      X := fun U ↦ U.val
      coversTop := (Opens.coversTop_iff X (fun U : X.affineOpens ↦ U.val)).mpr
        (iSup_affineOpens_eq_top X)
      presentation U := (exists_finiteAffinePresentation R X U).choose }
  have : q.IsFinitePresentation := by
    refine { isFinite_presentation := ?_ }
    intro U
    exact (exists_finiteAffinePresentation R X U).choose_spec
  exact SheafOfModules.IsFinitePresentation.mk (M := X.relativeDifferentials R)
    ⟨q, inferInstance⟩

/-- If `X` is locally of finite type over `Spec R`, then the ring of functions `Γ(X, U)` on every
affine open `U` is a finitely generated `R`-algebra. -/
theorem finiteType_sections_of_locallyOfFiniteType [LocallyOfFiniteType (X ↘ Spec (.of R))]
    (U : X.affineOpens) :
    letI : Algebra R Γ(X, U) :=
      ((X.baseRingToStructurePresheaf R).app (op U.val)).hom.toAlgebra
    Algebra.FiniteType R Γ(X, U) := by
  let : Algebra R Γ(X, U) :=
    ((X.baseRingToStructurePresheaf R).app (op U.val)).hom.toAlgebra
  let : U.property.fromSpec.IsOver (Spec (.of R)) := isOver_fromSpec R X U
  have : IsOpenImmersion U.property.fromSpec := IsAffineOpen.isOpenImmersion_fromSpec U.property
  have hc : LocallyOfFiniteType (U.property.fromSpec ≫ X ↘ Spec (.of R)) := inferInstance
  rw [HomIsOver.comp_over (f := U.property.fromSpec) (S := Spec (.of R))] at hc
  exact RingHom.finiteType_algebraMap.mp (HasRingHomProperty.Spec_iff.mp hc)

/-- Over an affine open `U`, the sections of the sheaf of relative differentials are the Kähler
differentials of the ring of functions: `Ω[Γ(X, U)⁄R] ≃ Γ(Ω_{X/R}, U)`, sending `D a` to `d a`
(`relativeDifferentialsSectionsEquiv_D`). -/
def relativeDifferentialsSectionsEquiv (U : X.affineOpens) :
    letI : Algebra R Γ(X, U) :=
      ((X.baseRingToStructurePresheaf R).app (op U.val)).hom.toAlgebra
    Ω[Γ(X, U)⁄R] ≃ₗ[Γ(X, U)] Γ(X.relativeDifferentials R, U) :=
  letI : Algebra R Γ(X, U) :=
    ((X.baseRingToStructurePresheaf R).app (op U.val)).hom.toAlgebra
  letI : U.property.fromSpec.IsOver (Spec (.of R)) := isOver_fromSpec R X U
  haveI : IsOpenImmersion U.property.fromSpec :=
    IsAffineOpen.isOpenImmersion_fromSpec U.property
  -- Pass through the affine chart `Spec Γ(X, U) ⟶ X`: the restriction comparison and the affine
  -- computation `Ω_{Spec A/R} ≅ Ω[A⁄R]~` identify the global sections of the restriction.
  (tilde.isoTop (.of Γ(X, U) Ω[Γ(X, U)⁄R]) ≪≫ moduleSpecΓFunctor.mapIso
    ((relativeDifferentialsSpecIso R Γ(X, U)).symm ≪≫
      (relativeDifferentialsRestrictIso R U.property.fromSpec).symm)).toLinearEquiv.trans
    ((X.relativeDifferentials R).fromSpecSectionsEquiv U.property).symm

/-- The identification `Ω[Γ(X, U)⁄R] ≃ Γ(Ω_{X/R}, U)` sends the Kähler differential `D a` of a
function `a` on `U` to its differential `d a`. -/
@[simp]
theorem relativeDifferentialsSectionsEquiv_D (U : X.affineOpens) (a : Γ(X, U)) :
    letI : Algebra R Γ(X, U) :=
      ((X.baseRingToStructurePresheaf R).app (op U.val)).hom.toAlgebra
    relativeDifferentialsSectionsEquiv R X U (KaehlerDifferential.D R Γ(X, U) a) =
      (X.universalDerivation R).d (X := op U.val) a := by
  let : Algebra R Γ(X, U) :=
    ((X.baseRingToStructurePresheaf R).app (op U.val)).hom.toAlgebra
  let : U.property.fromSpec.IsOver (Spec (.of R)) := isOver_fromSpec R X U
  have : IsOpenImmersion U.property.fromSpec := IsAffineOpen.isOpenImmersion_fromSpec U.property
  unfold relativeDifferentialsSectionsEquiv
  refine (LinearEquiv.trans_apply ..).trans ((LinearEquiv.symm_apply_eq _).mpr ?_)
  refine Eq.trans ?_ (Scheme.Modules.fromSpecSectionsEquiv_apply _ _ _).symm
  have h : U.property.fromSpec ''ᵁ ⊤ = U.val := by
    rw [Scheme.Hom.image_top_eq_opensRange, U.property.opensRange_fromSpec]
  -- The function on `Spec Γ(X, U)` corresponding to `a` is carried back to the restriction of
  -- `a` along `U.property.fromSpec ''ᵁ ⊤ = U`.
  have ha : (U.property.fromSpec.appIso ⊤).inv (algebraMap Γ(X, U) Γ(Spec Γ(X, U), ⊤) a) =
      X.presheaf.map (homOfLE h.le).op a := by
    have := ConcreteCategory.congr_hom (U.property.presheaf_map_fromSpec_appIso_hom ⊤) a
    simp only [ConcreteCategory.comp_apply] at this
    exact (congrArg (U.property.fromSpec.appIso ⊤).inv this.symm).trans
      (Iso.hom_inv_id_apply _ _)
  -- Follow `D a` through the three comparisons; each step is the defining property of one of
  -- them, and the restriction map of `M.restrict` at `⊤` is that of `M` by definition.
  refine (congrArg ((relativeDifferentialsRestrictIso R U.property.fromSpec).inv.app ⊤)
    (relativeDifferentialsSpecIso_inv_app_toOpen R Γ(X, U) ⊤ a)).trans ?_
  refine (relativeDifferentialsRestrictIso_inv_app_d R U.property.fromSpec ⊤ _).trans ?_
  rw [ha]
  exact (X.universalDerivation R).d_map (homOfLE h.le).op a

/-- If `X` is locally of finite type over `Spec R`, the sections of `Ω_{X/R}` over every affine
open `U` form a finitely generated `Γ(X, U)`-module. -/
instance finite_relativeDifferentials_sections [LocallyOfFiniteType (X ↘ Spec (.of R))]
    (U : X.affineOpens) : Module.Finite Γ(X, U) Γ(X.relativeDifferentials R, U) := by
  let : Algebra R Γ(X, U) :=
    ((X.baseRingToStructurePresheaf R).app (op U.val)).hom.toAlgebra
  have := finiteType_sections_of_locallyOfFiniteType R X U
  exact Module.Finite.equiv (relativeDifferentialsSectionsEquiv R X U)

end

end TauCeti.AlgebraicGeometry
