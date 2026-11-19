/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.RestrictScalars
public import TauCeti.AlgebraicGeometry.Modules.FinitePresentation.Basic
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Pushforward.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation

/-!
# Finite pushforward of module sheaves

Pushforward along a finite morphism preserves finite presentation in two settings:
* when the target is locally Noetherian and the source module is quasi-coherent and of finite type,
  permitting coherent coefficients on a closed subscheme to be viewed as coherent coefficients on
  its ambient scheme (in particular under a projective embedding);
* without Noetherian hypotheses, when the morphism is also locally of finite presentation and the
  source module is finitely presented (Stacks, Lemma 29.21.4 (0562)).

The affine calculation uses the existing quasi-coherent pushforward theorem and the
tilde/global-sections comparison. A finite module over a finite algebra is finite over the
base ring (giving a finite presentation over a Noetherian base), while a finitely presented module
over a finite and finitely presented algebra is finitely presented over the base ring.

## References

* R. Hartshorne, *Algebraic Geometry*, Proposition II.5.5.
* The Stacks Project, Tag 01Y6 (coherent pushforward along finite morphisms).
* [The Stacks Project, Lemma 29.21.4](https://stacks.math.columbia.edu/tag/0562)
-/

public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

/-- The sections of a finite pushforward over an affine open form a finite module if the
original sheaf is quasi-coherent and of finite type. No Noetherian hypothesis is needed. -/
theorem finite_sections_pushforward (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType]
    (f : X ⟶ Y) [IsFinite f] (U : Y.Opens) (hU : IsAffineOpen U) :
    Module.Finite Γ(Y, U) Γ((pushforward f).obj M, U) := by
  -- Pushforward sections are the restriction of scalars of the preimage sections
  -- along `f.app U`, definitionally as objects of `ModuleCat`.
  exact (ModuleCat.isFG_iff _).mp
    ((f.app U).hom.isFG_restrictScalars_of_finite (f.finite_app U hU)
      ((ModuleCat.isFG_iff _).mpr (M.finite_sections_of_isAffineOpen _ (hU.preimage f))))

/-- The sections of a finite pushforward along a locally finitely presented morphism over an affine
open form a finitely presented module if the original sheaf is finitely presented. -/
theorem finitePresentation_sections_pushforward (M : X.Modules) [M.IsFinitePresentation]
    (f : X ⟶ Y) [IsFinite f] [LocallyOfFinitePresentation f] (U : Y.Opens) (hU : IsAffineOpen U) :
    Module.FinitePresentation Γ(Y, U) Γ((pushforward f).obj M, U) := by
  have hfp : (f.app U).hom.FinitePresentation := by
    rw [f.app_eq_appLE]
    exact f.finitePresentation_appLE hU (hU.preimage f) le_rfl
  let : Algebra Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra
  have : Module.Finite Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := f.finite_app U hU
  have : Algebra.FinitePresentation Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := hfp
  have : Module.FinitePresentation Γ(Y, U) Γ(X, f ⁻¹ᵁ U) :=
    .of_finite_of_finitePresentation Γ(Y, U) Γ(X, f ⁻¹ᵁ U)
  have : Module.FinitePresentation Γ(X, f ⁻¹ᵁ U) Γ(M, f ⁻¹ᵁ U) :=
    M.finitePresentation_sections_of_isAffineOpen _ (hU.preimage f)
  let : Module Γ(Y, U) Γ(M, f ⁻¹ᵁ U) := Module.compHom _ (f.app U).hom
  have : IsScalarTower Γ(Y, U) Γ(X, f ⁻¹ᵁ U) Γ(M, f ⁻¹ᵁ U) :=
    ⟨fun r s m ↦ mul_smul ((f.app U).hom r) s m⟩
  -- Elaborate with the local `R`-module structure carrying the scalar tower before matching the
  -- restriction-of-scalars module structure on `Γ((pushforward f).obj M, U)`.
  have hRM : Module.FinitePresentation Γ(Y, U) Γ(M, f ⁻¹ᵁ U) :=
    .trans Γ(Y, U) Γ(M, f ⁻¹ᵁ U) Γ(X, f ⁻¹ᵁ U)
  exact hRM

-- First obtain a finite presentation on the spectrum of an affine open, then carry it
-- to the open subscheme and its slice site. Only these presentations are used in descent.
private theorem exists_isFinite_presentation_over_pushforward
    (M : X.Modules) [M.IsQuasicoherent] (f : X ⟶ Y) [IsFinite f] (U : Y.affineOpens)
    (hfp : Module.FinitePresentation Γ(Y, U.1) Γ((pushforward f).obj M, U.1)) :
    ∃ P : (((pushforward f).obj M).over U.1).Presentation, P.IsFinite := by
  let N := (pushforward f).obj M
  have : N.IsQuasicoherent := Scheme.Modules.isQuasicoherent_pushforward M f
  have : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
  let K := N.restrict U.2.fromSpec
  have : K.IsQuasicoherent := inferInstance
  have : Module.FinitePresentation Γ(Y, U.1) (moduleSpecΓFunctor.obj K) := by
    -- The global-section functor and `Γ(K, ⊤)` have the same sections and scalar action;
    -- their category wrappers differ. Convert this comparison explicitly.
    convert! Module.FinitePresentation.of_equiv (N.fromSpecSectionsEquiv U.2)
  have : K.IsFinitePresentation :=
    (SheafOfModules.isFinitePresentation (Spec Γ(Y, U.1)).ringCatSheaf).prop_of_iso
      (@asIso _ _ _ _ K.fromTildeΓ (isIso_fromTildeΓ_of_isQuasicoherent K))
      (TauCeti.AlgebraicGeometry.isFinitePresentation_tilde (moduleSpecΓFunctor.obj K))
  obtain ⟨P, hP⟩ := K.exists_isFinite_presentation_of_isAffine
  let F : SheafOfModules (Spec Γ(Y, U.1)).ringCatSheaf ⥤
      SheafOfModules U.1.toScheme.ringCatSheaf := restrictFunctor U.2.isoSpec.hom
  have : CategoryTheory.Limits.PreservesColimitsOfSize.{u, u} F :=
    (restrictAdjunction U.2.isoSpec.hom).leftAdjoint_preservesColimits
  let e : F.obj K ≅ N.restrict U.1.ι :=
    ((restrictFunctorComp U.2.isoSpec.hom U.2.fromSpec).app N).symm ≪≫
      (restrictFunctorCongr U.2.isoSpec_hom_fromSpec).app N
  -- The isomorphism is stated in scheme modules, while presentations use sheaves of
  -- modules. Supply its instance rather than asking instance search to cross the wrappers.
  let Q := @SheafOfModules.Presentation.ofIsIso _ _ _ _ _ _ _ _ e.hom
    (Iso.isIso_hom e) (P.map F (restrictUnitIso U.2.isoSpec.hom).symm)
  have : Q.IsFinite := by
    apply +allowSynthFailures SheafOfModules.instIsFiniteOfIsIso
    exact SheafOfModules.Presentation.isFinite_map _ _ _
  exact N.exists_isFinite_presentation_over_of_restrict U.1 Q

private theorem isFinitePresentation_pushforward_of_forall_affineOpens
    (M : X.Modules) [M.IsQuasicoherent] (f : X ⟶ Y) [IsFinite f]
    (hfp : ∀ U : Y.affineOpens,
      Module.FinitePresentation Γ(Y, U.1) Γ((pushforward f).obj M, U.1)) :
    ((pushforward f).obj M).IsFinitePresentation := by
  let N := (pushforward f).obj M
  have (U : Y.affineOpens) : (N.over U.1).IsFinitePresentation := by
    obtain ⟨P, _⟩ := exists_isFinite_presentation_over_pushforward M f U (hfp U)
    exact P.isFinitePresentation
  exact SheafOfModules.IsFinitePresentation.of_coversTop N (fun U : Y.affineOpens ↦ U.1)
    (by rw [Opens.coversTop_iff]; exact iSup_affineOpens_eq_top Y)

/-- Finite pushforward on a locally Noetherian target preserves finite presentation.
It suffices that the source coefficient is quasi-coherent and of finite type. -/
instance isFinitePresentation_pushforward_of_isFinite [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsFinite f] (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType] :
    ((pushforward f).obj M).IsFinitePresentation :=
  isFinitePresentation_pushforward_of_forall_affineOpens M f fun U ↦ by
    have : IsNoetherianRing Γ(Y, U.1) := IsLocallyNoetherian.component_noetherian U
    have : Module.Finite Γ(Y, U.1) Γ((pushforward f).obj M, U.1) :=
      M.finite_sections_pushforward f U.1 U.2
    exact Module.finitePresentation_of_finite _ _

/-- Direct image along a finite, locally finitely presented morphism preserves finite presentation
of `𝒪_X`-modules (Stacks, Lemma 29.21.4 (0562)). -/
@[stacks 0562]
instance isFinitePresentation_pushforward_of_isFinite_of_locallyOfFinitePresentation
    (f : X ⟶ Y) [IsFinite f] [LocallyOfFinitePresentation f]
    (M : X.Modules) [M.IsFinitePresentation] :
    ((pushforward f).obj M).IsFinitePresentation :=
  isFinitePresentation_pushforward_of_forall_affineOpens M f fun U ↦
    M.finitePresentation_sections_pushforward f U.1 U.2

end AlgebraicGeometry.Scheme.Modules
