/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.RestrictScalars
public import TauCeti.AlgebraicGeometry.Modules.FinitePresentation
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Pushforward.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Finite pushforward of module sheaves

Pushforward along a finite morphism preserves coherent sheaves when the target is locally
Noetherian. This permits coherent coefficients on a closed subscheme to be viewed as coherent
coefficients on its ambient scheme, in particular under a projective embedding.

The affine calculation uses the existing quasi-coherent pushforward theorem and the
tilde/global-sections comparison. A finite module over a finite algebra is finite over the
base ring; over a Noetherian base this gives a finite presentation.

## References

* R. Hartshorne, *Algebraic Geometry*, Proposition II.5.5.
* The Stacks Project, Tag 01Y6 (coherent pushforward along finite morphisms).
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

-- First obtain a finite presentation on the spectrum of an affine open, then carry it
-- to the open subscheme and its slice site. Only these presentations are used in descent.
private theorem exists_isFinite_presentation_over_pushforward [IsLocallyNoetherian Y]
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType] (f : X ⟶ Y) [IsFinite f]
    (U : Y.affineOpens) : ∃ P : (((pushforward f).obj M).over U.1).Presentation, P.IsFinite := by
  let N := (pushforward f).obj M
  have : N.IsQuasicoherent := Scheme.Modules.isQuasicoherent_pushforward M f
  have : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
  let K := N.restrict U.2.fromSpec
  have : K.IsQuasicoherent := inferInstance
  have : IsNoetherianRing Γ(Y, U.1) := IsLocallyNoetherian.component_noetherian U
  have : Module.Finite Γ(Y, U.1) Γ(N, U.1) := M.finite_sections_pushforward f U.1 U.2
  have : Module.FinitePresentation Γ(Y, U.1) Γ(N, U.1) :=
    Module.finitePresentation_of_finite _ _
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

/-- Finite pushforward on a locally Noetherian target preserves finite presentation.
It suffices that the source coefficient is quasi-coherent and of finite type. -/
instance isFinitePresentation_pushforward_of_isFinite [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsFinite f] (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType] :
    ((pushforward f).obj M).IsFinitePresentation := by
  let N := (pushforward f).obj M
  have (U : Y.affineOpens) : (N.over U.1).IsFinitePresentation := by
    obtain ⟨P, hP⟩ := exists_isFinite_presentation_over_pushforward M f U
    exact P.isFinitePresentation
  exact SheafOfModules.IsFinitePresentation.of_coversTop N (fun U : Y.affineOpens ↦ U.1)
    (by rw [Opens.coversTop_iff]; exact iSup_affineOpens_eq_top Y)

end AlgebraicGeometry.Scheme.Modules
