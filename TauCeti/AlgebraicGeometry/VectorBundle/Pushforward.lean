/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.ScalarChange
public import TauCeti.AlgebraicGeometry.AffineGroupScheme.HopfSpec
public import TauCeti.AlgebraicGeometry.FinitelyPresentedSheaf.Pushforward
public import TauCeti.AlgebraicGeometry.Modules.Algebra.Functoriality
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Colimits
public import TauCeti.AlgebraicGeometry.Morphisms.Finite.Basic
public import TauCeti.AlgebraicGeometry.VectorBundle.Affine.Basic
public import TauCeti.AlgebraicGeometry.VectorBundle.OpenCover

/-!
# Pushforward of finite locally free sheaves along finite locally free morphisms

A quasi-coherent `𝒪_X`-module `M` on a scheme `X` is finite locally free if and only if, over every
affine open `U` of `X`, its module of sections `Γ(M, U)` is finitely generated and projective over
`Γ(X, U)` (`AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree_iff_forall_isAffineOpen`). Over
each affine chart `Spec Γ(X, U) ⟶ X`, `M` restricts to the associated sheaf of `Γ(M, U)`, and on an
affine scheme associated sheaves of finitely generated projective modules are the finite locally
free sheaves (`TauCeti.AlgebraicGeometry.isFiniteLocallyFree_tilde_iff`).

Let `f : Y ⟶ X` be a finite, flat, locally finitely presented morphism of schemes (a finite locally
free morphism in the sense of Stacks, Tag 02KB). Over an affine open `U` of `X`, the preimage
`f⁻¹ U` is affine and `Γ(Y, f⁻¹ U)` is finitely generated and projective over `Γ(X, U)`
(`AlgebraicGeometry.Scheme.Hom.projective_app`). Since restriction of scalars along a finitely
generated projective algebra preserves finitely generated projective modules
(`RingHom.finiteProjectiveModules_le_inverseImage_restrictScalars_iff`), the direct image `f_* M` of
a finite locally free `𝒪_Y`-module `M` is a finite locally free `𝒪_X`-module
(`AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree_pushforward`). Conversely, an affine morphism
`f : Y ⟶ X` is finite, flat and locally of finite presentation if and only if `f_* 𝒪_Y` is finite
locally free (`AlgebraicGeometry.Scheme.Hom.isFinite_and_flat_and_locallyOfFinitePresentation_iff`,
Stacks, Lemma 29.48.2 (02KB)).

Packaging the direct image on the full subcategory gives the additive functor
`TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.pushforward f`.

## Main declarations

* `AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree_iff_forall_isAffineOpen`: a quasi-coherent
  module is finite locally free if and only if its sections over every affine open are finitely
  generated and projective;
* `AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree_pushforward`: pushforward along a finite,
  flat, locally finitely presented morphism preserves finite locally free modules;
* `AlgebraicGeometry.Scheme.Hom.isFinite_and_flat_and_locallyOfFinitePresentation_iff`: Stacks,
  Lemma 29.48.2 (02KB), characterizing finite locally free morphisms by affineness and finite local
  freeness of `f_* 𝒪_Y`;
* `TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.pushforward`: pushforward of finite locally
  free sheaves along a finite, flat, locally finitely presented morphism.

## References

* [The Stacks Project, Section 29.48 and Lemma 29.48.2](https://stacks.math.columbia.edu/tag/02KB)
-/

public section

open CategoryTheory MonoidalCategory
open TauCeti.AlgebraicGeometry

universe u

noncomputable section

namespace AlgebraicGeometry

namespace Scheme.Modules

variable {X Y : Scheme.{u}}

/-- **Affine-open criterion for finite local freeness.** A quasi-coherent `𝒪_X`-module `M` is
finite locally free if and only if, for every affine open `U` of `X`, the `Γ(X, U)`-module `Γ(M, U)`
is finitely generated and projective. -/
theorem isFiniteLocallyFree_iff_forall_isAffineOpen (M : X.Modules) [M.IsQuasicoherent] :
    isFiniteLocallyFree X M ↔
      ∀ U : X.Opens, IsAffineOpen U → Module.Finite Γ(X, U) Γ(M, U) ∧
        Module.Projective Γ(X, U) Γ(M, U) := by
  refine ⟨fun hM U hU ↦ ?_, fun h ↦ ?_⟩
  · have : IsOpenImmersion hU.fromSpec := hU.isOpenImmersion_fromSpec
    let K : (Spec Γ(X, U)).Modules := (restrictFunctor hU.fromSpec).obj M
    have hK : isFiniteLocallyFree (Spec Γ(X, U)) K :=
      have : isFiniteLocallyFree _ ((pullback hU.fromSpec).obj M) :=
        have := hM.1; have := hM.2
        ⟨isLocallyFree_pullback hU.fromSpec M, isFinitePresentation_pullback hU.fromSpec M⟩
      (isFiniteLocallyFree (Spec Γ(X, U))).prop_of_iso
        ((restrictFunctorIsoPullback hU.fromSpec).app M).symm this
    obtain ⟨_, _⟩ :
        Module.Finite Γ(X, U) ((restrictFunctor hU.fromSpec ⋙ moduleSpecΓFunctor).obj M) ∧
          Module.Projective Γ(X, U) ((restrictFunctor hU.fromSpec ⋙ moduleSpecΓFunctor).obj M) :=
      FiniteLocallyFreeSheaf.finite_projective_moduleSpecΓ ⟨K, hK⟩
    let e := (hU.restrictFromSpecCompModuleSpecΓFunctorIso.app M).toLinearEquiv
    exact ⟨Module.Finite.equiv e, Module.Projective.of_equiv e⟩
  · rw [isFiniteLocallyFree_iff_forall_pullback
      (X.openCoverOfIsOpenCover (fun U : X.affineOpens ↦ U.1) (iSup_affineOpens_eq_top X))]
    intro U
    have hU : IsAffineOpen U.1 := U.2
    have : IsOpenImmersion hU.fromSpec := hU.isOpenImmersion_fromSpec
    let K : (Spec Γ(X, U.1)).Modules := (restrictFunctor hU.fromSpec).obj M
    have : K.IsQuasicoherent := inferInstance
    obtain ⟨_, _⟩ : Module.Finite Γ(X, U.1) ((sectionsFunctor U.1).obj M) ∧
        Module.Projective Γ(X, U.1) ((sectionsFunctor U.1).obj M) := h U.1 hU
    let e := (hU.restrictFromSpecCompModuleSpecΓFunctorIso.app M).toLinearEquiv.symm
    have : Module.Finite Γ(X, U.1) (moduleSpecΓFunctor.obj K) := Module.Finite.equiv e
    have : Module.Projective Γ(X, U.1) (moduleSpecΓFunctor.obj K) := Module.Projective.of_equiv e
    have hK : isFiniteLocallyFree (Spec Γ(X, U.1)) K :=
      (isFiniteLocallyFree (Spec Γ(X, U.1))).prop_of_iso
        (@asIso _ _ _ _ K.fromTildeΓ (isIso_fromTildeΓ_of_isQuasicoherent K))
        (isFiniteLocallyFree_tilde (moduleSpecΓFunctor.obj K))
    have hpull : isFiniteLocallyFree (Spec Γ(X, U.1)) ((pullback hU.fromSpec).obj M) :=
      (isFiniteLocallyFree (Spec Γ(X, U.1))).prop_of_iso
        ((restrictFunctorIsoPullback hU.fromSpec).app M) hK
    have : isFiniteLocallyFree U.1.toScheme
        ((pullback hU.isoSpec.hom).obj ((pullback hU.fromSpec).obj M)) :=
      have := hpull.1; have := hpull.2
      ⟨isLocallyFree_pullback hU.isoSpec.hom _, isFinitePresentation_pullback hU.isoSpec.hom _⟩
    exact (isFiniteLocallyFree U.1.toScheme).prop_of_iso
      ((pullbackComp hU.isoSpec.hom hU.fromSpec).app M ≪≫
        (pullbackCongr hU.isoSpec_hom_fromSpec).app M) this

private theorem isQuasicoherent_of_isFiniteLocallyFree {M : X.Modules}
    (hM : isFiniteLocallyFree X M) : M.IsQuasicoherent :=
  -- Mathlib's instance deriving quasi-coherence from local freeness is stated for sheaves of
  -- modules, and instance search does not unfold `X.Modules`.
  let F : _root_.SheafOfModules X.ringCatSheaf := M
  have : F.IsLocallyFree := hM.1
  inferInstanceAs F.IsQuasicoherent

/-- The sections of a finite locally free `𝒪_X`-module over an affine open are finitely generated
over the functions on that open. -/
theorem finite_sections_of_isFiniteLocallyFree {M : X.Modules} (hM : isFiniteLocallyFree X M)
    (U : X.Opens) (hU : IsAffineOpen U) : Module.Finite Γ(X, U) Γ(M, U) :=
  have := isQuasicoherent_of_isFiniteLocallyFree hM
  ((isFiniteLocallyFree_iff_forall_isAffineOpen M).mp hM U hU).1

/-- The sections of a finite locally free `𝒪_X`-module over an affine open form a projective module
over the functions on that open. -/
theorem projective_sections_of_isFiniteLocallyFree {M : X.Modules} (hM : isFiniteLocallyFree X M)
    (U : X.Opens) (hU : IsAffineOpen U) : Module.Projective Γ(X, U) Γ(M, U) :=
  have := isQuasicoherent_of_isFiniteLocallyFree hM
  ((isFiniteLocallyFree_iff_forall_isAffineOpen M).mp hM U hU).2

/-- **Pushforward along a finite locally free morphism preserves finite locally free sheaves.** If
`f : Y ⟶ X` is finite, flat and locally of finite presentation, then the direct image `f_* M` of a
finite locally free `𝒪_Y`-module `M` is a finite locally free `𝒪_X`-module. -/
theorem isFiniteLocallyFree_pushforward (f : Y ⟶ X) [IsFinite f] [Flat f]
    [LocallyOfFinitePresentation f] {M : Y.Modules} (hM : isFiniteLocallyFree Y M) :
    isFiniteLocallyFree X ((pushforward f).obj M) := by
  have := isQuasicoherent_of_isFiniteLocallyFree hM
  have : ((pushforward f).obj M).IsQuasicoherent := isQuasicoherent_pushforward M f
  rw [isFiniteLocallyFree_iff_forall_isAffineOpen]
  intro U hU
  have hfin : (letI := (f.app U).hom.toModule; Module.Finite Γ(X, U) Γ(Y, f ⁻¹ᵁ U)) :=
    f.finite_app U hU
  have hproj : (letI := (f.app U).hom.toModule; Module.Projective Γ(X, U) Γ(Y, f ⁻¹ᵁ U)) :=
    f.projective_app ⟨U, hU⟩
  obtain ⟨hMfin, _⟩ :
      Module.Finite Γ(Y, f ⁻¹ᵁ U) ((sectionsFunctor (f ⁻¹ᵁ U)).obj M) ∧
        Module.Projective Γ(Y, f ⁻¹ᵁ U) ((sectionsFunctor (f ⁻¹ᵁ U)).obj M) :=
    (isFiniteLocallyFree_iff_forall_isAffineOpen M).mp hM (f ⁻¹ᵁ U) (hU.preimage f)
  -- Sections of `(pushforward f).obj M` over `U` are the restriction of scalars of `Γ(M, f⁻¹ U)`
  -- along `(f.app U).hom`.
  exact ⟨(ModuleCat.isFG_iff _).mp
      ((f.app U).hom.isFG_restrictScalars_of_finite hfin ((ModuleCat.isFG_iff _).mpr hMfin)),
    (f.app U).hom.projective_restrictScalars_of_projective hproj
      ((sectionsFunctor (f ⁻¹ᵁ U)).obj M)⟩

/-- If `f : Y ⟶ X` is finite, flat and locally of finite presentation, then `f_* 𝒪_Y` is a finite
locally free `𝒪_X`-module. -/
theorem isFiniteLocallyFree_pushforward_unit (f : Y ⟶ X) [IsFinite f] [Flat f]
    [LocallyOfFinitePresentation f] :
    isFiniteLocallyFree X ((pushforward f).obj (𝟙_ Y.Modules)) :=
  isFiniteLocallyFree_pushforward f (ObjectProperty.prop_unit (isFiniteLocallyFree Y))

end Scheme.Modules

namespace Scheme.Hom

variable {X Y : Scheme.{u}}

/-- The coordinate algebra `f_* 𝒪_Y` of a finite, flat, locally finitely presented morphism
`f : Y ⟶ X` has a finite locally free underlying `𝒪_X`-module. -/
theorem isFiniteLocallyFree_pushforwardStructureAlgebra (f : Y ⟶ X) [IsFinite f] [Flat f]
    [LocallyOfFinitePresentation f] :
    Scheme.Modules.isFiniteLocallyFree X f.pushforwardStructureAlgebra.X :=
  Scheme.Modules.isFiniteLocallyFree_pushforward_unit f

/-- **Characterization of finite locally free morphisms** (Stacks, Lemma 29.48.2 (02KB)). A morphism
of schemes `f : Y ⟶ X` is finite, flat and locally of finite presentation if and only if `f` is
affine and `f_* 𝒪_Y` is a finite locally free `𝒪_X`-module. -/
@[stacks 02KB]
theorem isFinite_and_flat_and_locallyOfFinitePresentation_iff (f : Y ⟶ X) :
    IsFinite f ∧ Flat f ∧ LocallyOfFinitePresentation f ↔
      IsAffineHom f ∧
        Scheme.Modules.isFiniteLocallyFree X
          ((Scheme.Modules.pushforward f).obj (𝟙_ Y.Modules)) := by
  refine ⟨fun ⟨_, _, _⟩ ↦ ⟨inferInstance, Scheme.Modules.isFiniteLocallyFree_pushforward_unit f⟩,
    fun ⟨_, h⟩ ↦ ?_⟩
  have hsec := (Scheme.Modules.isFiniteLocallyFree_iff_forall_isAffineOpen
    ((Scheme.Modules.pushforward f).obj (𝟙_ Y.Modules))).mp h
  have hfin : IsFinite f :=
    { finite_app U hU := (hsec U hU).1 }
  have hflat_fp (U : X.Opens) (hU : IsAffineOpen U) :
      (f.app U).hom.Flat ∧ (f.app U).hom.FinitePresentation := by
    algebraize [(f.app U).hom]
    have : Module.Finite Γ(X, U) Γ(Y, f ⁻¹ᵁ U) := (hsec U hU).1
    have hproj : Module.Projective Γ(X, U) Γ(Y, f ⁻¹ᵁ U) := (hsec U hU).2
    obtain ⟨hfl, hfp⟩ :=
      (TauCeti.moduleProjective_iff_flat_and_finitePresentation Γ(X, U) Γ(Y, f ⁻¹ᵁ U)).mp hproj
    exact ⟨RingHom.flat_algebraMap_iff.mpr hfl, RingHom.finitePresentation_algebraMap.mpr hfp⟩
  have hflat : Flat f := by
    have hloc := HasRingHomProperty.isLocal_ringHomProperty @Flat
    have key := (targetAffineLocally_affineAnd_iff' (Q := @RingHom.Flat)
      hloc.respectsIso f).symm.trans (targetAffineLocally_affineAnd_iff_affineLocally hloc f)
    rw [HasRingHomProperty.eq_affineLocally @Flat]
    exact (key.mp ⟨‹IsAffineHom f›, fun U hU ↦ (hflat_fp U hU).1⟩).2
  have hfp : LocallyOfFinitePresentation f := by
    have hloc := HasRingHomProperty.isLocal_ringHomProperty @LocallyOfFinitePresentation
    have key := (targetAffineLocally_affineAnd_iff' (Q := @RingHom.FinitePresentation)
      hloc.respectsIso f).symm.trans (targetAffineLocally_affineAnd_iff_affineLocally hloc f)
    rw [HasRingHomProperty.eq_affineLocally @LocallyOfFinitePresentation]
    exact (key.mp ⟨‹IsAffineHom f›, fun U hU ↦ (hflat_fp U hU).2⟩).2
  exact ⟨hfin, hflat, hfp⟩

/-- An affine morphism `f : Y ⟶ X` has finite locally free pushforward `f_* 𝒪_Y` if and only if `f`
is finite, flat and locally of finite presentation. -/
@[stacks 02KB]
theorem isFiniteLocallyFree_pushforward_unit_iff (f : Y ⟶ X) [IsAffineHom f] :
    Scheme.Modules.isFiniteLocallyFree X ((Scheme.Modules.pushforward f).obj (𝟙_ Y.Modules)) ↔
      IsFinite f ∧ Flat f ∧ LocallyOfFinitePresentation f := by
  rw [isFinite_and_flat_and_locallyOfFinitePresentation_iff, and_iff_right ‹IsAffineHom f›]

end Scheme.Hom

end AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf

open _root_.AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- Pushforward of finite locally free sheaves along a finite, flat, locally finitely presented
morphism `f : Y ⟶ X`. -/
def pushforward (f : Y ⟶ X) [IsFinite f] [Flat f] [LocallyOfFinitePresentation f] :
    FiniteLocallyFreeSheaf Y ⥤ FiniteLocallyFreeSheaf X :=
  (Scheme.Modules.isFiniteLocallyFree X).lift
    ((Scheme.Modules.isFiniteLocallyFree Y).ι ⋙ Scheme.Modules.pushforward f)
    fun E ↦ Scheme.Modules.isFiniteLocallyFree_pushforward f E.property

/-- The underlying sheaf of the pushforward of a finite locally free sheaf is its pushforward as an
`𝒪_Y`-module. -/
@[simp]
theorem pushforward_obj_obj (f : Y ⟶ X) [IsFinite f] [Flat f] [LocallyOfFinitePresentation f]
    (E : FiniteLocallyFreeSheaf Y) :
    ((pushforward f).obj E).obj = (Scheme.Modules.pushforward f).obj E.obj :=
  (rfl)

/-- Pushforward acts on a morphism of finite locally free sheaves by the underlying pushforward of
modules. -/
@[simp]
theorem pushforward_map_hom (f : Y ⟶ X) [IsFinite f] [Flat f] [LocallyOfFinitePresentation f]
    {E F : FiniteLocallyFreeSheaf Y} (φ : E ⟶ F) :
    ((pushforward f).map φ).hom =
      eqToHom (pushforward_obj_obj f E) ≫ (Scheme.Modules.pushforward f).map φ.hom ≫
        eqToHom (pushforward_obj_obj f F).symm := by
  cases pushforward_obj_obj f E
  cases pushforward_obj_obj f F
  unfold pushforward
  simp

/-- Forgetting finite local freeness commutes with pushforward. -/
@[simp]
theorem pushforward_comp_ι (f : Y ⟶ X) [IsFinite f] [Flat f] [LocallyOfFinitePresentation f] :
    pushforward f ⋙ (Scheme.Modules.isFiniteLocallyFree X).ι =
      (Scheme.Modules.isFiniteLocallyFree Y).ι ⋙ Scheme.Modules.pushforward f :=
  (rfl)

/-- Pushforward of finite locally free sheaves is additive. -/
instance pushforward_additive (f : Y ⟶ X) [IsFinite f] [Flat f] [LocallyOfFinitePresentation f] :
    (pushforward f).Additive := by
  dsimp only [pushforward]
  constructor
  intro E F g h
  exact ObjectProperty.hom_ext _
    ((Scheme.Modules.pushforward f).map_add (f := g.hom) (g := h.hom))

/-- Over a locally Noetherian target, pushforward of finite locally free sheaves agrees with
pushforward of finitely presented sheaves under the canonical inclusions. -/
def pushforwardCompToFinitelyPresentedIso [IsLocallyNoetherian X] (f : Y ⟶ X) [IsFinite f]
    [Flat f] [LocallyOfFinitePresentation f] :
    pushforward f ⋙ toFinitelyPresented X ≅
      toFinitelyPresented Y ⋙ FinitelyPresentedSheaf.pushforward f :=
  Functor.fullyFaithfulCancelRight (SheafOfModules.isFinitePresentation X.ringCatSheaf).ι
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (pushforward f) (ObjectProperty.ιOfLECompιIso _) ≪≫
      eqToIso (pushforward_comp_ι f) ≪≫
      Functor.isoWhiskerRight (ObjectProperty.ιOfLECompιIso _).symm
        (Scheme.Modules.pushforward f) ≪≫
      Functor.associator (toFinitelyPresented Y) _ (Scheme.Modules.pushforward f) ≪≫
      Functor.isoWhiskerLeft (toFinitelyPresented Y)
        (eqToIso (FinitelyPresentedSheaf.pushforward_comp_inclusion f).symm) ≪≫
      (Functor.associator (toFinitelyPresented Y) (FinitelyPresentedSheaf.pushforward f) _).symm)

end TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf

end
