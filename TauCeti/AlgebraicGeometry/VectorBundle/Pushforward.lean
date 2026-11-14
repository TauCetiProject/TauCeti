/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import TauCeti.AlgebraicGeometry.Modules.Algebra.RegularFunctions
public import TauCeti.AlgebraicGeometry.VectorBundle.FiniteLocallyFree
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Flat.EquationalCriterion
import TauCeti.Algebra.Category.ModuleCat.RestrictScalars
import TauCeti.AlgebraicGeometry.Modules.Pushforward.Basic
import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Pushforward.BaseChange
import TauCeti.AlgebraicGeometry.Modules.Tilde.Pushforward
import TauCeti.AlgebraicGeometry.VectorBundle.Affine.Basic
import TauCeti.AlgebraicGeometry.VectorBundle.OpenCover

/-!
# Pushforward of finite locally free sheaves along finite flat finitely presented morphisms

Along a finite, flat, locally finitely presented morphism of schemes `f : X ⟶ Y`, the direct image
`f_* M` of a finite locally free `𝒪_X`-module `M` is a finite locally free `𝒪_Y`-module, with no
Noetherian hypothesis on the base `Y`. In particular, the algebra of regular functions `f_* 𝒪_X`
is finite locally free over `𝒪_Y`.

The proof reduces to affine schemes via flat base change along an affine open cover of `Y`
(`AlgebraicGeometry.Scheme.Modules.isIso_pushforwardBaseChange_app`) and open-cover descent of
finite local freeness (`AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree_iff_forall_pullback`).
For a ring homomorphism `φ : R →+* S` that is finite, flat, and of finite presentation, `S` is a
finitely presented flat `R`-module (`Module.FinitePresentation.of_finite_of_finitePresentation`),
hence projective (`Module.Flat.projective_of_finitePresentation`). Restricting scalars along `φ`
therefore carries finitely generated projective `S`-modules to finitely generated projective
`R`-modules, and the tilde equivalence concludes on `Spec R`.

## Main declarations

* `AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree_pushforward`: direct image along a finite
  flat locally finitely presented morphism preserves finite local freeness;
* `AlgebraicGeometry.Scheme.Hom.isFiniteLocallyFree_pushforwardStructureAlgebra`: the coordinate
  algebra `f_* 𝒪_X` of a finite flat locally finitely presented morphism is finite locally free;
* `TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.pushforward`: the induced additive pushforward
  functor `FiniteLocallyFreeSheaf X ⥤ FiniteLocallyFreeSheaf Y`;
* `TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.pullbackPushforwardAdjunction`: the adjunction
  `pullback f ⊣ pushforward f` on finite locally free sheaves.

## References

* [The Stacks Project, Tag 02KB](https://stacks.math.columbia.edu/tag/02KB)
-/

public section

open CategoryTheory Limits MonoidalCategory AlgebraicGeometry

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

open TauCeti.AlgebraicGeometry

private theorem isFiniteLocallyFree_pushforward_spec {R S : CommRingCat.{u}} (φ : R ⟶ S)
    [IsFinite (Spec.map φ)] [Flat (Spec.map φ)] [LocallyOfFinitePresentation (Spec.map φ)]
    {M : (Spec S).Modules} (hM : isFiniteLocallyFree (Spec S) M) :
    isFiniteLocallyFree (Spec R) ((pushforward (Spec.map φ)).obj M) := by
  have hfin : RingHom.Finite φ.hom := (IsFinite.SpecMap_iff φ).mp ‹_›
  have hflat : RingHom.Flat φ.hom := Flat.SpecMap_iff.mp ‹_›
  have hfp : RingHom.FinitePresentation φ.hom :=
    (LocallyOfFinitePresentation.SpecMap_iff φ).mp ‹_›
  have hSproj : letI := φ.hom.toModule; Module.Projective R S := by
    algebraize [φ.hom]
    have : Module.FinitePresentation R S :=
      Module.FinitePresentation.of_finite_of_finitePresentation R S
    exact Module.Flat.projective_of_finitePresentation
  let E : FiniteLocallyFreeSheaf (Spec S) := ⟨M, hM⟩
  obtain ⟨hNfin, hNproj⟩ := FiniteLocallyFreeSheaf.finite_projective_moduleSpecΓ E
  let N : ModuleCat.{u} S := moduleSpecΓFunctor.obj M
  have hRNfin : Module.Finite R ((ModuleCat.restrictScalars φ.hom).obj N) :=
    (ModuleCat.isFG_iff _).mp
      (φ.hom.isFG_restrictScalars_of_finite hfin ((ModuleCat.isFG_iff _).mpr hNfin))
  have hRNproj : Module.Projective R ((ModuleCat.restrictScalars φ.hom).obj N) :=
    φ.hom.projective_restrictScalars_of_projective hSproj N
  let F : _root_.SheafOfModules (Spec S).ringCatSheaf := M
  have : F.IsLocallyFree := hM.1
  have : M.IsQuasicoherent := inferInstanceAs F.IsQuasicoherent
  let eM : tilde N ≅ M := @asIso _ _ _ _ M.fromTildeΓ (isIso_fromTildeΓ_of_isQuasicoherent M)
  let ePush : tilde ((ModuleCat.restrictScalars φ.hom).obj N) ≅
      (pushforward (Spec.map φ)).obj M :=
    tildeRestrictScalarsIsoPushforward φ N ≪≫ (pushforward (Spec.map φ)).mapIso eM
  exact (isFiniteLocallyFree (Spec R)).prop_of_iso ePush
    ((isFiniteLocallyFree_tilde_iff _).mpr ⟨hRNfin, hRNproj⟩)

private theorem isFiniteLocallyFree_pushforward_to_spec {X : Scheme.{u}} {R : CommRingCat.{u}}
    (f : X ⟶ Spec R) [IsFinite f] [Flat f] [LocallyOfFinitePresentation f]
    {M : X.Modules} (hM : isFiniteLocallyFree X M) :
    isFiniteLocallyFree (Spec R) ((pushforward f).obj M) := by
  have : IsAffine X := isAffine_of_isAffineHom f
  have : M.IsLocallyFree := hM.1
  have : M.IsFinitePresentation := hM.2
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (X.isoSpec.inv ≫ f)
  have hf' : X.isoSpec.inv ≫ f = Spec.map φ := hφ.symm
  have : IsFinite (Spec.map φ) := by rw [← hf']; infer_instance
  have : Flat (Spec.map φ) := by rw [← hf']; infer_instance
  have : LocallyOfFinitePresentation (Spec.map φ) := by rw [← hf']; infer_instance
  let e : (pushforward (Spec.map φ)).obj ((pullback X.isoSpec.inv).obj M) ≅
      (pushforward f).obj M :=
    (pushforwardCongr hf'.symm).app _ ≪≫
      (pushforward (X.isoSpec.inv ≫ f)).mapIso
        (((restrictFunctorIsoPullback X.isoSpec.inv).app M).symm ≪≫
          ((pushforwardIsoRestrictFunctor X.isoSpec).app M).symm) ≪≫
      (pushforwardComp X.isoSpec.hom (X.isoSpec.inv ≫ f)).app M ≪≫
      (pushforwardCongr (Iso.hom_inv_id_assoc X.isoSpec f)).app M
  exact (isFiniteLocallyFree (Spec R)).prop_of_iso e
    (isFiniteLocallyFree_pushforward_spec φ
      ⟨isLocallyFree_pullback _ M, isFinitePresentation_pullback _ M⟩)

/-- **Direct image of finite locally free sheaves.** Along a finite, flat, locally finitely
presented morphism `f : X ⟶ Y`, the pushforward of a finite locally free `𝒪_X`-module is a finite
locally free `𝒪_Y`-module. -/
theorem isFiniteLocallyFree_pushforward {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f] [Flat f] [LocallyOfFinitePresentation f]
    {M : X.Modules} (hM : isFiniteLocallyFree X M) :
    isFiniteLocallyFree Y ((pushforward f).obj M) := by
  have : M.IsLocallyFree := hM.1
  have : M.IsFinitePresentation := hM.2
  let F : _root_.SheafOfModules X.ringCatSheaf := M
  have : F.IsLocallyFree := hM.1
  have : M.IsQuasicoherent := inferInstanceAs F.IsQuasicoherent
  rw [isFiniteLocallyFree_iff_forall_pullback Y.affineCover]
  intro i
  let g : Spec _ ⟶ Y := Y.affineCover.f i
  have : IsOpenImmersion g := Y.affineCover.map_prop i
  have H := IsPullback.of_hasPullback f g
  have : IsIso ((pushforwardBaseChange H.toCommSq).app M) :=
    isIso_pushforwardBaseChange_app H M
  exact (isFiniteLocallyFree _).prop_of_iso
    (asIso ((pushforwardBaseChange H.toCommSq).app M)).symm
    (isFiniteLocallyFree_pushforward_to_spec (Limits.pullback.snd f g)
      ⟨isLocallyFree_pullback _ M, isFinitePresentation_pullback _ M⟩)

/-- Along a finite, flat, locally finitely presented morphism `f : X ⟶ Y`, the pushforward
`f_* 𝒪_X` of the structure sheaf is finite locally free. -/
theorem isFiniteLocallyFree_pushforward_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f] [Flat f] [LocallyOfFinitePresentation f] :
    isFiniteLocallyFree Y ((pushforward f).obj (𝟙_ X.Modules)) :=
  isFiniteLocallyFree_pushforward f (isFiniteLocallyFree X).prop_unit

end AlgebraicGeometry.Scheme.Modules

/-- The coordinate algebra `f_* 𝒪_X` of a finite, flat, locally finitely presented morphism
`f : X ⟶ Y` has finite locally free underlying `𝒪_Y`-module. -/
@[stacks 02KB]
theorem AlgebraicGeometry.Scheme.Hom.isFiniteLocallyFree_pushforwardStructureAlgebra
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [Flat f] [LocallyOfFinitePresentation f] :
    Scheme.Modules.isFiniteLocallyFree Y f.pushforwardStructureAlgebra.X :=
  Scheme.Modules.isFiniteLocallyFree_pushforward_unit f

namespace TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [Flat f] [LocallyOfFinitePresentation f]

/-- Pushforward of finite locally free sheaves along a finite, flat, locally finitely presented
morphism of schemes. -/
def pushforward : FiniteLocallyFreeSheaf X ⥤ FiniteLocallyFreeSheaf Y :=
  (Scheme.Modules.isFiniteLocallyFree Y).lift
    ((Scheme.Modules.isFiniteLocallyFree X).ι ⋙ Scheme.Modules.pushforward f)
    fun E ↦ Scheme.Modules.isFiniteLocallyFree_pushforward f E.property

/-- The underlying `𝒪_Y`-module of the pushforward of a finite locally free sheaf is its ordinary
pushforward. -/
@[simp]
theorem pushforward_obj_obj (E : FiniteLocallyFreeSheaf X) :
    ((pushforward f).obj E).obj = (Scheme.Modules.pushforward f).obj E.obj :=
  (rfl)

/-- Forgetting finite local freeness commutes strictly with pushforward. -/
@[simp]
theorem pushforward_comp_ι :
    pushforward f ⋙ (Scheme.Modules.isFiniteLocallyFree Y).ι =
      (Scheme.Modules.isFiniteLocallyFree X).ι ⋙ Scheme.Modules.pushforward f :=
  (rfl)

/-- Pushforward acts on morphisms of finite locally free sheaves by the underlying pushforward of
sheaves of modules. -/
@[simp]
theorem pushforward_map_hom {E F : FiniteLocallyFreeSheaf X} (φ : E ⟶ F) :
    ((pushforward f).map φ).hom =
      eqToHom (pushforward_obj_obj f E) ≫ (Scheme.Modules.pushforward f).map φ.hom ≫
        eqToHom (pushforward_obj_obj f F).symm := by
  cases pushforward_obj_obj f E
  cases pushforward_obj_obj f F
  unfold pushforward
  simp

/-- Pushforward of finite locally free sheaves is additive. -/
instance : (pushforward f).Additive where
  map_add {_ _} g h :=
    ObjectProperty.hom_ext _ ((Scheme.Modules.pushforward f).map_add (f := g.hom) (g := h.hom))

/-- Pullback is left adjoint to pushforward on finite locally free sheaves along a finite, flat,
locally finitely presented morphism. -/
def pullbackPushforwardAdjunction : pullback f ⊣ pushforward f :=
  (Scheme.Modules.pullbackPushforwardAdjunction f).restrictFullyFaithful
    (Scheme.Modules.isFiniteLocallyFree Y).fullyFaithfulι
    (Scheme.Modules.isFiniteLocallyFree X).fullyFaithfulι
    (NatIso.ofComponents (fun E ↦ eqToIso (pullback_obj_obj f E).symm) fun φ ↦ by
      simp [pullback_map_hom])
    (NatIso.ofComponents (fun E ↦ eqToIso (pushforward_obj_obj f E).symm) fun φ ↦ by
      simp [pushforward_map_hom])

/-- On underlying module sheaves, the unit of `pullbackPushforwardAdjunction` agrees with that of
`Scheme.Modules.pullbackPushforwardAdjunction`. -/
@[simp]
theorem pullbackPushforwardAdjunction_unit_app_hom (E : FiniteLocallyFreeSheaf Y) :
    ((pullbackPushforwardAdjunction f).unit.app E).hom =
      (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app E.obj ≫
        eqToHom (by simp only [Functor.comp_obj, pushforward_obj_obj, pullback_obj_obj]) := by
  simpa [pullbackPushforwardAdjunction, eqToHom_map] using
    (Scheme.Modules.pullbackPushforwardAdjunction f).map_restrictFullyFaithful_unit_app
      (L := pullback f) (R := pushforward f)
      (hiC := (Scheme.Modules.isFiniteLocallyFree Y).fullyFaithfulι)
      (hiD := (Scheme.Modules.isFiniteLocallyFree X).fullyFaithfulι)
      (comm1 := NatIso.ofComponents (fun E ↦ eqToIso (pullback_obj_obj f E).symm) fun φ ↦ by
        simp [pullback_map_hom])
      (comm2 := NatIso.ofComponents (fun E ↦ eqToIso (pushforward_obj_obj f E).symm) fun φ ↦ by
        simp [pushforward_map_hom]) E

/-- On underlying module sheaves, the counit of `pullbackPushforwardAdjunction` agrees with that of
`Scheme.Modules.pullbackPushforwardAdjunction`. -/
@[simp]
theorem pullbackPushforwardAdjunction_counit_app_hom (E : FiniteLocallyFreeSheaf X) :
    ((pullbackPushforwardAdjunction f).counit.app E).hom =
      eqToHom (by simp only [Functor.comp_obj, pullback_obj_obj, pushforward_obj_obj]) ≫
        (Scheme.Modules.pullbackPushforwardAdjunction f).counit.app E.obj := by
  simpa [pullbackPushforwardAdjunction, eqToHom_map] using
    (Scheme.Modules.pullbackPushforwardAdjunction f).map_restrictFullyFaithful_counit_app
      (L := pullback f) (R := pushforward f)
      (hiC := (Scheme.Modules.isFiniteLocallyFree Y).fullyFaithfulι)
      (hiD := (Scheme.Modules.isFiniteLocallyFree X).fullyFaithfulι)
      (comm1 := NatIso.ofComponents (fun E ↦ eqToIso (pullback_obj_obj f E).symm) fun φ ↦ by
        simp [pullback_map_hom])
      (comm2 := NatIso.ofComponents (fun E ↦ eqToIso (pushforward_obj_obj f E).symm) fun φ ↦ by
        simp [pushforward_map_hom]) E

end TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf

end
