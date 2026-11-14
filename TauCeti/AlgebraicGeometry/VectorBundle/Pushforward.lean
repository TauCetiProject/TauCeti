/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import TauCeti.AlgebraicGeometry.VectorBundle.FiniteLocallyFree
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Flat.EquationalCriterion
import TauCeti.Algebra.Category.ModuleCat.RestrictScalars
import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Pushforward.BaseChange
import TauCeti.AlgebraicGeometry.Modules.Tilde.Pushforward
import TauCeti.AlgebraicGeometry.Morphisms.Finite.Basic
import TauCeti.AlgebraicGeometry.VectorBundle.Affine.Basic
import TauCeti.AlgebraicGeometry.VectorBundle.OpenCover

/-!
# Pushforward of finite locally free sheaves along finite locally free morphisms

A morphism of schemes `f : X ⟶ Y` is *finite locally free* (Stacks, Lemma 29.48.2 (02KB)) if it is
finite, flat, and locally of finite presentation. This file shows that direct image `f_*` along such
a morphism preserves finite locally free sheaves, and proves the characterization of Stacks 02KB:
`f` is finite, flat, and locally of finite presentation if and only if `f` is affine and `f_* 𝒪_X`
is a finite locally free `𝒪_Y`-module.

Both directions reduce by flat base change (`Scheme.Modules.isIso_pushforwardBaseChange_app`) along
an affine open cover of `Y` (`Scheme.Modules.isFiniteLocallyFree_iff_forall_pullback`), and then
along `X.isoSpec.inv` for the affine source `X`, to a morphism `Spec φ : Spec S ⟶ Spec R` of
spectra of commutative rings:

* When `Spec φ` is finite, flat, and locally of finite presentation, `S` is a finite, flat, and
  finitely presented `R`-algebra, hence finitely presented and projective as an `R`-module
  (`Module.Flat.projective_of_finitePresentation`). A finite locally free sheaf on `Spec S` is `M~`
  for a finitely generated projective `S`-module `M`
  (`TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.finite_projective_moduleSpecΓ`), whose
  restriction of scalars to `R` remains finitely generated and projective
  (`RingHom.isFG_restrictScalars_of_finite`, `RingHom.projective_restrictScalars_of_projective`);
  its associated sheaf on `Spec R` is finite locally free and agrees with `(Spec φ)_* (M~)`
  (`TauCeti.AlgebraicGeometry.tildeRestrictScalarsIsoPushforward`).
* Conversely, when `(Spec φ)_* 𝒪_{Spec S} ≅ (S|_R)~` is finite locally free on `Spec R`, `S` is a
  finitely generated projective `R`-module
  (`TauCeti.AlgebraicGeometry.isFiniteLocallyFree_tilde_iff`), hence flat and finitely presented as
  an `R`-module, and therefore finitely presented as an `R`-algebra
  (`Algebra.FinitePresentation.of_finitePresentation`).

Packaging stability under `f_*` on the full subcategory `FiniteLocallyFreeSheaf` gives the direct
image functor `FiniteLocallyFreeSheaf.pushforward f`, together with its additivity and identity and
composition comparisons.

## Main declarations

* `AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree_pushforward`: direct image along a finite,
  flat, locally finitely presented morphism preserves finite local freeness;
* `AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree_pushforward_unit`: for such `f : X ⟶ Y`,
  `f_* 𝒪_X` is finite locally free;
* `AlgebraicGeometry.Scheme.Modules.isFinite_and_flat_and_locallyOfFinitePresentation_iff`:
  `f` is finite, flat, and locally of finite presentation if and only if `f` is affine and
  `f_* 𝒪_X` is finite locally free (Stacks 02KB);
* `TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.pushforward`: the direct image functor
  `FiniteLocallyFreeSheaf X ⥤ FiniteLocallyFreeSheaf Y`, with `pushforwardId` and `pushforwardComp`.

## References

* [The Stacks Project, Lemma 29.48.2](https://stacks.math.columbia.edu/tag/02KB)
-/

public section

open CategoryTheory Limits MonoidalCategory

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

open TauCeti.AlgebraicGeometry

private lemma isQuasicoherent_of_isFiniteLocallyFree {X : Scheme.{u}} {M : X.Modules}
    (hM : isFiniteLocallyFree X M) : M.IsQuasicoherent := by
  let F : _root_.SheafOfModules X.ringCatSheaf := M
  have : F.IsLocallyFree := hM.1
  exact inferInstanceAs F.IsQuasicoherent

private lemma isFiniteLocallyFree_pullback_of_isFiniteLocallyFree {X Y : Scheme.{u}} (g : X ⟶ Y)
    {M : Y.Modules} (hM : isFiniteLocallyFree Y M) :
    isFiniteLocallyFree X ((pullback g).obj M) := by
  obtain ⟨_, _⟩ := hM
  exact ⟨isLocallyFree_pullback g M, isFinitePresentation_pullback g M⟩

section SpecMap

variable {R S : CommRingCat.{u}} (φ : R ⟶ S)

private lemma isFiniteLocallyFree_pushforward_specMap [IsFinite (Spec.map φ)] [Flat (Spec.map φ)]
    [LocallyOfFinitePresentation (Spec.map φ)] {M : (Spec S).Modules}
    (hM : isFiniteLocallyFree (Spec S) M) :
    isFiniteLocallyFree (Spec R) ((pushforward (Spec.map φ)).obj M) := by
  let : Algebra R S := φ.hom.toAlgebra
  have hfinRS : _root_.Module.Finite R S := (IsFinite.SpecMap_iff φ).mp ‹_›
  have : _root_.Module.Flat R S := Flat.SpecMap_iff.mp ‹_›
  have : Algebra.FinitePresentation R S := (LocallyOfFinitePresentation.SpecMap_iff φ).mp ‹_›
  have : _root_.Module.FinitePresentation R S :=
    _root_.Module.FinitePresentation.of_finite_of_finitePresentation R S
  have hprojRS : _root_.Module.Projective R S := _root_.Module.Flat.projective_of_finitePresentation
  let E : FiniteLocallyFreeSheaf (Spec S) := ⟨M, hM⟩
  have : M.IsQuasicoherent := isQuasicoherent_of_isFiniteLocallyFree hM
  let N : ModuleCat.{u} S := moduleSpecΓFunctor.obj M
  obtain ⟨hfinN, hprojN⟩ := FiniteLocallyFreeSheaf.finite_projective_moduleSpecΓ E
  have : _root_.Module.Finite R ((ModuleCat.restrictScalars φ.hom).obj N) :=
    (ModuleCat.isFG_iff _).mp
      (φ.hom.isFG_restrictScalars_of_finite hfinRS ((ModuleCat.isFG_iff _).mpr hfinN))
  have : _root_.Module.Projective R ((ModuleCat.restrictScalars φ.hom).obj N) :=
    φ.hom.projective_restrictScalars_of_projective hprojRS N
  have hcounit : IsIso (fromTildeΓ M) := isIso_fromTildeΓ_of_isQuasicoherent M
  let e : tilde ((ModuleCat.restrictScalars φ.hom).obj N) ≅ (pushforward (Spec.map φ)).obj M :=
    tildeRestrictScalarsIsoPushforward φ N ≪≫
      (pushforward (Spec.map φ)).mapIso (@asIso _ _ _ _ (fromTildeΓ M) hcounit)
  exact (isFiniteLocallyFree (Spec R)).prop_of_iso e (isFiniteLocallyFree_tilde _)

private lemma isFinite_and_flat_and_locallyOfFinitePresentation_specMap
    (h : isFiniteLocallyFree (Spec R) ((pushforward (Spec.map φ)).obj (𝟙_ (Spec S).Modules))) :
    IsFinite (Spec.map φ) ∧ Flat (Spec.map φ) ∧ LocallyOfFinitePresentation (Spec.map φ) := by
  let e : tilde ((ModuleCat.restrictScalars φ.hom).obj (ModuleCat.of S S)) ≅
      (pushforward (Spec.map φ)).obj (𝟙_ (Spec S).Modules) :=
    tildeRestrictScalarsIsoPushforward φ (ModuleCat.of S S) ≪≫
      (pushforward (Spec.map φ)).mapIso (tildeSelf (R := S))
  obtain ⟨hfin, hproj⟩ := (isFiniteLocallyFree_tilde_iff _).mp
    ((isFiniteLocallyFree (Spec R)).prop_of_iso e.symm h)
  let : Algebra R S := φ.hom.toAlgebra
  -- Identify `S` as an `R`-algebra with the restriction of scalars of the regular `S`-module `S`.
  let linEquiv : ((ModuleCat.restrictScalars φ.hom).obj (ModuleCat.of S S) : Type u) ≃ₗ[R] S :=
    { toFun s := s
      invFun s := s
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl
      map_smul' r s := ModuleCat.restrictScalars.smul_def φ.hom r s }
  have : _root_.Module.Finite R S := _root_.Module.Finite.equiv linEquiv
  have : _root_.Module.Projective R S := _root_.Module.Projective.of_equiv linEquiv
  have hflat : _root_.Module.Flat R S := inferInstance
  have : _root_.Module.FinitePresentation R S := _root_.Module.finitePresentation_of_projective R S
  have hfp : Algebra.FinitePresentation R S := Algebra.FinitePresentation.of_finitePresentation R S
  exact ⟨(IsFinite.SpecMap_iff φ).mpr ‹_›, Flat.SpecMap_iff.mpr hflat,
    (LocallyOfFinitePresentation.SpecMap_iff φ).mpr hfp⟩

end SpecMap

section AffineTarget

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Between affine schemes, any morphism `f : X ⟶ Y` factors through `X.isoSpec` and `Y.isoSpec` as
`Spec.map φ`, identifying `(Y.isoSpec.inv)^* (f_* M)` with
`(Spec.map φ)_* ((X.isoSpec.inv)^* M)` for quasi-coherent `M` by flat base change along
`Y.isoSpec.inv`. -/
private def pushforwardIsoSpecMap [IsAffine X] [IsAffine Y] (M : X.Modules)
    [M.IsQuasicoherent] :
    (pullback Y.isoSpec.inv).obj ((pushforward f).obj M) ≅
      (pushforward (Spec.map (Spec.preimage (X.isoSpec.inv ≫ f ≫ Y.isoSpec.hom)))).obj
        ((pullback X.isoSpec.inv).obj M) := by
  let φ := Spec.preimage (X.isoSpec.inv ≫ f ≫ Y.isoSpec.hom)
  have hφ : Spec.map φ = X.isoSpec.inv ≫ f ≫ Y.isoSpec.hom := Spec.map_preimage _
  have H : IsPullback X.isoSpec.inv (Spec.map φ) f Y.isoSpec.inv :=
    IsPullback.of_horiz_isIso ⟨by rw [hφ, Category.assoc, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]⟩
  have := isIso_pushforwardBaseChange_app H M
  exact asIso ((pushforwardBaseChange H.toCommSq).app M)

private lemma isFiniteLocallyFree_pushforward_affine [IsAffine Y] [IsFinite f] [Flat f]
    [LocallyOfFinitePresentation f] {M : X.Modules} (hM : isFiniteLocallyFree X M) :
    isFiniteLocallyFree Y ((pushforward f).obj M) := by
  have : IsAffine X := isAffine_of_isAffineHom f
  have : M.IsQuasicoherent := isQuasicoherent_of_isFiniteLocallyFree hM
  let φ := Spec.preimage (X.isoSpec.inv ≫ f ≫ Y.isoSpec.hom)
  have hφ : Spec.map φ = X.isoSpec.inv ≫ f ≫ Y.isoSpec.hom := Spec.map_preimage _
  have : IsFinite (Spec.map φ) := by rw [hφ]; infer_instance
  have : Flat (Spec.map φ) := by rw [hφ]; infer_instance
  have : LocallyOfFinitePresentation (Spec.map φ) := by rw [hφ]; infer_instance
  have hpull : isFiniteLocallyFree (Spec Γ(X, ⊤)) ((pullback X.isoSpec.inv).obj M) :=
    isFiniteLocallyFree_pullback_of_isFiniteLocallyFree X.isoSpec.inv hM
  have hSpec : isFiniteLocallyFree (Spec Γ(Y, ⊤))
      ((pullback Y.isoSpec.inv).obj ((pushforward f).obj M)) :=
    (isFiniteLocallyFree (Spec Γ(Y, ⊤))).prop_of_iso (pushforwardIsoSpecMap f M).symm
      (isFiniteLocallyFree_pushforward_specMap φ hpull)
  let e : (pullback Y.isoSpec.hom).obj ((pullback Y.isoSpec.inv).obj ((pushforward f).obj M)) ≅
      (pushforward f).obj M :=
    (pullbackComp Y.isoSpec.hom Y.isoSpec.inv).app ((pushforward f).obj M) ≪≫
      eqToIso (congrArg (fun g ↦ (pullback g).obj ((pushforward f).obj M)) Y.isoSpec.hom_inv_id) ≪≫
      (pullbackId Y).app ((pushforward f).obj M)
  exact (isFiniteLocallyFree Y).prop_of_iso e
    (isFiniteLocallyFree_pullback_of_isFiniteLocallyFree Y.isoSpec.hom hSpec)

private lemma isFinite_and_flat_and_locallyOfFinitePresentation_affine [IsAffine X] [IsAffine Y]
    (h : isFiniteLocallyFree Y ((pushforward f).obj (𝟙_ X.Modules))) :
    IsFinite f ∧ Flat f ∧ LocallyOfFinitePresentation f := by
  let φ := Spec.preimage (X.isoSpec.inv ≫ f ≫ Y.isoSpec.hom)
  have hφ : Spec.map φ = X.isoSpec.inv ≫ f ≫ Y.isoSpec.hom := Spec.map_preimage _
  have hY : isFiniteLocallyFree (Spec Γ(Y, ⊤))
      ((pullback Y.isoSpec.inv).obj ((pushforward f).obj (𝟙_ X.Modules))) :=
    isFiniteLocallyFree_pullback_of_isFiniteLocallyFree Y.isoSpec.inv h
  let e : (pullback Y.isoSpec.inv).obj ((pushforward f).obj (𝟙_ X.Modules)) ≅
      (pushforward (Spec.map φ)).obj (𝟙_ (Spec Γ(X, ⊤)).Modules) :=
    pushforwardIsoSpecMap f (𝟙_ X.Modules) ≪≫
      (pushforward (Spec.map φ)).mapIso (pullbackObjUnitIso X.isoSpec.inv)
  obtain ⟨hfin, hflat, hfp⟩ :=
    isFinite_and_flat_and_locallyOfFinitePresentation_specMap φ
      ((isFiniteLocallyFree (Spec Γ(Y, ⊤))).prop_of_iso e hY)
  have hf : f = X.isoSpec.hom ≫ Spec.map φ ≫ Y.isoSpec.inv := by
    rw [hφ, Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id,
      Iso.hom_inv_id_assoc]
  rw [hf]
  exact ⟨inferInstance, inferInstance, inferInstance⟩

end AffineTarget

section General

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **Pushforward preserves finite locally free sheaves.** If `f : X ⟶ Y` is finite, flat, and
locally of finite presentation, then the direct image `f_* M` of every finite locally free
`𝒪_X`-module `M` is a finite locally free `𝒪_Y`-module. -/
theorem isFiniteLocallyFree_pushforward [IsFinite f] [Flat f] [LocallyOfFinitePresentation f]
    {M : X.Modules} (hM : isFiniteLocallyFree X M) :
    isFiniteLocallyFree Y ((pushforward f).obj M) := by
  let 𝒰 := Y.affineCover
  have : M.IsQuasicoherent := isQuasicoherent_of_isFiniteLocallyFree hM
  refine (isFiniteLocallyFree_iff_forall_pullback 𝒰 ((pushforward f).obj M)).mpr fun i ↦ ?_
  have H : IsPullback (Limits.pullback.fst f (𝒰.f i)) (Limits.pullback.snd f (𝒰.f i)) f (𝒰.f i) :=
    IsPullback.of_hasPullback f (𝒰.f i)
  have := isIso_pushforwardBaseChange_app H M
  have hpull : isFiniteLocallyFree (Limits.pullback f (𝒰.f i))
      ((pullback (Limits.pullback.fst f (𝒰.f i))).obj M) :=
    isFiniteLocallyFree_pullback_of_isFiniteLocallyFree (Limits.pullback.fst f (𝒰.f i)) hM
  exact (isFiniteLocallyFree (𝒰.X i)).prop_of_iso
    (asIso ((pushforwardBaseChange H.toCommSq).app M)).symm
    (isFiniteLocallyFree_pushforward_affine (Limits.pullback.snd f (𝒰.f i)) hpull)

/-- If `f : X ⟶ Y` is finite, flat, and locally of finite presentation, then `f_* 𝒪_X` is a finite
locally free `𝒪_Y`-module. -/
theorem isFiniteLocallyFree_pushforward_unit [IsFinite f] [Flat f]
    [LocallyOfFinitePresentation f] :
    isFiniteLocallyFree Y ((pushforward f).obj (𝟙_ X.Modules)) :=
  isFiniteLocallyFree_pushforward f (isMonoidal_isFiniteLocallyFree X).prop_unit

/-- **Characterization of finite locally free morphisms (Stacks, Lemma 29.48.2 (02KB)).** A
morphism of schemes `f : X ⟶ Y` is finite, flat, and locally of finite presentation if and only if
`f` is affine and `f_* 𝒪_X` is a finite locally free `𝒪_Y`-module. -/
@[stacks 02KB]
theorem isFinite_and_flat_and_locallyOfFinitePresentation_iff :
    IsFinite f ∧ Flat f ∧ LocallyOfFinitePresentation f ↔
      IsAffineHom f ∧ isFiniteLocallyFree Y ((pushforward f).obj (𝟙_ X.Modules)) := by
  refine ⟨fun ⟨_, _, _⟩ ↦ ⟨inferInstance, isFiniteLocallyFree_pushforward_unit f⟩,
    fun ⟨_, h⟩ ↦ ?_⟩
  let 𝒰 := Y.affineCover
  observe hasFiniteAffineProperty : HasAffineProperty @IsFinite.{u}
    (fun X _ f _ ↦ IsAffine X ∧ RingHom.Finite (f.appTop).hom)
  have : IsZariskiLocalAtTarget @IsFinite.{u} :=
    @HasAffineProperty.instIsZariskiLocalAtTarget _ _ hasFiniteAffineProperty
  have : IsZariskiLocalAtTarget @Flat.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtTarget _ (Q := @RingHom.Flat)
  have : IsZariskiLocalAtTarget @LocallyOfFinitePresentation.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtTarget _ (Q := @RingHom.FinitePresentation)
  rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @IsFinite) 𝒰,
    IsZariskiLocalAtTarget.iff_of_openCover (P := @Flat) 𝒰,
    IsZariskiLocalAtTarget.iff_of_openCover (P := @LocallyOfFinitePresentation) 𝒰]
  have hcover (i : 𝒰.I₀) : IsFinite (Limits.pullback.snd f (𝒰.f i)) ∧
      Flat (Limits.pullback.snd f (𝒰.f i)) ∧
      LocallyOfFinitePresentation (Limits.pullback.snd f (𝒰.f i)) := by
    have : IsAffineHom (Limits.pullback.snd f (𝒰.f i)) :=
      MorphismProperty.of_isPullback (IsPullback.of_hasPullback f (𝒰.f i)) ‹_›
    have : IsAffine (Limits.pullback f (𝒰.f i)) :=
      isAffine_of_isAffineHom (Limits.pullback.snd f (𝒰.f i))
    have H : IsPullback (Limits.pullback.fst f (𝒰.f i)) (Limits.pullback.snd f (𝒰.f i))
        f (𝒰.f i) :=
      IsPullback.of_hasPullback f (𝒰.f i)
    have := isIso_pushforwardBaseChange_app H (𝟙_ X.Modules)
    let e : (pullback (𝒰.f i)).obj ((pushforward f).obj (𝟙_ X.Modules)) ≅
        (pushforward (Limits.pullback.snd f (𝒰.f i))).obj
          (𝟙_ (Limits.pullback f (𝒰.f i)).Modules) :=
      asIso ((pushforwardBaseChange H.toCommSq).app (𝟙_ X.Modules)) ≪≫
        (pushforward (Limits.pullback.snd f (𝒰.f i))).mapIso
          (pullbackObjUnitIso (Limits.pullback.fst f (𝒰.f i)))
    exact isFinite_and_flat_and_locallyOfFinitePresentation_affine
      (Limits.pullback.snd f (𝒰.f i))
      ((isFiniteLocallyFree (𝒰.X i)).prop_of_iso e
        ((isFiniteLocallyFree_iff_forall_pullback 𝒰 _).mp h i))
  exact ⟨fun i ↦ by rw [Scheme.Cover.pullbackHom]; exact (hcover i).1,
    fun i ↦ by rw [Scheme.Cover.pullbackHom]; exact (hcover i).2.1,
    fun i ↦ by rw [Scheme.Cover.pullbackHom]; exact (hcover i).2.2⟩

end General

end AlgebraicGeometry.Scheme.Modules

namespace TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf

open _root_.AlgebraicGeometry

variable {X Y Z : Scheme.{u}}

/-- Direct image of finite locally free sheaves along a finite, flat, locally finitely presented
morphism `f : X ⟶ Y`. -/
def pushforward (f : X ⟶ Y) [IsFinite f] [Flat f] [LocallyOfFinitePresentation f] :
    FiniteLocallyFreeSheaf X ⥤ FiniteLocallyFreeSheaf Y :=
  (Scheme.Modules.isFiniteLocallyFree Y).lift
    ((Scheme.Modules.isFiniteLocallyFree X).ι ⋙ Scheme.Modules.pushforward f)
    fun E ↦ Scheme.Modules.isFiniteLocallyFree_pushforward f E.property

/-- The underlying `𝒪_Y`-module of `f_* E` is the module-level pushforward. -/
@[simp]
lemma pushforward_obj_obj (f : X ⟶ Y) [IsFinite f] [Flat f] [LocallyOfFinitePresentation f]
    (E : FiniteLocallyFreeSheaf X) :
    ((pushforward f).obj E).obj = (Scheme.Modules.pushforward f).obj E.obj :=
  (rfl)

/-- Pushforward acts on morphisms of finite locally free sheaves by the underlying pushforward of
modules. -/
@[simp]
lemma pushforward_map_hom (f : X ⟶ Y) [IsFinite f] [Flat f] [LocallyOfFinitePresentation f]
    {E F : FiniteLocallyFreeSheaf X} (φ : E ⟶ F) :
    ((pushforward f).map φ).hom =
      eqToHom (pushforward_obj_obj f E) ≫ (Scheme.Modules.pushforward f).map φ.hom ≫
        eqToHom (pushforward_obj_obj f F).symm := by
  cases pushforward_obj_obj f E
  cases pushforward_obj_obj f F
  unfold pushforward
  simp

/-- Direct image of finite locally free sheaves is additive. -/
instance pushforward_additive (f : X ⟶ Y) [IsFinite f] [Flat f] [LocallyOfFinitePresentation f] :
    (pushforward f).Additive where
  map_add := ObjectProperty.hom_ext _ ((Scheme.Modules.pushforward f).map_add)

/-- Direct image along the identity is naturally isomorphic to the identity functor on finite
locally free sheaves. -/
def pushforwardId (X : Scheme.{u}) : pushforward (𝟙 X) ≅ 𝟭 (FiniteLocallyFreeSheaf X) :=
  NatIso.ofComponents (fun E ↦
    ObjectProperty.isoMk (Scheme.Modules.isFiniteLocallyFree X)
      (eqToIso (pushforward_obj_obj (𝟙 X) E) ≪≫
        (Scheme.Modules.pushforwardId X).app E.obj)) fun {E F} φ ↦ by
    apply ObjectProperty.hom_ext
    simp [ObjectProperty.isoMk, ObjectProperty.homMk, pushforward_map_hom,
      Category.assoc, (Scheme.Modules.pushforwardId X).hom.naturality φ.hom]

/-- On underlying modules, the identity comparison is Mathlib's pushforward identity comparison. -/
@[simp]
theorem pushforwardId_hom_app_hom (X : Scheme.{u}) (E : FiniteLocallyFreeSheaf X) :
    ((pushforwardId X).hom.app E).hom =
      eqToHom (pushforward_obj_obj (𝟙 X) E) ≫
        (Scheme.Modules.pushforwardId X).hom.app E.obj := by
  simp only [pushforwardId, NatIso.ofComponents_hom_app, ObjectProperty.isoMk_hom,
    Iso.trans_hom, eqToIso.hom, ObjectProperty.homMk_hom, Iso.app_hom]

/-- The inverse identity comparison on underlying modules is Mathlib's inverse comparison. -/
@[simp]
theorem pushforwardId_inv_app_hom (X : Scheme.{u}) (E : FiniteLocallyFreeSheaf X) :
    ((pushforwardId X).inv.app E).hom =
      (Scheme.Modules.pushforwardId X).inv.app E.obj ≫
        eqToHom (pushforward_obj_obj (𝟙 X) E).symm := by
  simp only [pushforwardId, NatIso.ofComponents_inv_app, ObjectProperty.isoMk_inv,
    Iso.trans_inv, eqToIso.inv, ObjectProperty.homMk_hom, Iso.app_inv]

private lemma pushforwardComp_obj_obj (f : X ⟶ Y) (g : Y ⟶ Z) [IsFinite f] [Flat f]
    [LocallyOfFinitePresentation f] [IsFinite g] [Flat g] [LocallyOfFinitePresentation g]
    (E : FiniteLocallyFreeSheaf X) :
    ((pushforward f ⋙ pushforward g).obj E).obj =
      (Scheme.Modules.pushforward f ⋙ Scheme.Modules.pushforward g).obj E.obj :=
  (pushforward_obj_obj g ((pushforward f).obj E)).trans
    (congrArg (Scheme.Modules.pushforward g).obj (pushforward_obj_obj f E))

/-- Direct image along a composite is naturally isomorphic to successive direct image of finite
locally free sheaves. -/
def pushforwardComp (f : X ⟶ Y) (g : Y ⟶ Z) [IsFinite f] [Flat f]
    [LocallyOfFinitePresentation f] [IsFinite g] [Flat g] [LocallyOfFinitePresentation g] :
    pushforward f ⋙ pushforward g ≅ pushforward (f ≫ g) :=
  NatIso.ofComponents (fun E ↦
    ObjectProperty.isoMk (Scheme.Modules.isFiniteLocallyFree Z)
      (eqToIso (pushforwardComp_obj_obj f g E) ≪≫
        (Scheme.Modules.pushforwardComp f g).app E.obj ≪≫
        eqToIso (pushforward_obj_obj (f ≫ g) E).symm)) fun {E F} φ ↦ by
    apply ObjectProperty.hom_ext
    simp only [Functor.comp_obj, Functor.comp_map, ObjectProperty.isoMk_hom,
      Iso.trans_hom, eqToIso.hom, Iso.app_hom, ObjectProperty.FullSubcategory.comp_hom,
      pushforward_map_hom, Functor.map_comp, Category.assoc, ObjectProperty.homMk_hom,
      eqToHom_trans_assoc, eqToHom_refl, eqToHom_map, eqToHom_trans, Category.id_comp]
    have h := (Scheme.Modules.pushforwardComp f g).hom.naturality φ.hom
    simp only [Functor.comp_map] at h
    calc
      _ = eqToHom (pushforwardComp_obj_obj f g E) ≫
          ((Scheme.Modules.pushforward g).map ((Scheme.Modules.pushforward f).map φ.hom) ≫
            (Scheme.Modules.pushforwardComp f g).hom.app F.obj) ≫
          eqToHom (pushforward_obj_obj (f ≫ g) F).symm := by simp only [Category.assoc]
      _ = _ := by rw [h]; simp only [Category.assoc]

/-- On underlying modules, the composition comparison is Mathlib's pushforward composition
comparison. -/
@[simp]
theorem pushforwardComp_hom_app_hom (f : X ⟶ Y) (g : Y ⟶ Z) [IsFinite f] [Flat f]
    [LocallyOfFinitePresentation f] [IsFinite g] [Flat g] [LocallyOfFinitePresentation g]
    (E : FiniteLocallyFreeSheaf X) :
    ((pushforwardComp f g).hom.app E).hom =
      eqToHom (by simp only [Functor.comp_obj, pushforward_obj_obj]) ≫
        (Scheme.Modules.pushforwardComp f g).hom.app E.obj ≫
        eqToHom (pushforward_obj_obj (f ≫ g) E).symm := by
  simp only [pushforwardComp, NatIso.ofComponents_hom_app, ObjectProperty.isoMk_hom,
    Iso.trans_hom, eqToIso.hom, ObjectProperty.homMk_hom, Iso.app_hom]

/-- The inverse composition comparison on underlying modules is Mathlib's inverse comparison. -/
@[simp]
theorem pushforwardComp_inv_app_hom (f : X ⟶ Y) (g : Y ⟶ Z) [IsFinite f] [Flat f]
    [LocallyOfFinitePresentation f] [IsFinite g] [Flat g] [LocallyOfFinitePresentation g]
    (E : FiniteLocallyFreeSheaf X) :
    ((pushforwardComp f g).inv.app E).hom =
      eqToHom (pushforward_obj_obj (f ≫ g) E) ≫
        (Scheme.Modules.pushforwardComp f g).inv.app E.obj ≫
        eqToHom (show (Scheme.Modules.pushforward f ⋙ Scheme.Modules.pushforward g).obj E.obj =
          ((pushforward f ⋙ pushforward g).obj E).obj by
            simp only [Functor.comp_obj, pushforward_obj_obj]) := by
  simp only [pushforwardComp, NatIso.ofComponents_inv_app, ObjectProperty.isoMk_inv,
    Iso.trans_inv, eqToIso.inv, ObjectProperty.homMk_hom, Iso.app_inv, Category.assoc]

end TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf

end
