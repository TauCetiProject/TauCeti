/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import TauCeti.Algebra.Category.ModuleCat.RestrictScalars
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Pushforward.BaseChange
public import TauCeti.AlgebraicGeometry.Modules.Tilde.Pushforward
public import TauCeti.AlgebraicGeometry.VectorBundle.Affine.Basic
public import TauCeti.AlgebraicGeometry.VectorBundle.OpenCover

/-!
# Direct image of finite locally free sheaves along finite locally free morphisms

Let `f : X ⟶ Y` be a morphism of schemes that is finite, flat, and locally of finite presentation
(that is, finite locally free in the sense of Stacks Tag 02KB). For every finite locally free
`𝒪_X`-module `M`, the direct image `f_* M` is a finite locally free `𝒪_Y`-module
(`AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree_pushforward`); in particular, `f_* 𝒪_X` is
finite locally free (`AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree_pushforward_unit`). This
packages direct image along `f` as an additive functor
`TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.pushforward f` from `FiniteLocallyFreeSheaf X` to
`FiniteLocallyFreeSheaf Y`.

The proof reduces first to an affine target `Spec R` along an affine open cover of `Y`: pulling
back `f_* M` to each chart agrees with pushing forward the pulled-back sheaf by flat base change
(`AlgebraicGeometry.Scheme.Modules.isIso_pushforwardBaseChange_app`), and finite local freeness is
detected on open covers
(`AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree_iff_forall_pullback`). Over `Spec R`, since
`f` is finite, `X` is affine, so passing through `X.isoSpec` reduces further to `f = Spec.map φ`
for a ring homomorphism `φ : R ⟶ S`. Over `Spec S`, `M` is associated with a finitely generated
projective `S`-module `P`, while `S` is finitely generated, flat, and finitely presented over `R`,
hence projective over `R`; preservation of finite generation and projectivity under restriction of
scalars (`RingHom.isFG_restrictScalars_of_finite`,
`RingHom.projective_restrictScalars_of_projective`) together with
`TauCeti.AlgebraicGeometry.tildeRestrictScalarsIsoPushforward` show that `f_* M` is associated with
a finitely generated projective `R`-module, hence finite locally free.

## Main declarations

* `AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree_pushforward`: direct image along a finite,
  flat, locally finitely presented morphism preserves finite locally free sheaves;
* `AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree_pushforward_unit`: `f_* 𝒪_X` is finite
  locally free for a finite, flat, locally finitely presented morphism `f : X ⟶ Y`;
* `TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.pushforward`: the additive direct-image functor
  `FiniteLocallyFreeSheaf X ⥤ FiniteLocallyFreeSheaf Y`.

## References

* [The Stacks Project, Tag 02KB](https://stacks.math.columbia.edu/tag/02KB)
* [The Stacks Project, Tag 0BD2](https://stacks.math.columbia.edu/tag/0BD2)
-/

public section

open CategoryTheory Limits MonoidalCategory

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

open TauCeti.AlgebraicGeometry

/-- Over an affine morphism `Spec.map φ`, direct image preserves finite locally free sheaves when
`Spec.map φ` is finite, flat, and locally of finite presentation. -/
private lemma isFiniteLocallyFree_pushforward_spec {R S : CommRingCat.{u}} (φ : R ⟶ S)
    [IsFinite (Spec.map φ)] [Flat (Spec.map φ)] [LocallyOfFinitePresentation (Spec.map φ)]
    (M : (Spec S).Modules) (hM : isFiniteLocallyFree (Spec S) M) :
    isFiniteLocallyFree (Spec R) ((pushforward (Spec.map φ)).obj M) := by
  algebraize [φ.hom]
  have hfin : Module.Finite R S :=
    RingHom.finite_algebraMap.mp ((IsFinite.SpecMap_iff φ).mp ‹_›)
  have : Module.Flat R S :=
    RingHom.flat_algebraMap_iff.mp (Flat.SpecMap_iff.mp ‹_›)
  have : Algebra.FinitePresentation R S :=
    RingHom.finitePresentation_algebraMap.mp
      ((HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).mp ‹_›)
  have : Module.FinitePresentation R S :=
    (Module.FinitePresentation.iff_finitePresentation_of_finite (R := R) (S := S)).mpr ‹_›
  have hproj : Module.Projective R S := Module.Flat.projective_of_finitePresentation
  let E : FiniteLocallyFreeSheaf (Spec S) := ⟨M, hM⟩
  let P : ModuleCat.{u} S := moduleSpecΓFunctor.obj E.obj
  obtain ⟨hPfin, hPproj⟩ := FiniteLocallyFreeSheaf.finite_projective_moduleSpecΓ E
  have : Module.Finite R ((ModuleCat.restrictScalars φ.hom).obj P) :=
    (ModuleCat.isFG_iff _).mp
      (φ.hom.isFG_restrictScalars_of_finite hfin ((ModuleCat.isFG_iff P).mpr hPfin))
  have : Module.Projective R ((ModuleCat.restrictScalars φ.hom).obj P) :=
    φ.hom.projective_restrictScalars_of_projective hproj P
  have htilde : isFiniteLocallyFree (Spec R) (tilde ((ModuleCat.restrictScalars φ.hom).obj P)) :=
    (isFiniteLocallyFree_tilde_iff _).mpr ⟨‹_›, ‹_›⟩
  have : M.IsQuasicoherent := by
    let F : _root_.SheafOfModules (Spec S).ringCatSheaf := M
    have : F.IsLocallyFree := hM.1
    exact inferInstanceAs F.IsQuasicoherent
  let e : tilde ((ModuleCat.restrictScalars φ.hom).obj P) ≅ (pushforward (Spec.map φ)).obj M :=
    tildeRestrictScalarsIsoPushforward φ P ≪≫
      (pushforward (Spec.map φ)).mapIso
        (@asIso _ _ _ _ (fromTildeΓ (R := S) M) (isIso_fromTildeΓ_of_isQuasicoherent M))
  exact (isFiniteLocallyFree (Spec R)).prop_of_iso e htilde

/-- Direct image along an isomorphism of schemes preserves finite locally free sheaves, via flat
base change against the inverse isomorphism. -/
private lemma isFiniteLocallyFree_pushforward_of_isIso {X X' : Scheme.{u}} (g : X ⟶ X') [IsIso g]
    (M : X.Modules) (hM : isFiniteLocallyFree X M) :
    isFiniteLocallyFree X' ((pushforward g).obj M) := by
  obtain ⟨_, _⟩ := hM
  have : M.IsQuasicoherent := by
    let F : _root_.SheafOfModules X.ringCatSheaf := M
    exact inferInstanceAs F.IsQuasicoherent
  have H : IsPullback (𝟙 X) g (𝟙 X) (inv g) :=
    IsPullback.of_vert_isIso ⟨by simp⟩
  have := isIso_pushforwardBaseChange_app H M
  let e : (pullback (inv g)).obj M ≅ (pushforward g).obj M :=
    (pullback (inv g)).mapIso ((pushforwardId X).app M).symm ≪≫
      asIso ((pushforwardBaseChange H.toCommSq).app M) ≪≫
      (pushforward g).mapIso ((pullbackId X).app M)
  exact (isFiniteLocallyFree X').prop_of_iso e
    ⟨isLocallyFree_pullback (inv g) M, isFinitePresentation_pullback (inv g) M⟩

/-- Direct image into `Spec R` preserves finite locally free sheaves along finite, flat, locally
finitely presented morphisms. -/
private lemma isFiniteLocallyFree_pushforward_to_spec {X : Scheme.{u}} {R : CommRingCat.{u}}
    (f : X ⟶ Spec R) [IsFinite f] [Flat f] [LocallyOfFinitePresentation f]
    (M : X.Modules) (hM : isFiniteLocallyFree X M) :
    isFiniteLocallyFree (Spec R) ((pushforward f).obj M) := by
  have : IsAffine X := isAffine_of_isAffineHom f
  -- Abstract `X.isoSpec` into an opaque isomorphism so `whnf` never unfolds `ΓSpec`.
  obtain ⟨S, ⟨eX⟩⟩ : ∃ S : CommRingCat.{u}, Nonempty (X ≅ Spec S) := ⟨_, ⟨X.isoSpec⟩⟩
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (eX.inv ≫ f)
  have : IsFinite (Spec.map φ) := by rw [hφ]; infer_instance
  have : Flat (Spec.map φ) := by rw [hφ]; infer_instance
  have : LocallyOfFinitePresentation (Spec.map φ) := by rw [hφ]; infer_instance
  have hf_eq : eX.hom ≫ Spec.map φ = f := by rw [hφ, eX.hom_inv_id_assoc]
  have h₁ := isFiniteLocallyFree_pushforward_of_isIso eX.hom M hM
  have h₂ := isFiniteLocallyFree_pushforward_spec φ _ h₁
  let e_comp :
      (pushforward (Spec.map φ)).obj ((pushforward eX.hom).obj M) ≅ (pushforward f).obj M :=
    (pushforwardComp eX.hom (Spec.map φ)).symm.app M ≪≫ (pushforwardCongr hf_eq).app M
  exact (isFiniteLocallyFree (Spec R)).prop_of_iso e_comp h₂

/-- Pulling back `f_* M` along a flat morphism `g : Spec R ⟶ Y` yields a finite locally free sheaf
on `Spec R`. -/
private lemma isFiniteLocallyFree_pullback_pushforward_to_spec {X Y : Scheme.{u}}
    {R : CommRingCat.{u}} (f : X ⟶ Y) [IsFinite f] [Flat f] [LocallyOfFinitePresentation f]
    (g : Spec R ⟶ Y) [Flat g] (M : X.Modules) (hM : isFiniteLocallyFree X M) :
    isFiniteLocallyFree (Spec R) ((pullback g).obj ((pushforward f).obj M)) := by
  obtain ⟨_, _⟩ := hM
  have : M.IsQuasicoherent := by
    let F : _root_.SheafOfModules X.ringCatSheaf := M
    exact inferInstanceAs F.IsQuasicoherent
  have H : IsPullback (Limits.pullback.fst f g) (Limits.pullback.snd f g) f g :=
    IsPullback.of_hasPullback f g
  have := isIso_pushforwardBaseChange_app H M
  exact (isFiniteLocallyFree (Spec R)).prop_of_iso
    (asIso ((pushforwardBaseChange H.toCommSq).app M)).symm
    (isFiniteLocallyFree_pushforward_to_spec (Limits.pullback.snd f g) _
      ⟨isLocallyFree_pullback _ M, isFinitePresentation_pullback _ M⟩)

/-- **Direct image of a finite locally free sheaf along a finite locally free morphism.** If
`f : X ⟶ Y` is finite, flat, and locally of finite presentation, and `M` is a finite locally free
`𝒪_X`-module, then `f_* M` is a finite locally free `𝒪_Y`-module. -/
@[stacks 02KB]
theorem isFiniteLocallyFree_pushforward {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [Flat f]
    [LocallyOfFinitePresentation f] (M : X.Modules) (hM : isFiniteLocallyFree X M) :
    isFiniteLocallyFree Y ((pushforward f).obj M) :=
  (isFiniteLocallyFree_iff_forall_pullback Y.affineOpenCover.openCover _).mpr fun i ↦
    have := Y.affineOpenCover.map_prop i
    isFiniteLocallyFree_pullback_pushforward_to_spec f (Y.affineOpenCover.f i) M hM

/-- If `f : X ⟶ Y` is finite, flat, and locally of finite presentation, then `f_* 𝒪_X` is a finite
locally free `𝒪_Y`-module. -/
@[stacks 02KB]
theorem isFiniteLocallyFree_pushforward_unit {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [Flat f]
    [LocallyOfFinitePresentation f] :
    isFiniteLocallyFree Y ((pushforward f).obj (𝟙_ X.Modules)) :=
  isFiniteLocallyFree_pushforward f (𝟙_ X.Modules) (ObjectProperty.prop_unit _)

end AlgebraicGeometry.Scheme.Modules

namespace TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf

open _root_.AlgebraicGeometry

/-- The direct-image functor `FiniteLocallyFreeSheaf X ⥤ FiniteLocallyFreeSheaf Y` along a finite,
flat, locally finitely presented morphism `f : X ⟶ Y`. -/
def pushforward {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [Flat f]
    [LocallyOfFinitePresentation f] :
    FiniteLocallyFreeSheaf X ⥤ FiniteLocallyFreeSheaf Y :=
  (Scheme.Modules.isFiniteLocallyFree Y).lift
    ((Scheme.Modules.isFiniteLocallyFree X).ι ⋙ Scheme.Modules.pushforward f)
    fun E ↦ Scheme.Modules.isFiniteLocallyFree_pushforward f E.obj E.property

/-- The underlying `𝒪_Y`-module of the direct image of a finite locally free sheaf is its direct
image in `Y.Modules`. -/
@[simp]
lemma pushforward_obj_obj {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [Flat f]
    [LocallyOfFinitePresentation f] (E : FiniteLocallyFreeSheaf X) :
    ((pushforward f).obj E).obj = (Scheme.Modules.pushforward f).obj E.obj :=
  (rfl)

/-- Direct image acts on morphisms of finite locally free sheaves by the underlying direct image of
module morphisms. -/
@[simp]
lemma pushforward_map_hom {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [Flat f]
    [LocallyOfFinitePresentation f] {E F : FiniteLocallyFreeSheaf X} (φ : E ⟶ F) :
    ((pushforward f).map φ).hom =
      eqToHom (pushforward_obj_obj f E) ≫ (Scheme.Modules.pushforward f).map φ.hom ≫
        eqToHom (pushforward_obj_obj f F).symm := by
  cases pushforward_obj_obj f E
  cases pushforward_obj_obj f F
  unfold pushforward
  simp

/-- Direct image of finite locally free sheaves is an additive functor. -/
instance pushforward_additive {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [Flat f]
    [LocallyOfFinitePresentation f] : (pushforward f).Additive where
  map_add := ObjectProperty.hom_ext _ (Scheme.Modules.pushforward f).map_add

end TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf
