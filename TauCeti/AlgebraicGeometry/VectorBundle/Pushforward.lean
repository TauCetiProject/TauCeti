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
import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Pushforward.BaseChange
import TauCeti.AlgebraicGeometry.Modules.Tilde.Pushforward
import TauCeti.AlgebraicGeometry.VectorBundle.Affine.Basic
import TauCeti.AlgebraicGeometry.VectorBundle.OpenCover

/-!
# Pushforward of finite locally free sheaves along finite locally free morphisms

Let `f : Y ⟶ X` be a finite locally free morphism of schemes, meaning that `f` is finite, flat,
and locally of finite presentation (Stacks, Section 29.48, Tag 02KB). For any finite locally free
`𝒪_Y`-module `M`, the direct image `f_* M` is a finite locally free `𝒪_X`-module
(`AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree_pushforward`). In particular, the coordinate
algebra `f_* 𝒪_Y` of `f` has a finite locally free underlying `𝒪_X`-module
(`AlgebraicGeometry.Scheme.Hom.isFiniteLocallyFree_pushforwardStructureAlgebra`), and direct image
restricts to an additive functor `FiniteLocallyFreeSheaf.pushforward` from finite locally free
sheaves on `Y` to finite locally free sheaves on `X`.

No Noetherian hypothesis is imposed. The proof proceeds in three steps:

* For a morphism of affine schemes `Spec φ : Spec S ⟶ Spec R`, the ring homomorphism `φ : R ⟶ S`
  is finite, flat, and of finite presentation, so `S` is a finitely presented flat `R`-module,
  hence finitely generated and projective (`Module.Flat.projective_of_finitePresentation`). Under
  the affine equivalence between finite locally free sheaves and finitely generated projective
  modules (`TauCeti.AlgebraicGeometry.isFiniteLocallyFree_tilde_iff`), direct image corresponds to
  restriction of scalars (`TauCeti.AlgebraicGeometry.tildeRestrictScalarsIsoPushforward`), which
  preserves finite generation and projectivity
  (`RingHom.isFG_restrictScalars_of_finite`, `RingHom.projective_restrictScalars_of_projective`).
* A finite locally free morphism `f : Y ⟶ Spec R` has affine source `Y`, so identifying `Y` with
  `Spec Γ(Y, ⊤)` reduces to `Spec φ`.
* For a general base `X`, finite local freeness is checked on an affine open cover of `X`
  (`AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree_iff_forall_pullback`), where flat base
  change (`AlgebraicGeometry.Scheme.Modules.isIso_pushforwardBaseChange_app`) identifies the
  pullback of `f_* M` with the pushforward along the base-changed morphism over `Spec Rᵢ`.

## Main declarations

* `AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree_pushforward`: pushforward along a finite,
  flat morphism locally of finite presentation preserves finite locally free sheaves of modules;
* `AlgebraicGeometry.Scheme.Hom.isFiniteLocallyFree_pushforwardStructureAlgebra`: for a finite,
  flat morphism `f : Y ⟶ X` locally of finite presentation, the underlying `𝒪_X`-module of
  `f_* 𝒪_Y` is finite locally free;
* `TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.pushforward`: the pushforward functor
  `FiniteLocallyFreeSheaf Y ⥤ FiniteLocallyFreeSheaf X`.

## References

* [The Stacks Project, Section 29.48](https://stacks.math.columbia.edu/tag/02KB), finite locally
  free morphisms.
* [The Stacks Project, Lemma 30.5.2](https://stacks.math.columbia.edu/tag/02KH), flat base change.
-/

public section

open CategoryTheory Limits MonoidalCategory AlgebraicGeometry
open TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

private lemma isFiniteLocallyFree_pushforward_SpecMap {R S : CommRingCat.{u}} (φ : R ⟶ S)
    [IsFinite (Spec.map φ)] [Flat (Spec.map φ)] [LocallyOfFinitePresentation (Spec.map φ)]
    {M : (Spec S).Modules} (hM : isFiniteLocallyFree (Spec S) M) :
    isFiniteLocallyFree (Spec R) ((pushforward (Spec.map φ)).obj M) := by
  have : M.IsQuasicoherent :=
    let F : _root_.SheafOfModules (Spec S).ringCatSheaf := M
    have : F.IsLocallyFree := hM.1
    inferInstanceAs F.IsQuasicoherent
  obtain ⟨hfinP, hprojP⟩ := FiniteLocallyFreeSheaf.finite_projective_moduleSpecΓ ⟨M, hM⟩
  let P : ModuleCat.{u} S := moduleSpecΓFunctor.obj M
  have : Module.Finite S P := hfinP
  have : Module.Projective S P := hprojP
  have hφ_fin : φ.hom.Finite := (IsFinite.SpecMap_iff φ).mp inferInstance
  have hφ_flat : φ.hom.Flat := Flat.SpecMap_iff.mp inferInstance
  have hφ_fp : φ.hom.FinitePresentation :=
    (LocallyOfFinitePresentation.SpecMap_iff φ).mp inferInstance
  have hRS_proj : (letI := φ.hom.toModule; Module.Projective R S) := by
    let : Algebra R S := φ.hom.toAlgebra
    have : Module.Finite R S := hφ_fin
    have : Module.Flat R S := hφ_flat
    have : Algebra.FinitePresentation R S := hφ_fp
    have : Module.FinitePresentation R S :=
      Module.FinitePresentation.of_finite_of_finitePresentation R S
    exact Module.Flat.projective_of_finitePresentation
  let Q : ModuleCat.{u} R := (ModuleCat.restrictScalars φ.hom).obj P
  have hQ_fin : Module.Finite R Q :=
    (ModuleCat.isFG_iff Q).mp
      (φ.hom.isFG_restrictScalars_of_finite hφ_fin ((ModuleCat.isFG_iff P).mpr inferInstance))
  have hQ_proj : Module.Projective R Q :=
    φ.hom.projective_restrictScalars_of_projective hRS_proj P
  have hQ_tilde : isFiniteLocallyFree (Spec R) (tilde Q) :=
    (isFiniteLocallyFree_tilde_iff Q).mpr ⟨hQ_fin, hQ_proj⟩
  let eM : tilde P ≅ M :=
    @asIso _ _ _ _ (fromTildeΓ (R := S) M) (isIso_fromTildeΓ_of_isQuasicoherent (R := S) M)
  let ePush : tilde Q ≅ (pushforward (Spec.map φ)).obj M :=
    tildeRestrictScalarsIsoPushforward φ P ≪≫ (pushforward (Spec.map φ)).mapIso eM
  exact (isFiniteLocallyFree (Spec R)).prop_of_iso ePush hQ_tilde

private lemma isFiniteLocallyFree_pushforward_Spec {R : CommRingCat.{u}} {Y : Scheme.{u}}
    (f : Y ⟶ Spec R) [IsFinite f] [Flat f] [LocallyOfFinitePresentation f]
    {M : Y.Modules} (hM : isFiniteLocallyFree Y M) :
    isFiniteLocallyFree (Spec R) ((pushforward f).obj M) := by
  obtain ⟨_, _⟩ := hM
  have : IsAffine Y := isAffine_of_isAffineHom f
  have : M.IsQuasicoherent :=
    let F : _root_.SheafOfModules Y.ringCatSheaf := M
    have : F.IsLocallyFree := ‹_›
    inferInstanceAs F.IsQuasicoherent
  let e : Y ≅ Spec Γ(Y, ⊤) := Y.isoSpec
  let φ : R ⟶ Γ(Y, ⊤) := Spec.preimage (e.inv ≫ f)
  have hφ : Spec.map φ = e.inv ≫ f := Spec.map_preimage (e.inv ≫ f)
  have hf_eq : f = e.hom ≫ Spec.map φ := by rw [hφ, Iso.hom_inv_id_assoc]
  have : IsFinite (Spec.map φ) := by rw [hφ]; infer_instance
  have : Flat (Spec.map φ) := by rw [hφ]; infer_instance
  have : LocallyOfFinitePresentation (Spec.map φ) := by rw [hφ]; infer_instance
  -- Flat base change along the identity square for the isomorphism `e` identifies `e_* M` with
  -- `(e⁻¹)^* M`, which is finite locally free on `Spec Γ(Y, ⊤)`.
  have H : IsPullback e.inv (𝟙 (Spec Γ(Y, ⊤))) e.hom (𝟙 (Spec Γ(Y, ⊤))) :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  have := isIso_pushforwardBaseChange_app H M
  let eIso : (pushforward e.hom).obj M ≅ (pullback e.inv).obj M :=
    ((pullbackId (Spec Γ(Y, ⊤))).app ((pushforward e.hom).obj M)).symm ≪≫
      asIso ((pushforwardBaseChange H.toCommSq).app M) ≪≫
      (pushforwardId (Spec Γ(Y, ⊤))).app ((pullback e.inv).obj M)
  have heM : isFiniteLocallyFree (Spec Γ(Y, ⊤)) ((pushforward e.hom).obj M) :=
    (isFiniteLocallyFree (Spec Γ(Y, ⊤))).prop_of_iso eIso.symm
      ⟨isLocallyFree_pullback e.inv M, isFinitePresentation_pullback e.inv M⟩
  have hcomp : isFiniteLocallyFree (Spec R)
      ((pushforward (Spec.map φ)).obj ((pushforward e.hom).obj M)) :=
    isFiniteLocallyFree_pushforward_SpecMap φ heM
  exact (isFiniteLocallyFree (Spec R)).prop_of_iso
    ((pushforwardComp e.hom (Spec.map φ)).app M ≪≫ (pushforwardCongr hf_eq.symm).app M) hcomp

/-- **Pushforward preserves finite local freeness along finite locally free morphisms.** Let
`f : Y ⟶ X` be a finite, flat morphism locally of finite presentation. For every finite locally
free `𝒪_Y`-module `M`, the direct image `f_* M` is a finite locally free `𝒪_X`-module. -/
theorem isFiniteLocallyFree_pushforward {X Y : Scheme.{u}} (f : Y ⟶ X) [IsFinite f] [Flat f]
    [LocallyOfFinitePresentation f] {M : Y.Modules} (hM : isFiniteLocallyFree Y M) :
    isFiniteLocallyFree X ((pushforward f).obj M) := by
  obtain ⟨_, _⟩ := hM
  have : M.IsQuasicoherent :=
    let F : _root_.SheafOfModules Y.ringCatSheaf := M
    have : F.IsLocallyFree := ‹_›
    inferInstanceAs F.IsQuasicoherent
  let 𝒰 := X.affineOpenCover
  refine (isFiniteLocallyFree_iff_forall_pullback 𝒰.openCover _).mpr fun i ↦ ?_
  have : IsOpenImmersion (𝒰.f i) := 𝒰.openCover.map_prop i
  have H : IsPullback (Limits.pullback.fst f (𝒰.f i)) (Limits.pullback.snd f (𝒰.f i))
      f (𝒰.f i) := IsPullback.of_hasPullback f (𝒰.f i)
  have := isIso_pushforwardBaseChange_app H M
  have hpul : isFiniteLocallyFree (Limits.pullback f (𝒰.f i))
      ((pullback (Limits.pullback.fst f (𝒰.f i))).obj M) :=
    ⟨isLocallyFree_pullback _ M, isFinitePresentation_pullback _ M⟩
  exact (isFiniteLocallyFree (Spec (𝒰.X i))).prop_of_iso
    (asIso ((pushforwardBaseChange H.toCommSq).app M)).symm
    (isFiniteLocallyFree_pushforward_Spec (Limits.pullback.snd f (𝒰.f i)) hpul)

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Hom

/-- For a finite, flat morphism `f : Y ⟶ X` locally of finite presentation, the coordinate algebra
`f_* 𝒪_Y` has a finite locally free underlying `𝒪_X`-module. -/
theorem isFiniteLocallyFree_pushforwardStructureAlgebra {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsFinite f] [Flat f] [LocallyOfFinitePresentation f] :
    Scheme.Modules.isFiniteLocallyFree X f.pushforwardStructureAlgebra.X :=
  Scheme.Modules.isFiniteLocallyFree_pushforward f (Scheme.Modules.isFiniteLocallyFree Y).prop_unit

end AlgebraicGeometry.Scheme.Hom

namespace TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf

noncomputable section

variable {X Y : Scheme.{u}} (f : Y ⟶ X) [IsFinite f] [Flat f] [LocallyOfFinitePresentation f]

/-- Direct image of finite locally free sheaves along a finite, flat morphism `f : Y ⟶ X` locally
of finite presentation. -/
def pushforward : FiniteLocallyFreeSheaf Y ⥤ FiniteLocallyFreeSheaf X :=
  (Scheme.Modules.isFiniteLocallyFree X).lift
    ((Scheme.Modules.isFiniteLocallyFree Y).ι ⋙ Scheme.Modules.pushforward f)
    fun E ↦ Scheme.Modules.isFiniteLocallyFree_pushforward f E.property

/-- The underlying sheaf of the pushforward of a finite locally free sheaf is its pushforward as
an `𝒪_Y`-module. -/
@[simp]
lemma pushforward_obj_obj (E : FiniteLocallyFreeSheaf Y) :
    ((pushforward f).obj E).obj = (Scheme.Modules.pushforward f).obj E.obj :=
  (rfl)

/-- Pushforward acts on a morphism of finite locally free sheaves by the underlying pushforward of
modules. -/
@[simp]
lemma pushforward_map_hom {E F : FiniteLocallyFreeSheaf Y} (φ : E ⟶ F) :
    ((pushforward f).map φ).hom =
      eqToHom (pushforward_obj_obj f E) ≫ (Scheme.Modules.pushforward f).map φ.hom ≫
        eqToHom (pushforward_obj_obj f F).symm := by
  cases pushforward_obj_obj f E
  cases pushforward_obj_obj f F
  unfold pushforward
  simp

/-- Pushforward of finite locally free sheaves is additive. -/
instance : (pushforward f).Additive := by
  unfold pushforward
  infer_instance

end

end TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf
