/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicThickeningSystem.CoherentFormalModule.Basic
public import TauCeti.AlgebraicGeometry.FiniteEtale.Fiber
public import TauCeti.AlgebraicGeometry.VectorBundle.FiniteLocallyFree
import TauCeti.AlgebraicGeometry.AdicThickeningSystem.Etale
import TauCeti.AlgebraicGeometry.AdicThickeningSystem.Pullback
import TauCeti.AlgebraicGeometry.RelativeSpec.BaseChange
import TauCeti.AlgebraicGeometry.RelativeSpec.Equivalence
import TauCeti.AlgebraicGeometry.VectorBundle.Pushforward
import TauCeti.CategoryTheory.EqToHom

/-!
# Formal completion criterion for full faithfulness of finite étale restriction

Let `X` be a scheme and `I` an ideal sheaf on `X`, cutting out the closed subscheme `V(I)` with
inclusion `I.subschemeι : V(I) ⟶ X` and formal completion `X.formalCompletion I`. Suppose that the
completion functor

`FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙ Scheme.formalCompletion.completionFunctor X I`

from finite locally free `𝒪_X`-modules to coherent formal modules on `X.formalCompletion I` is
fully faithful. Then pulling back finite étale schemes along `I.subschemeι` is fully faithful
(Stacks, Lemma 58.17.1 (0EL8)). No Noetherian hypothesis on `X` is needed, and faithfulness of
restriction requires only faithfulness of the completion functor on finite locally free sheaves.

The proof separates the infinitesimal lifting on adic thickening systems from the algebraization of
sheaves of algebras:

1. **Coordinate algebras of finite étale schemes.** Every finite étale `p : Y ⟶ X` is affine, hence
   isomorphic over `X` to the relative spectrum of its function algebra `p_* 𝒪_Y`
   (`Scheme.Hom.relativeSpecFunctionsIso`), whose underlying `𝒪_X`-module is finite locally free
   (`Scheme.Modules.isFiniteLocallyFree_pushforward_unit`, since `p` is finite, flat, and locally of
   finite presentation). Thus it suffices to show bijectivity on morphisms between relative spectra
   `Spec_X A₁` and `Spec_X A₂` of finite locally free quasicoherent algebras whose relative spectra
   are finite étale over `X`.
2. **Infinitesimal lifting.** Forming the levelwise fibre product of `X.formalCompletion I ⟶ X` with
   `Spec_X Aₖ ⟶ X` produces an adic thickening system `formalRelSpec I Aₖ` levelwise étale over
   `X.formalCompletion I`, whose `n`-th level is `Spec_{Xₙ} (iₙ^* Aₖ)` for the `n`-th thickening
   `iₙ : V(I ^ (n + 1)) ⟶ X` (`isPullback_relativeSpecPullbackFst`). A morphism on level zero lifts
   uniquely to a morphism `formalRelSpec I A₁ ⟶ formalRelSpec I A₂` over `X.formalCompletion I`
   (`AdicThickeningSystem.hom_ext_of_formallyUnramified`, `AdicThickeningSystem.liftOfEtale`).
3. **Algebraization.** By the anti-equivalence `relativeSpec Xₙ` on each thickening `Xₙ`, a
   morphism `formalRelSpec I A₁ ⟶ formalRelSpec I A₂` over `X.formalCompletion I` is a compatible
   family of algebra maps `iₙ^* A₂ ⟶ iₙ^* A₁`, hence a morphism of coherent formal modules between
   the completions of the finite locally free underlying modules of `A₂` and `A₁`. Faithfulness of
   completion yields uniqueness of the algebra map `A₂ ⟶ A₁`; fullness lifts the module map
   `A₂ ⟶ A₁`, and faithfulness applied to the finite locally free sheaves `𝒪_X` and `A₂ ⊗ A₂`
   descends preservation of the unit and multiplication from the thickenings.

Finally, `V(I)` is canonically isomorphic over `X` to the zeroth level `V(I ^ 1)` of
`X.formalCompletion I` (`Scheme.formalCompletion.subschemeIsoLevelZero`), and any closed immersion
`i : Z ⟶ X` factors through an isomorphism `Z ≅ i.ker.subscheme` over `X` (`i.toImage`), giving the
corresponding statements for `I.subschemeι` and for arbitrary closed immersions.

## Main declarations

* `FiniteEtaleScheme.faithful_pullback_subschemeι_of_faithful_completionFunctor`: faithfulness of
  `FiniteEtaleScheme.pullback I.subschemeι` when completion on `FiniteLocallyFreeSheaf X` is
  faithful;
* `FiniteEtaleScheme.full_pullback_subschemeι_of_fullyFaithful_completionFunctor`: fullness when
  completion on `FiniteLocallyFreeSheaf X` is full and faithful;
* `FiniteEtaleScheme.fullyFaithfulPullbackSubschemeιOfFullyFaithfulCompletionFunctor`: full
  faithfulness (Stacks 0EL8);
* `FiniteEtaleScheme.faithful_pullback_of_isClosedImmersion_of_faithful_completionFunctor`,
  `FiniteEtaleScheme.full_pullback_of_isClosedImmersion_of_fullyFaithful_completionFunctor`, and
  `FiniteEtaleScheme.fullyFaithfulPullbackOfIsClosedImmersionOfFullyFaithfulCompletionFunctor`:
  the same for an arbitrary closed immersion `i : Z ⟶ X` with ideal sheaf `i.ker`.

## References

* [The Stacks Project, Lemma 58.17.1](https://stacks.math.columbia.edu/tag/0EL8)
-/

public section

open CategoryTheory Limits MonoidalCategory Opposite AlgebraicGeometry
open TauCeti.AlgebraicGeometry
open scoped MonObj

universe u

namespace TauCeti.FiniteEtaleScheme

noncomputable section

attribute [local instance] monoidalCategorySheafOfModules

section AlgebraPresentation

variable (X : Scheme.{u})

/-- The property of a quasicoherent commutative `𝒪_X`-algebra `A` having a finite locally free
underlying module and finite étale relative spectrum over `X`. -/
private def isFiniteEtaleAlgebra : ObjectProperty (QuasicoherentAlgebra X) :=
  fun A ↦ Scheme.Modules.isFiniteLocallyFree X A.obj.X ∧
    IsFinite A.obj.relativeSpecToBase ∧ Etale A.obj.relativeSpecToBase

/-- Relative Spec from finite étale quasicoherent `𝒪_X`-algebras to `FiniteEtaleScheme X`. -/
private def relSpecFiniteEtale :
    (isFiniteEtaleAlgebra X).FullSubcategoryᵒᵖ ⥤ FiniteEtaleScheme X where
  obj C := ⟨Over.mk C.unop.obj.obj.relativeSpecToBase,
    (finiteEtaleSchemeProperty_iff _).mpr ⟨C.unop.property.2.1, C.unop.property.2.2⟩⟩
  map f := ObjectProperty.homMk (Over.homMk (CommMon.relativeSpecMap f.unop.hom.hom)
    (CommMon.relativeSpecMap_relativeSpecToBase _))
  map_id _ := ObjectProperty.hom_ext _ (Over.OverMorphism.ext (CommMon.relativeSpecMap_id _))
  map_comp _ _ := ObjectProperty.hom_ext _
    (Over.OverMorphism.ext (CommMon.relativeSpecMap_comp _ _))

private instance full_relSpecFiniteEtale : (relSpecFiniteEtale X).Full where
  map_surjective {C₁ C₂} g := by
    obtain ⟨ψ, hψ⟩ :=
      exists_relativeSpecMap_eq C₁.unop.obj C₂.unop.obj g.hom.left (Over.w g.hom)
    refine ⟨(ObjectProperty.homMk ψ).op, ?_⟩
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    exact hψ

/-- Every finite étale scheme `p : Y ⟶ X` is isomorphic over `X` to the relative spectrum of its
finite locally free function algebra `p_* 𝒪_Y`. -/
private instance essSurj_relSpecFiniteEtale : (relSpecFiniteEtale X).EssSurj where
  mem_essImage Y := by
    let p := Y.obj.hom
    have hp : p.relativeSpecFunctionsToScheme ≫ p =
        p.pushforwardStructureAlgebra.relativeSpecToBase :=
      p.relativeSpecFunctionsToScheme_comp
    have hfin : IsFinite p.pushforwardStructureAlgebra.relativeSpecToBase := hp ▸ inferInstance
    have het : Etale p.pushforwardStructureAlgebra.relativeSpecToBase := hp ▸ inferInstance
    have hflf : Scheme.Modules.isFiniteLocallyFree X p.pushforwardStructureAlgebra.X :=
      Scheme.Modules.isFiniteLocallyFree_pushforward_unit p
    let C : (isFiniteEtaleAlgebra X).FullSubcategory :=
      ⟨⟨p.pushforwardStructureAlgebra, inferInstance⟩, hflf, hfin, het⟩
    exact ⟨op C, ⟨ObjectProperty.isoMk _ (Over.isoMk p.relativeSpecFunctionsIso
      (by rw [p.relativeSpecFunctionsIso_hom]; exact hp))⟩⟩

end AlgebraPresentation

section FormalSystem

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- The adic thickening system over `X.formalCompletion I` obtained by base-changing `Spec_X A ⟶ X`
to all infinitesimal neighbourhoods `V(I ^ (n + 1))`. -/
private abbrev formalRelSpec (A : QuasicoherentAlgebra X) : AdicThickeningSystem.{u} :=
  AdicThickeningSystem.pullback (Scheme.formalCompletion.toOfScheme X I)
    (AdicThickeningSystem.ofScheme.map A.obj.relativeSpecToBase)

/-- The structure morphism `formalRelSpec I A ⟶ X.formalCompletion I`. -/
private def formalRelSpecProj (A : QuasicoherentAlgebra X) :
    formalRelSpec I A ⟶ X.formalCompletion I :=
  AdicThickeningSystem.pullback.fst (Scheme.formalCompletion.toOfScheme X I)
    (AdicThickeningSystem.ofScheme.map A.obj.relativeSpecToBase)

private lemma formalRelSpecProj_app (A : QuasicoherentAlgebra X) (n : ℕ) :
    (formalRelSpecProj I A).app n =
      Limits.pullback.fst ((Scheme.formalCompletion.toOfScheme X I).app n)
        ((AdicThickeningSystem.ofScheme.map A.obj.relativeSpecToBase).app n) :=
  AdicThickeningSystem.pullback.fst_app _ _ n

/-- The second projection `formalRelSpec I A ⟶ ofScheme.obj (Spec_X A)`. -/
private def formalRelSpecSnd (A : QuasicoherentAlgebra X) :
    formalRelSpec I A ⟶ AdicThickeningSystem.ofScheme.obj A.obj.relativeSpec :=
  AdicThickeningSystem.pullback.snd (Scheme.formalCompletion.toOfScheme X I)
    (AdicThickeningSystem.ofScheme.map A.obj.relativeSpecToBase)

/-- The `n`-th component of `formalRelSpecSnd I A`, typed directly with codomain `Spec_X A` so
that `simp` and `reassoc` rewrites compose without unfolding `AdicThickeningSystem.ofScheme`. -/
private def formalRelSpecSndApp (A : QuasicoherentAlgebra X) (n : ℕ) :
    (formalRelSpec I A).X n ⟶ A.obj.relativeSpec :=
  (formalRelSpecSnd I A).app n

private lemma formalRelSpecSnd_app (A : QuasicoherentAlgebra X) (n : ℕ) :
    (formalRelSpecSnd I A).app n =
      Limits.pullback.snd ((Scheme.formalCompletion.toOfScheme X I).app n)
        ((AdicThickeningSystem.ofScheme.map A.obj.relativeSpecToBase).app n) :=
  AdicThickeningSystem.pullback.snd_app _ _ n

private lemma formalRelSpec_X_hom_ext {Z : Scheme.{u}} {A : QuasicoherentAlgebra X} {n : ℕ}
    {u v : Z ⟶ (formalRelSpec I A).X n}
    (hproj : u ≫ (formalRelSpecProj I A).app n = v ≫ (formalRelSpecProj I A).app n)
    (hsnd : u ≫ formalRelSpecSndApp I A n = v ≫ formalRelSpecSndApp I A n) :
    u = v := by
  have hsnd' : u ≫ (formalRelSpecSnd I A).app n = v ≫ (formalRelSpecSnd I A).app n := hsnd
  rw [formalRelSpecProj_app] at hproj
  rw [formalRelSpecSnd_app] at hsnd'
  exact Limits.pullback.hom_ext hproj hsnd'

private lemma formalRelSpec_ι_proj (A : QuasicoherentAlgebra X) (n : ℕ) :
    (formalRelSpec I A).ι n ≫ (formalRelSpecProj I A).app (n + 1) =
      (formalRelSpecProj I A).app n ≫ (X.formalCompletion I).ι n :=
  (formalRelSpecProj I A).naturality n

private lemma formalRelSpec_ι_snd (A : QuasicoherentAlgebra X) (n : ℕ) :
    (formalRelSpec I A).ι n ≫ formalRelSpecSndApp I A (n + 1) =
      formalRelSpecSndApp I A n :=
  ((formalRelSpecSnd I A).naturality n).trans (Category.comp_id _)

private instance etale_formalRelSpecProj_app (A : QuasicoherentAlgebra X)
    [het : Etale A.obj.relativeSpecToBase] (n : ℕ) :
    Etale ((formalRelSpecProj I A).app n) := by
  rw [formalRelSpecProj_app]
  have hmap : Etale ((AdicThickeningSystem.ofScheme.map A.obj.relativeSpecToBase).app n) := by
    rw [AdicThickeningSystem.ofScheme_map_app]
    exact het
  exact MorphismProperty.pullback_fst _ _ hmap

/-- The cartesian square exhibiting `Spec_{Xₙ} (iₙ^* A)` as the `n`-th level of `formalRelSpec I A`.
-/
private lemma isPullback_formalRelSpecLevel (A : QuasicoherentAlgebra X) (n : ℕ) :
    IsPullback
      (((QuasicoherentAlgebra.pullback
        (Scheme.formalCompletion.toScheme X I n)).obj A).obj.relativeSpecToBase)
      (relativeSpecPullbackFst A (Scheme.formalCompletion.toScheme X I n))
      ((Scheme.formalCompletion.toOfScheme X I).app n)
      ((AdicThickeningSystem.ofScheme.map A.obj.relativeSpecToBase).app n) := by
  rw [Scheme.formalCompletion.toOfScheme_app, AdicThickeningSystem.ofScheme_map_app]
  exact (isPullback_relativeSpecPullbackFst A (Scheme.formalCompletion.toScheme X I n)).flip

/-- The levelwise isomorphism `Spec_{Xₙ} (iₙ^* A) ≅ (formalRelSpec I A).X n`. -/
private def formalRelSpecLevelIso (A : QuasicoherentAlgebra X) (n : ℕ) :
    ((QuasicoherentAlgebra.pullback
      (Scheme.formalCompletion.toScheme X I n)).obj A).obj.relativeSpec ≅
      (formalRelSpec I A).X n :=
  (isPullback_formalRelSpecLevel I A n).isoPullback

@[reassoc (attr := simp)]
private lemma formalRelSpecLevelIso_hom_fst (A : QuasicoherentAlgebra X) (n : ℕ) :
    (formalRelSpecLevelIso I A n).hom ≫ (formalRelSpecProj I A).app n =
      ((QuasicoherentAlgebra.pullback
        (Scheme.formalCompletion.toScheme X I n)).obj A).obj.relativeSpecToBase := by
  rw [formalRelSpecProj_app]
  exact (isPullback_formalRelSpecLevel I A n).isoPullback_hom_fst

@[reassoc (attr := simp)]
private lemma formalRelSpecLevelIso_hom_snd (A : QuasicoherentAlgebra X) (n : ℕ) :
    (formalRelSpecLevelIso I A n).hom ≫ formalRelSpecSndApp I A n =
      relativeSpecPullbackFst A (Scheme.formalCompletion.toScheme X I n) :=
  (congrArg ((formalRelSpecLevelIso I A n).hom ≫ ·) (formalRelSpecSnd_app I A n)).trans
    (isPullback_formalRelSpecLevel I A n).isoPullback_hom_snd

@[reassoc (attr := simp)]
private lemma formalRelSpecLevelIso_inv_toBase (A : QuasicoherentAlgebra X) (n : ℕ) :
    (formalRelSpecLevelIso I A n).inv ≫
        ((QuasicoherentAlgebra.pullback
          (Scheme.formalCompletion.toScheme X I n)).obj A).obj.relativeSpecToBase =
      (formalRelSpecProj I A).app n := by
  rw [formalRelSpecProj_app]
  exact (isPullback_formalRelSpecLevel I A n).isoPullback_inv_fst

/-- Base change of an algebra map `b : A₂ ⟶ A₁` to a morphism
`formalRelSpec I A₁ ⟶ formalRelSpec I A₂` over `X.formalCompletion I`. -/
private def formalRelSpecMap {A₁ A₂ : QuasicoherentAlgebra X} (b : A₂ ⟶ A₁) :
    formalRelSpec I A₁ ⟶ formalRelSpec I A₂ :=
  AdicThickeningSystem.pullback.lift (formalRelSpecProj I A₁)
    (formalRelSpecSnd I A₁ ≫ AdicThickeningSystem.ofScheme.map (CommMon.relativeSpecMap b.hom))
    (by
      dsimp only [formalRelSpecProj, formalRelSpecSnd]
      rw [Category.assoc, ← AdicThickeningSystem.ofScheme.map_comp,
        CommMon.relativeSpecMap_relativeSpecToBase, AdicThickeningSystem.pullback.condition])

@[reassoc (attr := simp)]
private lemma formalRelSpecMap_proj {A₁ A₂ : QuasicoherentAlgebra X} (b : A₂ ⟶ A₁) :
    formalRelSpecMap I b ≫ formalRelSpecProj I A₂ = formalRelSpecProj I A₁ :=
  AdicThickeningSystem.pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
private lemma formalRelSpecMap_snd {A₁ A₂ : QuasicoherentAlgebra X} (b : A₂ ⟶ A₁) :
    formalRelSpecMap I b ≫ formalRelSpecSnd I A₂ =
      formalRelSpecSnd I A₁ ≫
        AdicThickeningSystem.ofScheme.map (CommMon.relativeSpecMap b.hom) :=
  AdicThickeningSystem.pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
private lemma formalRelSpecMap_app_proj {A₁ A₂ : QuasicoherentAlgebra X} (b : A₂ ⟶ A₁) (n : ℕ) :
    (formalRelSpecMap I b).app n ≫ (formalRelSpecProj I A₂).app n =
      (formalRelSpecProj I A₁).app n := by
  rw [← AdicThickeningSystem.comp_app, formalRelSpecMap_proj]

@[reassoc (attr := simp)]
private lemma formalRelSpecMap_app_snd {A₁ A₂ : QuasicoherentAlgebra X} (b : A₂ ⟶ A₁) (n : ℕ) :
    (formalRelSpecMap I b).app n ≫ formalRelSpecSndApp I A₂ n =
      formalRelSpecSndApp I A₁ n ≫ CommMon.relativeSpecMap b.hom := by
  have h := congrArg (fun k ↦ k.app n) (formalRelSpecMap_snd I b)
  rw [AdicThickeningSystem.comp_app, AdicThickeningSystem.comp_app] at h
  exact h.trans (congrArg (_ ≫ ·) (AdicThickeningSystem.ofScheme_map_app _ n))

/-- Under `formalRelSpecLevelIso`, the `n`-th component of `formalRelSpecMap I b` is the relative
spectrum map of the pulled-back algebra morphism `iₙ^* b`. -/
private lemma formalRelSpecLevelIso_hom_map_inv {A₁ A₂ : QuasicoherentAlgebra X} (b : A₂ ⟶ A₁)
    (n : ℕ) :
    (formalRelSpecLevelIso I A₁ n).hom ≫ (formalRelSpecMap I b).app n ≫
        (formalRelSpecLevelIso I A₂ n).inv =
      CommMon.relativeSpecMap
        ((QuasicoherentAlgebra.pullback (Scheme.formalCompletion.toScheme X I n)).map b).hom := by
  rw [← cancel_mono (formalRelSpecLevelIso I A₂ n).hom, Category.assoc, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]
  apply formalRelSpec_X_hom_ext
  · simp
  · simp [relativeSpecMap_pullback_map_relativeSpecPullbackFst]

/-- The algebra reduction isomorphism `(ι n)^* (i_{n + 1}^* A) ≅ iₙ^* A` on the `n`-th thickening.
-/
private def pullbackTransitionAlgIso (A : QuasicoherentAlgebra X) (n : ℕ) :
    (QuasicoherentAlgebra.pullback ((X.formalCompletion I).ι n)).obj
        ((QuasicoherentAlgebra.pullback (Scheme.formalCompletion.toScheme X I (n + 1))).obj A) ≅
      (QuasicoherentAlgebra.pullback (Scheme.formalCompletion.toScheme X I n)).obj A :=
  (QuasicoherentAlgebra.pullbackComp ((X.formalCompletion I).ι n)
      (Scheme.formalCompletion.toScheme X I (n + 1))).app A ≪≫
    eqToIso (congrArg (fun f ↦ (QuasicoherentAlgebra.pullback f).obj A)
      (Scheme.formalCompletion.ι_toScheme X I n))

/-- Under `formalRelSpecLevelIso`, the transition `(formalRelSpec I A).ι n` is the projection
`Spec_{Xₙ} (iₙ^* A) ≅ Spec_{Xₙ} ((ι n)^* i_{n+1}^* A) ⟶ Spec_{X_{n+1}} (i_{n+1}^* A)`. -/
private lemma formalRelSpecLevelIso_hom_ι (A : QuasicoherentAlgebra X) (n : ℕ) :
    (formalRelSpecLevelIso I A n).hom ≫ (formalRelSpec I A).ι n =
      CommMon.relativeSpecMap (pullbackTransitionAlgIso I A n).hom.hom ≫
        relativeSpecPullbackFst
          ((QuasicoherentAlgebra.pullback (Scheme.formalCompletion.toScheme X I (n + 1))).obj A)
          ((X.formalCompletion I).ι n) ≫
        (formalRelSpecLevelIso I A (n + 1)).hom := by
  apply formalRelSpec_X_hom_ext
  · rw [Category.assoc, formalRelSpec_ι_proj, formalRelSpecLevelIso_hom_fst_assoc]
    simp
  · simp only [Category.assoc, formalRelSpec_ι_snd, formalRelSpecLevelIso_hom_snd,
      pullbackTransitionAlgIso, Iso.trans_hom, Iso.app_hom, eqToIso.hom,
      ObjectProperty.FullSubcategory.comp_hom, CommMon.relativeSpecMap_comp]
    exact (relativeSpecPullbackFst_congr A (Scheme.formalCompletion.ι_toScheme X I n)).symm.trans
      (congrArg (_ ≫ ·) (relativeSpecPullbackFst_comp A
        (Scheme.formalCompletion.toScheme X I (n + 1)) ((X.formalCompletion I).ι n)))

/-- On underlying modules, `pullbackTransitionAlgIso` agrees with the `transitionIso` of
`Scheme.formalCompletion.completionFunctor X I`. -/
private lemma pullbackTransitionAlgIso_hom_module_eq (A : QuasicoherentAlgebra X) (n : ℕ) :
    (pullbackTransitionAlgIso I A n).hom.hom.hom.hom =
      eqToHom ((QuasicoherentAlgebra.pullback_obj_X ((X.formalCompletion I).ι n) _).trans
          (congrArg _ (QuasicoherentAlgebra.pullback_obj_X
            (Scheme.formalCompletion.toScheme X I (n + 1)) A))) ≫
        ((Scheme.Modules.pullbackComp ((X.formalCompletion I).ι n)
            (Scheme.formalCompletion.toScheme X I (n + 1)) ≪≫
          Scheme.Modules.pullbackCongr
            (Scheme.formalCompletion.ι_toScheme X I n)).app A.obj.X).hom ≫
        eqToHom
          (QuasicoherentAlgebra.pullback_obj_X
            (Scheme.formalCompletion.toScheme X I n) A).symm :=
  QuasicoherentAlgebra.pullbackComp_hom_app_comp_eqToHom_hom_hom_hom
    (Scheme.formalCompletion.ι_toScheme X I n) A

/-- The cartesian square identifying `(formalRelSpec I A).X 0` with the fibre product
`Limits.pullback A.obj.relativeSpecToBase (Scheme.formalCompletion.toScheme X I 0)` used by
`Over.pullback`. -/
private lemma isPullback_formalRelSpecZero (A : QuasicoherentAlgebra X) :
    IsPullback
      (formalRelSpecSndApp I A 0)
      ((formalRelSpecProj I A).app 0)
      A.obj.relativeSpecToBase
      (Scheme.formalCompletion.toScheme X I 0) := by
  rw [← Scheme.formalCompletion.toOfScheme_app X I 0]
  have h :
      IsPullback
        ((formalRelSpecSnd I A).app 0)
        ((formalRelSpecProj I A).app 0)
        ((AdicThickeningSystem.ofScheme.map A.obj.relativeSpecToBase).app 0)
        ((Scheme.formalCompletion.toOfScheme X I).app 0) := by
    rw [formalRelSpecSnd_app, formalRelSpecProj_app]
    exact (IsPullback.of_hasPullback _ _).flip
  exact h

/-- The level-zero isomorphism `(formalRelSpec I A).X 0 ≅ Spec_X A ×_X V(I ^ 1)`. -/
private def formalRelSpecZeroIso (A : QuasicoherentAlgebra X) :
    (formalRelSpec I A).X 0 ≅
      Limits.pullback A.obj.relativeSpecToBase (Scheme.formalCompletion.toScheme X I 0) :=
  (isPullback_formalRelSpecZero I A).isoPullback

@[reassoc (attr := simp)]
private lemma formalRelSpecZeroIso_hom_fst (A : QuasicoherentAlgebra X) :
    (formalRelSpecZeroIso I A).hom ≫
        Limits.pullback.fst A.obj.relativeSpecToBase (Scheme.formalCompletion.toScheme X I 0) =
      formalRelSpecSndApp I A 0 :=
  (isPullback_formalRelSpecZero I A).isoPullback_hom_fst

@[reassoc (attr := simp)]
private lemma formalRelSpecZeroIso_hom_snd (A : QuasicoherentAlgebra X) :
    (formalRelSpecZeroIso I A).hom ≫
        Limits.pullback.snd A.obj.relativeSpecToBase (Scheme.formalCompletion.toScheme X I 0) =
      (formalRelSpecProj I A).app 0 :=
  (isPullback_formalRelSpecZero I A).isoPullback_hom_snd

@[reassoc (attr := simp)]
private lemma formalRelSpecZeroIso_inv_snd (A : QuasicoherentAlgebra X) :
    (formalRelSpecZeroIso I A).inv ≫ formalRelSpecSndApp I A 0 =
      Limits.pullback.fst A.obj.relativeSpecToBase (Scheme.formalCompletion.toScheme X I 0) :=
  (isPullback_formalRelSpecZero I A).isoPullback_inv_fst

@[reassoc (attr := simp)]
private lemma formalRelSpecZeroIso_inv_proj (A : QuasicoherentAlgebra X) :
    (formalRelSpecZeroIso I A).inv ≫ (formalRelSpecProj I A).app 0 =
      Limits.pullback.snd A.obj.relativeSpecToBase (Scheme.formalCompletion.toScheme X I 0) :=
  (isPullback_formalRelSpecZero I A).isoPullback_inv_snd

/-- Conjugation by `formalRelSpecZeroIso` relates `(formalRelSpecMap I b).app 0` to the action
of `FiniteEtaleScheme.pullback (toScheme X I 0)` on `relSpecFiniteEtale`. -/
private lemma formalRelSpecZeroIso_inv_map_hom
    {C₁ C₂ : (isFiniteEtaleAlgebra X).FullSubcategoryᵒᵖ} (f : C₁ ⟶ C₂) :
    (formalRelSpecZeroIso I C₁.unop.obj).inv ≫
        (formalRelSpecMap I f.unop.hom).app 0 ≫
        (formalRelSpecZeroIso I C₂.unop.obj).hom =
      (((pullback (Scheme.formalCompletion.toScheme X I 0)).map
        ((relSpecFiniteEtale X).map f)).hom).left := by
  apply Limits.pullback.hom_ext
  · simp [relSpecFiniteEtale]
  · simp [relSpecFiniteEtale]

private lemma naturality_of_eqToHom_conj {C₁ C₂ : Type*} [Category C₁] [Category C₂]
    (G : C₁ ⥤ C₂) {M₂ M₁ P₂ P₁ : C₁} {Q₂ Q₁ N₂ N₁ R₂ R₁ : C₂}
    (eA₂ : P₂ = M₂) (eA₁ : P₁ = M₁)
    (p₂ : Q₂ = G.obj P₂) (p₁ : Q₁ = G.obj P₁)
    (q₂ : Q₂ = G.obj M₂) (q₁ : Q₁ = G.obj M₁)
    (r₂ : R₂ = N₂) (r₁ : R₁ = N₁)
    (u : P₂ ⟶ P₁) (v : R₂ ⟶ R₁)
    (T₁ : G.obj M₁ ⟶ N₁) (T₂ : G.obj M₂ ⟶ N₂)
    (h : (eqToHom p₂ ≫ G.map u ≫ eqToHom p₁.symm) ≫ (eqToHom q₁ ≫ T₁ ≫ eqToHom r₁.symm) =
      (eqToHom q₂ ≫ T₂ ≫ eqToHom r₂.symm) ≫ v) :
    G.map (eqToHom eA₂.symm ≫ u ≫ eqToHom eA₁) ≫ T₁ =
      T₂ ≫ (eqToHom r₂.symm ≫ v ≫ eqToHom r₁) := by
  subst eA₂ eA₁ p₂ p₁ r₂ r₁
  simpa using h

-- `FiniteLocallyFreeSheaf X` lives in `X.Modules` while `FinitelyPresentedSheaf X` lives in
-- `SheafOfModules X.ringCatSheaf`, so we package `completionFunctor_map_app` on the composite.
private lemma toFinitelyPresented_comp_completionFunctor_map_app
    {E₁ E₂ : FiniteLocallyFreeSheaf X} (u : E₁ ⟶ E₂) (n : ℕ) :
    ((FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
        Scheme.formalCompletion.completionFunctor X I).map u).app n =
      (Scheme.Modules.pullback (Scheme.formalCompletion.toScheme X I n)).map u.hom :=
  Scheme.formalCompletion.completionFunctor_map_app X I
    ((FiniteLocallyFreeSheaf.toFinitelyPresented X).map u) n

/-- Two `𝒪_X`-module morphisms between finite locally free sheaves agree if their pullbacks to all
thickenings `V(I ^ (n + 1))` agree, provided completion on finite locally free sheaves is faithful.
-/
private lemma module_hom_eq_of_forall_pullback_toScheme_map_eq
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).Faithful]
    {M₁ M₂ : X.Modules}
    (hM₁ : Scheme.Modules.isFiniteLocallyFree X M₁)
    (hM₂ : Scheme.Modules.isFiniteLocallyFree X M₂)
    {g₁ g₂ : M₁ ⟶ M₂}
    (hg : ∀ n,
      (Scheme.Modules.pullback (Scheme.formalCompletion.toScheme X I n)).map g₁ =
        (Scheme.Modules.pullback (Scheme.formalCompletion.toScheme X I n)).map g₂) :
    g₁ = g₂ := by
  let E₁ : FiniteLocallyFreeSheaf X := ⟨M₁, hM₁⟩
  let E₂ : FiniteLocallyFreeSheaf X := ⟨M₂, hM₂⟩
  suffices (ObjectProperty.homMk g₁ : E₁ ⟶ E₂) = ObjectProperty.homMk g₂ from
    congrArg (·.hom) this
  apply (FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
    Scheme.formalCompletion.completionFunctor X I).map_injective
  refine AdicThickeningSystem.CoherentFormalModule.hom_ext fun n ↦ ?_
  simp only [toFinitelyPresented_comp_completionFunctor_map_app, ObjectProperty.homMk_hom]
  exact hg n

/-- Two morphisms between quasicoherent algebras with finite locally free underlying modules
agree if their pullbacks to all thickenings `V(I ^ (n + 1))` agree, provided completion on
finite locally free sheaves is faithful. -/
private lemma eq_of_forall_pullback_toScheme_map_eq
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).Faithful]
    {A₁ A₂ : QuasicoherentAlgebra X}
    (hA₁ : Scheme.Modules.isFiniteLocallyFree X A₁.obj.X)
    (hA₂ : Scheme.Modules.isFiniteLocallyFree X A₂.obj.X)
    {b₁ b₂ : A₂ ⟶ A₁}
    (hb : ∀ n,
      (QuasicoherentAlgebra.pullback (Scheme.formalCompletion.toScheme X I n)).map b₁ =
        (QuasicoherentAlgebra.pullback (Scheme.formalCompletion.toScheme X I n)).map b₂) :
    b₁ = b₂ := by
  apply ObjectProperty.hom_ext
  apply CommMon.hom_ext
  refine module_hom_eq_of_forall_pullback_toScheme_map_eq I hA₂ hA₁ fun n ↦ ?_
  have hmod := congrArg (fun k ↦ k.hom.hom.hom) (hb n)
  simp only [QuasicoherentAlgebra.pullback_map_hom_hom_hom] at hmod
  exact TauCeti.eq_of_eqToHom_conjugate _ _ hmod

/-- A morphism `formalRelSpec I A₁ ⟶ formalRelSpec I A₂` over `X.formalCompletion I` corresponds
to a compatible tower of algebra morphisms `iₙ^* A₂ ⟶ iₙ^* A₁`. -/
private lemma exists_compatible_tower_of_formalRelSpec_hom {A₁ A₂ : QuasicoherentAlgebra X}
    (a : formalRelSpec I A₁ ⟶ formalRelSpec I A₂)
    (ha : ∀ n, a.app n ≫ (formalRelSpecProj I A₂).app n = (formalRelSpecProj I A₁).app n) :
    ∃ ψ : ∀ n,
        (QuasicoherentAlgebra.pullback (Scheme.formalCompletion.toScheme X I n)).obj A₂ ⟶
          (QuasicoherentAlgebra.pullback (Scheme.formalCompletion.toScheme X I n)).obj A₁,
      (∀ n, CommMon.relativeSpecMap (ψ n).hom =
        (formalRelSpecLevelIso I A₁ n).hom ≫ a.app n ≫ (formalRelSpecLevelIso I A₂ n).inv) ∧
      (∀ n, (QuasicoherentAlgebra.pullback ((X.formalCompletion I).ι n)).map (ψ (n + 1)) ≫
        (pullbackTransitionAlgIso I A₁ n).hom =
          (pullbackTransitionAlgIso I A₂ n).hom ≫ ψ n) := by
  have hex (n : ℕ) :
      ∃ ψ : (QuasicoherentAlgebra.pullback (Scheme.formalCompletion.toScheme X I n)).obj A₂ ⟶
          (QuasicoherentAlgebra.pullback (Scheme.formalCompletion.toScheme X I n)).obj A₁,
        CommMon.relativeSpecMap ψ.hom =
          (formalRelSpecLevelIso I A₁ n).hom ≫ a.app n ≫ (formalRelSpecLevelIso I A₂ n).inv := by
    apply exists_relativeSpecMap_eq
    simp [ha n]
  choose ψ hψ using hex
  refine ⟨ψ, hψ, fun n ↦ ?_⟩
  apply eq_of_relativeSpecMap_eq
  apply (isPullback_relativeSpecPullbackFst
    ((QuasicoherentAlgebra.pullback (Scheme.formalCompletion.toScheme X I (n + 1))).obj A₂)
    ((X.formalCompletion I).ι n)).hom_ext
  · calc
      CommMon.relativeSpecMap
          ((QuasicoherentAlgebra.pullback ((X.formalCompletion I).ι n)).map (ψ (n + 1)) ≫
            (pullbackTransitionAlgIso I A₁ n).hom).hom ≫
          relativeSpecPullbackFst _ ((X.formalCompletion I).ι n) =
        CommMon.relativeSpecMap (pullbackTransitionAlgIso I A₁ n).hom.hom ≫
          CommMon.relativeSpecMap
            ((QuasicoherentAlgebra.pullback ((X.formalCompletion I).ι n)).map (ψ (n + 1))).hom ≫
          relativeSpecPullbackFst _ ((X.formalCompletion I).ι n) := by
        simp only [ObjectProperty.FullSubcategory.comp_hom, CommMon.relativeSpecMap_comp,
          Category.assoc]
      _ = CommMon.relativeSpecMap (pullbackTransitionAlgIso I A₁ n).hom.hom ≫
            relativeSpecPullbackFst _ ((X.formalCompletion I).ι n) ≫
            CommMon.relativeSpecMap (ψ (n + 1)).hom := by
        simp only [relativeSpecMap_pullback_map_relativeSpecPullbackFst]
      _ = ((formalRelSpecLevelIso I A₁ n).hom ≫ (formalRelSpec I A₁).ι n) ≫
            a.app (n + 1) ≫ (formalRelSpecLevelIso I A₂ (n + 1)).inv := by
        simp only [hψ (n + 1), formalRelSpecLevelIso_hom_ι I A₁ n, Category.assoc]
      _ = (formalRelSpecLevelIso I A₁ n).hom ≫ a.app n ≫
            ((formalRelSpecLevelIso I A₂ n).inv ≫ (formalRelSpecLevelIso I A₂ n).hom) ≫
            (formalRelSpec I A₂).ι n ≫ (formalRelSpecLevelIso I A₂ (n + 1)).inv := by
        simp only [Category.assoc, reassoc_of% (a.naturality n), Iso.inv_hom_id_assoc]
      _ = CommMon.relativeSpecMap (ψ n).hom ≫
            CommMon.relativeSpecMap (pullbackTransitionAlgIso I A₂ n).hom.hom ≫
            relativeSpecPullbackFst _ ((X.formalCompletion I).ι n) := by
        simp only [hψ n, Category.assoc, reassoc_of% (formalRelSpecLevelIso_hom_ι I A₂ n),
          Iso.hom_inv_id, Category.comp_id]
      _ = _ := by
        simp only [ObjectProperty.FullSubcategory.comp_hom, CommMon.relativeSpecMap_comp,
          Category.assoc]
  · simp only [CommMon.relativeSpecMap_relativeSpecToBase]

private lemma toFinitelyPresented_completionFunctor_transitionIso_hom
    {M : X.Modules} (hM : Scheme.Modules.isFiniteLocallyFree X M) (n : ℕ) :
    (((FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
        Scheme.formalCompletion.completionFunctor X I).obj ⟨M, hM⟩).transitionIso n).hom =
      ((Scheme.Modules.pullbackComp ((X.formalCompletion I).ι n)
          (Scheme.formalCompletion.toScheme X I (n + 1)) ≪≫
        Scheme.Modules.pullbackCongr
          (Scheme.formalCompletion.ι_toScheme X I n)).app M).hom :=
  congrArg Iso.hom (Scheme.formalCompletion.completionFunctor_obj_transitionIso X I
    ((FiniteLocallyFreeSheaf.toFinitelyPresented X).obj ⟨M, hM⟩) n)

/-- Package a compatible tower of pulled-back algebra morphisms `iₙ^* A₂ ⟶ iₙ^* A₁` as a morphism
of coherent formal modules between the completions of the underlying finite locally free sheaves. -/
private def coherentFormalModuleHomOfTower
    {A₁ A₂ : QuasicoherentAlgebra X}
    (hA₁ : Scheme.Modules.isFiniteLocallyFree X A₁.obj.X)
    (hA₂ : Scheme.Modules.isFiniteLocallyFree X A₂.obj.X)
    (ψ : ∀ n,
      (QuasicoherentAlgebra.pullback (Scheme.formalCompletion.toScheme X I n)).obj A₂ ⟶
        (QuasicoherentAlgebra.pullback (Scheme.formalCompletion.toScheme X I n)).obj A₁)
    (hψ_nat : ∀ n,
      (QuasicoherentAlgebra.pullback ((X.formalCompletion I).ι n)).map (ψ (n + 1)) ≫
        (pullbackTransitionAlgIso I A₁ n).hom =
          (pullbackTransitionAlgIso I A₂ n).hom ≫ ψ n) :
    (FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
        Scheme.formalCompletion.completionFunctor X I).obj ⟨A₂.obj.X, hA₂⟩ ⟶
      (FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
        Scheme.formalCompletion.completionFunctor X I).obj ⟨A₁.obj.X, hA₁⟩ where
  app n :=
    eqToHom
      (QuasicoherentAlgebra.pullback_obj_X (Scheme.formalCompletion.toScheme X I n) A₂).symm ≫
      (ψ n).hom.hom.hom ≫
      eqToHom (QuasicoherentAlgebra.pullback_obj_X (Scheme.formalCompletion.toScheme X I n) A₁)
  naturality n := by
    rw [toFinitelyPresented_completionFunctor_transitionIso_hom,
      toFinitelyPresented_completionFunctor_transitionIso_hom]
    have hmod := congrArg (fun k ↦ k.hom.hom.hom) (hψ_nat n)
    dsimp only [ObjectProperty.FullSubcategory.comp_hom, CommMon.comp_hom, Mon.comp_hom] at hmod
    simp only [QuasicoherentAlgebra.pullback_map_hom_hom_hom,
      pullbackTransitionAlgIso_hom_module_eq] at hmod
    exact naturality_of_eqToHom_conj (Scheme.Modules.pullback ((X.formalCompletion I).ι n))
      (QuasicoherentAlgebra.pullback_obj_X (Scheme.formalCompletion.toScheme X I (n + 1)) A₂) _
      _ (QuasicoherentAlgebra.pullback_obj_X ((X.formalCompletion I).ι n) _) _ _
      (QuasicoherentAlgebra.pullback_obj_X (Scheme.formalCompletion.toScheme X I n) A₂) _
      _ _ _ _ hmod

@[simp]
private lemma coherentFormalModuleHomOfTower_app
    {A₁ A₂ : QuasicoherentAlgebra X}
    (hA₁ : Scheme.Modules.isFiniteLocallyFree X A₁.obj.X)
    (hA₂ : Scheme.Modules.isFiniteLocallyFree X A₂.obj.X)
    (ψ : ∀ n,
      (QuasicoherentAlgebra.pullback (Scheme.formalCompletion.toScheme X I n)).obj A₂ ⟶
        (QuasicoherentAlgebra.pullback (Scheme.formalCompletion.toScheme X I n)).obj A₁)
    (hψ_nat : ∀ n,
      (QuasicoherentAlgebra.pullback ((X.formalCompletion I).ι n)).map (ψ (n + 1)) ≫
        (pullbackTransitionAlgIso I A₁ n).hom =
          (pullbackTransitionAlgIso I A₂ n).hom ≫ ψ n)
    (n : ℕ) :
    (coherentFormalModuleHomOfTower I hA₁ hA₂ ψ hψ_nat).app n =
      eqToHom
        (QuasicoherentAlgebra.pullback_obj_X (Scheme.formalCompletion.toScheme X I n) A₂).symm ≫
        (ψ n).hom.hom.hom ≫
        eqToHom
          (QuasicoherentAlgebra.pullback_obj_X (Scheme.formalCompletion.toScheme X I n) A₁) :=
  (rfl)

/-- Any compatible tower of algebra morphisms `iₙ^* A₂ ⟶ iₙ^* A₁` between pullbacks of
quasicoherent algebras with finite locally free underlying modules descends to an algebra
morphism `A₂ ⟶ A₁` when completion on finite locally free sheaves is full and faithful. -/
private lemma exists_hom_of_compatible_tower
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).Full]
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).Faithful]
    {A₁ A₂ : QuasicoherentAlgebra X}
    (hA₁ : Scheme.Modules.isFiniteLocallyFree X A₁.obj.X)
    (hA₂ : Scheme.Modules.isFiniteLocallyFree X A₂.obj.X)
    (ψ : ∀ n,
      (QuasicoherentAlgebra.pullback (Scheme.formalCompletion.toScheme X I n)).obj A₂ ⟶
        (QuasicoherentAlgebra.pullback (Scheme.formalCompletion.toScheme X I n)).obj A₁)
    (hψ_nat : ∀ n,
      (QuasicoherentAlgebra.pullback ((X.formalCompletion I).ι n)).map (ψ (n + 1)) ≫
        (pullbackTransitionAlgIso I A₁ n).hom =
          (pullbackTransitionAlgIso I A₂ n).hom ≫ ψ n) :
    ∃ b : A₂ ⟶ A₁, ∀ n,
      (QuasicoherentAlgebra.pullback (Scheme.formalCompletion.toScheme X I n)).map b = ψ n := by
  -- Lift the compatible tower of module maps along the full completion functor.
  let F₀ := FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
    Scheme.formalCompletion.completionFunctor X I
  let α := coherentFormalModuleHomOfTower I hA₁ hA₂ ψ hψ_nat
  let β : A₂.obj.X ⟶ A₁.obj.X := (F₀.preimage α).hom
  have hβ (n : ℕ) : (ψ n).hom.hom.hom =
      eqToHom (QuasicoherentAlgebra.pullback_obj_X (Scheme.formalCompletion.toScheme X I n) A₂) ≫
        (Scheme.Modules.pullback (Scheme.formalCompletion.toScheme X I n)).map β ≫
        eqToHom
          (QuasicoherentAlgebra.pullback_obj_X
            (Scheme.formalCompletion.toScheme X I n) A₁).symm := by
    let iₙ := Scheme.formalCompletion.toScheme X I n
    have h : ((FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
        Scheme.formalCompletion.completionFunctor X I).map (F₀.preimage α)).app n =
      (coherentFormalModuleHomOfTower I hA₁ hA₂ ψ hψ_nat).app n :=
      congrArg (fun k ↦ k.app n) (F₀.map_preimage α)
    rw [toFinitelyPresented_comp_completionFunctor_map_app, coherentFormalModuleHomOfTower_app] at h
    rw [h]
    exact (TauCeti.eqToHom_conjugate_cancel
      (QuasicoherentAlgebra.pullback_obj_X iₙ A₂).symm
      (QuasicoherentAlgebra.pullback_obj_X iₙ A₁).symm
      (ψ n).hom.hom.hom).symm
  -- Descend preservation of unit and multiplication by faithfulness of completion on `𝒪_X`
  -- and `A₂ ⊗ A₂`.
  have hone : η[A₂.obj.X] ≫ β = η[A₁.obj.X] :=
    module_hom_eq_of_forall_pullback_toScheme_map_eq I
      (Scheme.Modules.isMonoidal_isFiniteLocallyFree X).prop_unit hA₁ fun n ↦ by
        rw [← QuasicoherentAlgebra.one_comp_eqToHom_pullback_map_iff, ← hβ n]
        exact (ψ n).hom.hom.isMonHom_hom.one_hom
  have hmul : μ[A₂.obj.X] ≫ β = (β ⊗ₘ β) ≫ μ[A₁.obj.X] :=
    module_hom_eq_of_forall_pullback_toScheme_map_eq I
      ((Scheme.Modules.isMonoidal_isFiniteLocallyFree X).prop_tensor _ _ hA₂ hA₂) hA₁ fun n ↦ by
        rw [← QuasicoherentAlgebra.mul_comp_eqToHom_pullback_map_iff, ← hβ n]
        exact (ψ n).hom.hom.isMonHom_hom.mul_hom
  refine ⟨ObjectProperty.homMk (CommMon.homMk (@Mon.Hom.mk _ _ _ _ _ β ⟨hone, hmul⟩)), fun n ↦ ?_⟩
  apply ObjectProperty.hom_ext
  apply CommMon.hom_ext
  exact (QuasicoherentAlgebra.pullback_map_hom_hom_hom _ _).trans (hβ n).symm

/-- Faithfulness of pullback to the zeroth level `V(I ^ 1)` of `X.formalCompletion I`. -/
private lemma faithful_pullback_toScheme_zero
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).Faithful] :
    (pullback (Scheme.formalCompletion.toScheme X I 0)).Faithful := by
  refine (pullback (Scheme.formalCompletion.toScheme X I 0)).faithful_of_comp_essSurj
    (relSpecFiniteEtale X) fun {C₁ C₂} f₁ f₂ hfg ↦ ?_
  obtain ⟨f₁, rfl⟩ := (relSpecFiniteEtale X).map_surjective f₁
  obtain ⟨f₂, rfl⟩ := (relSpecFiniteEtale X).map_surjective f₂
  congr 1
  have h0 : (formalRelSpecMap I f₁.unop.hom).app 0 = (formalRelSpecMap I f₂.unop.hom).app 0 := by
    rw [← cancel_epi (formalRelSpecZeroIso I C₁.unop.obj).inv,
      ← cancel_mono (formalRelSpecZeroIso I C₂.unop.obj).hom,
      Category.assoc, Category.assoc,
      formalRelSpecZeroIso_inv_map_hom I f₁,
      formalRelSpecZeroIso_inv_map_hom I f₂]
    exact congrArg (fun k ↦ k.hom.left) hfg
  have : Etale C₂.unop.obj.obj.relativeSpecToBase := C₂.unop.property.2.2
  have hsys : formalRelSpecMap I f₁.unop.hom = formalRelSpecMap I f₂.unop.hom :=
    AdicThickeningSystem.hom_ext_of_formallyUnramified (formalRelSpecProj I C₂.unop.obj)
      ((formalRelSpecMap_proj I f₁.unop.hom).trans (formalRelSpecMap_proj I f₂.unop.hom).symm) h0
  apply Quiver.Hom.unop_inj
  apply ObjectProperty.hom_ext
  refine eq_of_forall_pullback_toScheme_map_eq I C₁.unop.property.1 C₂.unop.property.1 fun n ↦ ?_
  apply eq_of_relativeSpecMap_eq
  rw [← formalRelSpecLevelIso_hom_map_inv I f₁.unop.hom n,
    ← formalRelSpecLevelIso_hom_map_inv I f₂.unop.hom n, hsys]

/-- Fullness of pullback to the zeroth level `V(I ^ 1)` of `X.formalCompletion I`. -/
private lemma full_pullback_toScheme_zero
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).Full]
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).Faithful] :
    (pullback (Scheme.formalCompletion.toScheme X I 0)).Full := by
  refine (pullback (Scheme.formalCompletion.toScheme X I 0)).full_of_comp_essSurj
    (relSpecFiniteEtale X) fun {C₁ C₂} φ₀ ↦ ?_
  let A₁ := C₁.unop.obj
  let A₂ := C₂.unop.obj
  have : Etale A₂.obj.relativeSpecToBase := C₂.unop.property.2.2
  let φ₀' :
      Limits.pullback A₁.obj.relativeSpecToBase (Scheme.formalCompletion.toScheme X I 0) ⟶
        Limits.pullback A₂.obj.relativeSpecToBase (Scheme.formalCompletion.toScheme X I 0) :=
    φ₀.hom.left
  have hφ₀' :
      φ₀' ≫ Limits.pullback.snd A₂.obj.relativeSpecToBase
          (Scheme.formalCompletion.toScheme X I 0) =
        Limits.pullback.snd A₁.obj.relativeSpecToBase
          (Scheme.formalCompletion.toScheme X I 0) :=
    Over.w φ₀.hom
  let a₀ : (formalRelSpec I A₁).X 0 ⟶ (formalRelSpec I A₂).X 0 :=
    (formalRelSpecZeroIso I A₁).hom ≫ φ₀' ≫ (formalRelSpecZeroIso I A₂).inv
  have ha₀ : a₀ ≫ (formalRelSpecProj I A₂).app 0 = (formalRelSpecProj I A₁).app 0 := by
    simp [a₀, hφ₀']
  let a : formalRelSpec I A₁ ⟶ formalRelSpec I A₂ :=
    AdicThickeningSystem.liftOfEtale (formalRelSpecProj I A₁) (formalRelSpecProj I A₂) a₀ ha₀
  obtain ⟨ψ, hψ, hψ_nat⟩ := exists_compatible_tower_of_formalRelSpec_hom I a fun n ↦
    AdicThickeningSystem.liftOfEtale_app_comp _ _ a₀ ha₀ n
  obtain ⟨b, hb⟩ := exists_hom_of_compatible_tower I C₁.unop.property.1 C₂.unop.property.1 ψ hψ_nat
  let f : C₁ ⟶ C₂ := (ObjectProperty.homMk b).op
  refine ⟨(relSpecFiniteEtale X).map f, ?_⟩
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  have hmap₀ : (formalRelSpecMap I b).app 0 = a₀ := by
    have hconj := formalRelSpecLevelIso_hom_map_inv I b 0
    rw [hb 0, hψ 0, AdicThickeningSystem.liftOfEtale_app_zero] at hconj
    rwa [cancel_epi, cancel_mono] at hconj
  change _ = φ₀'
  rw [← formalRelSpecZeroIso_inv_map_hom I f]
  simp [f, a₀, hmap₀]

end FormalSystem

section Transport

/-- If the completion functor on finite locally free `𝒪_X`-modules is faithful, then restricting
finite étale schemes over `X` to the closed subscheme `V(I)` is faithful. -/
instance faithful_pullback_subschemeι_of_faithful_completionFunctor
    (X : Scheme.{u}) (I : X.IdealSheafData)
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).Faithful] :
    (pullback I.subschemeι).Faithful := by
  have := faithful_pullback_toScheme_zero I
  exact faithful_pullback_of_fac (Scheme.formalCompletion.subschemeIsoLevelZero X I).hom
    (Scheme.formalCompletion.toScheme X I 0) I.subschemeι
    (Scheme.formalCompletion.subschemeIsoLevelZero_hom_toScheme X I)

/-- If the completion functor on finite locally free `𝒪_X`-modules is fully faithful, then
restricting finite étale schemes over `X` to the closed subscheme `V(I)` is full. -/
instance full_pullback_subschemeι_of_fullyFaithful_completionFunctor
    (X : Scheme.{u}) (I : X.IdealSheafData)
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).Full]
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).Faithful] :
    (pullback I.subschemeι).Full := by
  have := full_pullback_toScheme_zero I
  exact full_pullback_of_fac (Scheme.formalCompletion.subschemeIsoLevelZero X I).hom
    (Scheme.formalCompletion.toScheme X I 0) I.subschemeι
    (Scheme.formalCompletion.subschemeIsoLevelZero_hom_toScheme X I)

/-- **Full faithfulness of restriction to a closed subscheme from coherent completion.** When
completion on finite locally free `𝒪_X`-modules along `V(I)` is fully faithful, pulling back finite
étale schemes along `I.subschemeι` is fully faithful. Stacks, Lemma 58.17.1 (0EL8). -/
@[stacks 0EL8]
def fullyFaithfulPullbackSubschemeιOfFullyFaithfulCompletionFunctor
    (X : Scheme.{u}) (I : X.IdealSheafData)
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).Full]
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).Faithful] :
    (pullback I.subschemeι).FullyFaithful :=
  .ofFullyFaithful _

/-- If completion on finite locally free `𝒪_X`-modules along the closed immersion `i : Z ⟶ X` is
faithful, then pulling back finite étale schemes along `i` is faithful. -/
theorem faithful_pullback_of_isClosedImmersion_of_faithful_completionFunctor
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X i.ker).Faithful] :
    (pullback i).Faithful :=
  faithful_pullback_of_fac i.toImage i.ker.subschemeι i i.toImage_imageι

/-- If completion on finite locally free `𝒪_X`-modules along the closed immersion `i : Z ⟶ X` is
fully faithful, then pulling back finite étale schemes along `i` is full. -/
theorem full_pullback_of_isClosedImmersion_of_fullyFaithful_completionFunctor
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X i.ker).Full]
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X i.ker).Faithful] :
    (pullback i).Full :=
  full_pullback_of_fac i.toImage i.ker.subschemeι i i.toImage_imageι

/-- **Full faithfulness of restriction along an arbitrary closed immersion `i : Z ⟶ X`** when
completion on finite locally free `𝒪_X`-modules along `i.ker` is fully faithful.
Stacks, Lemma 58.17.1 (0EL8). -/
@[stacks 0EL8]
def fullyFaithfulPullbackOfIsClosedImmersionOfFullyFaithfulCompletionFunctor
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X i.ker).Full]
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X i.ker).Faithful] :
    (pullback i).FullyFaithful :=
  have := full_pullback_of_isClosedImmersion_of_fullyFaithful_completionFunctor i
  have := faithful_pullback_of_isClosedImmersion_of_faithful_completionFunctor i
  .ofFullyFaithful _

end Transport

end

end TauCeti.FiniteEtaleScheme
