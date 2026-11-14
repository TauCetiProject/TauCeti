/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicThickeningSystem.CoherentFormalModule.Basic
public import TauCeti.AlgebraicGeometry.FiniteEtale.Fiber
public import TauCeti.AlgebraicGeometry.FiniteEtale.MorphismProperty
public import TauCeti.AlgebraicGeometry.VectorBundle.FiniteLocallyFree
import TauCeti.AlgebraicGeometry.AdicThickeningSystem.Etale
import TauCeti.AlgebraicGeometry.AdicThickeningSystem.Pullback
import TauCeti.AlgebraicGeometry.RelativeSpec.BaseChange
import TauCeti.AlgebraicGeometry.RelativeSpec.Equivalence
import TauCeti.AlgebraicGeometry.VectorBundle.Pushforward

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
`X.formalCompletion I`, and any closed immersion `i : Z ⟶ X` is canonically isomorphic over `X` to
`i.ker.subschemeι`, giving the corresponding statements for `I.subschemeι`, for arbitrary closed
immersions, and for Mathlib's `MorphismProperty.Over` presentation.

## Main declarations

* `TauCeti.FiniteEtaleScheme.faithful_pullback_subschemeι`: faithfulness of
  `FiniteEtaleScheme.pullback I.subschemeι` when completion on `FiniteLocallyFreeSheaf X` is
  faithful;
* `TauCeti.FiniteEtaleScheme.full_pullback_subschemeι`: fullness when completion on
  `FiniteLocallyFreeSheaf X` is full and faithful;
* `TauCeti.FiniteEtaleScheme.fullyFaithfulPullbackSubschemeι` and
  `TauCeti.FiniteEtaleScheme.fullyFaithful_of_completion_coherent`: full faithfulness (Stacks 0EL8);
* `TauCeti.FiniteEtaleScheme.faithful_pullback_of_isClosedImmersion`,
  `TauCeti.FiniteEtaleScheme.full_pullback_of_isClosedImmersion`, and
  `TauCeti.FiniteEtaleScheme.fullyFaithfulPullbackOfIsClosedImmersion`: the same for an arbitrary
  closed immersion `i : Z ⟶ X` with ideal sheaf `i.ker`;
* `TauCeti.FiniteEtaleScheme.overPullback_fullyFaithful_of_completion_coherent`: the companion
  statement for `MorphismProperty.Over.pullback (@IsFinite ⊓ @Etale) ⊤ I.subschemeι`.

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

/-- The monoidal structure of `Z.Modules`, stated for the unfolded type
`SheafOfModules Z.ringCatSheaf`, which typeclass search does not see through the definition of
`Scheme.Modules`. -/
local instance monoidalCategorySheafOfModules (Z : Scheme.{u}) :
    MonoidalCategory (_root_.SheafOfModules Z.ringCatSheaf) :=
  Scheme.Modules.instMonoidalCategory Z

section AlgebraPresentation

/-- Faithfulness of `relativeSpec Z` at the level of underlying algebra morphisms. -/
private lemma eq_of_relativeSpecMap_eq {Z : Scheme.{u}} {B₁ B₂ : QuasicoherentAlgebra Z}
    {u v : B₁ ⟶ B₂} (h : CommMon.relativeSpecMap u.hom = CommMon.relativeSpecMap v.hom) :
    u = v := by
  have hmap : (relativeSpec Z).map u.op = (relativeSpec Z).map v.op := by
    apply MorphismProperty.Over.Hom.ext
    exact h
  exact Quiver.Hom.op_inj ((relativeSpec Z).map_injective hmap)

/-- Fullness of `relativeSpec Z`: any morphism `Spec_Z B₁ ⟶ Spec_Z B₂` over `Z` is
`CommMon.relativeSpecMap ψ.hom` for some `ψ : B₂ ⟶ B₁`. -/
private lemma exists_relativeSpecMap_eq {Z : Scheme.{u}} (B₁ B₂ : QuasicoherentAlgebra Z)
    (g : B₁.obj.relativeSpec ⟶ B₂.obj.relativeSpec)
    (hg : g ≫ B₂.obj.relativeSpecToBase = B₁.obj.relativeSpecToBase) :
    ∃ ψ : B₂ ⟶ B₁, CommMon.relativeSpecMap ψ.hom = g := by
  let g' : (relativeSpec Z).obj (op B₁) ⟶ (relativeSpec Z).obj (op B₂) :=
    MorphismProperty.Over.homMk g hg
  refine ⟨((relativeSpec Z).preimage g').unop, ?_⟩
  exact congrArg (·.left) ((relativeSpec Z).map_preimage g')

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

private lemma formalRelSpecSnd_app (A : QuasicoherentAlgebra X) (n : ℕ) :
    (formalRelSpecSnd I A).app n =
      Limits.pullback.snd ((Scheme.formalCompletion.toOfScheme X I).app n)
        ((AdicThickeningSystem.ofScheme.map A.obj.relativeSpecToBase).app n) :=
  AdicThickeningSystem.pullback.snd_app _ _ n

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
    (formalRelSpecLevelIso I A n).hom ≫ (formalRelSpecSnd I A).app n =
      relativeSpecPullbackFst A (Scheme.formalCompletion.toScheme X I n) := by
  rw [formalRelSpecSnd_app]
  exact (isPullback_formalRelSpecLevel I A n).isoPullback_hom_snd

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
  let lhs := (formalRelSpecLevelIso I A₁ n).hom ≫ (formalRelSpecMap I b).app n
  let m := CommMon.relativeSpecMap
    ((QuasicoherentAlgebra.pullback (Scheme.formalCompletion.toScheme X I n)).map b).hom
  let rhs := m ≫ (formalRelSpecLevelIso I A₂ n).hom
  apply Limits.pullback.hom_ext
  · have hfst := (formalRelSpecProj_app I A₂ n).symm
    have hmap :
        (formalRelSpecMap I b).app n ≫ (formalRelSpecProj I A₂).app n =
          (formalRelSpecProj I A₁).app n :=
      (AdicThickeningSystem.comp_app _ _ n).symm.trans
        (congrArg (·.app n) (formalRelSpecMap_proj I b))
    have hL :=
      (congrArg (lhs ≫ ·) hfst).trans <|
        (Category.assoc _ _ _).trans <|
          (congrArg ((formalRelSpecLevelIso I A₁ n).hom ≫ ·) hmap).trans
            (formalRelSpecLevelIso_hom_fst I A₁ n)
    have hR :=
      (congrArg (rhs ≫ ·) hfst).trans <|
        (Category.assoc _ _ _).trans <|
          (congrArg (m ≫ ·) (formalRelSpecLevelIso_hom_fst I A₂ n)).trans
            (CommMon.relativeSpecMap_relativeSpecToBase _)
    exact hL.trans hR.symm
  · have hsnd := (formalRelSpecSnd_app I A₂ n).symm
    have hmap :
        (formalRelSpecMap I b).app n ≫ (formalRelSpecSnd I A₂).app n =
          (formalRelSpecSnd I A₁).app n ≫ CommMon.relativeSpecMap b.hom :=
      (AdicThickeningSystem.comp_app _ _ n).symm.trans <|
        (congrArg (·.app n) (formalRelSpecMap_snd I b)).trans <|
          (AdicThickeningSystem.comp_app _ _ n).trans
            (congrArg ((formalRelSpecSnd I A₁).app n ≫ ·)
              (AdicThickeningSystem.ofScheme_map_app _ n))
    have hL :=
      (congrArg (lhs ≫ ·) hsnd).trans <|
        (Category.assoc _ _ _).trans <|
          (congrArg ((formalRelSpecLevelIso I A₁ n).hom ≫ ·) hmap).trans
            (formalRelSpecLevelIso_hom_snd_assoc I A₁ n _)
    have hR :=
      (congrArg (rhs ≫ ·) hsnd).trans <|
        (Category.assoc _ _ _).trans <|
          (congrArg (m ≫ ·) (formalRelSpecLevelIso_hom_snd I A₂ n)).trans
            (relativeSpecMap_pullback_map_relativeSpecPullbackFst A₁
              (Scheme.formalCompletion.toScheme X I n) b)
    exact hL.trans hR.symm

/-- Transporting `relativeSpecPullbackFst` along an equality of base morphisms. -/
private lemma relativeSpecPullbackFst_congr {Y : Scheme.{u}} (A : QuasicoherentAlgebra X)
    {f₁ f₂ : Y ⟶ X} (hf : f₁ = f₂) :
    CommMon.relativeSpecMap
        (eqToHom (congrArg (fun f ↦ (QuasicoherentAlgebra.pullback f).obj A) hf)).hom ≫
      relativeSpecPullbackFst A f₁ = relativeSpecPullbackFst A f₂ := by
  subst hf
  simp

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
  let lhs := (formalRelSpecLevelIso I A n).hom ≫ (formalRelSpec I A).ι n
  let c₁ := ((QuasicoherentAlgebra.pullbackComp ((X.formalCompletion I).ι n)
      (Scheme.formalCompletion.toScheme X I (n + 1))).hom.app A).hom
  let c₂ := (eqToHom (congrArg (fun f ↦ (QuasicoherentAlgebra.pullback f).obj A)
      (Scheme.formalCompletion.ι_toScheme X I n))).hom
  let p₁ := CommMon.relativeSpecMap (pullbackTransitionAlgIso I A n).hom.hom
  let p₂ := relativeSpecPullbackFst
    ((QuasicoherentAlgebra.pullback (Scheme.formalCompletion.toScheme X I (n + 1))).obj A)
    ((X.formalCompletion I).ι n)
  let rhs := p₁ ≫ p₂ ≫ (formalRelSpecLevelIso I A (n + 1)).hom
  apply Limits.pullback.hom_ext
  · have hfst := (formalRelSpecProj_app I A (n + 1)).symm
    have hL :=
      (congrArg (lhs ≫ ·) hfst).trans <|
        (Category.assoc _ _ _).trans <|
          (congrArg ((formalRelSpecLevelIso I A n).hom ≫ ·)
            ((formalRelSpecProj I A).naturality n)).trans
            (formalRelSpecLevelIso_hom_fst_assoc I A n ((X.formalCompletion I).ι n))
    have hR :=
      (congrArg (rhs ≫ ·) hfst).trans <|
        (Category.assoc p₁ (p₂ ≫ (formalRelSpecLevelIso I A (n + 1)).hom) _).trans <|
          (congrArg (p₁ ≫ ·) <|
            (Category.assoc p₂ (formalRelSpecLevelIso I A (n + 1)).hom _).trans <|
              (congrArg (p₂ ≫ ·) (formalRelSpecLevelIso_hom_fst I A (n + 1))).trans
                (relativeSpecPullbackFst_relativeSpecToBase _ _)).trans
            (CommMon.relativeSpecMap_relativeSpecToBase_assoc
              (pullbackTransitionAlgIso I A n).hom.hom ((X.formalCompletion I).ι n))
    exact hL.trans hR.symm
  · have hsnd := (formalRelSpecSnd_app I A (n + 1)).symm
    have hnat :
        (formalRelSpec I A).ι n ≫ (formalRelSpecSnd I A).app (n + 1) =
          (formalRelSpecSnd I A).app n :=
      ((formalRelSpecSnd I A).naturality n).trans (Category.comp_id _)
    have hL :=
      (congrArg (lhs ≫ ·) hsnd).trans <|
        (Category.assoc _ _ _).trans <|
          (congrArg ((formalRelSpecLevelIso I A n).hom ≫ ·) hnat).trans
            (formalRelSpecLevelIso_hom_snd I A n)
    have hpull :
        p₁ ≫ p₂ ≫ relativeSpecPullbackFst A (Scheme.formalCompletion.toScheme X I (n + 1)) =
          relativeSpecPullbackFst A (Scheme.formalCompletion.toScheme X I n) :=
      (congrArg (· ≫ p₂ ≫ relativeSpecPullbackFst A (Scheme.formalCompletion.toScheme X I (n + 1)))
          (CommMon.relativeSpecMap_comp c₁ c₂)).trans <|
        (Category.assoc _ _ _).trans <|
          (congrArg (CommMon.relativeSpecMap c₂ ≫ ·)
            (relativeSpecPullbackFst_comp A (Scheme.formalCompletion.toScheme X I (n + 1))
              ((X.formalCompletion I).ι n)).symm).trans
            (relativeSpecPullbackFst_congr A (Scheme.formalCompletion.ι_toScheme X I n))
    have hR :=
      (congrArg (rhs ≫ ·) hsnd).trans <|
        (Category.assoc p₁ (p₂ ≫ (formalRelSpecLevelIso I A (n + 1)).hom) _).trans <|
          (congrArg (p₁ ≫ ·) <|
            (Category.assoc p₂ (formalRelSpecLevelIso I A (n + 1)).hom _).trans <|
              congrArg (p₂ ≫ ·) (formalRelSpecLevelIso_hom_snd I A (n + 1))).trans hpull
    exact hL.trans hR.symm

/-- Auxiliary equality identifying `(pullbackComp g f).hom.app A ≫ eqToHom _` on underlying modules.
-/
private lemma pullbackComp_eqToHom_module_eq {Y Z : Scheme.{u}} {f : Y ⟶ X} {g : Z ⟶ Y}
    {h : Z ⟶ X} (hf : g ≫ f = h) (A : QuasicoherentAlgebra X) :
    ((QuasicoherentAlgebra.pullbackComp g f).hom.app A ≫
        eqToHom (congrArg (fun k ↦ (QuasicoherentAlgebra.pullback k).obj A) hf)).hom.hom.hom =
      eqToHom ((QuasicoherentAlgebra.pullback_obj_X g _).trans
          (congrArg _ (QuasicoherentAlgebra.pullback_obj_X f A))) ≫
        ((Scheme.Modules.pullbackComp g f ≪≫ Scheme.Modules.pullbackCongr hf).app A.obj.X).hom ≫
        eqToHom (QuasicoherentAlgebra.pullback_obj_X h A).symm := by
  subst hf
  simp only [eqToHom_refl, Category.comp_id,
    QuasicoherentAlgebra.pullbackComp_hom_app_hom_hom_hom]
  rfl

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
  pullbackComp_eqToHom_module_eq (Scheme.formalCompletion.ι_toScheme X I n) A

/-- If `f^* β` underlies an algebra map `f^* A₂ ⟶ f^* A₁`, then `f^*` equalizes the two composites
in the multiplicativity equation `μ ≫ β = (β ⊗ₘ β) ≫ μ`. -/
private lemma pullback_map_mul_eq {Z : Scheme.{u}} (f : Z ⟶ X)
    {A₁ A₂ : QuasicoherentAlgebra X} (β : A₂.obj.X ⟶ A₁.obj.X)
    (ψ : (QuasicoherentAlgebra.pullback f).obj A₂ ⟶ (QuasicoherentAlgebra.pullback f).obj A₁)
    (hβ : ψ.hom.hom.hom =
      eqToHom (QuasicoherentAlgebra.pullback_obj_X f A₂) ≫
        (Scheme.Modules.pullback f).map β ≫
        eqToHom (QuasicoherentAlgebra.pullback_obj_X f A₁).symm) :
    (Scheme.Modules.pullback f).map (μ[A₂.obj.X] ≫ β) =
      (Scheme.Modules.pullback f).map ((β ⊗ₘ β) ≫ μ[A₁.obj.X]) := by
  let F := Scheme.Modules.pullback f
  let φ : F.obj A₂.obj.X ⟶ ((QuasicoherentAlgebra.pullback f).obj A₁).obj.X :=
    F.map β ≫ eqToHom (QuasicoherentAlgebra.pullback_obj_X f A₁).symm
  have hmul :
      μ[((QuasicoherentAlgebra.pullback f).obj A₂).obj.X] ≫
          eqToHom (QuasicoherentAlgebra.pullback_obj_X f A₂) ≫ φ =
        ((eqToHom (QuasicoherentAlgebra.pullback_obj_X f A₂) ≫ φ) ⊗ₘ
            (eqToHom (QuasicoherentAlgebra.pullback_obj_X f A₂) ≫ φ)) ≫
          μ[((QuasicoherentAlgebra.pullback f).obj A₁).obj.X] := by
    have h := ψ.hom.hom.isMonHom_hom.mul_hom
    simp only [hβ] at h
    exact h
  rw [QuasicoherentAlgebra.pullback_obj_mul f A₂, ← tensorHom_comp_tensorHom] at hmul
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp] at hmul
  rw [cancel_epi, IsIso.inv_comp_eq] at hmul
  dsimp only [φ] at hmul
  rw [QuasicoherentAlgebra.pullback_obj_mul f A₁, ← tensorHom_comp_tensorHom] at hmul
  simp only [Category.assoc, tensorHom_comp_tensorHom_assoc, eqToHom_trans, eqToHom_refl,
    id_tensorHom_id, Category.id_comp] at hmul
  rw [Functor.OplaxMonoidal.δ_natural_assoc, IsIso.hom_inv_id_assoc, ← Functor.map_comp_assoc,
    ← Functor.map_comp_assoc, cancel_mono] at hmul
  exact hmul

/-- The cartesian square identifying `(formalRelSpec I A).X 0` with the fibre product
`Limits.pullback A.obj.relativeSpecToBase (Scheme.formalCompletion.toScheme X I 0)` used by
`Over.pullback`. -/
private lemma isPullback_formalRelSpecZero (A : QuasicoherentAlgebra X) :
    IsPullback
      ((formalRelSpecSnd I A).app 0)
      ((formalRelSpecProj I A).app 0)
      A.obj.relativeSpecToBase
      (Scheme.formalCompletion.toScheme X I 0) := by
  rw [formalRelSpecSnd_app, formalRelSpecProj_app, ← Scheme.formalCompletion.toOfScheme_app X I 0]
  exact (IsPullback.of_hasPullback _ _).flip

/-- The level-zero isomorphism `(formalRelSpec I A).X 0 ≅ Spec_X A ×_X V(I ^ 1)`. -/
private def formalRelSpecZeroIso (A : QuasicoherentAlgebra X) :
    (formalRelSpec I A).X 0 ≅
      Limits.pullback A.obj.relativeSpecToBase (Scheme.formalCompletion.toScheme X I 0) :=
  (isPullback_formalRelSpecZero I A).isoPullback

@[reassoc (attr := simp)]
private lemma formalRelSpecZeroIso_hom_fst (A : QuasicoherentAlgebra X) :
    (formalRelSpecZeroIso I A).hom ≫
        Limits.pullback.fst A.obj.relativeSpecToBase (Scheme.formalCompletion.toScheme X I 0) =
      (formalRelSpecSnd I A).app 0 :=
  (isPullback_formalRelSpecZero I A).isoPullback_hom_fst

@[reassoc (attr := simp)]
private lemma formalRelSpecZeroIso_hom_snd (A : QuasicoherentAlgebra X) :
    (formalRelSpecZeroIso I A).hom ≫
        Limits.pullback.snd A.obj.relativeSpecToBase (Scheme.formalCompletion.toScheme X I 0) =
      (formalRelSpecProj I A).app 0 :=
  (isPullback_formalRelSpecZero I A).isoPullback_hom_snd

@[reassoc (attr := simp)]
private lemma formalRelSpecZeroIso_inv_snd (A : QuasicoherentAlgebra X) :
    (formalRelSpecZeroIso I A).inv ≫ (formalRelSpecSnd I A).app 0 =
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
  · have hmap :
        (formalRelSpecMap I f.unop.hom).app 0 ≫ (formalRelSpecSnd I C₂.unop.obj).app 0 =
          (formalRelSpecSnd I C₁.unop.obj).app 0 ≫ CommMon.relativeSpecMap f.unop.hom.hom :=
      (AdicThickeningSystem.comp_app _ _ 0).symm.trans <|
        (congrArg (·.app 0) (formalRelSpecMap_snd I f.unop.hom)).trans <|
          (AdicThickeningSystem.comp_app _ _ 0).trans
            (congrArg ((formalRelSpecSnd I C₁.unop.obj).app 0 ≫ ·)
              (AdicThickeningSystem.ofScheme_map_app _ 0))
    have hL :=
      (Category.assoc (formalRelSpecZeroIso I C₁.unop.obj).inv
          ((formalRelSpecMap I f.unop.hom).app 0 ≫ (formalRelSpecZeroIso I C₂.unop.obj).hom)
          _).trans <|
        (congrArg ((formalRelSpecZeroIso I C₁.unop.obj).inv ≫ ·) <|
          (Category.assoc ((formalRelSpecMap I f.unop.hom).app 0)
              (formalRelSpecZeroIso I C₂.unop.obj).hom _).trans <|
            (congrArg ((formalRelSpecMap I f.unop.hom).app 0 ≫ ·)
              (formalRelSpecZeroIso_hom_fst I C₂.unop.obj)).trans hmap).trans
          (formalRelSpecZeroIso_inv_snd_assoc I C₁.unop.obj _)
    exact hL.trans (Limits.pullback.lift_fst _ _ _).symm
  · have hmap :
        (formalRelSpecMap I f.unop.hom).app 0 ≫ (formalRelSpecProj I C₂.unop.obj).app 0 =
          (formalRelSpecProj I C₁.unop.obj).app 0 :=
      (AdicThickeningSystem.comp_app _ _ 0).symm.trans
        (congrArg (·.app 0) (formalRelSpecMap_proj I f.unop.hom))
    have hL :=
      (Category.assoc (formalRelSpecZeroIso I C₁.unop.obj).inv
          ((formalRelSpecMap I f.unop.hom).app 0 ≫ (formalRelSpecZeroIso I C₂.unop.obj).hom)
          _).trans <|
        (congrArg ((formalRelSpecZeroIso I C₁.unop.obj).inv ≫ ·) <|
          (Category.assoc ((formalRelSpecMap I f.unop.hom).app 0)
              (formalRelSpecZeroIso I C₂.unop.obj).hom _).trans <|
            (congrArg ((formalRelSpecMap I f.unop.hom).app 0 ≫ ·)
              (formalRelSpecZeroIso_hom_snd I C₂.unop.obj)).trans hmap).trans
          (formalRelSpecZeroIso_inv_proj I C₁.unop.obj)
    exact hL.trans (Limits.pullback.lift_snd _ _ _).symm

private lemma iso_hom_comp_inv_comp {C : Type*} [Category C] {X₁ Y₁ X₂ Y₂ Z : C}
    (e₁ : X₁ ≅ Y₁) (e₂ : X₂ ≅ Y₂) (g : Y₁ ⟶ Y₂) (p₁ : X₁ ⟶ Z) (p₂ : X₂ ⟶ Z)
    (q₁ : Y₁ ⟶ Z) (q₂ : Y₂ ⟶ Z)
    (h₁ : e₁.hom ≫ q₁ = p₁) (h₂ : e₂.inv ≫ p₂ = q₂) (hg : g ≫ q₂ = q₁) :
    (e₁.hom ≫ g ≫ e₂.inv) ≫ p₂ = p₁ := by
  rw [Category.assoc, Category.assoc, h₂, hg, h₁]

private lemma iso_inv_hom_conj_inv_hom {C : Type*} [Category C] {X₁ Y₁ X₂ Y₂ : C}
    (e₁ : X₁ ≅ Y₁) (e₂ : X₂ ≅ Y₂) (g : Y₁ ⟶ Y₂) :
    e₁.inv ≫ (e₁.hom ≫ g ≫ e₂.inv) ≫ e₂.hom = g := by
  simp

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

private lemma eq_eqToHom_conj_of_eq {C : Type*} [Category C] {X₂ X₁ Y₂ Y₁ : C}
    (e₂ : X₂ = Y₂) (e₁ : X₁ = Y₁) (f : X₂ ⟶ X₁) (g : Y₂ ⟶ Y₁)
    (h : g = eqToHom e₂.symm ≫ f ≫ eqToHom e₁) :
    f = eqToHom e₂ ≫ g ≫ eqToHom e₁.symm := by
  subst e₂ e₁
  simpa using h.symm

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
  let E₁ : FiniteLocallyFreeSheaf X := ⟨C₁.unop.obj.obj.X, C₁.unop.property.1⟩
  let E₂ : FiniteLocallyFreeSheaf X := ⟨C₂.unop.obj.obj.X, C₂.unop.property.1⟩
  let u₁ : E₂ ⟶ E₁ := ObjectProperty.homMk f₁.unop.hom.hom.hom.hom
  let u₂ : E₂ ⟶ E₁ := ObjectProperty.homMk f₂.unop.hom.hom.hom.hom
  have hu : (FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
        Scheme.formalCompletion.completionFunctor X I).map u₁ =
      (FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
        Scheme.formalCompletion.completionFunctor X I).map u₂ := by
    refine AdicThickeningSystem.CoherentFormalModule.hom_ext fun n ↦ ?_
    have hn :
        (QuasicoherentAlgebra.pullback (Scheme.formalCompletion.toScheme X I n)).map f₁.unop.hom =
          (QuasicoherentAlgebra.pullback (Scheme.formalCompletion.toScheme X I n)).map
            f₂.unop.hom := by
      apply eq_of_relativeSpecMap_eq
      rw [← formalRelSpecLevelIso_hom_map_inv I f₁.unop.hom n,
        ← formalRelSpecLevelIso_hom_map_inv I f₂.unop.hom n, hsys]
    have hmod := congrArg (fun k ↦ k.hom.hom.hom) hn
    simp only [QuasicoherentAlgebra.pullback_map_hom_hom_hom] at hmod
    exact (cancel_mono (eqToHom (QuasicoherentAlgebra.pullback_obj_X _ _).symm)).mp
      ((cancel_epi (eqToHom (QuasicoherentAlgebra.pullback_obj_X _ _))).mp hmod)
  have heq : u₁ = u₂ :=
    (FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).map_injective hu
  apply Quiver.Hom.unop_inj
  apply ObjectProperty.hom_ext
  apply ObjectProperty.hom_ext
  apply CommMon.hom_ext
  exact congrArg (·.hom) heq

/-- Fullness of pullback to the zeroth level `V(I ^ 1)` of `X.formalCompletion I`. -/
private lemma full_pullback_toScheme_zero
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).Full]
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).Faithful] :
    (pullback (Scheme.formalCompletion.toScheme X I 0)).Full := by
  let F₀ := FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
    Scheme.formalCompletion.completionFunctor X I
  refine (pullback (Scheme.formalCompletion.toScheme X I 0)).full_of_comp_essSurj
    (relSpecFiniteEtale X) fun {C₁ C₂} φ₀ ↦ ?_
  let A₁ := C₁.unop.obj
  let A₂ := C₂.unop.obj
  have : Etale A₂.obj.relativeSpecToBase := C₂.unop.property.2.2
  -- Step 1: lift `φ₀` across all levels of `X.formalCompletion I`.
  let a₀ : (formalRelSpec I A₁).X 0 ⟶ (formalRelSpec I A₂).X 0 :=
    (formalRelSpecZeroIso I A₁).hom ≫ φ₀.hom.left ≫ (formalRelSpecZeroIso I A₂).inv
  have ha₀ : a₀ ≫ (formalRelSpecProj I A₂).app 0 = (formalRelSpecProj I A₁).app 0 :=
    iso_hom_comp_inv_comp (formalRelSpecZeroIso I A₁) (formalRelSpecZeroIso I A₂) φ₀.hom.left
      _ _ _ _ (formalRelSpecZeroIso_hom_snd I A₁) (formalRelSpecZeroIso_inv_proj I A₂)
      (Over.w φ₀.hom)
  let a : formalRelSpec I A₁ ⟶ formalRelSpec I A₂ :=
    AdicThickeningSystem.liftOfEtale (formalRelSpecProj I A₁) (formalRelSpecProj I A₂) a₀ ha₀
  -- Step 2: convert each level `a.app n` to an algebra morphism `ψ n : iₙ^* A₂ ⟶ iₙ^* A₁`.
  have hex (n : ℕ) :
      ∃ ψ : (QuasicoherentAlgebra.pullback (Scheme.formalCompletion.toScheme X I n)).obj A₂ ⟶
          (QuasicoherentAlgebra.pullback (Scheme.formalCompletion.toScheme X I n)).obj A₁,
        CommMon.relativeSpecMap ψ.hom =
          (formalRelSpecLevelIso I A₁ n).hom ≫ a.app n ≫ (formalRelSpecLevelIso I A₂ n).inv := by
    apply exists_relativeSpecMap_eq
    simp only [a, Category.assoc, formalRelSpecLevelIso_inv_toBase,
      AdicThickeningSystem.liftOfEtale_app_comp, formalRelSpecLevelIso_hom_fst]
  choose ψ hψ using hex
  -- Step 3: verify that `ψ` commutes with the algebra reduction isomorphisms.
  have hψ_nat (n : ℕ) :
      (QuasicoherentAlgebra.pullback ((X.formalCompletion I).ι n)).map (ψ (n + 1)) ≫
          (pullbackTransitionAlgIso I A₁ n).hom =
        (pullbackTransitionAlgIso I A₂ n).hom ≫ ψ n := by
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
  -- Step 4: package the underlying module maps as a morphism in `CoherentFormalModule` and lift.
  let E₁ : FiniteLocallyFreeSheaf X := ⟨A₁.obj.X, C₁.unop.property.1⟩
  let E₂ : FiniteLocallyFreeSheaf X := ⟨A₂.obj.X, C₂.unop.property.1⟩
  let α : F₀.obj E₂ ⟶ F₀.obj E₁ :=
    { app n :=
        eqToHom
          (QuasicoherentAlgebra.pullback_obj_X (Scheme.formalCompletion.toScheme X I n) A₂).symm ≫
          (ψ n).hom.hom.hom ≫
          eqToHom (QuasicoherentAlgebra.pullback_obj_X (Scheme.formalCompletion.toScheme X I n) A₁)
      naturality n := by
        have hmod := congrArg (fun k ↦ k.hom.hom.hom) (hψ_nat n)
        dsimp only [ObjectProperty.FullSubcategory.comp_hom, CommMon.comp_hom, Mon.comp_hom]
          at hmod
        simp only [QuasicoherentAlgebra.pullback_map_hom_hom_hom,
          pullbackTransitionAlgIso_hom_module_eq] at hmod
        exact naturality_of_eqToHom_conj (Scheme.Modules.pullback ((X.formalCompletion I).ι n))
          (QuasicoherentAlgebra.pullback_obj_X (Scheme.formalCompletion.toScheme X I (n + 1)) A₂) _
          _ (QuasicoherentAlgebra.pullback_obj_X ((X.formalCompletion I).ι n) _) _ _
          (QuasicoherentAlgebra.pullback_obj_X (Scheme.formalCompletion.toScheme X I n) A₂) _
          _ _ _ _ hmod }
  let β₀ : E₂ ⟶ E₁ := F₀.preimage α
  let β : A₂.obj.X ⟶ A₁.obj.X := β₀.hom
  have hβ (n : ℕ) : (ψ n).hom.hom.hom =
      eqToHom (QuasicoherentAlgebra.pullback_obj_X (Scheme.formalCompletion.toScheme X I n) A₂) ≫
        (Scheme.Modules.pullback (Scheme.formalCompletion.toScheme X I n)).map β ≫
        eqToHom
          (QuasicoherentAlgebra.pullback_obj_X (Scheme.formalCompletion.toScheme X I n) A₁).symm :=
    eq_eqToHom_conj_of_eq _ _ _ _ (congrArg (fun k ↦ k.app n) (F₀.map_preimage α))
  -- Step 5: descend `IsMonHom` from all thickenings to `X` using `F₀.Faithful`.
  have hone : η[A₂.obj.X] ≫ β = η[A₁.obj.X] := by
    let Uflf : FiniteLocallyFreeSheaf X :=
      ⟨𝟙_ X.Modules, (Scheme.Modules.isMonoidal_isFiniteLocallyFree X).prop_unit⟩
    let m₁ : Uflf ⟶ E₁ := ObjectProperty.homMk (η[A₂.obj.X] ≫ β)
    let m₂ : Uflf ⟶ E₁ := ObjectProperty.homMk η[A₁.obj.X]
    suffices m₁ = m₂ from congrArg (·.hom) this
    apply F₀.map_injective
    refine AdicThickeningSystem.CoherentFormalModule.hom_ext fun n ↦ ?_
    let iₙ := Scheme.formalCompletion.toScheme X I n
    have h₁ :
        η[((QuasicoherentAlgebra.pullback iₙ).obj A₂).obj.X] ≫
            eqToHom (QuasicoherentAlgebra.pullback_obj_X iₙ A₂) ≫
            (Scheme.Modules.pullback iₙ).map β ≫
            eqToHom (QuasicoherentAlgebra.pullback_obj_X iₙ A₁).symm =
          η[((QuasicoherentAlgebra.pullback iₙ).obj A₁).obj.X] := by
      have h := (ψ n).hom.hom.isMonHom_hom.one_hom
      simp only [hβ n] at h
      exact h
    rw [QuasicoherentAlgebra.pullback_obj_one iₙ A₂,
      QuasicoherentAlgebra.pullback_obj_one iₙ A₁] at h₁
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp] at h₁
    rw [cancel_epi, ← Category.assoc, cancel_mono] at h₁
    dsimp only [F₀, Functor.comp_map, Scheme.formalCompletion.completionFunctor_map_app, m₁, m₂,
      ObjectProperty.homMk_hom]
    exact (Functor.map_comp _ _ _).trans h₁
  have hmul : μ[A₂.obj.X] ≫ β = (β ⊗ₘ β) ≫ μ[A₁.obj.X] := by
    let Tflf : FiniteLocallyFreeSheaf X :=
      ⟨A₂.obj.X ⊗ A₂.obj.X,
        (Scheme.Modules.isMonoidal_isFiniteLocallyFree X).prop_tensor _ _ C₂.unop.property.1
          C₂.unop.property.1⟩
    let m₁ : Tflf ⟶ E₁ := ObjectProperty.homMk (μ[A₂.obj.X] ≫ β)
    let m₂ : Tflf ⟶ E₁ := ObjectProperty.homMk ((β ⊗ₘ β) ≫ μ[A₁.obj.X])
    suffices m₁ = m₂ from congrArg (·.hom) this
    apply F₀.map_injective
    refine AdicThickeningSystem.CoherentFormalModule.hom_ext fun n ↦ ?_
    exact pullback_map_mul_eq (Scheme.formalCompletion.toScheme X I n) β (ψ n) (hβ n)
  -- Step 6: assemble the lifted algebra map `b : A₂ ⟶ A₁` and verify its level-zero base change.
  let b : A₂ ⟶ A₁ := ObjectProperty.homMk (CommMon.homMk (@Mon.Hom.mk _ _ _ _ _ β ⟨hone, hmul⟩))
  let f : C₁ ⟶ C₂ := (ObjectProperty.homMk b).op
  refine ⟨(relSpecFiniteEtale X).map f, ?_⟩
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  have hb₀ :
      (QuasicoherentAlgebra.pullback (Scheme.formalCompletion.toScheme X I 0)).map b = ψ 0 := by
    apply ObjectProperty.hom_ext
    apply CommMon.hom_ext
    exact (QuasicoherentAlgebra.pullback_map_hom_hom_hom _ b).trans (hβ 0).symm
  have hmap₀ : (formalRelSpecMap I b).app 0 = a₀ := by
    have hconj := formalRelSpecLevelIso_hom_map_inv I b 0
    rw [hb₀, hψ 0, AdicThickeningSystem.liftOfEtale_app_zero] at hconj
    rwa [cancel_epi, cancel_mono] at hconj
  exact (formalRelSpecZeroIso_inv_map_hom I f).symm.trans <|
    (congrArg (fun x ↦ (formalRelSpecZeroIso I A₁).inv ≫ x ≫ (formalRelSpecZeroIso I A₂).hom)
      hmap₀).trans
      (iso_inv_hom_conj_inv_hom (formalRelSpecZeroIso I A₁) (formalRelSpecZeroIso I A₂)
        φ₀.hom.left)

end FormalSystem

section Transport

/-- Base change of finite étale schemes along a scheme isomorphism is an equivalence. -/
private def pullbackIsoEquiv {Z Z' : Scheme.{u}} (e : Z ≅ Z') :
    FiniteEtaleScheme Z' ≌ FiniteEtaleScheme Z :=
  CategoryTheory.Equivalence.mk (pullback e.hom) (pullback e.inv)
    (pullbackId.symm ≪≫ eqToIso (congrArg pullback e.inv_hom_id.symm) ≪≫
      pullbackComp e.inv e.hom)
    ((pullbackComp e.hom e.inv).symm ≪≫ eqToIso (congrArg pullback e.hom_inv_id) ≪≫ pullbackId)

private lemma faithful_pullback_of_iso {Z Z' X : Scheme.{u}} (e : Z ≅ Z') (f : Z' ⟶ X)
    (g : Z ⟶ X) (he : e.hom ≫ f = g) [(pullback f).Faithful] :
    (pullback g).Faithful := by
  have : (pullback e.hom).IsEquivalence := (pullbackIsoEquiv e).isEquivalence_functor
  exact Functor.Faithful.of_iso (eqToIso (congrArg pullback he.symm) ≪≫ pullbackComp e.hom f).symm

private lemma full_pullback_of_iso {Z Z' X : Scheme.{u}} (e : Z ≅ Z') (f : Z' ⟶ X)
    (g : Z ⟶ X) (he : e.hom ≫ f = g) [(pullback f).Full] :
    (pullback g).Full := by
  have : (pullback e.hom).IsEquivalence := (pullbackIsoEquiv e).isEquivalence_functor
  exact Functor.Full.of_iso (eqToIso (congrArg pullback he.symm) ≪≫ pullbackComp e.hom f).symm

/-- The canonical isomorphism `V(I) ≅ V(I ^ 1)` between the closed subscheme of `I` and the zeroth
level of `X.formalCompletion I`. -/
private def subschemeIsoLevelZero (X : Scheme.{u}) (I : X.IdealSheafData) :
    I.subscheme ≅ (X.formalCompletion I).X 0 where
  hom := Scheme.IdealSheafData.inclusion (pow_one I).le
  inv := Scheme.IdealSheafData.inclusion (pow_one I).ge
  hom_inv_id := (Scheme.IdealSheafData.inclusion_comp _ _).trans
    (Scheme.IdealSheafData.inclusion_id _)
  inv_hom_id := (Scheme.IdealSheafData.inclusion_comp _ _).trans
    (Scheme.IdealSheafData.inclusion_id _)

/-- If the completion functor on finite locally free `𝒪_X`-modules is faithful, then restricting
finite étale schemes over `X` to the closed subscheme `V(I)` is faithful. -/
instance faithful_pullback_subschemeι (X : Scheme.{u}) (I : X.IdealSheafData)
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).Faithful] :
    (pullback I.subschemeι).Faithful := by
  have := faithful_pullback_toScheme_zero I
  exact faithful_pullback_of_iso (subschemeIsoLevelZero X I)
    (Scheme.formalCompletion.toScheme X I 0) I.subschemeι
    (by
      rw [Scheme.formalCompletion.toScheme_def]
      exact Scheme.IdealSheafData.inclusion_subschemeι (pow_one I).le)

/-- If the completion functor on finite locally free `𝒪_X`-modules is fully faithful, then
restricting finite étale schemes over `X` to the closed subscheme `V(I)` is full. -/
instance full_pullback_subschemeι (X : Scheme.{u}) (I : X.IdealSheafData)
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).Full]
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).Faithful] :
    (pullback I.subschemeι).Full := by
  have := full_pullback_toScheme_zero I
  exact full_pullback_of_iso (subschemeIsoLevelZero X I)
    (Scheme.formalCompletion.toScheme X I 0) I.subschemeι
    (by
      rw [Scheme.formalCompletion.toScheme_def]
      exact Scheme.IdealSheafData.inclusion_subschemeι (pow_one I).le)

/-- **Full faithfulness of restriction to a closed subscheme from coherent completion.** When
completion on finite locally free `𝒪_X`-modules along `V(I)` is fully faithful, pulling back finite
étale schemes along `I.subschemeι` is fully faithful. Stacks, Lemma 58.17.1 (0EL8). -/
@[stacks 0EL8]
def fullyFaithfulPullbackSubschemeι (X : Scheme.{u}) (I : X.IdealSheafData)
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).Full]
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).Faithful] :
    (pullback I.subschemeι).FullyFaithful :=
  .ofFullyFaithful _

/-- **Formal completion criterion for finite étale covers (Stacks, Lemma 58.17.1 (0EL8)).** If the
completion functor from finite locally free `𝒪_X`-modules to coherent formal modules on
`X.formalCompletion I` is fully faithful, then restriction of finite étale schemes from `X` to
`V(I)` is full and faithful. -/
@[stacks 0EL8]
theorem fullyFaithful_of_completion_coherent (X : Scheme.{u}) (I : X.IdealSheafData)
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).Full]
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).Faithful] :
    (pullback I.subschemeι).Full ∧ (pullback I.subschemeι).Faithful :=
  ⟨inferInstance, inferInstance⟩

/-- Any closed immersion `i : Z ⟶ X` factors through an isomorphism `Z ≅ V(i.ker)` over `X`. -/
private def closedImmersionIsoSubscheme {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    Z ≅ i.ker.subscheme :=
  @asIso _ _ _ _
    (IsClosedImmersion.lift i.ker.subschemeι i (Scheme.IdealSheafData.ker_subschemeι i.ker).le)
    (IsClosedImmersion.isIso_lift i.ker.subschemeι i (Scheme.IdealSheafData.ker_subschemeι i.ker))

/-- If completion on finite locally free `𝒪_X`-modules along the closed immersion `i : Z ⟶ X` is
faithful, then pulling back finite étale schemes along `i` is faithful. -/
theorem faithful_pullback_of_isClosedImmersion {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i]
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X i.ker).Faithful] :
    (pullback i).Faithful :=
  faithful_pullback_of_iso (closedImmersionIsoSubscheme i) i.ker.subschemeι i
    (IsClosedImmersion.lift_fac _ _ _)

/-- If completion on finite locally free `𝒪_X`-modules along the closed immersion `i : Z ⟶ X` is
fully faithful, then pulling back finite étale schemes along `i` is full. -/
theorem full_pullback_of_isClosedImmersion {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i]
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X i.ker).Full]
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X i.ker).Faithful] :
    (pullback i).Full :=
  full_pullback_of_iso (closedImmersionIsoSubscheme i) i.ker.subschemeι i
    (IsClosedImmersion.lift_fac _ _ _)

/-- **Full faithfulness of restriction along an arbitrary closed immersion `i : Z ⟶ X`** when
completion on finite locally free `𝒪_X`-modules along `i.ker` is fully faithful.
Stacks, Lemma 58.17.1 (0EL8). -/
@[stacks 0EL8]
def fullyFaithfulPullbackOfIsClosedImmersion {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i]
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X i.ker).Full]
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X i.ker).Faithful] :
    (pullback i).FullyFaithful :=
  have := full_pullback_of_isClosedImmersion i
  have := faithful_pullback_of_isClosedImmersion i
  .ofFullyFaithful _

/-- Companion form of `fullyFaithful_of_completion_coherent` for Mathlib's
`(@IsFinite ⊓ @Etale).Over ⊤` presentation of finite étale schemes.
Stacks, Lemma 58.17.1 (0EL8). -/
@[stacks 0EL8]
theorem overPullback_fullyFaithful_of_completion_coherent (X : Scheme.{u}) (I : X.IdealSheafData)
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).Full]
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).Faithful] :
    letI : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).IsStableUnderBaseChange := .inf
    (MorphismProperty.Over.pullback (@IsFinite ⊓ @Etale) ⊤ I.subschemeι).Full ∧
      (MorphismProperty.Over.pullback (@IsFinite ⊓ @Etale) ⊤ I.subschemeι).Faithful := by
  have : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).IsStableUnderBaseChange := .inf
  let G := MorphismProperty.Over.pullback (@IsFinite ⊓ @Etale) ⊤ I.subschemeι
  let e : (equivOver X).inverse ⋙ pullback I.subschemeι ⋙ (equivOver I.subscheme).functor ≅ G :=
    Functor.isoWhiskerLeft (equivOver X).inverse (pullbackCompEquivOver I.subschemeι) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (equivOver X).counitIso G ≪≫
      Functor.leftUnitor G
  exact ⟨Functor.Full.of_iso e, Functor.Faithful.of_iso e⟩

end Transport

end

end TauCeti.FiniteEtaleScheme
