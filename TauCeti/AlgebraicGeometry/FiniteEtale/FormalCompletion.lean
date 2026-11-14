/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicThickeningSystem.CoherentFormalModule.Algebra
public import TauCeti.AlgebraicGeometry.AdicThickeningSystem.Etale
public import TauCeti.AlgebraicGeometry.AdicThickeningSystem.Pullback
public import TauCeti.AlgebraicGeometry.FiniteEtale.MorphismProperty
public import TauCeti.AlgebraicGeometry.FiniteEtale.PuncturedSpectrum
public import TauCeti.AlgebraicGeometry.IdealSheaf.OfIdealTop
public import TauCeti.AlgebraicGeometry.RelativeSpec.BaseChange
public import TauCeti.AlgebraicGeometry.RelativeSpec.Equivalence
public import TauCeti.AlgebraicGeometry.Restrict
public import TauCeti.AlgebraicGeometry.VectorBundle.Pushforward

/-!
# Formal completion and base change of finite étale schemes

Let `X` be a scheme and `I` an ideal sheaf on `X`, with closed subscheme `Z = V(I)` and formal
completion `X/Z = {V(I ^ (n + 1))}_{n ≥ 0}` (`X.formalCompletion I`). Suppose that completion of
finite locally free `𝒪_X`-modules (for instance, completion of finitely presented `𝒪_X`-modules)
along `I` is faithful, respectively fully faithful. Then base change of finite étale schemes from
`X` to `Z` — or along any closed immersion `i : Z' ⟶ X` with `i.ker = I` — is faithful,
respectively fully faithful (Stacks Project, Lemma 58.17.1, Tag 0EL8).

## Mathematical overview

A finite étale morphism `p : Y ⟶ X` is affine, and its structure algebra `p_* 𝒪_Y` is finite
locally free as an `𝒪_X`-module (`Scheme.Hom.isFiniteLocallyFree_pushforwardStructureAlgebra`).
Under the anti-equivalence between `AffineSchemeOver X` and `QuasicoherentAlgebra X`
(`TauCeti.AlgebraicGeometry.relativeSpecEquiv`), morphisms `Y₁ ⟶ Y₂` over `X` correspond to
algebra morphisms `p_{2,*} 𝒪_{Y₂} ⟶ p_{1,*} 𝒪_{Y₁}`:

1. **Faithfulness:** Two morphisms `Y₁ ⟶ Y₂` over `X` that agree over `V(I)` induce morphisms of
   the levelwise pullback adic thickening systems `{V(I ^ (n + 1)) ×_X Y_k}_{n ≥ 0}` over
   `X.formalCompletion I` with the same initial component. Because `Y₂ ⟶ X` is formally unramified,
   `AdicThickeningSystem.hom_ext_of_formallyUnramified` forces them to agree on every infinitesimal
   level `V(I ^ (n + 1))`. Faithfulness of formal completion on the coordinate algebras then yields
   equality on `X` (`QuasicoherentAlgebra.hom_ext_of_formalCompletion_of_prop`).
2. **Fullness:** A morphism on `V(I)` lifts uniquely to a compatible family of morphisms on all
   infinitesimal levels `V(I ^ (n + 1))` by étale infinitesimal lifting
   (`AdicThickeningSystem.liftOfEtale`). Under `relativeSpecBaseChangeIso`, this compatible family
   corresponds to a compatible system of algebra morphisms over `V(I ^ (n + 1))`, which descends to
   a unique algebra morphism on `X` when completion is fully faithful
   (`QuasicoherentAlgebra.existsUnique_hom_of_formalCompletion_of_prop`).

Neither Noetherian nor finite-generation hypotheses on `X` or `I` are needed once faithfulness or
full faithfulness of the completion functor on finite locally free sheaves is given.

## Main declarations

* `TauCeti.AlgebraicGeometry.AffineSchemeOver.hom_ext_of_formalCompletion_of_prop` and
  `TauCeti.AlgebraicGeometry.AffineSchemeOver.existsUnique_hom_of_formalCompletion_of_prop`:
  infinitesimal uniqueness (for a formally unramified target) and algebraization of compatible lifts
  (for an étale target) in `AffineSchemeOver X`.
* `TauCeti.FiniteEtaleScheme.toAffineSchemeOver` and
  `TauCeti.FiniteEtaleScheme.pullbackCompToAffineSchemeOver`: the fully faithful inclusion of finite
  étale schemes into affine schemes over the base and its compatibility with base change.
* `TauCeti.FiniteEtaleScheme.faithful_pullback_of_completion_finiteLocallyFree`,
  `TauCeti.FiniteEtaleScheme.full_pullback_of_completion_finiteLocallyFree`, and
  `TauCeti.FiniteEtaleScheme.fullyFaithfulPullbackOfCompletionFiniteLocallyFree`: Stacks, Lemma
  58.17.1 (Tag 0EL8) assuming faithfulness / full faithfulness on finite locally free sheaves.
* `TauCeti.FiniteEtaleScheme.faithful_pullback_of_completion_coherent`,
  `TauCeti.FiniteEtaleScheme.full_pullback_of_completion_coherent`, and
  `TauCeti.FiniteEtaleScheme.fullyFaithfulPullbackOfCompletionCoherent`: Stacks, Lemma 58.17.1
  (Tag 0EL8) assuming faithfulness / full faithfulness on finitely presented sheaves.
* `TauCeti.IsLocalRing.faithful_restrictPuncturedQuotient_of_completion_finiteLocallyFree` and
  `TauCeti.IsLocalRing.full_restrictPuncturedQuotient_of_completion_finiteLocallyFree` (and their
  coherent counterparts): specialization to restriction of finite étale covers from the punctured
  spectrum of a local ring `A` to the punctured spectrum of `A ⧸ I`.

## References

* [The Stacks Project, Tag 0EL8](https://stacks.math.columbia.edu/tag/0EL8) (Lemma 58.17.1).
-/

public section

open CategoryTheory Limits Opposite AlgebraicGeometry

universe u

noncomputable section

namespace TauCeti.AlgebraicGeometry

section RelativeSpecLift

open AdicThickeningSystem Scheme.formalCompletion

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- The adic thickening system `{V(I ^ (n + 1)) ×_X V}_{n ≥ 0}` obtained by pulling an affine
scheme `V` over `X` back along `X.formalCompletion I`. -/
private abbrev thickeningOfAffineOver (V : AffineSchemeOver X) : AdicThickeningSystem.{u} :=
  AdicThickeningSystem.pullback (toOfScheme X I) (AdicThickeningSystem.ofScheme.map V.hom)

/-- The projection `{V(I ^ (n + 1)) ×_X V}_{n ≥ 0} ⟶ X.formalCompletion I` to the base thickening
system. -/
private def thickeningProj (V : AffineSchemeOver X) :
    thickeningOfAffineOver I V ⟶ X.formalCompletion I :=
  AdicThickeningSystem.pullback.fst (toOfScheme X I) (AdicThickeningSystem.ofScheme.map V.hom)

@[simp]
private lemma thickeningProj_app (V : AffineSchemeOver X) (n : ℕ) :
    (thickeningProj I V).app n = Limits.pullback.fst (toScheme X I n) V.hom :=
  AdicThickeningSystem.pullback.fst_app _ _ n

/-- Functoriality of `thickeningOfAffineOver I` with respect to morphisms in
`AffineSchemeOver X`. -/
private def mapThickening {V W : AffineSchemeOver X} (u : V ⟶ W) :
    thickeningOfAffineOver I V ⟶ thickeningOfAffineOver I W :=
  AdicThickeningSystem.pullback.lift (thickeningProj I V)
    (AdicThickeningSystem.pullback.snd (toOfScheme X I)
      (AdicThickeningSystem.ofScheme.map V.hom) ≫ AdicThickeningSystem.ofScheme.map u.left)
    ((AdicThickeningSystem.pullback.condition (toOfScheme X I)
      (AdicThickeningSystem.ofScheme.map V.hom)).trans
      ((congrArg (AdicThickeningSystem.pullback.snd (toOfScheme X I)
          (AdicThickeningSystem.ofScheme.map V.hom) ≫ ·)
        ((congrArg AdicThickeningSystem.ofScheme.map (MorphismProperty.Over.w u).symm).trans
          (AdicThickeningSystem.ofScheme.map_comp u.left W.hom))).trans
        (Category.assoc _ _ _).symm))

private lemma mapThickening_proj {V W : AffineSchemeOver X} (u : V ⟶ W) :
    mapThickening I u ≫ thickeningProj I W = thickeningProj I V :=
  AdicThickeningSystem.pullback.lift_fst _ _ _

private lemma mapThickening_app_fst {V W : AffineSchemeOver X} (u : V ⟶ W) (n : ℕ) :
    (mapThickening I u).app n ≫ Limits.pullback.fst (toScheme X I n) W.hom =
      Limits.pullback.fst (toScheme X I n) V.hom :=
  (congrArg (· ≫ Limits.pullback.fst (toScheme X I n) W.hom)
    (AdicThickeningSystem.pullback.lift_app _ _ _ n)).trans
    ((Limits.pullback.lift_fst _ _ _).trans (thickeningProj_app I V n))

private lemma mapThickening_app_snd {V W : AffineSchemeOver X} (u : V ⟶ W) (n : ℕ) :
    (mapThickening I u).app n ≫ Limits.pullback.snd (toScheme X I n) W.hom =
      Limits.pullback.snd (toScheme X I n) V.hom ≫ u.left :=
  (congrArg (· ≫ Limits.pullback.snd (toScheme X I n) W.hom)
    (AdicThickeningSystem.pullback.lift_app _ _ _ n)).trans
    ((Limits.pullback.lift_snd _ _ _).trans
      ((AdicThickeningSystem.comp_app _ _ n).trans
        (congrArg (· ≫ u.left) (AdicThickeningSystem.pullback.snd_app _ _ n))))

/-- At each level `n`, `mapThickening I u` agrees with `(baseChangeAffineSchemeOver _).map u` up to
swapping the fibre-product factors via `Limits.pullbackSymmetry`. -/
private lemma pullbackSymmetry_hom_mapThickening_app {V W : AffineSchemeOver X} (u : V ⟶ W)
    (n : ℕ) :
    (Limits.pullbackSymmetry V.hom (toScheme X I n)).hom ≫ (mapThickening I u).app n =
      ((baseChangeAffineSchemeOver (toScheme X I n)).map u).left ≫
        (Limits.pullbackSymmetry W.hom (toScheme X I n)).hom := by
  let symV := (Limits.pullbackSymmetry V.hom (toScheme X I n)).hom
  let symW := (Limits.pullbackSymmetry W.hom (toScheme X I n)).hom
  let bu := ((baseChangeAffineSchemeOver (toScheme X I n)).map u).left
  apply Limits.pullback.hom_ext
  · exact (Category.assoc symV _ _).trans
      ((congrArg (symV ≫ ·) (mapThickening_app_fst I u n)).trans
        ((Limits.pullbackSymmetry_hom_comp_fst V.hom (toScheme X I n)).trans
          ((baseChangeAffineSchemeOver_map_left_snd (toScheme X I n) u).symm.trans
            ((congrArg (bu ≫ ·)
              (Limits.pullbackSymmetry_hom_comp_fst W.hom (toScheme X I n)).symm).trans
              (Category.assoc bu symW _).symm))))
  · exact (Category.assoc symV _ _).trans
      ((congrArg (symV ≫ ·) (mapThickening_app_snd I u n)).trans
        ((Category.assoc symV _ u.left).symm.trans
          ((congrArg (· ≫ u.left)
            (Limits.pullbackSymmetry_hom_comp_snd V.hom (toScheme X I n))).trans
            ((baseChangeAffineSchemeOver_map_left_fst (toScheme X I n) u).symm.trans
              ((congrArg (bu ≫ ·)
                (Limits.pullbackSymmetry_hom_comp_snd W.hom (toScheme X I n)).symm).trans
                (Category.assoc bu symW _).symm)))))

private lemma relativeSpecPullbackFst_congr {Y : Scheme.{u}} {f g : Y ⟶ X} (h : f = g)
    (C : QuasicoherentAlgebra X) :
    CommMon.relativeSpecMap
        (eqToHom (congrArg (fun k ↦ (QuasicoherentAlgebra.pullback k).obj C) h)).hom ≫
      relativeSpecPullbackFst C f =
    relativeSpecPullbackFst C g := by
  subst h
  simp

/-- Levelwise identification of `Spec_{X_n} (C|_{X_n})` with `(thickeningOfAffineOver I _).X n`. -/
private def relativeSpecLevelIso (C : QuasicoherentAlgebra X) (n : ℕ) :
    ((QuasicoherentAlgebra.pullback (toScheme X I n)).obj C).obj.relativeSpec ≅
      (thickeningOfAffineOver I ((relativeSpec X).obj (op C))).X n :=
  ((MorphismProperty.Over.forget (@IsAffineHom) ⊤ _ ⋙ Over.forget _).mapIso
    (relativeSpecPullbackIso C (toScheme X I n))) ≪≫
    Limits.pullbackSymmetry C.obj.relativeSpecToBase (toScheme X I n)

private lemma relativeSpecLevelIso_hom_fst (C : QuasicoherentAlgebra X) (n : ℕ) :
    (relativeSpecLevelIso I C n).hom ≫
        Limits.pullback.fst (toScheme X I n) C.obj.relativeSpecToBase =
      ((QuasicoherentAlgebra.pullback (toScheme X I n)).obj C).obj.relativeSpecToBase :=
  (Category.assoc _ _ _).trans
    ((congrArg (_ ≫ ·)
      (Limits.pullbackSymmetry_hom_comp_fst C.obj.relativeSpecToBase (toScheme X I n))).trans
      (relativeSpecPullbackIso_hom_left_snd C (toScheme X I n)))

private lemma relativeSpecLevelIso_hom_snd (C : QuasicoherentAlgebra X) (n : ℕ) :
    (relativeSpecLevelIso I C n).hom ≫
        Limits.pullback.snd (toScheme X I n) C.obj.relativeSpecToBase =
      relativeSpecPullbackFst C (toScheme X I n) :=
  (Category.assoc _ _ _).trans
    ((congrArg (_ ≫ ·)
      (Limits.pullbackSymmetry_hom_comp_snd C.obj.relativeSpecToBase (toScheme X I n))).trans
      (relativeSpecPullbackIso_hom_left_fst C (toScheme X I n)))

/-- The canonical transition morphism `Spec_{X_n} (C|_{X_n}) ⟶ Spec_{X_{n+1}} (C|_{X_{n+1}})`
induced by `QuasicoherentAlgebra.formalCompletionTransitionIso`. -/
private def relativeSpecTransition (C : QuasicoherentAlgebra X) (n : ℕ) :
    ((QuasicoherentAlgebra.pullback (toScheme X I n)).obj C).obj.relativeSpec ⟶
      ((QuasicoherentAlgebra.pullback (toScheme X I (n + 1))).obj C).obj.relativeSpec :=
  CommMon.relativeSpecMap (QuasicoherentAlgebra.formalCompletionTransitionIso X I C n).hom.hom ≫
    relativeSpecPullbackFst ((QuasicoherentAlgebra.pullback (toScheme X I (n + 1))).obj C)
      ((X.formalCompletion I).ι n)

private lemma relativeSpecTransition_comp_levelIso_hom_fst (C : QuasicoherentAlgebra X) (n : ℕ) :
    (relativeSpecTransition I C n ≫ (relativeSpecLevelIso I C (n + 1)).hom) ≫
        Limits.pullback.fst (toScheme X I (n + 1)) C.obj.relativeSpecToBase =
      ((relativeSpecLevelIso I C n).hom ≫
          (thickeningOfAffineOver I ((relativeSpec X).obj (op C))).ι n) ≫
        Limits.pullback.fst (toScheme X I (n + 1)) C.obj.relativeSpecToBase := by
  let j := (X.formalCompletion I).ι n
  let f₁ := toScheme X I (n + 1)
  let f₀ := toScheme X I n
  let p := C.obj.relativeSpecToBase
  have hLHS : (relativeSpecTransition I C n ≫ (relativeSpecLevelIso I C (n + 1)).hom) ≫
      Limits.pullback.fst f₁ p =
      ((QuasicoherentAlgebra.pullback f₀).obj C).obj.relativeSpecToBase ≫ j :=
    (Category.assoc _ _ _).trans
      ((congrArg (relativeSpecTransition I C n ≫ ·)
        (relativeSpecLevelIso_hom_fst I C (n + 1))).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (_ ≫ ·) (relativeSpecPullbackFst_relativeSpecToBase
            ((QuasicoherentAlgebra.pullback f₁).obj C) j)).trans
            (CommMon.relativeSpecMap_relativeSpecToBase_assoc
              (QuasicoherentAlgebra.formalCompletionTransitionIso X I C n).hom.hom j))))
  have hRHS : ((relativeSpecLevelIso I C n).hom ≫
      (thickeningOfAffineOver I ((relativeSpec X).obj (op C))).ι n) ≫
      Limits.pullback.fst f₁ p =
      ((QuasicoherentAlgebra.pullback f₀).obj C).obj.relativeSpecToBase ≫ j :=
    (Category.assoc _ _ _).trans
      ((congrArg ((relativeSpecLevelIso I C n).hom ≫ ·)
        (Limits.pullback.lift_fst _ _ _)).trans
        ((Category.assoc _ _ _).symm.trans
          (congrArg (· ≫ j) (relativeSpecLevelIso_hom_fst I C n))))
  exact hLHS.trans hRHS.symm

private lemma relativeSpecTransition_comp_levelIso_hom_snd (C : QuasicoherentAlgebra X) (n : ℕ) :
    (relativeSpecTransition I C n ≫ (relativeSpecLevelIso I C (n + 1)).hom) ≫
        Limits.pullback.snd (toScheme X I (n + 1)) C.obj.relativeSpecToBase =
      ((relativeSpecLevelIso I C n).hom ≫
          (thickeningOfAffineOver I ((relativeSpec X).obj (op C))).ι n) ≫
        Limits.pullback.snd (toScheme X I (n + 1)) C.obj.relativeSpecToBase := by
  let j := (X.formalCompletion I).ι n
  let f₁ := toScheme X I (n + 1)
  let f₀ := toScheme X I n
  let p := C.obj.relativeSpecToBase
  let mEq := CommMon.relativeSpecMap
    (eqToHom (congrArg (fun k ↦ (QuasicoherentAlgebra.pullback k).obj C) (ι_toScheme X I n))).hom
  let mComp := CommMon.relativeSpecMap
    ((QuasicoherentAlgebra.pullbackComp j f₁).hom.app C).hom
  have hmap : CommMon.relativeSpecMap
      (QuasicoherentAlgebra.formalCompletionTransitionIso X I C n).hom.hom = mEq ≫ mComp :=
    (congrArg CommMon.relativeSpecMap
      (QuasicoherentAlgebra.formalCompletionTransitionIso_hom_hom X I C n)).trans
      (CommMon.relativeSpecMap_comp _ _)
  have hLHS : (relativeSpecTransition I C n ≫ (relativeSpecLevelIso I C (n + 1)).hom) ≫
      Limits.pullback.snd f₁ p = relativeSpecPullbackFst C f₀ :=
    (Category.assoc _ _ _).trans
      ((congrArg (relativeSpecTransition I C n ≫ ·)
        (relativeSpecLevelIso_hom_snd I C (n + 1))).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (· ≫ (relativeSpecPullbackFst _ j ≫ relativeSpecPullbackFst C f₁))
            hmap).trans
            ((Category.assoc mEq mComp _).trans
              ((congrArg (mEq ≫ ·) (relativeSpecPullbackFst_comp C f₁ j).symm).trans
                (relativeSpecPullbackFst_congr (ι_toScheme X I n) C))))))
  have hRHS : ((relativeSpecLevelIso I C n).hom ≫
      (thickeningOfAffineOver I ((relativeSpec X).obj (op C))).ι n) ≫
      Limits.pullback.snd f₁ p = relativeSpecPullbackFst C f₀ :=
    (Category.assoc _ _ _).trans
      ((congrArg ((relativeSpecLevelIso I C n).hom ≫ ·)
        (Limits.pullback.lift_snd _ _ _)).trans
        ((congrArg ((relativeSpecLevelIso I C n).hom ≫ ·) (Category.comp_id _)).trans
          (relativeSpecLevelIso_hom_snd I C n)))
  exact hLHS.trans hRHS.symm

/-- Under `relativeSpecLevelIso`, `relativeSpecTransition` corresponds to the transition thickening
`ι n` of `thickeningOfAffineOver`. -/
private lemma relativeSpecTransition_comp_levelIso_hom (C : QuasicoherentAlgebra X) (n : ℕ) :
    relativeSpecTransition I C n ≫ (relativeSpecLevelIso I C (n + 1)).hom =
      (relativeSpecLevelIso I C n).hom ≫
        (thickeningOfAffineOver I ((relativeSpec X).obj (op C))).ι n :=
  Limits.pullback.hom_ext
    (relativeSpecTransition_comp_levelIso_hom_fst I C n)
    (relativeSpecTransition_comp_levelIso_hom_snd I C n)

private lemma formallyUnramified_of_isIso_comp {Z₁ Z₂ S : Scheme.{u}} (e : Z₁ ⟶ Z₂) [IsIso e]
    (p : Z₂ ⟶ S) (q : Z₁ ⟶ S) (h : e ≫ p = q) [FormallyUnramified p] : FormallyUnramified q := by
  subst h
  exact (inferInstance : MorphismProperty.IsStableUnderComposition
    (@FormallyUnramified : MorphismProperty Scheme.{u})).comp_mem e p inferInstance ‹_›

private lemma etale_of_isIso_comp {Z₁ Z₂ S : Scheme.{u}} (e : Z₁ ⟶ Z₂) [IsIso e]
    (p : Z₂ ⟶ S) (q : Z₁ ⟶ S) (h : e ≫ p = q) [Etale p] : Etale q := by
  subst h
  infer_instance

/-- Faithfulness of base change to `V(I)` for relative spectra of algebras in `P` when the target
is formally unramified and `propCompletionFunctor I hP` is faithful. -/
private theorem relativeSpec_hom_ext_of_formalCompletion_of_prop {P : ObjectProperty X.Modules}
    (hP : P ≤ _root_.SheafOfModules.isFinitePresentation X.ringCatSheaf)
    [(QuasicoherentAlgebra.propCompletionFunctor I hP).Faithful]
    {A B : QuasicoherentAlgebra X} (hA : P A.obj.X) (hB : P B.obj.X)
    [FormallyUnramified B.obj.relativeSpecToBase] {Ψ₁ Ψ₂ : B ⟶ A}
    (h₀ : (baseChangeAffineSchemeOver (toScheme X I 0)).map ((relativeSpec X).map Ψ₁.op) =
      (baseChangeAffineSchemeOver (toScheme X I 0)).map ((relativeSpec X).map Ψ₂.op)) :
    Ψ₁ = Ψ₂ := by
  let u₁ := (relativeSpec X).map Ψ₁.op
  let u₂ := (relativeSpec X).map Ψ₂.op
  have : FormallyUnramified ((relativeSpec X).obj (op B)).hom :=
    ‹FormallyUnramified B.obj.relativeSpecToBase›
  have : ∀ n, FormallyUnramified ((thickeningProj I ((relativeSpec X).obj (op B))).app n) := by
    intro n
    rw [thickeningProj_app]
    exact (inferInstance : MorphismProperty.IsStableUnderBaseChange
      (@FormallyUnramified : MorphismProperty Scheme.{u})).of_isPullback
      (IsPullback.of_hasPullback (toScheme X I n) ((relativeSpec X).obj (op B)).hom).flip ‹_›
  have ha₀ : (mapThickening I u₁).app 0 = (mapThickening I u₂).app 0 :=
    (Iso.cancel_iso_hom_left (Limits.pullbackSymmetry _ _) _ _).mp
      ((pullbackSymmetry_hom_mapThickening_app I u₁ 0).trans
        ((congrArg (· ≫ _) (congrArg (fun g ↦ g.left) h₀)).trans
          (pullbackSymmetry_hom_mapThickening_app I u₂ 0).symm))
  have ha : mapThickening I u₁ = mapThickening I u₂ :=
    AdicThickeningSystem.hom_ext_of_formallyUnramified
      (thickeningProj I ((relativeSpec X).obj (op B)))
      ((mapThickening_proj I u₁).trans (mapThickening_proj I u₂).symm) ha₀
  refine QuasicoherentAlgebra.hom_ext_of_formalCompletion_of_prop (I := I) hP hA hB fun n ↦ ?_
  have hn : (baseChangeAffineSchemeOver (toScheme X I n)).map u₁ =
      (baseChangeAffineSchemeOver (toScheme X I n)).map u₂ := by
    apply MorphismProperty.Over.Hom.ext
    exact (Iso.cancel_iso_hom_right _ _ (Limits.pullbackSymmetry _ _)).mp
      ((pullbackSymmetry_hom_mapThickening_app I u₁ n).symm.trans
        ((congrArg (_ ≫ ·) (congrArg (fun g ↦ g.app n) ha)).trans
          (pullbackSymmetry_hom_mapThickening_app I u₂ n)))
  have hnat₁ := (relativeSpecBaseChangeIso (toScheme X I n)).hom.naturality Ψ₁.op
  have hnat₂ := (relativeSpecBaseChangeIso (toScheme X I n)).hom.naturality Ψ₂.op
  have hmap : (relativeSpec ((X.formalCompletion I).X n)).map
      ((QuasicoherentAlgebra.pullback (toScheme X I n)).map Ψ₁).op =
    (relativeSpec ((X.formalCompletion I).X n)).map
      ((QuasicoherentAlgebra.pullback (toScheme X I n)).map Ψ₂).op :=
    (Iso.cancel_iso_hom_right _ _ ((relativeSpecBaseChangeIso (toScheme X I n)).app (op B))).mp
      (hnat₁.trans ((congrArg (_ ≫ ·) hn).trans hnat₂.symm))
  exact Quiver.Hom.op_inj ((relativeSpec ((X.formalCompletion I).X n)).map_injective hmap)

/-- Compatibility of the levelwise algebra morphisms induced by a morphism of adic thickening
systems between relative spectra. -/
private lemma compatible_of_thickeningHom {A B : QuasicoherentAlgebra X}
    (a : thickeningOfAffineOver I ((relativeSpec X).obj (op A)) ⟶
      thickeningOfAffineOver I ((relativeSpec X).obj (op B)))
    (ψ : ∀ n, (QuasicoherentAlgebra.pullback (toScheme X I n)).obj B ⟶
      (QuasicoherentAlgebra.pullback (toScheme X I n)).obj A)
    (hψ : ∀ n, CommMon.relativeSpecMap (ψ n).hom =
      (relativeSpecLevelIso I A n).hom ≫ a.app n ≫ (relativeSpecLevelIso I B n).inv) (n : ℕ) :
    (QuasicoherentAlgebra.pullback ((X.formalCompletion I).ι n)).map (ψ (n + 1)) ≫
        (QuasicoherentAlgebra.formalCompletionTransitionIso X I A n).hom =
      (QuasicoherentAlgebra.formalCompletionTransitionIso X I B n).hom ≫ ψ n := by
  apply Quiver.Hom.op_inj
  apply (relativeSpec ((X.formalCompletion I).X n)).map_injective
  rw [op_comp, op_comp, (relativeSpec _).map_comp, (relativeSpec _).map_comp]
  apply MorphismProperty.Over.Hom.ext
  have hL : (((relativeSpec ((X.formalCompletion I).X n)).map
        (QuasicoherentAlgebra.formalCompletionTransitionIso X I A n).hom.op) ≫
      ((relativeSpec ((X.formalCompletion I).X n)).map
        ((QuasicoherentAlgebra.pullback ((X.formalCompletion I).ι n)).map (ψ (n + 1))).op)).left =
    CommMon.relativeSpecMap
        (QuasicoherentAlgebra.formalCompletionTransitionIso X I A n).hom.hom ≫
      CommMon.relativeSpecMap
        ((QuasicoherentAlgebra.pullback ((X.formalCompletion I).ι n)).map (ψ (n + 1))).hom := rfl
  have hR : (((relativeSpec ((X.formalCompletion I).X n)).map (ψ n).op) ≫
      ((relativeSpec ((X.formalCompletion I).X n)).map
        (QuasicoherentAlgebra.formalCompletionTransitionIso X I B n).hom.op)).left =
    CommMon.relativeSpecMap (ψ n).hom ≫
      CommMon.relativeSpecMap
        (QuasicoherentAlgebra.formalCompletionTransitionIso X I B n).hom.hom := rfl
  refine hL.trans (Eq.trans ?_ hR.symm)
  apply (isPullback_relativeSpecPullbackFst
    ((QuasicoherentAlgebra.pullback (toScheme X I (n + 1))).obj B)
    ((X.formalCompletion I).ι n)).hom_ext
  · have hB : (relativeSpecLevelIso I B n).inv ≫ relativeSpecTransition I B n =
        (thickeningOfAffineOver I ((relativeSpec X).obj (op B))).ι n ≫
          (relativeSpecLevelIso I B (n + 1)).inv := by
      rw [Iso.inv_comp_eq, ← Category.assoc, ← relativeSpecTransition_comp_levelIso_hom,
        Category.assoc, Iso.hom_inv_id, Category.comp_id]
    calc _ = CommMon.relativeSpecMap
              (QuasicoherentAlgebra.formalCompletionTransitionIso X I A n).hom.hom ≫
            (CommMon.relativeSpecMap
              ((QuasicoherentAlgebra.pullback ((X.formalCompletion I).ι n)).map (ψ (n + 1))).hom ≫
            relativeSpecPullbackFst ((QuasicoherentAlgebra.pullback (toScheme X I (n + 1))).obj B)
              ((X.formalCompletion I).ι n)) := Category.assoc _ _ _
      _ = relativeSpecTransition I A n ≫ CommMon.relativeSpecMap (ψ (n + 1)).hom := by
          rw [relativeSpecMap_pullback_map_relativeSpecPullbackFst]
          exact (Category.assoc _ _ _).symm
      _ = (relativeSpecLevelIso I A n).hom ≫
            ((thickeningOfAffineOver I ((relativeSpec X).obj (op A))).ι n ≫ a.app (n + 1)) ≫
            (relativeSpecLevelIso I B (n + 1)).inv := by
          rw [hψ (n + 1), ← Category.assoc (relativeSpecTransition I A n),
            relativeSpecTransition_comp_levelIso_hom]
          simp only [Category.assoc]
      _ = (relativeSpecLevelIso I A n).hom ≫ a.app n ≫
            ((relativeSpecLevelIso I B n).inv ≫ relativeSpecTransition I B n) := by
          rw [a.naturality n]
          simp only [Category.assoc, hB]
      _ = CommMon.relativeSpecMap (ψ n).hom ≫ relativeSpecTransition I B n := by
          rw [hψ n]
          simp only [Category.assoc]
      _ = _ := (Category.assoc (CommMon.relativeSpecMap (ψ n).hom) _ _).symm
  · rw [Category.assoc, CommMon.relativeSpecMap_relativeSpecToBase,
      CommMon.relativeSpecMap_relativeSpecToBase, Category.assoc,
      CommMon.relativeSpecMap_relativeSpecToBase, CommMon.relativeSpecMap_relativeSpecToBase]

private lemma pullbackSymmetry_conj_inv_hom_fst {Y₁ Y₂ S : Scheme.{u}}
    (p₁ : Y₁ ⟶ X) (p₂ : Y₂ ⟶ X) (i : S ⟶ X)
    (g : Limits.pullback p₁ i ⟶ Limits.pullback p₂ i)
    (hg : g ≫ Limits.pullback.snd p₂ i = Limits.pullback.snd p₁ i) :
    ((Limits.pullbackSymmetry p₁ i).inv ≫ g ≫ (Limits.pullbackSymmetry p₂ i).hom) ≫
        Limits.pullback.fst i p₂ =
      Limits.pullback.fst i p₁ := by
  simp [hg]

private lemma pullbackSymmetry_conj_hom_inv_snd {Y₁ Y₂ S : Scheme.{u}}
    (p₁ : Y₁ ⟶ X) (p₂ : Y₂ ⟶ X) (i : S ⟶ X)
    (h : Limits.pullback i p₁ ⟶ Limits.pullback i p₂)
    (hh : h ≫ Limits.pullback.fst i p₂ = Limits.pullback.fst i p₁) :
    ((Limits.pullbackSymmetry p₁ i).hom ≫ h ≫ (Limits.pullbackSymmetry p₂ i).inv) ≫
        Limits.pullback.snd p₂ i =
      Limits.pullback.snd p₁ i := by
  simp [hh]

private lemma iso_conj_hom_inv_cancel {C : Type*} [Category* C] {X₁ X₂ Y₁ Y₂ : C}
    (e₁ : X₁ ≅ Y₁) (e₂ : X₂ ≅ Y₂) (g : X₁ ⟶ X₂) :
    e₁.hom ≫ (e₁.inv ≫ g ≫ e₂.hom) ≫ e₂.inv = g := by
  simp

private lemma comp_five_assoc {C : Type*} [Category* C] {Z₁ Z₂ Z₃ Z₄ Z₅ Z₆ : C}
    (u₁ : Z₁ ⟶ Z₂) (u₂ : Z₂ ⟶ Z₃) (u₃ : Z₃ ⟶ Z₄) (u₄ : Z₄ ⟶ Z₅) (u₅ : Z₅ ⟶ Z₆) :
    u₁ ≫ (u₂ ≫ u₃ ≫ u₄) ≫ u₅ = (u₁ ≫ u₂) ≫ u₃ ≫ u₄ ≫ u₅ := by
  simp only [Category.assoc]

private lemma baseChangeAffineSchemeOver_map_relativeSpec_eq {Y : Scheme.{u}} (f : Y ⟶ X)
    {A B : QuasicoherentAlgebra X} {Ψ : B ⟶ A}
    {f₀ : (baseChangeAffineSchemeOver f).obj ((relativeSpec X).obj (op A)) ⟶
      (baseChangeAffineSchemeOver f).obj ((relativeSpec X).obj (op B))}
    (h : (relativeSpec Y).map ((QuasicoherentAlgebra.pullback f).map Ψ).op =
      (relativeSpecPullbackIso A f).hom ≫ f₀ ≫ (relativeSpecPullbackIso B f).inv) :
    (baseChangeAffineSchemeOver f).map ((relativeSpec X).map Ψ.op) = f₀ := by
  let e := relativeSpecBaseChangeIso f
  have hnat := e.hom.naturality Ψ.op
  have heA : e.hom.app (op A) = (relativeSpecPullbackIso A f).hom :=
    (Iso.app_hom e (op A)).symm.trans
      (congrArg Iso.hom (relativeSpecBaseChangeIso_app f (op A)))
  have heB : e.hom.app (op B) = (relativeSpecPullbackIso B f).hom :=
    (Iso.app_hom e (op B)).symm.trans
      (congrArg Iso.hom (relativeSpecBaseChangeIso_app f (op B)))
  refine (Iso.cancel_iso_hom_left (relativeSpecPullbackIso A f) _ _).mp ?_
  calc (relativeSpecPullbackIso A f).hom ≫
          (baseChangeAffineSchemeOver f).map ((relativeSpec X).map Ψ.op)
      _ = e.hom.app (op A) ≫
            (baseChangeAffineSchemeOver f).map ((relativeSpec X).map Ψ.op) :=
          congrArg (· ≫ _) heA.symm
      _ = (relativeSpec Y).map ((QuasicoherentAlgebra.pullback f).map Ψ).op ≫
            e.hom.app (op B) := hnat.symm
      _ = ((relativeSpecPullbackIso A f).hom ≫ f₀ ≫ (relativeSpecPullbackIso B f).inv) ≫
            (relativeSpecPullbackIso B f).hom := congrArg₂ (· ≫ ·) h heB
      _ = (relativeSpecPullbackIso A f).hom ≫ f₀ := by simp

/-- Fullness of base change to `V(I)` for relative spectra of algebras in `P` when the target is
étale and `propCompletionFunctor I hP` is fully faithful. -/
private theorem relativeSpec_exists_hom_of_formalCompletion_of_prop {P : ObjectProperty X.Modules}
    [P.IsMonoidal] (hP : P ≤ _root_.SheafOfModules.isFinitePresentation X.ringCatSheaf)
    [(QuasicoherentAlgebra.propCompletionFunctor I hP).Full]
    [(QuasicoherentAlgebra.propCompletionFunctor I hP).Faithful]
    {A B : QuasicoherentAlgebra X} (hA : P A.obj.X) (hB : P B.obj.X)
    [Etale B.obj.relativeSpecToBase]
    (f₀ : (baseChangeAffineSchemeOver (toScheme X I 0)).obj ((relativeSpec X).obj (op A)) ⟶
      (baseChangeAffineSchemeOver (toScheme X I 0)).obj ((relativeSpec X).obj (op B))) :
    ∃ Ψ : B ⟶ A,
      (baseChangeAffineSchemeOver (toScheme X I 0)).map ((relativeSpec X).map Ψ.op) = f₀ := by
  let VA := (relativeSpec X).obj (op A)
  let VB := (relativeSpec X).obj (op B)
  have : Etale VB.hom := ‹Etale B.obj.relativeSpecToBase›
  have : ∀ n, Etale ((thickeningProj I VB).app n) := by
    intro n
    rw [thickeningProj_app]
    exact (inferInstance : MorphismProperty.IsStableUnderBaseChange
      (@Etale : MorphismProperty Scheme.{u})).of_isPullback
      (IsPullback.of_hasPullback (toScheme X I n) VB.hom).flip ‹_›
  let a₀ : (thickeningOfAffineOver I VA).X 0 ⟶ (thickeningOfAffineOver I VB).X 0 :=
    (Limits.pullbackSymmetry VA.hom (toScheme X I 0)).inv ≫ f₀.left ≫
      (Limits.pullbackSymmetry VB.hom (toScheme X I 0)).hom
  have ha₀ : a₀ ≫ (thickeningProj I VB).app 0 = (thickeningProj I VA).app 0 :=
    (congrArg (a₀ ≫ ·) (thickeningProj_app I VB 0)).trans
      ((pullbackSymmetry_conj_inv_hom_fst VA.hom VB.hom (toScheme X I 0) f₀.left
        (MorphismProperty.Over.w f₀)).trans (thickeningProj_app I VA 0).symm)
  let a := AdicThickeningSystem.liftOfEtale (thickeningProj I VA) (thickeningProj I VB) a₀ ha₀
  let bOver (n : ℕ) : (baseChangeAffineSchemeOver (toScheme X I n)).obj VA ⟶
      (baseChangeAffineSchemeOver (toScheme X I n)).obj VB :=
    MorphismProperty.Over.homMk
      ((Limits.pullbackSymmetry VA.hom (toScheme X I n)).hom ≫ a.app n ≫
        (Limits.pullbackSymmetry VB.hom (toScheme X I n)).inv)
      (pullbackSymmetry_conj_hom_inv_snd VA.hom VB.hom (toScheme X I n) (a.app n)
        ((congrArg (a.app n ≫ ·) (thickeningProj_app I VB n).symm).trans
          ((AdicThickeningSystem.liftOfEtale_app_comp (thickeningProj I VA)
            (thickeningProj I VB) a₀ ha₀ n).trans (thickeningProj_app I VA n))))
  have hb₀ : bOver 0 = f₀ :=
    MorphismProperty.Over.Hom.ext
      ((congrArg ((Limits.pullbackSymmetry VA.hom (toScheme X I 0)).hom ≫ ·)
        (congrArg (· ≫ (Limits.pullbackSymmetry VB.hom (toScheme X I 0)).inv)
          (AdicThickeningSystem.liftOfEtale_app_zero (thickeningProj I VA)
            (thickeningProj I VB) a₀ ha₀))).trans
        (iso_conj_hom_inv_cancel (Limits.pullbackSymmetry VA.hom (toScheme X I 0))
          (Limits.pullbackSymmetry VB.hom (toScheme X I 0)) f₀.left))
  let gOver (n : ℕ) := (relativeSpecPullbackIso A (toScheme X I n)).hom ≫ bOver n ≫
    (relativeSpecPullbackIso B (toScheme X I n)).inv
  let ψ (n : ℕ) : (QuasicoherentAlgebra.pullback (toScheme X I n)).obj B ⟶
      (QuasicoherentAlgebra.pullback (toScheme X I n)).obj A :=
    ((relativeSpec ((X.formalCompletion I).X n)).preimage (gOver n)).unop
  have hψ (n : ℕ) : CommMon.relativeSpecMap (ψ n).hom =
      (relativeSpecLevelIso I A n).hom ≫ a.app n ≫ (relativeSpecLevelIso I B n).inv :=
    (congrArg (fun g ↦ g.left)
      ((relativeSpec ((X.formalCompletion I).X n)).map_preimage (gOver n))).trans
      (comp_five_assoc _ _ _ _ _)
  obtain ⟨Ψ, hΨ, -⟩ := QuasicoherentAlgebra.existsUnique_hom_of_formalCompletion_of_prop hP hA hB ψ
    (compatible_of_thickeningHom I a ψ hψ)
  exact ⟨Ψ, baseChangeAffineSchemeOver_map_relativeSpec_eq (toScheme X I 0)
    ((congrArg (fun g ↦ (relativeSpec ((X.formalCompletion I).X 0)).map g.op) (hΨ 0)).trans
      (((relativeSpec ((X.formalCompletion I).X 0)).map_preimage (gOver 0)).trans
        (congrArg ((relativeSpecPullbackIso A (toScheme X I 0)).hom ≫ ·)
          (congrArg (· ≫ (relativeSpecPullbackIso B (toScheme X I 0)).inv) hb₀))))⟩

namespace AffineSchemeOver

/-- **Formal uniqueness for affine schemes into a formally unramified target.** Let `P` be a
property of finitely presented `𝒪_X`-modules on which `propCompletionFunctor I hP` is faithful.
If `V, W : AffineSchemeOver X` have coordinate algebras in `P` and `W ⟶ X` is formally unramified,
any two morphisms `V ⟶ W` over `X` with the same base change to `V(I)` are equal. -/
theorem hom_ext_of_formalCompletion_of_prop {P : ObjectProperty X.Modules}
    (hP : P ≤ _root_.SheafOfModules.isFinitePresentation X.ringCatSheaf)
    [(QuasicoherentAlgebra.propCompletionFunctor I hP).Faithful]
    {V W : AffineSchemeOver X}
    (hV : P ((affineFunctions X).obj V).unop.obj.X)
    (hW : P ((affineFunctions X).obj W).unop.obj.X)
    [FormallyUnramified W.hom] {u₁ u₂ : V ⟶ W}
    (h₀ : (baseChangeAffineSchemeOver (toScheme X I 0)).map u₁ =
      (baseChangeAffineSchemeOver (toScheme X I 0)).map u₂) :
    u₁ = u₂ := by
  let AV := ((affineFunctions X).obj V).unop
  let AW := ((affineFunctions X).obj W).unop
  let εV := (relativeSpecCounit X).app V
  let εW := (relativeSpecCounit X).app W
  have : IsIso εW.hom.left :=
    ((MorphismProperty.Over.forget (@IsAffineHom) ⊤ X ⋙ Over.forget X).mapIso εW).isIso_hom
  have : FormallyUnramified AW.obj.relativeSpecToBase :=
    formallyUnramified_of_isIso_comp εW.hom.left W.hom AW.obj.relativeSpecToBase
      (MorphismProperty.Over.w εW.hom)
  let Ψ₁ : AW ⟶ AV := ((relativeSpec X).preimage (εV.hom ≫ u₁ ≫ εW.inv)).unop
  let Ψ₂ : AW ⟶ AV := ((relativeSpec X).preimage (εV.hom ≫ u₂ ≫ εW.inv)).unop
  have hΨ : Ψ₁ = Ψ₂ := by
    apply relativeSpec_hom_ext_of_formalCompletion_of_prop I hP hV hW
    simp only [Ψ₁, Ψ₂, Quiver.Hom.op_unop, (relativeSpec X).map_preimage, Functor.map_comp, h₀]
  have hconj : εV.hom ≫ u₁ ≫ εW.inv = εV.hom ≫ u₂ ≫ εW.inv := by
    calc εV.hom ≫ u₁ ≫ εW.inv = (relativeSpec X).map Ψ₁.op :=
          ((relativeSpec X).map_preimage _).symm
      _ = (relativeSpec X).map Ψ₂.op := congrArg (fun g ↦ (relativeSpec X).map g.op) hΨ
      _ = εV.hom ≫ u₂ ≫ εW.inv := (relativeSpec X).map_preimage _
  exact (Iso.cancel_iso_inv_right _ _ εW).mp ((Iso.cancel_iso_hom_left εV _ _).mp hconj)

/-- **Formal lifting and descent for affine schemes into an étale target.** Let `P` be a monoidal
property of finitely presented `𝒪_X`-modules on which `propCompletionFunctor I hP` is fully
faithful. If `V, W : AffineSchemeOver X` have coordinate algebras in `P` and `W ⟶ X` is étale,
every morphism `V ×_X V(I) ⟶ W ×_X V(I)` over `V(I)` lifts to a unique morphism `V ⟶ W` over `X`. -/
theorem existsUnique_hom_of_formalCompletion_of_prop {P : ObjectProperty X.Modules} [P.IsMonoidal]
    (hP : P ≤ _root_.SheafOfModules.isFinitePresentation X.ringCatSheaf)
    [(QuasicoherentAlgebra.propCompletionFunctor I hP).Full]
    [(QuasicoherentAlgebra.propCompletionFunctor I hP).Faithful]
    {V W : AffineSchemeOver X}
    (hV : P ((affineFunctions X).obj V).unop.obj.X)
    (hW : P ((affineFunctions X).obj W).unop.obj.X)
    [Etale W.hom]
    (f₀ : (baseChangeAffineSchemeOver (toScheme X I 0)).obj V ⟶
      (baseChangeAffineSchemeOver (toScheme X I 0)).obj W) :
    ∃! u : V ⟶ W, (baseChangeAffineSchemeOver (toScheme X I 0)).map u = f₀ := by
  let AW := ((affineFunctions X).obj W).unop
  let εV := (relativeSpecCounit X).app V
  let εW := (relativeSpecCounit X).app W
  let F₀ := baseChangeAffineSchemeOver (toScheme X I 0)
  have : IsIso εW.hom.left :=
    ((MorphismProperty.Over.forget (@IsAffineHom) ⊤ X ⋙ Over.forget X).mapIso εW).isIso_hom
  have : Etale AW.obj.relativeSpecToBase :=
    etale_of_isIso_comp εW.hom.left W.hom AW.obj.relativeSpecToBase
      (MorphismProperty.Over.w εW.hom)
  obtain ⟨Ψ, hΨ⟩ := relativeSpec_exists_hom_of_formalCompletion_of_prop I hP hV hW
    (F₀.map εV.hom ≫ f₀ ≫ F₀.map εW.inv)
  let u := εV.inv ≫ (relativeSpec X).map Ψ.op ≫ εW.hom
  have hu : F₀.map u = f₀ := by
    calc F₀.map u
        _ = F₀.map εV.inv ≫ F₀.map ((relativeSpec X).map Ψ.op) ≫ F₀.map εW.hom := by
            simp [u, Functor.map_comp]
        _ = (F₀.map εV.inv ≫ F₀.map εV.hom) ≫ f₀ ≫ (F₀.map εW.inv ≫ F₀.map εW.hom) := by
            rw [hΨ]
            simp only [Category.assoc]
        _ = f₀ := by
            rw [← F₀.map_comp, ← F₀.map_comp, Iso.inv_hom_id, Iso.inv_hom_id, F₀.map_id,
              F₀.map_id, Category.comp_id, Category.id_comp]
  exact ⟨u, hu, fun u' hu' ↦ hom_ext_of_formalCompletion_of_prop I hP hV hW (hu'.trans hu.symm)⟩

end AffineSchemeOver

end RelativeSpecLift

end TauCeti.AlgebraicGeometry

namespace TauCeti.FiniteEtaleScheme

open TauCeti.AlgebraicGeometry Scheme.formalCompletion

section ToAffineSchemeOver

variable (S : Scheme.{u})

/-- Every finite étale `S`-scheme is affine over `S` because finite morphisms are affine. -/
-- `@[expose]` is forced by dependent typing of `((toAffineSchemeOver S).obj Y).hom`: without
-- `(toAffineSchemeOver S).obj Y` reducing to `MorphismProperty.Comma.lift`, its codomain is
-- `(Functor.fromPUnit S).obj _.right` rather than `S`, matching `FiniteEtaleScheme.toEtale`.
@[expose]
def toAffineSchemeOver : FiniteEtaleScheme S ⥤ AffineSchemeOver S :=
  MorphismProperty.Comma.lift (finiteEtaleSchemeProperty S).ι
    (fun Y ↦ inferInstanceAs (IsAffineHom Y.obj.hom))
    (fun _ ↦ trivial) (fun _ ↦ trivial)

/-- Forgetting affineness of `toAffineSchemeOver S` recovers the full-subcategory inclusion into
`Over S`. -/
@[simp]
theorem toAffineSchemeOver_comp_forget :
    toAffineSchemeOver S ⋙ MorphismProperty.Over.forget (@IsAffineHom) ⊤ S =
      (finiteEtaleSchemeProperty S).ι :=
  (rfl)

/-- The underlying scheme of `(toAffineSchemeOver S).obj Y` is `Y.obj.left`. -/
@[simp]
theorem toAffineSchemeOver_obj_left (Y : FiniteEtaleScheme S) :
    ((toAffineSchemeOver S).obj Y).left = Y.obj.left :=
  (rfl)

/-- The structure morphism of `(toAffineSchemeOver S).obj Y` is `Y.obj.hom`. -/
@[simp]
theorem toAffineSchemeOver_obj_hom (Y : FiniteEtaleScheme S) :
    ((toAffineSchemeOver S).obj Y).hom = Y.obj.hom :=
  (rfl)

/-- Finite étale schemes over `S` form a full subcategory of `AffineSchemeOver S`. -/
def toAffineSchemeOverFullyFaithful : (toAffineSchemeOver S).FullyFaithful :=
  let hff : (MorphismProperty.Over.forget (@IsAffineHom) ⊤ S).FullyFaithful :=
    MorphismProperty.Comma.forgetFullyFaithful _ _ _
  letI := hff.faithful
  Functor.FullyFaithful.ofCompFaithful (G := MorphismProperty.Over.forget (@IsAffineHom) ⊤ S)
    (ObjectProperty.fullyFaithfulι _)

instance : (toAffineSchemeOver S).Full := (toAffineSchemeOverFullyFaithful S).full

instance : (toAffineSchemeOver S).Faithful := (toAffineSchemeOverFullyFaithful S).faithful

variable {S}

/-- Base change of finite étale schemes commutes with the inclusion `toAffineSchemeOver` into
affine schemes over the base. -/
def pullbackCompToAffineSchemeOver {T : Scheme.{u}} (f : T ⟶ S) :
    pullback f ⋙ toAffineSchemeOver T ≅
      toAffineSchemeOver S ⋙ baseChangeAffineSchemeOver f := by
  letI : MorphismProperty.HasPullbacksAlong (@IsAffineHom : MorphismProperty Scheme.{u}) f :=
    ⟨fun _ _ ↦ inferInstance⟩
  letI : MorphismProperty.IsStableUnderBaseChangeAlong
      (@IsAffineHom : MorphismProperty Scheme.{u}) f :=
    ⟨fun h hg ↦ isAffineHom_isStableUnderBaseChange.of_isPullback h hg⟩
  let hff : (MorphismProperty.Over.forget (@IsAffineHom) ⊤ T).FullyFaithful :=
    MorphismProperty.Comma.forgetFullyFaithful _ _ _
  letI := hff.full
  letI := hff.faithful
  apply Functor.fullyFaithfulCancelRight (MorphismProperty.Over.forget (@IsAffineHom) ⊤ T)
  refine Functor.associator _ _ _ ≪≫ eqToIso (pullback_comp_ι f) ≪≫
    (Functor.isoWhiskerLeft (toAffineSchemeOver S)
      (MorphismProperty.Over.pullbackCompForgetIso (P := @IsAffineHom) (Q := ⊤) f)).symm ≪≫
    (Functor.associator _ _ _).symm

/-- Base change of finite étale schemes along an isomorphism of schemes is an equivalence of
categories. -/
instance isEquivalence_pullback_of_isIso {T : Scheme.{u}} (g : T ⟶ S) [IsIso g] :
    (pullback g).IsEquivalence :=
  Functor.IsEquivalence.mk' (pullback (inv g))
    (pullbackId.symm ≪≫ eqToIso (congrArg pullback (IsIso.inv_hom_id g).symm) ≪≫
      pullbackComp (inv g) g)
    ((pullbackComp g (inv g)).symm ≪≫ eqToIso (congrArg pullback (IsIso.hom_inv_id g)) ≪≫
      pullbackId)

end ToAffineSchemeOver

section FormalCompletion

variable {X Z : Scheme.{u}} (I : X.IdealSheafData)

private lemma isFiniteLocallyFree_coordinateAlgebra (Y : FiniteEtaleScheme X) :
    Scheme.Modules.isFiniteLocallyFree X
      ((affineFunctions X).obj ((toAffineSchemeOver X).obj Y)).unop.obj.X :=
  Scheme.Hom.isFiniteLocallyFree_pushforwardStructureAlgebra Y.obj.hom

/-- Faithfulness of `FiniteEtaleScheme.pullback (toScheme X I 0)` when formal completion on finite
locally free sheaves is faithful. -/
private theorem faithful_pullback_toScheme_zero
    [(FiniteLocallyFreeSheaf.completionFunctor X I).Faithful] :
    (pullback (toScheme X I 0)).Faithful where
  map_injective {Y₁ Y₂} {g₁ g₂} hg := by
    have : FormallyUnramified ((toAffineSchemeOver X).obj Y₂).hom :=
      inferInstanceAs (FormallyUnramified Y₂.obj.hom)
    let e := pullbackCompToAffineSchemeOver (toScheme X I 0)
    have hmap : (baseChangeAffineSchemeOver (toScheme X I 0)).map ((toAffineSchemeOver X).map g₁) =
        (baseChangeAffineSchemeOver (toScheme X I 0)).map ((toAffineSchemeOver X).map g₂) :=
      (Iso.cancel_iso_hom_left (e.app Y₁) _ _).mp
        ((e.hom.naturality g₁).symm.trans
          ((congrArg (· ≫ e.hom.app Y₂) (congrArg (toAffineSchemeOver _).map hg)).trans
            (e.hom.naturality g₂)))
    exact (toAffineSchemeOver X).map_injective
      (AffineSchemeOver.hom_ext_of_formalCompletion_of_prop I (fun _ hE ↦ hE.2)
        (isFiniteLocallyFree_coordinateAlgebra Y₁) (isFiniteLocallyFree_coordinateAlgebra Y₂) hmap)

/-- Fullness of `FiniteEtaleScheme.pullback (toScheme X I 0)` when formal completion on finite
locally free sheaves is fully faithful. -/
private theorem full_pullback_toScheme_zero
    [(FiniteLocallyFreeSheaf.completionFunctor X I).Full]
    [(FiniteLocallyFreeSheaf.completionFunctor X I).Faithful] :
    (pullback (toScheme X I 0)).Full where
  map_surjective {Y₁ Y₂} f₀ := by
    have : Etale ((toAffineSchemeOver X).obj Y₂).hom :=
      inferInstanceAs (Etale Y₂.obj.hom)
    let e := pullbackCompToAffineSchemeOver (toScheme X I 0)
    obtain ⟨u, hu, -⟩ := AffineSchemeOver.existsUnique_hom_of_formalCompletion_of_prop I
      (fun _ hE ↦ hE.2) (isFiniteLocallyFree_coordinateAlgebra Y₁)
      (isFiniteLocallyFree_coordinateAlgebra Y₂)
      ((e.app Y₁).inv ≫ (toAffineSchemeOver _).map f₀ ≫ (e.app Y₂).hom)
    let g : Y₁ ⟶ Y₂ := (toAffineSchemeOver X).preimage u
    refine ⟨g, (toAffineSchemeOver _).map_injective ?_⟩
    refine (Iso.cancel_iso_hom_right _ _ (e.app Y₂)).mp ?_
    calc (toAffineSchemeOver _).map ((pullback (toScheme X I 0)).map g) ≫ (e.app Y₂).hom
        _ = (e.app Y₁).hom ≫
              (baseChangeAffineSchemeOver (toScheme X I 0)).map ((toAffineSchemeOver X).map g) :=
            e.hom.naturality g
        _ = (e.app Y₁).hom ≫ (baseChangeAffineSchemeOver (toScheme X I 0)).map u := by
            rw [(toAffineSchemeOver X).map_preimage]
        _ = (toAffineSchemeOver _).map f₀ ≫ (e.app Y₂).hom := by
            rw [hu]
            simp

/-- Comparison between `FiniteEtaleScheme.pullback i` and `pullback (toScheme X I 0)` for any
closed immersion `i : Z ⟶ X` with `i.ker = I`. -/
private theorem exists_pullbackClosedImmersionIso (i : Z ⟶ X) [IsClosedImmersion i]
    (hi : i.ker = I) :
    ∃ (g : Z ⟶ (X.formalCompletion I).X 0),
      IsIso g ∧ Nonempty (pullback i ≅ pullback (toScheme X I 0) ⋙ pullback g) := by
  have hker : (toScheme X I 0).ker = i.ker :=
    (ker_toScheme X I 0).trans ((pow_one I).trans hi.symm)
  let g : Z ⟶ (X.formalCompletion I).X 0 := IsClosedImmersion.lift (toScheme X I 0) i hker.le
  have hg : IsIso g := IsClosedImmersion.isIso_lift (toScheme X I 0) i hker
  have hfac : g ≫ toScheme X I 0 = i := IsClosedImmersion.lift_fac (toScheme X I 0) i hker.le
  exact ⟨g, hg, ⟨eqToIso (congrArg pullback hfac.symm) ≪≫ pullbackComp g (toScheme X I 0)⟩⟩

/-- **Stacks Project, Lemma 58.17.1 (Tag 0EL8), faithfulness (finite locally free form).**
If formal completion of finite locally free `𝒪_X`-modules along an ideal sheaf `I` is faithful,
then base change of finite étale schemes along any closed immersion `i : Z ⟶ X` with `i.ker = I`
is faithful. -/
@[stacks 0EL8 "faithfulness, assuming faithfulness on finite locally free sheaves"]
theorem faithful_pullback_of_completion_finiteLocallyFree
    [(FiniteLocallyFreeSheaf.completionFunctor X I).Faithful]
    (i : Z ⟶ X) [IsClosedImmersion i] (hi : i.ker = I) :
    (pullback i).Faithful := by
  obtain ⟨g, _, ⟨e⟩⟩ := exists_pullbackClosedImmersionIso I i hi
  have := faithful_pullback_toScheme_zero I
  exact Functor.Faithful.of_iso e.symm

/-- **Stacks Project, Lemma 58.17.1 (Tag 0EL8), fullness (finite locally free form).**
If formal completion of finite locally free `𝒪_X`-modules along an ideal sheaf `I` is fully
faithful, then base change of finite étale schemes along any closed immersion `i : Z ⟶ X` with
`i.ker = I` is full. -/
@[stacks 0EL8 "fullness, assuming full faithfulness on finite locally free sheaves"]
theorem full_pullback_of_completion_finiteLocallyFree
    [(FiniteLocallyFreeSheaf.completionFunctor X I).Full]
    [(FiniteLocallyFreeSheaf.completionFunctor X I).Faithful]
    (i : Z ⟶ X) [IsClosedImmersion i] (hi : i.ker = I) :
    (pullback i).Full := by
  obtain ⟨g, _, ⟨e⟩⟩ := exists_pullbackClosedImmersionIso I i hi
  have := faithful_pullback_toScheme_zero I
  have := full_pullback_toScheme_zero I
  exact Functor.Full.of_iso e.symm

/-- **Stacks Project, Lemma 58.17.1 (Tag 0EL8) (finite locally free form).**
If formal completion of finite locally free `𝒪_X`-modules along an ideal sheaf `I` is fully
faithful, then base change of finite étale schemes along any closed immersion `i : Z ⟶ X` with
`i.ker = I` is fully faithful. -/
@[stacks 0EL8 "assuming full faithfulness on finite locally free sheaves"]
def fullyFaithfulPullbackOfCompletionFiniteLocallyFree
    [(FiniteLocallyFreeSheaf.completionFunctor X I).Full]
    [(FiniteLocallyFreeSheaf.completionFunctor X I).Faithful]
    (i : Z ⟶ X) [IsClosedImmersion i] (hi : i.ker = I) :
    (pullback i).FullyFaithful :=
  letI := faithful_pullback_of_completion_finiteLocallyFree I i hi
  letI := full_pullback_of_completion_finiteLocallyFree I i hi
  Functor.FullyFaithful.ofFullyFaithful (pullback i)

/-- **Stacks Project, Lemma 58.17.1 (Tag 0EL8), faithfulness (coherent / finitely presented form).**
If formal completion of finitely presented `𝒪_X`-modules along `I` is faithful, then base change
of finite étale schemes along any closed immersion `i : Z ⟶ X` with `i.ker = I` is faithful. -/
@[stacks 0EL8 "faithfulness"]
theorem faithful_pullback_of_completion_coherent [(completionFunctor X I).Faithful]
    (i : Z ⟶ X) [IsClosedImmersion i] (hi : i.ker = I) :
    (pullback i).Faithful :=
  faithful_pullback_of_completion_finiteLocallyFree I i hi

/-- **Stacks Project, Lemma 58.17.1 (Tag 0EL8), fullness (coherent / finitely presented form).**
If formal completion of finitely presented `𝒪_X`-modules along `I` is fully faithful, then base
change of finite étale schemes along any closed immersion `i : Z ⟶ X` with `i.ker = I` is full. -/
@[stacks 0EL8 "fullness"]
theorem full_pullback_of_completion_coherent [(completionFunctor X I).Full]
    [(completionFunctor X I).Faithful] (i : Z ⟶ X) [IsClosedImmersion i] (hi : i.ker = I) :
    (pullback i).Full :=
  full_pullback_of_completion_finiteLocallyFree I i hi

/-- **Stacks Project, Lemma 58.17.1 (Tag 0EL8).**
If formal completion of finitely presented `𝒪_X`-modules along `I` is fully faithful, then base
change of finite étale schemes along any closed immersion `i : Z ⟶ X` with `i.ker = I` is fully
faithful. -/
@[stacks 0EL8]
def fullyFaithfulPullbackOfCompletionCoherent [(completionFunctor X I).Full]
    [(completionFunctor X I).Faithful] (i : Z ⟶ X) [IsClosedImmersion i] (hi : i.ker = I) :
    (pullback i).FullyFaithful :=
  fullyFaithfulPullbackOfCompletionFiniteLocallyFree I i hi

instance faithful_pullback_of_isClosedImmersion (i : Z ⟶ X) [IsClosedImmersion i]
    [(FiniteLocallyFreeSheaf.completionFunctor X i.ker).Faithful] :
    (pullback i).Faithful :=
  faithful_pullback_of_completion_finiteLocallyFree i.ker i rfl

instance full_pullback_of_isClosedImmersion (i : Z ⟶ X) [IsClosedImmersion i]
    [(FiniteLocallyFreeSheaf.completionFunctor X i.ker).Full]
    [(FiniteLocallyFreeSheaf.completionFunctor X i.ker).Faithful] :
    (pullback i).Full :=
  full_pullback_of_completion_finiteLocallyFree i.ker i rfl

instance faithful_pullback_subschemeι
    [(FiniteLocallyFreeSheaf.completionFunctor X I).Faithful] :
    (pullback I.subschemeι).Faithful :=
  faithful_pullback_of_completion_finiteLocallyFree I I.subschemeι I.ker_subschemeι

instance full_pullback_subschemeι
    [(FiniteLocallyFreeSheaf.completionFunctor X I).Full]
    [(FiniteLocallyFreeSheaf.completionFunctor X I).Faithful] :
    (pullback I.subschemeι).Full :=
  full_pullback_of_completion_finiteLocallyFree I I.subschemeι I.ker_subschemeι

instance faithful_pullback_toScheme_zero_inst
    [(FiniteLocallyFreeSheaf.completionFunctor X I).Faithful] :
    (pullback (toScheme X I 0)).Faithful :=
  faithful_pullback_toScheme_zero I

instance full_pullback_toScheme_zero_inst
    [(FiniteLocallyFreeSheaf.completionFunctor X I).Full]
    [(FiniteLocallyFreeSheaf.completionFunctor X I).Faithful] :
    (pullback (toScheme X I 0)).Full :=
  full_pullback_toScheme_zero I

/-- Transport of `faithful_pullback_of_completion_finiteLocallyFree` to Mathlib's
`MorphismProperty.Over.pullback (@IsFinite ⊓ @Etale) ⊤ i`. -/
@[stacks 0EL8 "faithfulness, MorphismProperty.Over presentation"]
theorem faithful_overPullback_of_completion_finiteLocallyFree
    [(FiniteLocallyFreeSheaf.completionFunctor X I).Faithful]
    (i : Z ⟶ X) [IsClosedImmersion i] (hi : i.ker = I) :
    letI : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).IsStableUnderBaseChange := .inf
    (MorphismProperty.Over.pullback (@IsFinite ⊓ @Etale) ⊤ i).Faithful := by
  have : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).IsStableUnderBaseChange := .inf
  have := faithful_pullback_of_completion_finiteLocallyFree I i hi
  have : (pullback i ⋙ (equivOver Z).functor).Faithful := inferInstance
  have : ((equivOver X).functor ⋙
      MorphismProperty.Over.pullback (@IsFinite ⊓ @Etale) ⊤ i).Faithful :=
    Functor.Faithful.of_iso (pullbackCompEquivOver i)
  have := Functor.Faithful.comp (equivOver X).inverse
    ((equivOver X).functor ⋙ MorphismProperty.Over.pullback (@IsFinite ⊓ @Etale) ⊤ i)
  exact Functor.Faithful.of_iso ((Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (equivOver X).counitIso _ ≪≫ Functor.leftUnitor _)

/-- Transport of `full_pullback_of_completion_finiteLocallyFree` to Mathlib's
`MorphismProperty.Over.pullback (@IsFinite ⊓ @Etale) ⊤ i`. -/
@[stacks 0EL8 "fullness, MorphismProperty.Over presentation"]
theorem full_overPullback_of_completion_finiteLocallyFree
    [(FiniteLocallyFreeSheaf.completionFunctor X I).Full]
    [(FiniteLocallyFreeSheaf.completionFunctor X I).Faithful]
    (i : Z ⟶ X) [IsClosedImmersion i] (hi : i.ker = I) :
    letI : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).IsStableUnderBaseChange := .inf
    (MorphismProperty.Over.pullback (@IsFinite ⊓ @Etale) ⊤ i).Full := by
  have : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).IsStableUnderBaseChange := .inf
  have := faithful_pullback_of_completion_finiteLocallyFree I i hi
  have := full_pullback_of_completion_finiteLocallyFree I i hi
  have : (pullback i ⋙ (equivOver Z).functor).Full := inferInstance
  have : ((equivOver X).functor ⋙
      MorphismProperty.Over.pullback (@IsFinite ⊓ @Etale) ⊤ i).Full :=
    Functor.Full.of_iso (pullbackCompEquivOver i)
  have := Functor.Full.comp (equivOver X).inverse
    ((equivOver X).functor ⋙ MorphismProperty.Over.pullback (@IsFinite ⊓ @Etale) ⊤ i)
  exact Functor.Full.of_iso ((Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (equivOver X).counitIso _ ≪≫ Functor.leftUnitor _)

end FormalCompletion

end TauCeti.FiniteEtaleScheme

namespace TauCeti.IsLocalRing

open TauCeti.AlgebraicGeometry

section PuncturedQuotient

variable {A : Type u} [CommRing A] [IsLocalRing A] (I : Ideal A)

/-- The ideal sheaf on the punctured spectrum of `A` generated by an ideal `I` of `A`, defined as
the inverse image along `(puncturedSpectrum A).ι` of the ideal sheaf of `I` on `Spec A`. -/
def puncturedIdealSheaf : (puncturedSpectrum A).toScheme.IdealSheafData :=
  (Scheme.IdealSheafData.ofIdealTop
    (I.map (Scheme.ΓSpecIso (.of A)).inv.hom)).comap (puncturedSpectrum A).ι

/-- On global sections of `puncturedSpectrum A`, `puncturedIdealSheaf I` is generated by the image
of `I` in `Γ(puncturedSpectrum A, ⊤)`. -/
theorem puncturedIdealSheaf_eq_ofIdealTop :
    puncturedIdealSheaf I = Scheme.IdealSheafData.ofIdealTop
      (I.map ((puncturedSpectrum A).ι.appTop.hom.comp (Scheme.ΓSpecIso (.of A)).inv.hom)) := by
  simp [puncturedIdealSheaf, Scheme.IdealSheafData.comap_ofIdealTop, Ideal.map_map]

variable [IsLocalRing (A ⧸ I)]

/-- The inclusion of the punctured spectrum of `A ⧸ I` into the punctured spectrum of `A` induced
by `Spec (A ⧸ I) ⟶ Spec A`. -/
abbrev puncturedQuotientι : (puncturedSpectrum (A ⧸ I)).toScheme ⟶ (puncturedSpectrum A).toScheme :=
  (Spec.map (CommRingCat.ofHom (algebraMap A (A ⧸ I)))).resLE
    (puncturedSpectrum A) (puncturedSpectrum (A ⧸ I))
    (preimage_puncturedSpectrum (radical_map_maximalIdeal_of_surjective
      (Ideal.Quotient.algebraMap_eq I ▸ Ideal.Quotient.mk_surjective))).ge

private lemma isPullback_puncturedQuotientι :
    IsPullback (puncturedQuotientι I) (puncturedSpectrum (A ⧸ I)).ι
      (puncturedSpectrum A).ι (Spec.map (CommRingCat.ofHom (algebraMap A (A ⧸ I)))) :=
  Scheme.Hom.isPullback_resLE_of_eq (Spec.map (CommRingCat.ofHom (algebraMap A (A ⧸ I))))
    (puncturedSpectrum A) (preimage_puncturedSpectrum (radical_map_maximalIdeal_of_surjective
      (Ideal.Quotient.algebraMap_eq I ▸ Ideal.Quotient.mk_surjective))).symm

/-- The inclusion `puncturedSpectrum (A ⧸ I) ⟶ puncturedSpectrum A` is a closed immersion. -/
instance isClosedImmersion_puncturedQuotientι : IsClosedImmersion (puncturedQuotientι I) := by
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (algebraMap A (A ⧸ I)))) :=
    IsClosedImmersion.spec_of_surjective _
      (Ideal.Quotient.algebraMap_eq I ▸ Ideal.Quotient.mk_surjective)
  rw [← (isPullback_puncturedQuotientι I).isoPullback_hom_fst]
  infer_instance

/-- The kernel ideal sheaf of `puncturedQuotientι I` is `puncturedIdealSheaf I`. -/
@[simp]
theorem ker_puncturedQuotientι : (puncturedQuotientι I).ker = puncturedIdealSheaf I := by
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (algebraMap A (A ⧸ I)))) :=
    IsClosedImmersion.spec_of_surjective _
      (Ideal.Quotient.algebraMap_eq I ▸ Ideal.Quotient.mk_surjective)
  rw [Scheme.IdealSheafData.ker_eq_comap_of_isPullback _ (isPullback_puncturedQuotientι I),
    Scheme.Hom.ker_Spec_map, CommRingCat.hom_ofHom, Ideal.Quotient.algebraMap_eq, Ideal.mk_ker]
  rfl

/-- Restriction of finite étale covers from the punctured spectrum of `A` to the punctured spectrum
of `A ⧸ I` is faithful when formal completion of finite locally free sheaves on the punctured
spectrum of `A` along `puncturedIdealSheaf I` is faithful. -/
theorem faithful_restrictPuncturedQuotient_of_completion_finiteLocallyFree
    [(FiniteLocallyFreeSheaf.completionFunctor (puncturedSpectrum A).toScheme
      (puncturedIdealSheaf I)).Faithful] :
    (restrictPuncturedQuotient I).Faithful :=
  FiniteEtaleScheme.faithful_pullback_of_completion_finiteLocallyFree
    (puncturedIdealSheaf I) (puncturedQuotientι I) (ker_puncturedQuotientι I)

/-- Restriction of finite étale covers from the punctured spectrum of `A` to the punctured spectrum
of `A ⧸ I` is full when formal completion of finite locally free sheaves on the punctured spectrum
of `A` along `puncturedIdealSheaf I` is fully faithful. -/
theorem full_restrictPuncturedQuotient_of_completion_finiteLocallyFree
    [(FiniteLocallyFreeSheaf.completionFunctor (puncturedSpectrum A).toScheme
      (puncturedIdealSheaf I)).Full]
    [(FiniteLocallyFreeSheaf.completionFunctor (puncturedSpectrum A).toScheme
      (puncturedIdealSheaf I)).Faithful] :
    (restrictPuncturedQuotient I).Full :=
  FiniteEtaleScheme.full_pullback_of_completion_finiteLocallyFree
    (puncturedIdealSheaf I) (puncturedQuotientι I) (ker_puncturedQuotientι I)

/-- Restriction of finite étale covers from the punctured spectrum of `A` to the punctured spectrum
of `A ⧸ I` is faithful when formal completion of finitely presented sheaves on the punctured
spectrum of `A` along `puncturedIdealSheaf I` is faithful. -/
theorem faithful_restrictPuncturedQuotient_of_completion_coherent
    [(Scheme.formalCompletion.completionFunctor (puncturedSpectrum A).toScheme
      (puncturedIdealSheaf I)).Faithful] :
    (restrictPuncturedQuotient I).Faithful :=
  faithful_restrictPuncturedQuotient_of_completion_finiteLocallyFree I

/-- Restriction of finite étale covers from the punctured spectrum of `A` to the punctured spectrum
of `A ⧸ I` is full when formal completion of finitely presented sheaves on the punctured spectrum
of `A` along `puncturedIdealSheaf I` is fully faithful. -/
theorem full_restrictPuncturedQuotient_of_completion_coherent
    [(Scheme.formalCompletion.completionFunctor (puncturedSpectrum A).toScheme
      (puncturedIdealSheaf I)).Full]
    [(Scheme.formalCompletion.completionFunctor (puncturedSpectrum A).toScheme
      (puncturedIdealSheaf I)).Faithful] :
    (restrictPuncturedQuotient I).Full :=
  full_restrictPuncturedQuotient_of_completion_finiteLocallyFree I

end PuncturedQuotient

end TauCeti.IsLocalRing

end
