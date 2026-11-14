/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicThickeningSystem.FiniteLocallyFree
public import TauCeti.AlgebraicGeometry.FiniteEtale.Fiber
import TauCeti.AlgebraicGeometry.AdicThickeningSystem.Etale

/-!
# Full faithfulness of finite étale pullback from formal completion

Let `X` be a scheme, `I` an ideal sheaf on `X`, and `i : Z ⟶ X` a closed immersion with kernel `I`
(for example `I.subschemeι : V(I) ⟶ X`). Suppose that the formal completion functor on finite
locally free `𝒪_X`-modules (`Scheme.formalCompletion.finiteLocallyFreeCompletionFunctor X I`) is
fully faithful—as happens automatically whenever `Scheme.formalCompletion.completionFunctor X I` is
fully faithful, or under the local-cohomology hypotheses of Stacks, Lemma 52.15.5 (0EKS). Then
pullback of finite étale schemes along `i`,
`TauCeti.FiniteEtaleScheme.pullback i : FiniteEtaleScheme X ⥤ FiniteEtaleScheme Z`,
is fully faithful (Stacks, Lemma 58.17.1 (0EL8)). Moreover, faithfulness of `pullback i` already
follows from faithfulness of `finiteLocallyFreeCompletionFunctor X I` alone.

The proof combines two ingredients without any Noetherian hypothesis on `X`:

1. Infinitesimal invariance of étale morphisms (`AdicThickeningSystem.hom_ext_of_formallyUnramified`
   and `AdicThickeningSystem.liftOfEtale`): for finite étale schemes `V` and `W` over `X`, morphisms
   between their level-zero reductions over `V(I)` correspond bijectively to morphisms between their
   formal completions `V/V(I.comap p)` and `W/V(I.comap q)` over `X.formalCompletion I`.
2. Formal algebraization for finite locally free morphisms
   (`Scheme.formalCompletion.hom_ext_of_finite_of_flat` and
   `Scheme.formalCompletion.exists_hom_of_finite_of_flat`): since a finite étale morphism is finite,
   flat, and locally of finite presentation, morphisms over `X` correspond bijectively to morphisms
   between formal completions over `X.formalCompletion I`.

Transporting from the zeroth infinitesimal level `toScheme X I 0 : V(I ^ 1) ⟶ X` to any closed
immersion `i : Z ⟶ X` with `i.ker = I` uses `IsClosedImmersion.isIso_lift` together with the fact
that `FiniteEtaleScheme.pullback u` is an equivalence for any isomorphism `u`.

## Main results

* `AlgebraicGeometry.Scheme.formalCompletion.etale_map_app`: the morphism of formal completions
  induced by an étale morphism, for the inverse image ideal sheaf, is étale at every level.
* `TauCeti.FiniteEtaleScheme.faithful_pullback_of_ker_eq`,
  `TauCeti.FiniteEtaleScheme.full_pullback_of_ker_eq`,
  `TauCeti.FiniteEtaleScheme.fullyFaithfulPullbackOfKerEq`: Stacks, Lemma 58.17.1 (0EL8) for an
  arbitrary closed immersion `i : Z ⟶ X` with `i.ker = I`.
* `TauCeti.FiniteEtaleScheme.faithful_pullback_of_isClosedImmersion`,
  `TauCeti.FiniteEtaleScheme.full_pullback_of_isClosedImmersion`,
  `TauCeti.FiniteEtaleScheme.fullyFaithfulPullbackOfIsClosedImmersion`: instances and bundled
  `FullyFaithful` for any closed immersion `i : Z ⟶ X` in terms of `i.ker`.
* `TauCeti.FiniteEtaleScheme.faithful_pullback_subschemeι`,
  `TauCeti.FiniteEtaleScheme.full_pullback_subschemeι`,
  `TauCeti.FiniteEtaleScheme.fullyFaithfulPullbackSubschemeι`: instances and bundled `FullyFaithful`
  for the canonical closed subscheme inclusion `I.subschemeι : V(I) ⟶ X`.

## References

* [The Stacks Project, Lemma 58.17.1](https://stacks.math.columbia.edu/tag/0EL8).
-/

public section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.formalCompletion

/-- The morphism of formal completions induced by an étale morphism `f : X ⟶ Y`, for the inverse
image of an ideal sheaf on `Y`, is étale at every level. -/
instance etale_map_app {X Y : Scheme.{u}} {J : Y.IdealSheafData} (f : X ⟶ Y) [Etale f] (n : ℕ) :
    Etale ((map (I := J.comap f) f le_rfl).app n) :=
  MorphismProperty.of_isPullback (P := @Etale) (isPullback_map_app f rfl n) ‹_›

end AlgebraicGeometry.Scheme.formalCompletion

namespace TauCeti.FiniteEtaleScheme

open TauCeti.AlgebraicGeometry

section LevelZero

/-- Canonical identification of the zeroth level of the formal completion of `V` along
`I.comap V.obj.hom` with the pullback of `V` along `toScheme X I 0`. -/
private noncomputable def levelZeroPullbackIso {X : Scheme.{u}} (I : X.IdealSheafData)
    (V : FiniteEtaleScheme X) :
    (V.obj.left.formalCompletion (I.comap V.obj.hom)).X 0 ≅
      ((pullback (Scheme.formalCompletion.toScheme X I 0)).obj V).obj.left :=
  (Scheme.formalCompletion.isPullback_map_app (J := I) V.obj.hom rfl 0).isoPullback

private lemma levelZeroPullbackIso_hom_pullback_map {X : Scheme.{u}} (I : X.IdealSheafData)
    {V W : FiniteEtaleScheme X} (g : V ⟶ W) :
    (levelZeroPullbackIso I V).hom ≫
        ((pullback (Scheme.formalCompletion.toScheme X I 0)).map g).hom.left =
      (Scheme.formalCompletion.map (I := I.comap V.obj.hom) (J := I.comap W.obj.hom) g.hom.left
        (by rw [← Scheme.IdealSheafData.comap_comp, Over.w g.hom])).app 0 ≫
        (levelZeroPullbackIso I W).hom := by
  apply Limits.pullback.hom_ext
  · calc ((levelZeroPullbackIso I V).hom ≫
            ((pullback (Scheme.formalCompletion.toScheme X I 0)).map g).hom.left) ≫
            Limits.pullback.fst W.obj.hom (Scheme.formalCompletion.toScheme X I 0)
        _ = (levelZeroPullbackIso I V).hom ≫
              Limits.pullback.fst V.obj.hom (Scheme.formalCompletion.toScheme X I 0) ≫
                g.hom.left :=
          (Category.assoc _ _ _).trans
            (congrArg (_ ≫ ·) (Limits.pullback.lift_fst _ _ _))
        _ = Scheme.formalCompletion.toScheme V.obj.left (I.comap V.obj.hom) 0 ≫ g.hom.left :=
          IsPullback.isoPullback_hom_fst_assoc _ _
        _ = (Scheme.formalCompletion.map (I := I.comap V.obj.hom) (J := I.comap W.obj.hom)
              g.hom.left _).app 0 ≫
              Scheme.formalCompletion.toScheme W.obj.left (I.comap W.obj.hom) 0 :=
          (Scheme.formalCompletion.map_app_toScheme _ _ 0).symm
        _ = _ :=
          (congrArg (_ ≫ ·) (IsPullback.isoPullback_hom_fst _).symm).trans
            (Category.assoc _ _ _).symm
  · calc ((levelZeroPullbackIso I V).hom ≫
            ((pullback (Scheme.formalCompletion.toScheme X I 0)).map g).hom.left) ≫
            Limits.pullback.snd W.obj.hom (Scheme.formalCompletion.toScheme X I 0)
        _ = (levelZeroPullbackIso I V).hom ≫
              Limits.pullback.snd V.obj.hom (Scheme.formalCompletion.toScheme X I 0) :=
          (Category.assoc _ _ _).trans
            (congrArg (_ ≫ ·) (Limits.pullback.lift_snd _ _ _))
        _ = (Scheme.formalCompletion.map (I := I.comap V.obj.hom) V.obj.hom le_rfl).app 0 :=
          IsPullback.isoPullback_hom_snd _
        _ = (Scheme.formalCompletion.map (I := I.comap V.obj.hom) (J := I.comap W.obj.hom)
              g.hom.left _).app 0 ≫
              (Scheme.formalCompletion.map (I := I.comap W.obj.hom) W.obj.hom le_rfl).app 0 := by
          rw [← cancel_mono (Scheme.formalCompletion.toScheme X I 0), Category.assoc,
            Scheme.formalCompletion.map_app_toScheme, Scheme.formalCompletion.map_app_toScheme,
            Scheme.formalCompletion.map_app_toScheme_assoc, Over.w g.hom]
        _ = _ :=
          (congrArg (_ ≫ ·) (IsPullback.isoPullback_hom_snd _).symm).trans
            (Category.assoc _ _ _).symm

private lemma formalCompletion_map_comp_hom {X : Scheme.{u}} (I : X.IdealSheafData)
    {V W : FiniteEtaleScheme X} (g : V.obj.left ⟶ W.obj.left) (hg : g ≫ W.obj.hom = V.obj.hom) :
    Scheme.formalCompletion.map (I := I.comap V.obj.hom) (J := I.comap W.obj.hom) g
        (by rw [← Scheme.IdealSheafData.comap_comp, hg]) ≫
      Scheme.formalCompletion.map (I := I.comap W.obj.hom) W.obj.hom le_rfl =
    Scheme.formalCompletion.map (I := I.comap V.obj.hom) V.obj.hom le_rfl := by
  ext n
  rw [← cancel_mono (Scheme.formalCompletion.toScheme X I n),
    AdicThickeningSystem.comp_app, Category.assoc,
    Scheme.formalCompletion.map_app_toScheme, Scheme.formalCompletion.map_app_toScheme,
    Scheme.formalCompletion.map_app_toScheme_assoc, hg]

/-- If `finiteLocallyFreeCompletionFunctor X I` is faithful, pullback of finite étale schemes from
`X` to the zeroth infinitesimal level `V(I ^ 1)` of `X.formalCompletion I` is faithful. -/
@[stacks 0EL8]
instance faithful_pullback_toScheme_zero {X : Scheme.{u}} (I : X.IdealSheafData)
    [(Scheme.formalCompletion.finiteLocallyFreeCompletionFunctor X I).Faithful] :
    (pullback (Scheme.formalCompletion.toScheme X I 0)).Faithful where
  map_injective {V W} {g₁ g₂} h := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    have h0 :
        (Scheme.formalCompletion.map (I := I.comap V.obj.hom) (J := I.comap W.obj.hom) g₁.hom.left
            (by rw [← Scheme.IdealSheafData.comap_comp, Over.w g₁.hom])).app 0 =
          (Scheme.formalCompletion.map (I := I.comap V.obj.hom) (J := I.comap W.obj.hom) g₂.hom.left
            (by rw [← Scheme.IdealSheafData.comap_comp, Over.w g₂.hom])).app 0 := by
      apply (cancel_mono (levelZeroPullbackIso I W).hom).mp
      rw [← levelZeroPullbackIso_hom_pullback_map I g₁,
        ← levelZeroPullbackIso_hom_pullback_map I g₂, h]
    have hmap := AdicThickeningSystem.hom_ext_of_formallyUnramified
      (Scheme.formalCompletion.map (I := I.comap W.obj.hom) W.obj.hom le_rfl)
      ((formalCompletion_map_comp_hom I g₁.hom.left (Over.w g₁.hom)).trans
        (formalCompletion_map_comp_hom I g₂.hom.left (Over.w g₂.hom)).symm) h0
    exact Scheme.formalCompletion.hom_ext_of_finite_of_flat V.obj.hom W.obj.hom rfl rfl
      (Over.w g₁.hom) (Over.w g₂.hom) hmap

/-- If `finiteLocallyFreeCompletionFunctor X I` is full and faithful, pullback of finite étale
schemes from `X` to the zeroth infinitesimal level `V(I ^ 1)` of `X.formalCompletion I` is full. -/
@[stacks 0EL8]
instance full_pullback_toScheme_zero {X : Scheme.{u}} (I : X.IdealSheafData)
    [(Scheme.formalCompletion.finiteLocallyFreeCompletionFunctor X I).Full]
    [(Scheme.formalCompletion.finiteLocallyFreeCompletionFunctor X I).Faithful] :
    (pullback (Scheme.formalCompletion.toScheme X I 0)).Full where
  map_surjective {V W} φ₀ := by
    let a₀ : (V.obj.left.formalCompletion (I.comap V.obj.hom)).X 0 ⟶
        (W.obj.left.formalCompletion (I.comap W.obj.hom)).X 0 :=
      (levelZeroPullbackIso I V).hom ≫ φ₀.hom.left ≫ (levelZeroPullbackIso I W).inv
    have ha₀ : a₀ ≫ (Scheme.formalCompletion.map (I := I.comap W.obj.hom)
        W.obj.hom le_rfl).app 0 =
        (Scheme.formalCompletion.map (I := I.comap V.obj.hom) V.obj.hom le_rfl).app 0 :=
      calc ((levelZeroPullbackIso I V).hom ≫ φ₀.hom.left ≫ (levelZeroPullbackIso I W).inv) ≫
              (Scheme.formalCompletion.map (I := I.comap W.obj.hom) W.obj.hom le_rfl).app 0
          _ = (levelZeroPullbackIso I V).hom ≫ φ₀.hom.left ≫
                ((levelZeroPullbackIso I W).inv ≫
                  (Scheme.formalCompletion.map (I := I.comap W.obj.hom) W.obj.hom le_rfl).app 0) :=
            (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Category.assoc _ _ _))
          _ = (levelZeroPullbackIso I V).hom ≫
                (φ₀.hom.left ≫
                  ((pullback (Scheme.formalCompletion.toScheme X I 0)).obj W).obj.hom) :=
            congrArg (_ ≫ ·) (congrArg (φ₀.hom.left ≫ ·) (IsPullback.isoPullback_inv_snd _))
          _ = (levelZeroPullbackIso I V).hom ≫
                ((pullback (Scheme.formalCompletion.toScheme X I 0)).obj V).obj.hom :=
            congrArg (_ ≫ ·) (Over.w φ₀.hom)
          _ = _ := IsPullback.isoPullback_hom_snd _
    let a := AdicThickeningSystem.liftOfEtale
      (Scheme.formalCompletion.map (I := I.comap V.obj.hom) V.obj.hom le_rfl)
      (Scheme.formalCompletion.map (I := I.comap W.obj.hom) W.obj.hom le_rfl) a₀ ha₀
    obtain ⟨g, hg, hg_map⟩ := Scheme.formalCompletion.exists_hom_of_finite_of_flat
      V.obj.hom W.obj.hom rfl rfl a
      (AdicThickeningSystem.liftOfEtale_comp _ _ a₀ ha₀)
    refine ⟨ObjectProperty.homMk (Over.homMk g hg), ?_⟩
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply (cancel_epi (levelZeroPullbackIso I V).hom).mp
    have hg₀ : (Scheme.formalCompletion.map (I := I.comap V.obj.hom) (J := I.comap W.obj.hom) g
        (by rw [← Scheme.IdealSheafData.comap_comp, hg])).app 0 = a₀ :=
      (congrArg (·.app 0) hg_map).trans
        (AdicThickeningSystem.liftOfEtale_app_zero _ _ a₀ ha₀)
    exact (levelZeroPullbackIso_hom_pullback_map I (ObjectProperty.homMk (Over.homMk g hg))).trans
      ((congrArg (· ≫ (levelZeroPullbackIso I W).hom) hg₀).trans
        (by simp only [a₀, Category.assoc, Iso.inv_hom_id, Category.comp_id]))

end LevelZero

section ClosedImmersion

/-- For a morphism `i : Z ⟶ X` with `i.ker = I`, `pullback i` factors up to natural isomorphism as
`pullback (toScheme X I 0)` followed by pullback along `IsClosedImmersion.lift`. -/
private noncomputable def pullbackClosedImmersionIso {Z X : Scheme.{u}} {i : Z ⟶ X}
    {I : X.IdealSheafData} (hi : i.ker = I) :
    pullback i ≅
      pullback (Scheme.formalCompletion.toScheme X I 0) ⋙
        pullback (IsClosedImmersion.lift (Scheme.formalCompletion.toScheme X I 0) i
          ((Scheme.formalCompletion.ker_toScheme X I 0).trans ((pow_one I).trans hi.symm)).le) :=
  eqToIso (congrArg pullback (IsClosedImmersion.lift_fac _ i _).symm) ≪≫ pullbackComp _ _

/-- **Faithfulness of finite étale pullback from formal completion** (Stacks, Lemma 58.17.1 (0EL8)):
let `i : Z ⟶ X` be a closed immersion with `i.ker = I`. If
`finiteLocallyFreeCompletionFunctor X I` is faithful, then `FiniteEtaleScheme.pullback i` is
faithful. -/
@[stacks 0EL8]
theorem faithful_pullback_of_ker_eq {Z X : Scheme.{u}} {i : Z ⟶ X} [IsClosedImmersion i]
    {I : X.IdealSheafData} (hi : i.ker = I)
    [(Scheme.formalCompletion.finiteLocallyFreeCompletionFunctor X I).Faithful] :
    (pullback i).Faithful := by
  have hker : (Scheme.formalCompletion.toScheme X I 0).ker = i.ker :=
    (Scheme.formalCompletion.ker_toScheme X I 0).trans ((pow_one I).trans hi.symm)
  have : IsIso (IsClosedImmersion.lift (Scheme.formalCompletion.toScheme X I 0) i hker.le) :=
    IsClosedImmersion.isIso_lift _ i hker
  exact Functor.Faithful.of_iso (pullbackClosedImmersionIso hi).symm

/-- **Fullness of finite étale pullback from formal completion** (Stacks, Lemma 58.17.1 (0EL8)):
let `i : Z ⟶ X` be a closed immersion with `i.ker = I`. If
`finiteLocallyFreeCompletionFunctor X I` is full and faithful, then `FiniteEtaleScheme.pullback i`
is full. -/
@[stacks 0EL8]
theorem full_pullback_of_ker_eq {Z X : Scheme.{u}} {i : Z ⟶ X} [IsClosedImmersion i]
    {I : X.IdealSheafData} (hi : i.ker = I)
    [(Scheme.formalCompletion.finiteLocallyFreeCompletionFunctor X I).Full]
    [(Scheme.formalCompletion.finiteLocallyFreeCompletionFunctor X I).Faithful] :
    (pullback i).Full := by
  have hker : (Scheme.formalCompletion.toScheme X I 0).ker = i.ker :=
    (Scheme.formalCompletion.ker_toScheme X I 0).trans ((pow_one I).trans hi.symm)
  have : IsIso (IsClosedImmersion.lift (Scheme.formalCompletion.toScheme X I 0) i hker.le) :=
    IsClosedImmersion.isIso_lift _ i hker
  exact Functor.Full.of_iso (pullbackClosedImmersionIso hi).symm

/-- **Full faithfulness of finite étale pullback from formal completion** (Stacks, Lemma 58.17.1
(0EL8)): let `i : Z ⟶ X` be a closed immersion with `i.ker = I`. If
`finiteLocallyFreeCompletionFunctor X I` is full and faithful, then `FiniteEtaleScheme.pullback i`
is fully faithful. -/
@[stacks 0EL8]
noncomputable def fullyFaithfulPullbackOfKerEq {Z X : Scheme.{u}} {i : Z ⟶ X}
    [IsClosedImmersion i] {I : X.IdealSheafData} (hi : i.ker = I)
    [(Scheme.formalCompletion.finiteLocallyFreeCompletionFunctor X I).Full]
    [(Scheme.formalCompletion.finiteLocallyFreeCompletionFunctor X I).Faithful] :
    (pullback i).FullyFaithful :=
  have := faithful_pullback_of_ker_eq hi
  have := full_pullback_of_ker_eq hi
  .ofFullyFaithful _

/-- If `finiteLocallyFreeCompletionFunctor X i.ker` is faithful for a closed immersion `i : Z ⟶ X`,
then `FiniteEtaleScheme.pullback i` is faithful. -/
@[stacks 0EL8]
instance faithful_pullback_of_isClosedImmersion {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i]
    [(Scheme.formalCompletion.finiteLocallyFreeCompletionFunctor X i.ker).Faithful] :
    (pullback i).Faithful :=
  faithful_pullback_of_ker_eq rfl

/-- If `finiteLocallyFreeCompletionFunctor X i.ker` is full and faithful for a closed immersion
`i : Z ⟶ X`, then `FiniteEtaleScheme.pullback i` is full. -/
@[stacks 0EL8]
instance full_pullback_of_isClosedImmersion {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i]
    [(Scheme.formalCompletion.finiteLocallyFreeCompletionFunctor X i.ker).Full]
    [(Scheme.formalCompletion.finiteLocallyFreeCompletionFunctor X i.ker).Faithful] :
    (pullback i).Full :=
  full_pullback_of_ker_eq rfl

/-- Bundled `FullyFaithful` structure on `FiniteEtaleScheme.pullback i` for a closed immersion
`i : Z ⟶ X` when `finiteLocallyFreeCompletionFunctor X i.ker` is full and faithful. -/
@[stacks 0EL8]
noncomputable def fullyFaithfulPullbackOfIsClosedImmersion {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i]
    [(Scheme.formalCompletion.finiteLocallyFreeCompletionFunctor X i.ker).Full]
    [(Scheme.formalCompletion.finiteLocallyFreeCompletionFunctor X i.ker).Faithful] :
    (pullback i).FullyFaithful :=
  .ofFullyFaithful _

/-- If `finiteLocallyFreeCompletionFunctor X I` is faithful, pullback of finite étale schemes along
`I.subschemeι : V(I) ⟶ X` is faithful. -/
@[stacks 0EL8]
instance faithful_pullback_subschemeι {X : Scheme.{u}} (I : X.IdealSheafData)
    [(Scheme.formalCompletion.finiteLocallyFreeCompletionFunctor X I).Faithful] :
    (pullback I.subschemeι).Faithful :=
  faithful_pullback_of_ker_eq (Scheme.IdealSheafData.ker_subschemeι I)

/-- If `finiteLocallyFreeCompletionFunctor X I` is full and faithful, pullback of finite étale
schemes along `I.subschemeι : V(I) ⟶ X` is full. -/
@[stacks 0EL8]
instance full_pullback_subschemeι {X : Scheme.{u}} (I : X.IdealSheafData)
    [(Scheme.formalCompletion.finiteLocallyFreeCompletionFunctor X I).Full]
    [(Scheme.formalCompletion.finiteLocallyFreeCompletionFunctor X I).Faithful] :
    (pullback I.subschemeι).Full :=
  full_pullback_of_ker_eq (Scheme.IdealSheafData.ker_subschemeι I)

/-- Bundled `FullyFaithful` structure on `FiniteEtaleScheme.pullback I.subschemeι` when
`finiteLocallyFreeCompletionFunctor X I` is full and faithful (Stacks, Lemma 58.17.1 (0EL8)). -/
@[stacks 0EL8]
noncomputable def fullyFaithfulPullbackSubschemeι {X : Scheme.{u}} (I : X.IdealSheafData)
    [(Scheme.formalCompletion.finiteLocallyFreeCompletionFunctor X I).Full]
    [(Scheme.formalCompletion.finiteLocallyFreeCompletionFunctor X I).Faithful] :
    (pullback I.subschemeι).FullyFaithful :=
  .ofFullyFaithful _

end ClosedImmersion

end TauCeti.FiniteEtaleScheme
