/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicThickeningSystem.CoherentFormalModule.Basic
public import TauCeti.AlgebraicGeometry.FiniteEtale.Fiber
import TauCeti.AlgebraicGeometry.AdicThickeningSystem.Etale
import TauCeti.AlgebraicGeometry.AdicThickeningSystem.FiniteLocallyFree

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
   (`Scheme.formalCompletion.hom_ext_of_isFinite_of_flat` and
   `Scheme.formalCompletion.exists_hom_of_isFinite_of_flat`): since a finite étale morphism is
   finite, flat, and locally of finite presentation, morphisms over `X` correspond bijectively to
   morphisms between formal completions over `X.formalCompletion I`.

Transporting from the zeroth infinitesimal level `toScheme X I 0 : V(I ^ 1) ⟶ X` to any closed
immersion `i : Z ⟶ X` with `i.ker = I` uses `IsClosedImmersion.isIso_lift` together with the fact
that `FiniteEtaleScheme.pullback u` is an equivalence for any isomorphism `u`.

## Main results

* `TauCeti.FiniteEtaleScheme.faithful_pullback_of_formalCompletion_of_ker_eq`,
  `TauCeti.FiniteEtaleScheme.full_pullback_of_formalCompletion_of_ker_eq`,
  `TauCeti.FiniteEtaleScheme.fullyFaithfulPullbackOfFormalCompletionOfKerEq`: Stacks, Lemma 58.17.1
  (0EL8) for an arbitrary closed immersion `i : Z ⟶ X` with `i.ker = I`.
* `TauCeti.FiniteEtaleScheme.faithful_pullback_subschemeι_of_formalCompletion`,
  `TauCeti.FiniteEtaleScheme.full_pullback_subschemeι_of_formalCompletion`: instances for the
  canonical closed subscheme inclusion `I.subschemeι : V(I) ⟶ X`.

## References

* [The Stacks Project, Lemma 58.17.1](https://stacks.math.columbia.edu/tag/0EL8).
-/

public section

open CategoryTheory Limits AlgebraicGeometry

universe u

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

/-- The first projection from `V ×_X V(I)` back to `V`, typed with domain
`((pullback (toScheme X I 0)).obj V).obj.left`. -/
private noncomputable def levelZeroPullbackFst {X : Scheme.{u}} (I : X.IdealSheafData)
    (V : FiniteEtaleScheme X) :
    ((pullback (Scheme.formalCompletion.toScheme X I 0)).obj V).obj.left ⟶ V.obj.left :=
  Limits.pullback.fst V.obj.hom (Scheme.formalCompletion.toScheme X I 0)

@[reassoc (attr := simp)]
private lemma levelZeroPullbackIso_hom_fst {X : Scheme.{u}} (I : X.IdealSheafData)
    (V : FiniteEtaleScheme X) :
    (levelZeroPullbackIso I V).hom ≫ levelZeroPullbackFst I V =
      Scheme.formalCompletion.toScheme V.obj.left (I.comap V.obj.hom) 0 :=
  IsPullback.isoPullback_hom_fst _

@[reassoc (attr := simp)]
private lemma levelZeroPullbackIso_hom_obj_hom {X : Scheme.{u}} (I : X.IdealSheafData)
    (V : FiniteEtaleScheme X) :
    (levelZeroPullbackIso I V).hom ≫
        ((pullback (Scheme.formalCompletion.toScheme X I 0)).obj V).obj.hom =
      (Scheme.formalCompletion.map (I := I.comap V.obj.hom) V.obj.hom le_rfl).app 0 := by
  have hhom : ((pullback (Scheme.formalCompletion.toScheme X I 0)).obj V).obj.hom =
      Limits.pullback.snd V.obj.hom (Scheme.formalCompletion.toScheme X I 0) :=
    Over.pullback_obj_hom _ _
  rw [hhom]
  exact IsPullback.isoPullback_hom_snd _

@[reassoc (attr := simp)]
private lemma levelZeroPullbackIso_inv_obj_hom {X : Scheme.{u}} (I : X.IdealSheafData)
    (V : FiniteEtaleScheme X) :
    (levelZeroPullbackIso I V).inv ≫
        (Scheme.formalCompletion.map (I := I.comap V.obj.hom) V.obj.hom le_rfl).app 0 =
      ((pullback (Scheme.formalCompletion.toScheme X I 0)).obj V).obj.hom := by
  have hhom : ((pullback (Scheme.formalCompletion.toScheme X I 0)).obj V).obj.hom =
      Limits.pullback.snd V.obj.hom (Scheme.formalCompletion.toScheme X I 0) :=
    Over.pullback_obj_hom _ _
  rw [hhom]
  exact IsPullback.isoPullback_inv_snd _

private lemma levelZeroPullbackIso_hom_pullback_map {X : Scheme.{u}} (I : X.IdealSheafData)
    {V W : FiniteEtaleScheme X} (g : V ⟶ W) :
    (levelZeroPullbackIso I V).hom ≫
        ((pullback (Scheme.formalCompletion.toScheme X I 0)).map g).hom.left =
      (Scheme.formalCompletion.map (I := I.comap V.obj.hom) (J := I.comap W.obj.hom) g.hom.left
        (by rw [← Scheme.IdealSheafData.comap_comp, Over.w g.hom])).app 0 ≫
        (levelZeroPullbackIso I W).hom := by
  have hpb : IsPullback (levelZeroPullbackFst I W)
      ((pullback (Scheme.formalCompletion.toScheme X I 0)).obj W).obj.hom
      W.obj.hom (Scheme.formalCompletion.toScheme X I 0) :=
    IsPullback.of_hasPullback W.obj.hom (Scheme.formalCompletion.toScheme X I 0)
  refine hpb.hom_ext ?_ ?_
  · have hmap : ((pullback (Scheme.formalCompletion.toScheme X I 0)).map g).hom.left =
        Limits.pullback.lift
          (Limits.pullback.fst V.obj.hom (Scheme.formalCompletion.toScheme X I 0) ≫ g.hom.left)
          (Limits.pullback.snd V.obj.hom (Scheme.formalCompletion.toScheme X I 0))
          (by simp [Limits.pullback.condition]) :=
      Over.pullback_map_left _ _
    have hfst : ((pullback (Scheme.formalCompletion.toScheme X I 0)).map g).hom.left ≫
        levelZeroPullbackFst I W = levelZeroPullbackFst I V ≫ g.hom.left :=
      (congrArg (· ≫ _) hmap).trans (Limits.pullback.lift_fst _ _ _)
    rw [Category.assoc, hfst, Category.assoc, levelZeroPullbackIso_hom_fst_assoc,
      levelZeroPullbackIso_hom_fst, Scheme.formalCompletion.map_app_toScheme]
  · have hcomp : Scheme.formalCompletion.map (I := I.comap V.obj.hom) (J := I.comap W.obj.hom)
          g.hom.left (by rw [← Scheme.IdealSheafData.comap_comp, Over.w g.hom]) ≫
          Scheme.formalCompletion.map (I := I.comap W.obj.hom) W.obj.hom le_rfl =
        Scheme.formalCompletion.map (I := I.comap V.obj.hom) V.obj.hom le_rfl :=
      Scheme.formalCompletion.map_comp_eq (Over.w g.hom) _ le_rfl le_rfl
    rw [Category.assoc, Over.w ((pullback (Scheme.formalCompletion.toScheme X I 0)).map g).hom,
      levelZeroPullbackIso_hom_obj_hom, Category.assoc, levelZeroPullbackIso_hom_obj_hom,
      ← AdicThickeningSystem.comp_app, hcomp]

/-- If `finiteLocallyFreeCompletionFunctor X I` is faithful, pullback of finite étale schemes from
`X` to the zeroth infinitesimal level `V(I ^ 1)` of `X.formalCompletion I` is faithful. -/
private lemma faithful_pullback_toScheme_zero {X : Scheme.{u}} (I : X.IdealSheafData)
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
      ((Scheme.formalCompletion.map_comp_eq (Over.w g₁.hom) _ le_rfl le_rfl).trans
        (Scheme.formalCompletion.map_comp_eq (Over.w g₂.hom) _ le_rfl le_rfl).symm) h0
    exact Scheme.formalCompletion.hom_ext_of_isFinite_of_flat V.obj.hom W.obj.hom rfl rfl
      (Over.w g₁.hom) (Over.w g₂.hom) hmap

/-- If `finiteLocallyFreeCompletionFunctor X I` is full and faithful, pullback of finite étale
schemes from `X` to the zeroth infinitesimal level `V(I ^ 1)` of `X.formalCompletion I` is full. -/
private lemma full_pullback_toScheme_zero {X : Scheme.{u}} (I : X.IdealSheafData)
    [(Scheme.formalCompletion.finiteLocallyFreeCompletionFunctor X I).Full]
    [(Scheme.formalCompletion.finiteLocallyFreeCompletionFunctor X I).Faithful] :
    (pullback (Scheme.formalCompletion.toScheme X I 0)).Full where
  map_surjective {V W} φ₀ := by
    let a₀ : (V.obj.left.formalCompletion (I.comap V.obj.hom)).X 0 ⟶
        (W.obj.left.formalCompletion (I.comap W.obj.hom)).X 0 :=
      (levelZeroPullbackIso I V).hom ≫ φ₀.hom.left ≫ (levelZeroPullbackIso I W).inv
    have ha₀ : a₀ ≫ (Scheme.formalCompletion.map (I := I.comap W.obj.hom)
        W.obj.hom le_rfl).app 0 =
        (Scheme.formalCompletion.map (I := I.comap V.obj.hom) V.obj.hom le_rfl).app 0 := by
      simp [a₀, Over.w φ₀.hom]
    let a := AdicThickeningSystem.liftOfEtale
      (Scheme.formalCompletion.map (I := I.comap V.obj.hom) V.obj.hom le_rfl)
      (Scheme.formalCompletion.map (I := I.comap W.obj.hom) W.obj.hom le_rfl) a₀ ha₀
    obtain ⟨g, hg, hg_map⟩ := Scheme.formalCompletion.exists_hom_of_isFinite_of_flat
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
theorem faithful_pullback_of_formalCompletion_of_ker_eq {Z X : Scheme.{u}} {i : Z ⟶ X}
    [IsClosedImmersion i] {I : X.IdealSheafData} (hi : i.ker = I)
    [(Scheme.formalCompletion.finiteLocallyFreeCompletionFunctor X I).Faithful] :
    (pullback i).Faithful := by
  have := faithful_pullback_toScheme_zero I
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
theorem full_pullback_of_formalCompletion_of_ker_eq {Z X : Scheme.{u}} {i : Z ⟶ X}
    [IsClosedImmersion i] {I : X.IdealSheafData} (hi : i.ker = I)
    [(Scheme.formalCompletion.finiteLocallyFreeCompletionFunctor X I).Full]
    [(Scheme.formalCompletion.finiteLocallyFreeCompletionFunctor X I).Faithful] :
    (pullback i).Full := by
  have := full_pullback_toScheme_zero I
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
noncomputable def fullyFaithfulPullbackOfFormalCompletionOfKerEq {Z X : Scheme.{u}} {i : Z ⟶ X}
    [IsClosedImmersion i] {I : X.IdealSheafData} (hi : i.ker = I)
    [(Scheme.formalCompletion.finiteLocallyFreeCompletionFunctor X I).Full]
    [(Scheme.formalCompletion.finiteLocallyFreeCompletionFunctor X I).Faithful] :
    (pullback i).FullyFaithful :=
  have := faithful_pullback_of_formalCompletion_of_ker_eq hi
  have := full_pullback_of_formalCompletion_of_ker_eq hi
  .ofFullyFaithful _

/-- If `finiteLocallyFreeCompletionFunctor X I` is faithful, pullback of finite étale schemes along
`I.subschemeι : V(I) ⟶ X` is faithful. -/
@[stacks 0EL8]
instance faithful_pullback_subschemeι_of_formalCompletion {X : Scheme.{u}} (I : X.IdealSheafData)
    [(Scheme.formalCompletion.finiteLocallyFreeCompletionFunctor X I).Faithful] :
    (pullback I.subschemeι).Faithful :=
  faithful_pullback_of_formalCompletion_of_ker_eq (Scheme.IdealSheafData.ker_subschemeι I)

/-- If `finiteLocallyFreeCompletionFunctor X I` is full and faithful, pullback of finite étale
schemes along `I.subschemeι : V(I) ⟶ X` is full. -/
@[stacks 0EL8]
instance full_pullback_subschemeι_of_formalCompletion {X : Scheme.{u}} (I : X.IdealSheafData)
    [(Scheme.formalCompletion.finiteLocallyFreeCompletionFunctor X I).Full]
    [(Scheme.formalCompletion.finiteLocallyFreeCompletionFunctor X I).Faithful] :
    (pullback I.subschemeι).Full :=
  full_pullback_of_formalCompletion_of_ker_eq (Scheme.IdealSheafData.ker_subschemeι I)

end ClosedImmersion

end TauCeti.FiniteEtaleScheme
