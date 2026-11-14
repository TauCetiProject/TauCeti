/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicThickeningSystem.CoherentFormalModule
public import TauCeti.AlgebraicGeometry.FiniteEtale.Fiber
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
import TauCeti.AlgebraicGeometry.AdicThickeningSystem.Algebraization
import TauCeti.AlgebraicGeometry.AdicThickeningSystem.Etale
import TauCeti.AlgebraicGeometry.FiniteEtale.MorphismProperty
import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Pushforward.Finite
import TauCeti.AlgebraicGeometry.Modules.Tensor.Product

/-!
# Formal comparison for morphisms of finite étale schemes

Let `X` be a scheme and `i : Z ⟶ X` a closed immersion cut out by an ideal sheaf `I`. When the
completion functor `Scheme.formalCompletion.completionFunctor X I`, from finitely presented
`𝒪_X`-modules to coherent formal modules on the formal completion `X.formalCompletion I`, is full
and faithful, base change of finite étale schemes along `i` is fully faithful (Stacks, Lemma
58.17.1 (0EL8)): every morphism `Y₁ ×_X Z ⟶ Y₂ ×_X Z` over `Z` between restrictions of finite
étale `X`-schemes comes from a unique morphism `Y₁ ⟶ Y₂` over `X`. Faithfulness of
`completionFunctor X I` alone suffices for faithfulness of base change along `i`.

The proof combines two ingredients that require neither Noetherian nor flatness hypotheses:

* **Infinitesimal lifting.** For finite étale `X`-schemes `Y₁, Y₂`, the levels of
  `Y₂.formalCompletion (I.comap p₂) ⟶ X.formalCompletion I` are base changes of `p₂`, hence étale.
  By `AdicThickeningSystem.existsUnique_hom_of_etale`, a morphism between the initial levels lifts
  uniquely to a morphism of formal completions over `X.formalCompletion I`.
* **Algebraization.** Since a finite étale morphism `p : Y ⟶ X` is affine, finite and locally of
  finite presentation, its coordinate algebra `p_* 𝒪_Y` is a finitely presented `𝒪_X`-module
  (`Modules.isFinitePresentation_pushforward_of_locallyOfFinitePresentation`).
  Full faithfulness of `completionFunctor X I` therefore algebraizes the lifted morphism of formal
  completions to a unique morphism `Y₁ ⟶ Y₂` over `X`
  (`AlgebraicGeometry.Scheme.formalCompletion.existsUnique_hom_of_formalCompletion`).

Comparing the arbitrary closed immersion `i` with `V(I) ⟶ X`, which is level `0` of
`X.formalCompletion I`, transports full faithfulness to `FiniteEtaleScheme.pullback i` and to
Mathlib's `MorphismProperty.Over.pullback (@IsFinite ⊓ @Etale) ⊤ i`.

## Main results

* `TauCeti.FiniteEtaleScheme.faithful_pullback_of_isClosedImmersion`: if `completionFunctor X I`
  is faithful and `i : Z ⟶ X` is a closed immersion with `i.ker = I`, then
  `FiniteEtaleScheme.pullback i` is faithful.
* `TauCeti.FiniteEtaleScheme.full_pullback_of_isClosedImmersion` and
  `TauCeti.FiniteEtaleScheme.fullyFaithfulPullbackOfIsClosedImmersion`: if `completionFunctor X I`
  is full and faithful, then `FiniteEtaleScheme.pullback i` is full and fully faithful (Stacks
  0EL8).
* `TauCeti.FiniteEtaleScheme.faithful_pullback_subschemeι`,
  `TauCeti.FiniteEtaleScheme.full_pullback_subschemeι`,
  `TauCeti.FiniteEtaleScheme.faithful_pullback_of_isClosedImmersion_ker`, and
  `TauCeti.FiniteEtaleScheme.full_pullback_of_isClosedImmersion_ker`: typeclass instances for
  `I.subschemeι` and for arbitrary closed immersions via `i.ker`.
* `AlgebraicGeometry.Scheme.Hom.finiteEtalePullback_faithful_of_isClosedImmersion`,
  `AlgebraicGeometry.Scheme.Hom.finiteEtalePullback_full_of_isClosedImmersion`, and
  `AlgebraicGeometry.Scheme.Hom.finiteEtalePullbackFullyFaithful`: the corresponding statements
  for `MorphismProperty.Over.pullback (@IsFinite ⊓ @Etale) ⊤ i`.

## References

* [The Stacks Project, Lemma 58.17.1](https://stacks.math.columbia.edu/tag/0EL8).
* A. Grothendieck, *Cohomologie locale des faisceaux cohérents et théorèmes de Lefschetz locaux et
  globaux* (SGA 2), Exposé X, §2.
-/

public section

open CategoryTheory Limits AlgebraicGeometry
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.AdicThickeningSystem

universe u

/-- The morphism of formal completions induced by an étale morphism `p : Y ⟶ X`, for the inverse
image of an ideal sheaf on `X`, is étale at every level. -/
instance AlgebraicGeometry.Scheme.formalCompletion.etale_map_app {X Y : Scheme.{u}} (p : Y ⟶ X)
    [Etale p] {I : X.IdealSheafData} (n : ℕ) :
    Etale ((Scheme.formalCompletion.map (I := I.comap p) p le_rfl).app n) :=
  MorphismProperty.of_isPullback (P := @Etale)
    (Scheme.formalCompletion.isPullback_map_app p rfl n) ‹_›

namespace TauCeti.FiniteEtaleScheme

section FormalCompletion

variable {X Z : Scheme.{u}}

/-- On level `0`, the morphism of formal completions induced by a morphism `g : Y₁ ⟶ Y₂` of finite
étale `X`-schemes agrees with `(Over.pullback (toScheme X I 0)).map g.hom` under the pullback
isomorphisms of `isPullback_map_app`. -/
private lemma formalCompletion_map_app_zero_comp_isoPullback (I : X.IdealSheafData)
    {Y₁ Y₂ : FiniteEtaleScheme X} (g : Y₁ ⟶ Y₂) :
    (Scheme.formalCompletion.map (I := I.comap Y₁.obj.hom) (J := I.comap Y₂.obj.hom) g.hom.left
        (by rw [← Scheme.IdealSheafData.comap_comp, Over.w])).app 0 ≫
      (Scheme.formalCompletion.isPullback_map_app Y₂.obj.hom (J := I) rfl 0).isoPullback.hom =
      (Scheme.formalCompletion.isPullback_map_app Y₁.obj.hom (J := I) rfl 0).isoPullback.hom ≫
        ((Over.pullback (Scheme.formalCompletion.toScheme X I 0)).map g.hom).left := by
  apply Limits.pullback.hom_ext
  · rw [Category.assoc, IsPullback.isoPullback_hom_fst, Scheme.formalCompletion.map_app_toScheme]
    simp [IsPullback.isoPullback_hom_fst_assoc]
  · rw [Category.assoc, IsPullback.isoPullback_hom_snd, ← AdicThickeningSystem.comp_app,
      Scheme.formalCompletion.map_comp,
      Scheme.formalCompletion.map_congr (Over.w g.hom) _ le_rfl]
    simp [IsPullback.isoPullback_hom_snd]

/-- Base change of finite étale `X`-schemes to level `0` of `X.formalCompletion I` is faithful
when `completionFunctor X I` is faithful. -/
private lemma faithful_pullback_toScheme_zero (I : X.IdealSheafData)
    [(Scheme.formalCompletion.completionFunctor X I).Faithful] :
    (pullback (Scheme.formalCompletion.toScheme X I 0)).Faithful where
  map_injective {Y₁ Y₂} g₁ g₂ h := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply Scheme.formalCompletion.hom_ext_of_map_eq (I := I) Y₁.obj.hom Y₂.obj.hom
      (Over.w g₁.hom) (Over.w g₂.hom)
    let π₂ := Scheme.formalCompletion.map (I := I.comap Y₂.obj.hom) Y₂.obj.hom le_rfl
    apply AdicThickeningSystem.hom_ext_of_formallyUnramified π₂
    · simp only [π₂, Scheme.formalCompletion.map_comp]
      exact Scheme.formalCompletion.map_congr ((Over.w g₁.hom).trans (Over.w g₂.hom).symm) _ _
    · have h' : (Over.pullback (Scheme.formalCompletion.toScheme X I 0)).map g₁.hom =
          (Over.pullback (Scheme.formalCompletion.toScheme X I 0)).map g₂.hom :=
        (pullback_map_hom _ g₁).symm.trans
          ((congrArg (fun u ↦ u.hom) h).trans (pullback_map_hom _ g₂))
      refine (cancel_mono
        (Scheme.formalCompletion.isPullback_map_app Y₂.obj.hom (J := I) rfl 0).isoPullback.hom).mp
          ?_
      rw [formalCompletion_map_app_zero_comp_isoPullback,
        formalCompletion_map_app_zero_comp_isoPullback, h']

/-- Base change of finite étale `X`-schemes to level `0` of `X.formalCompletion I` is full when
`completionFunctor X I` is full and faithful. -/
private lemma full_pullback_toScheme_zero (I : X.IdealSheafData)
    [(Scheme.formalCompletion.completionFunctor X I).Full]
    [(Scheme.formalCompletion.completionFunctor X I).Faithful] :
    (pullback (Scheme.formalCompletion.toScheme X I 0)).Full where
  map_surjective {Y₁ Y₂} φ := by
    let φ' : (Over.pullback (Scheme.formalCompletion.toScheme X I 0)).obj Y₁.obj ⟶
        (Over.pullback (Scheme.formalCompletion.toScheme X I 0)).obj Y₂.obj := φ.hom
    let H₁ := Scheme.formalCompletion.isPullback_map_app Y₁.obj.hom (J := I) rfl 0
    let H₂ := Scheme.formalCompletion.isPullback_map_app Y₂.obj.hom (J := I) rfl 0
    let π₁ := Scheme.formalCompletion.map (I := I.comap Y₁.obj.hom) Y₁.obj.hom le_rfl
    let π₂ := Scheme.formalCompletion.map (I := I.comap Y₂.obj.hom) Y₂.obj.hom le_rfl
    let a₀ := H₁.isoPullback.hom ≫ φ'.left ≫ H₂.isoPullback.inv
    have ha₀ : a₀ ≫ π₂.app 0 = π₁.app 0 := by
      have hw : φ'.left ≫ Limits.pullback.snd Y₂.obj.hom
          (Scheme.formalCompletion.toScheme X I 0) =
          Limits.pullback.snd Y₁.obj.hom (Scheme.formalCompletion.toScheme X I 0) :=
        Over.w φ'
      dsimp only [a₀, π₁, π₂]
      rw [Category.assoc, Category.assoc, H₂.isoPullback_inv_snd, hw, H₁.isoPullback_hom_snd]
    let a := AdicThickeningSystem.liftOfEtale π₁ π₂ a₀ ha₀
    let g₀ := Scheme.formalCompletion.liftOfFormalCompletion (I := I) Y₁.obj.hom Y₂.obj.hom a
      (AdicThickeningSystem.liftOfEtale_comp π₁ π₂ a₀ ha₀)
    let g : Y₁ ⟶ Y₂ := ObjectProperty.homMk (Over.homMk g₀
      (Scheme.formalCompletion.liftOfFormalCompletion_comp (I := I) Y₁.obj.hom Y₂.obj.hom a _))
    refine ⟨g, ObjectProperty.hom_ext _ ?_⟩
    rw [pullback_map_hom]
    apply Over.OverMorphism.ext
    refine (cancel_epi H₁.isoPullback.hom).mp ?_
    rw [← formalCompletion_map_app_zero_comp_isoPullback I g]
    have hg₀ : Scheme.formalCompletion.map (I := I.comap Y₁.obj.hom) (J := I.comap Y₂.obj.hom)
        g.hom.left (by rw [← Scheme.IdealSheafData.comap_comp, Over.w]) = a :=
      Scheme.formalCompletion.map_liftOfFormalCompletion (I := I) Y₁.obj.hom Y₂.obj.hom a _
    rw [hg₀, AdicThickeningSystem.liftOfEtale_app_zero]
    dsimp only [a₀]
    rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- For a closed immersion `i : Z ⟶ X` with `i.ker = I`, base change along `i` factors through
base change to level `0` of `X.formalCompletion I` followed by an equivalence. -/
private lemma pullbackIsoCompPullbackToSchemeZero (i : Z ⟶ X) [IsClosedImmersion i]
    (I : X.IdealSheafData) (hi : i.ker = I) :
    ∃ (e : Z ⟶ (X.formalCompletion I).X 0) (_ : IsIso e),
      Nonempty (pullback i ≅ pullback (Scheme.formalCompletion.toScheme X I 0) ⋙ pullback e) := by
  have hker : (Scheme.formalCompletion.toScheme X I 0).ker = i.ker := by
    rw [Scheme.formalCompletion.ker_toScheme, pow_one, hi]
  let e : Z ⟶ (X.formalCompletion I).X 0 :=
    IsClosedImmersion.lift (Scheme.formalCompletion.toScheme X I 0) i hker.le
  have : IsIso e :=
    @IsClosedImmersion.isIso_lift _ _ _ _ _ _ _ hker
  exact ⟨e, inferInstance, ⟨(pullbackCongr (IsClosedImmersion.lift_fac _ _ _)).symm ≪≫
    pullbackComp e (Scheme.formalCompletion.toScheme X I 0)⟩⟩

/-- **Faithfulness of finite étale restriction to a closed subscheme.** Let `i : Z ⟶ X` be a
closed immersion with ideal sheaf `I`. If the completion functor `completionFunctor X I` on
finitely presented `𝒪_X`-modules is faithful, then `FiniteEtaleScheme.pullback i` is faithful. -/
@[stacks 0EL8 "faithfulness"]
theorem faithful_pullback_of_isClosedImmersion (i : Z ⟶ X) [IsClosedImmersion i]
    (I : X.IdealSheafData) (hi : i.ker = I)
    [(Scheme.formalCompletion.completionFunctor X I).Faithful] :
    (pullback i).Faithful := by
  obtain ⟨e, _, ⟨iso⟩⟩ := pullbackIsoCompPullbackToSchemeZero i I hi
  have := faithful_pullback_toScheme_zero I
  exact Functor.Faithful.of_iso iso.symm

/-- **Formal comparison for morphisms of finite étale schemes (fullness).** Let `i : Z ⟶ X` be a
closed immersion with ideal sheaf `I`. If `completionFunctor X I` is full and faithful, then
`FiniteEtaleScheme.pullback i` is full. Stacks, Lemma 58.17.1 (0EL8). -/
@[stacks 0EL8 "fullness"]
theorem full_pullback_of_isClosedImmersion (i : Z ⟶ X) [IsClosedImmersion i]
    (I : X.IdealSheafData) (hi : i.ker = I)
    [(Scheme.formalCompletion.completionFunctor X I).Full]
    [(Scheme.formalCompletion.completionFunctor X I).Faithful] :
    (pullback i).Full := by
  obtain ⟨e, _, ⟨iso⟩⟩ := pullbackIsoCompPullbackToSchemeZero i I hi
  have := full_pullback_toScheme_zero I
  exact Functor.Full.of_iso iso.symm

/-- **Formal comparison for morphisms of finite étale schemes.** Let `i : Z ⟶ X` be a closed
immersion with ideal sheaf `I`. If `completionFunctor X I` is full and faithful, then
`FiniteEtaleScheme.pullback i` is fully faithful. Stacks, Lemma 58.17.1 (0EL8). -/
@[stacks 0EL8]
noncomputable def fullyFaithfulPullbackOfIsClosedImmersion (i : Z ⟶ X) [IsClosedImmersion i]
    (I : X.IdealSheafData) (hi : i.ker = I)
    [(Scheme.formalCompletion.completionFunctor X I).Full]
    [(Scheme.formalCompletion.completionFunctor X I).Faithful] :
    (pullback i).FullyFaithful :=
  haveI := faithful_pullback_of_isClosedImmersion i I hi
  haveI := full_pullback_of_isClosedImmersion i I hi
  .ofFullyFaithful _

/-- Restriction of finite étale `X`-schemes to `V(I)` is faithful when `completionFunctor X I` is
faithful. -/
@[stacks 0EL8 "faithfulness"]
instance faithful_pullback_subschemeι (I : X.IdealSheafData)
    [(Scheme.formalCompletion.completionFunctor X I).Faithful] :
    (pullback I.subschemeι).Faithful :=
  faithful_pullback_of_isClosedImmersion I.subschemeι I (Scheme.IdealSheafData.ker_subschemeι I)

/-- Restriction of finite étale `X`-schemes to `V(I)` is full when `completionFunctor X I` is full
and faithful. -/
@[stacks 0EL8 "fullness"]
instance full_pullback_subschemeι (I : X.IdealSheafData)
    [(Scheme.formalCompletion.completionFunctor X I).Full]
    [(Scheme.formalCompletion.completionFunctor X I).Faithful] :
    (pullback I.subschemeι).Full :=
  full_pullback_of_isClosedImmersion I.subschemeι I (Scheme.IdealSheafData.ker_subschemeι I)

/-- Restriction of finite étale `X`-schemes to `V(I)` is fully faithful when
`completionFunctor X I` is full and faithful. Stacks, Lemma 58.17.1 (0EL8). -/
@[stacks 0EL8]
noncomputable def fullyFaithfulPullbackSubschemeι (I : X.IdealSheafData)
    [(Scheme.formalCompletion.completionFunctor X I).Full]
    [(Scheme.formalCompletion.completionFunctor X I).Faithful] :
    (pullback I.subschemeι).FullyFaithful :=
  .ofFullyFaithful _

/-- Base change of finite étale `X`-schemes along a closed immersion `i : Z ⟶ X` is faithful when
`completionFunctor X i.ker` is faithful. -/
@[stacks 0EL8 "faithfulness"]
instance faithful_pullback_of_isClosedImmersion_ker (i : Z ⟶ X) [IsClosedImmersion i]
    [(Scheme.formalCompletion.completionFunctor X i.ker).Faithful] :
    (pullback i).Faithful :=
  faithful_pullback_of_isClosedImmersion i i.ker rfl

/-- Base change of finite étale `X`-schemes along a closed immersion `i : Z ⟶ X` is full when
`completionFunctor X i.ker` is full and faithful. -/
@[stacks 0EL8 "fullness"]
instance full_pullback_of_isClosedImmersion_ker (i : Z ⟶ X) [IsClosedImmersion i]
    [(Scheme.formalCompletion.completionFunctor X i.ker).Full]
    [(Scheme.formalCompletion.completionFunctor X i.ker).Faithful] :
    (pullback i).Full :=
  full_pullback_of_isClosedImmersion i i.ker rfl

/-- Base change of finite étale `X`-schemes along a closed immersion `i : Z ⟶ X` is fully faithful
when `completionFunctor X i.ker` is full and faithful. Stacks, Lemma 58.17.1 (0EL8). -/
@[stacks 0EL8]
noncomputable def fullyFaithfulPullbackOfIsClosedImmersionKer (i : Z ⟶ X) [IsClosedImmersion i]
    [(Scheme.formalCompletion.completionFunctor X i.ker).Full]
    [(Scheme.formalCompletion.completionFunctor X i.ker).Faithful] :
    (pullback i).FullyFaithful :=
  .ofFullyFaithful _

end FormalCompletion

end TauCeti.FiniteEtaleScheme

namespace AlgebraicGeometry.Scheme.Hom

open TauCeti.FiniteEtaleScheme

variable {X Z : Scheme.{u}}

private noncomputable def overPullbackIso (i : Z ⟶ X) :
    letI : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).IsStableUnderBaseChange := .inf
    ((equivOver X).inverse ⋙ pullback i) ⋙ (equivOver Z).functor ≅
      MorphismProperty.Over.pullback (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}) ⊤ i :=
  letI : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).IsStableUnderBaseChange := .inf
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (equivOver X).inverse (pullbackCompEquivOver i) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (equivOver X).counitIso _ ≪≫
    Functor.leftUnitor _

/-- Base change of finite étale schemes along a closed immersion `i : Z ⟶ X` with `i.ker = I` is
faithful when `completionFunctor X I` is faithful. -/
@[stacks 0EL8 "faithfulness"]
theorem finiteEtalePullback_faithful_of_isClosedImmersion (i : Z ⟶ X) [IsClosedImmersion i]
    (I : X.IdealSheafData) (hi : i.ker = I)
    [(Scheme.formalCompletion.completionFunctor X I).Faithful] :
    letI : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).IsStableUnderBaseChange := .inf
    (MorphismProperty.Over.pullback
      (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}) ⊤ i).Faithful := by
  let : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).IsStableUnderBaseChange := .inf
  have := faithful_pullback_of_isClosedImmersion i I hi
  exact Functor.Faithful.of_iso (overPullbackIso i)

/-- Base change of finite étale schemes along a closed immersion `i : Z ⟶ X` with `i.ker = I` is
full when `completionFunctor X I` is full and faithful. Stacks, Lemma 58.17.1 (0EL8). -/
@[stacks 0EL8 "fullness"]
theorem finiteEtalePullback_full_of_isClosedImmersion (i : Z ⟶ X) [IsClosedImmersion i]
    (I : X.IdealSheafData) (hi : i.ker = I)
    [(Scheme.formalCompletion.completionFunctor X I).Full]
    [(Scheme.formalCompletion.completionFunctor X I).Faithful] :
    letI : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).IsStableUnderBaseChange := .inf
    (MorphismProperty.Over.pullback
      (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}) ⊤ i).Full := by
  let : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).IsStableUnderBaseChange := .inf
  have := full_pullback_of_isClosedImmersion i I hi
  exact Functor.Full.of_iso (overPullbackIso i)

/-- **Formal comparison for morphisms of finite étale schemes** in Mathlib's morphism-property
over-category: base change along a closed immersion `i : Z ⟶ X` with `i.ker = I` is fully faithful
when `completionFunctor X I` is full and faithful. Stacks, Lemma 58.17.1 (0EL8). -/
@[stacks 0EL8]
noncomputable def finiteEtalePullbackFullyFaithful (i : Z ⟶ X) [IsClosedImmersion i]
    (I : X.IdealSheafData) (hi : i.ker = I)
    [(Scheme.formalCompletion.completionFunctor X I).Full]
    [(Scheme.formalCompletion.completionFunctor X I).Faithful] :
    letI : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).IsStableUnderBaseChange := .inf
    (MorphismProperty.Over.pullback
      (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}) ⊤ i).FullyFaithful :=
  letI : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).IsStableUnderBaseChange := .inf
  haveI := finiteEtalePullback_faithful_of_isClosedImmersion i I hi
  haveI := finiteEtalePullback_full_of_isClosedImmersion i I hi
  .ofFullyFaithful _

end AlgebraicGeometry.Scheme.Hom
