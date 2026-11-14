/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Morphisms.FiniteEtale

import Mathlib.RingTheory.Etale.Basic
import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.LocallyOfFiniteType.Local
import TauCeti.Topology.Algebra.Nonarchimedean.Quotient
import TauCeti.Topology.Algebra.Ring.Ideal

/-!
# Étale morphisms of analytic adic spaces

A morphism `f : Y ⟶ X` of analytic adic spaces is *étale* in the local-factorisation sense of
Kedlaya–Liu and Scholze (`TauCeti.AdicSpace.IsEtaleLocalDescription`) when `X` and `Y` are analytic
and every point `y` of `Y` has an open neighbourhood `U` over which `f` factors as an open immersion
`j : U ⟶ W`, followed by a finite étale morphism `g : W ⟶ V`, followed by an open immersion
`i : V ⟶ X`. Neither locally noetherian hypotheses nor separatedness are imposed. The name
`IsEtaleLocalDescription` distinguishes this local-factorisation notion on general analytic adic
spaces from Huber's infinitesimal criterion on locally noetherian spaces.

Finite étale morphisms (`IsEtaleLocalDescription.of_isFiniteEtale`) and open immersions into
analytic adic spaces (`IsEtaleLocalDescription.of_isOpenImmersion`) are étale. The property is
invariant under source and target isomorphisms, stable under precomposing or postcomposing with open
immersions, and local on the source (`IsEtaleLocalDescription.of_jointly_surjective`). Refining the
finite étale middle factor to a complete Hausdorff Tate affinoid chart puts every étale morphism
locally into standard affinoid form (`IsEtaleLocalDescription.exists_affinoid_factorisation`).

Consequently, étale morphisms are locally of finite type
(`IsEtaleLocalDescription.locallyOfFiniteType`) and carry locally noetherian analytic structure from
target to source (`IsEtaleLocalDescription.isLocallyNoetherianAnalytic_source`). Moreover, they
satisfy Huber's infinitesimal lifting property along square-zero quotients by closed ideals of
complete Hausdorff sheafy Huber pairs with singleton spectrum
(`IsEtaleLocalDescription.existsUnique_of_sqZero_quotient`): this obstructs both ramified finite
morphisms such as `T ↦ S²` (failure of uniqueness) and unramified closed immersions such as
`{T = 0}` into the closed unit disc (failure of existence).

## Main definitions

* `TauCeti.AdicSpace.IsEtaleLocalDescription`: étale morphisms of analytic adic spaces via local
  factorisation through finite étale morphisms and open immersions.

## Main results

* `TauCeti.AdicSpace.IsEtaleLocalDescription.of_isFiniteEtale` and
  `TauCeti.AdicSpace.IsEtaleLocalDescription.of_isOpenImmersion`: finite étale morphisms and open
  immersions into analytic adic spaces are étale.
* `TauCeti.AdicSpace.IsEtaleLocalDescription.respectsIso`,
  `TauCeti.AdicSpace.IsEtaleLocalDescription.isOpenImmersion_comp`,
  `TauCeti.AdicSpace.IsEtaleLocalDescription.comp_isOpenImmersion`, and
  `TauCeti.AdicSpace.IsEtaleLocalDescription.of_jointly_surjective`: invariance under isomorphisms,
  stability under open immersions, and source locality.
* `TauCeti.AdicSpace.IsEtaleLocalDescription.exists_affinoid_factorisation`: refinement of local
  factorisations to complete Hausdorff Tate affinoid pairs.
* `TauCeti.AdicSpace.IsEtaleLocalDescription.locallyOfFiniteType` and
  `TauCeti.AdicSpace.IsEtaleLocalDescription.isLocallyNoetherianAnalytic_source`: finiteness and
  ascent of locally noetherian analytic structure.
* `TauCeti.AdicSpace.IsEtaleLocalDescription.eq_of_sqZero_quotient`,
  `TauCeti.AdicSpace.IsEtaleLocalDescription.exists_of_sqZero_quotient`, and
  `TauCeti.AdicSpace.IsEtaleLocalDescription.existsUnique_of_sqZero_quotient`: infinitesimal
  lifting along square-zero quotients over singleton spectra.

## References

* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory: foundations*, Astérisque 371 (2015),
  §8.2, Definition 8.2.16.
* P. Scholze, *Perfectoid spaces*, Publ. Math. IHÉS 116 (2012), §7, Definition 7.1(iii).
* P. Scholze, *Étale cohomology of diamonds*, arXiv:1709.07343, §6, Definition 6.2(ii).
* R. Huber, *Étale cohomology of rigid analytic varieties and adic spaces*, Aspects of Mathematics
  E30 (1996), §1.6–1.7.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology

namespace TauCeti

open Huber PreAdicSpace ValuationSpectrum

universe u

namespace AdicSpace

variable {X Y Z : AdicSpace.{u}}

/-- Lifting an open immersion through an open immersion in `𝒱^pre` gives an open immersion. -/
private theorem isOpenImmersion_lift {X' Y' Z' : PreAdicSpace.{u}}
    (f : X' ⟶ Z') (g : Y' ⟶ Z') [PreAdicSpace.IsOpenImmersion f] [PreAdicSpace.IsOpenImmersion g]
    (H : Set.range g.base ⊆ Set.range f.base) :
    PreAdicSpace.IsOpenImmersion (PreAdicSpace.IsOpenImmersion.lift f g H) := by
  unfold PreAdicSpace.IsOpenImmersion
  rw [PreAdicSpace.IsOpenImmersion.lift_toHom]
  have := PresheafedSpace.IsOpenImmersion.pullback_snd_isIso_of_range_subset f.toHom g.toHom H
  dsimp only [PresheafedSpace.IsOpenImmersion.lift]
  infer_instance

/-! ### Definition and basic constructors -/

/-- **Étale morphisms of analytic adic spaces** (Kedlaya–Liu I, Definition 8.2.16; Scholze,
*Étale cohomology of diamonds*, Definition 6.2(ii)): a morphism `f : Y ⟶ X` in `AdicSpace` satisfies
`IsEtaleLocalDescription` when `X` and `Y` are analytic and every point `y` of `Y` lies in the image
of an open immersion `u : U ⟶ Y` such that `u ≫ f` factors as `j ≫ g ≫ i` for open immersions
`j : U ⟶ W` and `i : V ⟶ X` and a finite étale morphism `g : W ⟶ V`. -/
def IsEtaleLocalDescription : MorphismProperty AdicSpace.{u} := fun Y X f ↦
  X.IsAnalytic ∧ Y.IsAnalytic ∧ ∀ y : Y.obj,
    ∃ (U V W : AdicSpace.{u}) (u : U ⟶ Y) (i : V ⟶ X) (j : U ⟶ W) (g : W ⟶ V),
      PreAdicSpace.IsOpenImmersion u.hom ∧ y ∈ Set.range u.hom.base ∧
        PreAdicSpace.IsOpenImmersion i.hom ∧ PreAdicSpace.IsOpenImmersion j.hom ∧
        IsFiniteEtale g ∧ u ≫ f = j ≫ g ≫ i

/-- Unfolding lemma for `TauCeti.AdicSpace.IsEtaleLocalDescription`. -/
theorem isEtaleLocalDescription_iff (f : Y ⟶ X) :
    IsEtaleLocalDescription f ↔
      X.IsAnalytic ∧ Y.IsAnalytic ∧ ∀ y : Y.obj,
        ∃ (U V W : AdicSpace.{u}) (u : U ⟶ Y) (i : V ⟶ X) (j : U ⟶ W) (g : W ⟶ V),
          PreAdicSpace.IsOpenImmersion u.hom ∧ y ∈ Set.range u.hom.base ∧
            PreAdicSpace.IsOpenImmersion i.hom ∧ PreAdicSpace.IsOpenImmersion j.hom ∧
            IsFiniteEtale g ∧ u ≫ f = j ≫ g ≫ i :=
  (Iff.rfl)

/-- The target of an étale morphism is analytic. -/
theorem IsEtaleLocalDescription.isAnalytic_target {f : Y ⟶ X}
    (hf : IsEtaleLocalDescription f) : X.IsAnalytic :=
  hf.1

/-- The source of an étale morphism is analytic. -/
theorem IsEtaleLocalDescription.isAnalytic_source {f : Y ⟶ X}
    (hf : IsEtaleLocalDescription f) : Y.IsAnalytic :=
  hf.2.1

/-- **Every finite étale morphism is étale.** -/
theorem IsEtaleLocalDescription.of_isFiniteEtale {f : Y ⟶ X} (hf : IsFiniteEtale f) :
    IsEtaleLocalDescription f :=
  ⟨hf.isAnalytic_target, hf.isAnalytic_source, fun y ↦
    ⟨Y, X, Y, 𝟙 Y, 𝟙 X, 𝟙 Y, f, inferInstance, ⟨y, rfl⟩, inferInstance, inferInstance, hf,
      by simp⟩⟩

/-- **Every open immersion into an analytic adic space is étale.** -/
theorem IsEtaleLocalDescription.of_isOpenImmersion (f : Y ⟶ X)
    [PreAdicSpace.IsOpenImmersion f.hom] (hX : X.IsAnalytic) :
    IsEtaleLocalDescription f :=
  ⟨hX, hX.of_isOpenImmersion f, fun y ↦
    ⟨Y, X, X, 𝟙 Y, 𝟙 X, f, 𝟙 X, inferInstance, ⟨y, rfl⟩, inferInstance, inferInstance,
      IsFiniteEtale.id hX, by simp⟩⟩

/-- **An open immersion in `AdicSpace` is étale if and only if its target is analytic.** -/
theorem isEtaleLocalDescription_of_isOpenImmersion_iff (f : Y ⟶ X)
    [PreAdicSpace.IsOpenImmersion f.hom] :
    IsEtaleLocalDescription f ↔ X.IsAnalytic :=
  ⟨IsEtaleLocalDescription.isAnalytic_target, IsEtaleLocalDescription.of_isOpenImmersion f⟩

/-- **The identity of an analytic adic space is étale.** -/
theorem IsEtaleLocalDescription.id {X : AdicSpace.{u}} (hX : X.IsAnalytic) :
    IsEtaleLocalDescription (𝟙 X) :=
  .of_isFiniteEtale (IsFiniteEtale.id hX)

/-- **The identity of an adic space `X` is étale if and only if `X` is analytic.** -/
theorem isEtaleLocalDescription_id_iff {X : AdicSpace.{u}} :
    IsEtaleLocalDescription (𝟙 X) ↔ X.IsAnalytic :=
  ⟨IsEtaleLocalDescription.isAnalytic_target, IsEtaleLocalDescription.id⟩

/-- **An isomorphism onto an analytic adic space is étale.** -/
theorem IsEtaleLocalDescription.of_isIso (f : Y ⟶ X) [IsIso f] (hX : X.IsAnalytic) :
    IsEtaleLocalDescription f :=
  .of_isFiniteEtale (IsFiniteEtale.of_isIso f hX)

/-- **An isomorphism in `AdicSpace` is étale if and only if its target is analytic.** -/
theorem isEtaleLocalDescription_of_isIso_iff (f : Y ⟶ X) [IsIso f] :
    IsEtaleLocalDescription f ↔ X.IsAnalytic :=
  ⟨IsEtaleLocalDescription.isAnalytic_target, IsEtaleLocalDescription.of_isIso f⟩

/-- **Every morphism from an empty adic space into an analytic adic space is étale.** -/
theorem IsEtaleLocalDescription.of_isEmpty (f : Y ⟶ X) [IsEmpty Y.obj] (hX : X.IsAnalytic) :
    IsEtaleLocalDescription f :=
  .of_isFiniteEtale (IsFiniteEtale.of_isEmpty f hX)

/-- **A morphism from an empty adic space into `X` is étale if and only if `X` is analytic.** -/
theorem isEtaleLocalDescription_of_isEmpty_iff (f : Y ⟶ X) [IsEmpty Y.obj] :
    IsEtaleLocalDescription f ↔ X.IsAnalytic :=
  ⟨IsEtaleLocalDescription.isAnalytic_target, IsEtaleLocalDescription.of_isEmpty f⟩

/-! ### Stability under open immersions, isomorphisms, and source covers -/

/-- **Precomposing an étale morphism with an open immersion gives an étale morphism.** -/
theorem IsEtaleLocalDescription.isOpenImmersion_comp {f : Y ⟶ X}
    (hf : IsEtaleLocalDescription f) (v : Z ⟶ Y) [PreAdicSpace.IsOpenImmersion v.hom] :
    IsEtaleLocalDescription (v ≫ f) := by
  refine ⟨hf.isAnalytic_target, hf.isAnalytic_source.of_isOpenImmersion v, fun z ↦ ?_⟩
  obtain ⟨U, V, W, u, i, j, g, hu, ⟨u₀, hu₀⟩, hi, hj, hg, hfac⟩ := hf.2.2 (v.hom.base z)
  let O : Opens Z.obj :=
    ⟨v.hom.base ⁻¹' Set.range u.hom.base,
      hu.base_open.isOpen_range.preimage v.hom.base.hom.continuous⟩
  let U' : AdicSpace.{u} := ⟨Z.obj.restrict O.isOpenEmbedding, isAdic_restrict _ Z.property⟩
  let rO : U' ⟶ Z := ObjectProperty.homMk (Z.obj.ofRestrict O.isOpenEmbedding)
  have _ : PreAdicSpace.IsOpenImmersion rO.hom :=
    inferInstanceAs (PreAdicSpace.IsOpenImmersion (Z.obj.ofRestrict O.isOpenEmbedding))
  have hrange : Set.range (rO ≫ v).hom.base ⊆ Set.range u.hom.base := by
    rintro _ ⟨q, rfl⟩
    exact q.2
  have _ : PreAdicSpace.IsOpenImmersion (rO ≫ v).hom := by
    rw [ObjectProperty.FullSubcategory.comp_hom]
    infer_instance
  let l : U' ⟶ U := ObjectProperty.homMk (IsOpenImmersion.lift u.hom (rO ≫ v).hom hrange)
  have _ : PreAdicSpace.IsOpenImmersion l.hom := isOpenImmersion_lift u.hom (rO ≫ v).hom hrange
  have hl_u : l ≫ u = rO ≫ v := by
    ext1
    exact IsOpenImmersion.lift_fac u.hom (rO ≫ v).hom hrange
  refine ⟨U', V, W, rO, i, l ≫ j, g, inferInstance, ⟨⟨z, u₀, hu₀⟩, rfl⟩, hi, ?_, hg, ?_⟩
  · rw [ObjectProperty.FullSubcategory.comp_hom]
    infer_instance
  · rw [← Category.assoc, ← hl_u, Category.assoc, hfac, Category.assoc]

/-- **Postcomposing an étale morphism with an open immersion into an analytic target gives an étale
morphism.** -/
theorem IsEtaleLocalDescription.comp_isOpenImmersion {f : Y ⟶ X}
    (hf : IsEtaleLocalDescription f) (v : X ⟶ Z) [PreAdicSpace.IsOpenImmersion v.hom]
    (hZ : Z.IsAnalytic) : IsEtaleLocalDescription (f ≫ v) := by
  refine ⟨hZ, hf.isAnalytic_source, fun y ↦ ?_⟩
  obtain ⟨U, V, W, u, i, j, g, hu, hy, hi, hj, hg, hfac⟩ := hf.2.2 y
  refine ⟨U, V, W, u, i ≫ v, j, g, hu, hy, ?_, hj, hg, ?_⟩
  · rw [ObjectProperty.FullSubcategory.comp_hom]
    infer_instance
  · rw [← Category.assoc, hfac, Category.assoc, Category.assoc]

/-- Being étale (`IsEtaleLocalDescription`) is invariant under isomorphisms of source and target. -/
instance IsEtaleLocalDescription.respectsIso :
    MorphismProperty.RespectsIso (@IsEtaleLocalDescription.{u}) :=
  MorphismProperty.RespectsIso.mk _
    (fun e _ hf ↦
      have : IsIso e.hom.hom := (ObjectProperty.ι isAdic).map_isIso e.hom
      hf.isOpenImmersion_comp e.hom)
    (fun e _ hf ↦
      have : IsIso e.hom.hom := (ObjectProperty.ι isAdic).map_isIso e.hom
      hf.comp_isOpenImmersion e.hom (hf.isAnalytic_target.of_iso e.symm))

/-- **Source locality of étale morphisms.** Let `f : Y ⟶ X` be a morphism into an analytic adic
space `X`. If open immersions `u k : U k ⟶ Y` jointly cover `Y` and every composite `u k ≫ f`
satisfies `IsEtaleLocalDescription`, then `f` satisfies `IsEtaleLocalDescription`. -/
theorem IsEtaleLocalDescription.of_jointly_surjective {f : Y ⟶ X} (hX : X.IsAnalytic) {ι : Type*}
    {U : ι → AdicSpace.{u}} (u : ∀ k, U k ⟶ Y) [∀ k, PreAdicSpace.IsOpenImmersion (u k).hom]
    (hcov : ∀ y : Y.obj, ∃ (k : ι) (z : (U k).obj), (u k).hom.base z = y)
    (hf : ∀ k, IsEtaleLocalDescription (u k ≫ f)) :
    IsEtaleLocalDescription f := by
  have hY : Y.IsAnalytic := by
    rw [isAnalytic_iff_analyticPoints_eq_univ, Set.eq_univ_iff_forall]
    intro y
    obtain ⟨k, z, rfl⟩ := hcov y
    exact Set.mem_preimage.mp ((preimage_analyticPoints_of_isOpenImmersion (u k).hom).symm ▸
      (hf k).isAnalytic_source.mem_analyticPoints z)
  refine ⟨hX, hY, fun y ↦ ?_⟩
  obtain ⟨k, z, rfl⟩ := hcov y
  obtain ⟨U', V', W', u', i, j, g, hu', ⟨q, hq⟩, hi, hj, hg, hfac⟩ := (hf k).2.2 z
  refine ⟨U', V', W', u' ≫ u k, i, j, g, ?_, ⟨q, by simp [hq]⟩, hi, hj, hg, ?_⟩
  · rw [ObjectProperty.FullSubcategory.comp_hom]
    infer_instance
  · rw [Category.assoc, hfac]

/-! ### Standard affinoid factorisation and finiteness properties -/

/-- **Standard affinoid local factorisation of an étale morphism.** Around any `y : Y.obj`, an étale
morphism `f : Y ⟶ X` factors as
`u ≫ f = j ≫ comapOfPresentation S P hP hsheafS T P' hP' hsheafT ψ ≫ i` where `(A, S)` and `(B, T)`
are complete Hausdorff Tate Huber pairs, `ψ : Pair.Hom S T` is finite étale, and `u`, `j`, `i` are
open immersions with `y ∈ Set.range u.hom.base`. -/
theorem IsEtaleLocalDescription.exists_affinoid_factorisation {f : Y ⟶ X}
    (hf : IsEtaleLocalDescription f) (y : Y.obj) :
    ∃ (A : Type u) (_ : CommRing A) (_ : UniformSpace A) (_ : IsUniformAddGroup A)
      (_ : IsTopologicalRing A) (_ : CompleteSpace A) (_ : T2Space A) (_ : IsTateRing A)
      (S : Pair A) (P : PairOfDefinition A) (hP : P.ringOfDefinition ≤ S.plus)
      (hsheafS : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(ValuationSpectrum.spa S.plus))
        (presentationLimitPresheaf P S.plus))
      (B : Type u) (_ : CommRing B) (_ : UniformSpace B) (_ : IsUniformAddGroup B)
      (_ : IsTopologicalRing B) (_ : CompleteSpace B) (_ : T2Space B) (_ : IsTateRing B)
      (T : Pair B) (P' : PairOfDefinition B) (hP' : P'.ringOfDefinition ≤ T.plus)
      (hsheafT : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(ValuationSpectrum.spa T.plus))
        (presentationLimitPresheaf P' T.plus))
      (ψ : Pair.Hom S T) (_ : ψ.IsFiniteEtale)
      (U : AdicSpace.{u}) (u : U ⟶ Y) (j : U ⟶ ofPresentation T P' hP' hsheafT)
      (i : ofPresentation S P hP hsheafS ⟶ X),
      PreAdicSpace.IsOpenImmersion u.hom ∧ y ∈ Set.range u.hom.base ∧
        PreAdicSpace.IsOpenImmersion j.hom ∧ PreAdicSpace.IsOpenImmersion i.hom ∧
        u ≫ f = j ≫ AdicSpace.comapOfPresentation S P hP hsheafS T P' hP' hsheafT ψ ≫ i := by
  obtain ⟨U₀, V₀, W₀, u₀, i₀, j₀, g₀, hu₀, ⟨p₀, hp₀⟩, hi₀, hj₀, hg₀, hfac₀⟩ := hf.2.2 y
  obtain ⟨V', hv₀, A, _, _, _, _, _, _, _, S, P, hP, B, _, _, _, _, _, _, _, T, P', hP',
    hsheafT, ψ, hψ, eV, eW, hg_fac⟩ := hg₀.exists_complete_tate_chart (g₀.hom.base (j₀.hom.base p₀))
  have hsheafS : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(ValuationSpectrum.spa S.plus))
      (presentationLimitPresheaf P S.plus) :=
    (isSheafy_presentationLimitPreAdicSpace_iff P S.plus
        S.isRingOfIntegralElements.isPowerBounded_of_mem hP).mp
      ((ObjectProperty.prop_iff_of_iso PreAdicSpace.isSheafy eV).mp
        (isSheafy_restrict _ (isAdic_iff.mp V₀.property).1))
  let O : Opens U₀.obj := (Opens.map (j₀ ≫ g₀).hom.base).obj V'
  let U : AdicSpace.{u} := ⟨U₀.obj.restrict O.isOpenEmbedding, isAdic_restrict _ U₀.property⟩
  let rO : U ⟶ U₀ := ObjectProperty.homMk (U₀.obj.ofRestrict O.isOpenEmbedding)
  have _ : PreAdicSpace.IsOpenImmersion rO.hom :=
    inferInstanceAs (PreAdicSpace.IsOpenImmersion (U₀.obj.ofRestrict O.isOpenEmbedding))
  have hrange : Set.range (rO.hom ≫ j₀.hom).base ⊆
      Set.range (W₀.obj.ofRestrict ((Opens.map g₀.hom.base).obj V').isOpenEmbedding).base := by
    rintro _ ⟨q, rfl⟩
    exact ⟨⟨j₀.hom.base q.1, Opens.mem_map.mpr q.2⟩, rfl⟩
  let l := IsOpenImmersion.lift
    (W₀.obj.ofRestrict ((Opens.map g₀.hom.base).obj V').isOpenEmbedding)
    (rO.hom ≫ j₀.hom) hrange
  have _ : PreAdicSpace.IsOpenImmersion l := isOpenImmersion_lift _ _ hrange
  let j : U ⟶ ofPresentation T P' hP' hsheafT := ObjectProperty.homMk (l ≫ eW.hom)
  have _ : PreAdicSpace.IsOpenImmersion j.hom :=
    inferInstanceAs (PreAdicSpace.IsOpenImmersion (l ≫ eW.hom))
  let i : ofPresentation S P hP hsheafS ⟶ X :=
    ObjectProperty.homMk (eV.inv ≫ V₀.obj.ofRestrict V'.isOpenEmbedding ≫ i₀.hom)
  have _ : PreAdicSpace.IsOpenImmersion i.hom :=
    inferInstanceAs
      (PreAdicSpace.IsOpenImmersion (eV.inv ≫ V₀.obj.ofRestrict V'.isOpenEmbedding ≫ i₀.hom))
  refine ⟨A, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, S, P, hP, hsheafS, B, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, T, P', hP',
    hsheafT, ψ, hψ, U, rO ≫ u₀, j, i, ?_, ⟨⟨p₀, hv₀⟩, hp₀⟩, inferInstance, inferInstance, ?_⟩
  · rw [ObjectProperty.FullSubcategory.comp_hom]
    infer_instance
  · ext1
    simp only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom,
      AdicSpace.comapOfPresentation_hom, j, i]
    have h1 := congrArg (fun k ↦ rO.hom ≫ k) (congrArg InducedCategory.Hom.hom hfac₀)
    simp only [ObjectProperty.FullSubcategory.comp_hom, ← Category.assoc] at h1
    have h2 : rO.hom ≫ j₀.hom ≫ g₀.hom =
        l ≫ eW.hom ≫ presentationLimitPreAdicSpacePairComap P P' hP hP' hsheafT ψ ≫
          eV.inv ≫ V₀.obj.ofRestrict V'.isOpenEmbedding := by
      rw [← Category.assoc, ← IsOpenImmersion.lift_fac
        (W₀.obj.ofRestrict ((Opens.map g₀.hom.base).obj V').isOpenEmbedding)
        (rO.hom ≫ j₀.hom) hrange, Category.assoc, hg_fac]
    simpa only [Category.assoc] using h1.trans (congrArg (fun k ↦ k ≫ i₀.hom) h2)

/-- **An étale morphism of analytic adic spaces is locally of finite type.** -/
theorem IsEtaleLocalDescription.locallyOfFiniteType {f : Y ⟶ X}
    (hf : IsEtaleLocalDescription f) : PreAdicSpace.LocallyOfFiniteType f.hom := by
  choose U V W u i j g hu hy hi hj hg hfac using hf.2.2
  let O : Y.obj → Opens Y.obj := fun y ↦
    ⟨Set.range (u y).hom.base, (hu y).base_open.isOpen_range⟩
  have hcov : iSup O = ⊤ := eq_top_iff.mpr fun y _ ↦ Opens.mem_iSup.mpr ⟨y, hy y⟩
  refine PreAdicSpace.LocallyOfFiniteType.of_iSup_eq_top O hcov fun y ↦ ?_
  have huf : PreAdicSpace.LocallyOfFiniteType ((u y).hom ≫ f.hom) := by
    have hhom := congrArg InducedCategory.Hom.hom (hfac y)
    simp only [ObjectProperty.FullSubcategory.comp_hom] at hhom
    rw [hhom, ← Category.assoc]
    exact ((hg y).locallyOfFiniteType.comp_of_isOpenImmersion (i y).hom).isOpenImmersion_comp
      (j y).hom
  have hr : Set.range (u y).hom.base = Set.range (Y.obj.ofRestrict (O y).isOpenEmbedding).base :=
    (Opens.set_range_inclusion' (O y)).symm
  rw [← IsOpenImmersion.isoOfRangeEq_inv_comp (u y).hom (Y.obj.ofRestrict (O y).isOpenEmbedding) hr,
    Category.assoc,
    MorphismProperty.cancel_left_of_respectsIso @PreAdicSpace.LocallyOfFiniteType.{u}]
  exact huf

/-- **Locally noetherian analytic structure ascends along étale morphisms.** -/
theorem IsEtaleLocalDescription.isLocallyNoetherianAnalytic_source {f : Y ⟶ X}
    (hf : IsEtaleLocalDescription f) (hX : X.IsLocallyNoetherianAnalytic) :
    Y.IsLocallyNoetherianAnalytic :=
  isLocallyNoetherianAnalytic_iff.mpr
    ⟨hX.isLocallyNoetherian.of_locallyOfFiniteType hf.locallyOfFiniteType, hf.isAnalytic_source⟩

/-! ### Infinitesimal lifting along square-zero quotients -/

section InfinitesimalLifting

/-- Helper equivalence identifying morphisms `ofPair R hR ⟶ ofPresentation S P hS hsheafS` with
`Pair.Hom S R` when both `A` and `C` are complete and Hausdorff. -/
private noncomputable def ofPairToOfPresentationHomEquiv
    {A : Type u} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]
    [CompleteSpace A] [T0Space A] [IsHuberRing A]
    {C : Type u} [CommRing C] [UniformSpace C] [IsUniformAddGroup C] [IsTopologicalRing C]
    [CompleteSpace C] [T0Space C] [IsHuberRing C]
    (S : Pair A) (P : PairOfDefinition A) (hS : P.ringOfDefinition ≤ S.plus)
    (hsheafS : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(ValuationSpectrum.spa S.plus))
      (presentationLimitPresheaf P S.plus))
    (R : Pair C) (hR : IsSheafyForEveryPresentation R.plus) :
    (ofPair R hR ⟶ ofPresentation S P hS hsheafS) ≃ Pair.Hom S R :=
  (Iso.homCongr (ofPairIsoOfPresentation R hR hR.exists_compatible_isSheaf.choose
      hR.exists_compatible_isSheaf.choose_spec.1) (Iso.refl _)).trans
    (ofPresentationHomEquiv S P hS hsheafS R hR.exists_compatible_isSheaf.choose
      hR.exists_compatible_isSheaf.choose_spec.1 hR.exists_compatible_isSheaf.choose_spec.2)

private theorem ofPairToOfPresentationHomEquiv_symm_apply
    {A : Type u} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]
    [CompleteSpace A] [T0Space A] [IsHuberRing A]
    {C : Type u} [CommRing C] [UniformSpace C] [IsUniformAddGroup C] [IsTopologicalRing C]
    [CompleteSpace C] [T0Space C] [IsHuberRing C]
    (S : Pair A) (P : PairOfDefinition A) (hS : P.ringOfDefinition ≤ S.plus)
    (hsheafS : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(ValuationSpectrum.spa S.plus))
      (presentationLimitPresheaf P S.plus))
    (R : Pair C) (hR : IsSheafyForEveryPresentation R.plus) (α : Pair.Hom S R) :
    (ofPairToOfPresentationHomEquiv S P hS hsheafS R hR).symm α =
      (ofPairIsoOfPresentation R hR hR.exists_compatible_isSheaf.choose
        hR.exists_compatible_isSheaf.choose_spec.1).hom ≫
        AdicSpace.comapOfPresentation S P hS hsheafS R hR.exists_compatible_isSheaf.choose
          hR.exists_compatible_isSheaf.choose_spec.1
          hR.exists_compatible_isSheaf.choose_spec.2 α := by
  simp [ofPairToOfPresentationHomEquiv]

private theorem ofPairToOfPresentationHomEquiv_comp_right
    {A : Type u} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]
    [CompleteSpace A] [T0Space A] [IsHuberRing A]
    {B : Type u} [CommRing B] [UniformSpace B] [IsUniformAddGroup B] [IsTopologicalRing B]
    [CompleteSpace B] [T0Space B] [IsHuberRing B]
    {C : Type u} [CommRing C] [UniformSpace C] [IsUniformAddGroup C] [IsTopologicalRing C]
    [CompleteSpace C] [T0Space C] [IsHuberRing C]
    (S : Pair A) (P : PairOfDefinition A) (hS : P.ringOfDefinition ≤ S.plus)
    (hsheafS : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(ValuationSpectrum.spa S.plus))
      (presentationLimitPresheaf P S.plus))
    (T : Pair B) (P' : PairOfDefinition B) (hT : P'.ringOfDefinition ≤ T.plus)
    (hsheafT : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(ValuationSpectrum.spa T.plus))
      (presentationLimitPresheaf P' T.plus))
    (R : Pair C) (hR : IsSheafyForEveryPresentation R.plus)
    (k : ofPair R hR ⟶ ofPresentation T P' hT hsheafT) (ψ : Pair.Hom S T) :
    ofPairToOfPresentationHomEquiv S P hS hsheafS R hR
        (k ≫ AdicSpace.comapOfPresentation S P hS hsheafS T P' hT hsheafT ψ) =
      (ofPairToOfPresentationHomEquiv T P' hT hsheafT R hR k).comp ψ := by
  apply (ofPairToOfPresentationHomEquiv S P hS hsheafS R hR).symm.injective
  rw [Equiv.symm_apply_apply, ofPairToOfPresentationHomEquiv_symm_apply,
    AdicSpace.comapOfPresentation_comp S P hS hsheafS T P' hT hsheafT, ← Category.assoc,
    ← ofPairToOfPresentationHomEquiv_symm_apply, Equiv.symm_apply_apply]

private theorem ofPairToOfPresentationHomEquiv_comp_left
    {A : Type u} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]
    [CompleteSpace A] [T0Space A] [IsHuberRing A]
    {C : Type u} [CommRing C] [UniformSpace C] [IsUniformAddGroup C] [IsTopologicalRing C]
    [CompleteSpace C] [T0Space C] [IsHuberRing C]
    {D : Type u} [CommRing D] [UniformSpace D] [IsUniformAddGroup D] [IsTopologicalRing D]
    [CompleteSpace D] [T0Space D] [IsHuberRing D]
    (S : Pair A) (P : PairOfDefinition A) (hS : P.ringOfDefinition ≤ S.plus)
    (hsheafS : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(ValuationSpectrum.spa S.plus))
      (presentationLimitPresheaf P S.plus))
    {R : Pair C} {R' : Pair D} (hR : IsSheafyForEveryPresentation R.plus)
    (hR' : IsSheafyForEveryPresentation R'.plus) (φ : Pair.Hom R R')
    (k : ofPair R hR ⟶ ofPresentation S P hS hsheafS) :
    ofPairToOfPresentationHomEquiv S P hS hsheafS R' hR' (comapOfPair hR hR' φ ≫ k) =
      φ.comp (ofPairToOfPresentationHomEquiv S P hS hsheafS R hR k) := by
  apply (ofPairToOfPresentationHomEquiv S P hS hsheafS R' hR').symm.injective
  rw [Equiv.symm_apply_apply, ofPairToOfPresentationHomEquiv_symm_apply,
    AdicSpace.comapOfPresentation_comp S P hS hsheafS R hR.exists_compatible_isSheaf.choose
      hR.exists_compatible_isSheaf.choose_spec.1 hR.exists_compatible_isSheaf.choose_spec.2,
    ofPairIsoOfPresentation_hom_comapOfPresentation_assoc,
    ← ofPairToOfPresentationHomEquiv_symm_apply, Equiv.symm_apply_apply]

/-- The quotient of a singleton-spectrum sheafy Huber pair again has subsingleton spectrum. -/
private theorem subsingleton_ofPair_quotient
    {C : Type u} [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsHuberRing C]
    (R : Pair C) (I : Ideal C) (hR : IsSheafyForEveryPresentation R.plus)
    (hRI : IsSheafyForEveryPresentation (R.quotient I).plus)
    [Subsingleton (ofPair R hR).obj] :
    Subsingleton (ofPair (R.quotient I) hRI).obj := by
  have : Subsingleton (ValuationSpectrum.spa R.plus) :=
    (ofPairHomeomorph R hR).symm.injective.subsingleton
  have : Subsingleton (ValuationSpectrum.spa (R.quotient I).plus) :=
    (Pair.Hom.isClosedEmbedding_spaComap_quotientHom R I).injective.subsingleton
  exact (ofPairHomeomorph (R.quotient I) hRI).injective.subsingleton

private theorem exists_lift_of_subsingleton {Z' U Y' : AdicSpace.{u}} [Subsingleton Z'.obj]
    (u : U ⟶ Y') [PreAdicSpace.IsOpenImmersion u.hom] (f : Z' ⟶ Y') (z₀ : Z'.obj)
    (hz₀ : f.hom.base z₀ ∈ Set.range u.hom.base) :
    ∃ l : Z' ⟶ U, l ≫ u = f := by
  have hr : Set.range f.hom.base ⊆ Set.range u.hom.base := by
    rintro _ ⟨z, rfl⟩
    rwa [Subsingleton.elim z z₀]
  exact ⟨ObjectProperty.homMk (IsOpenImmersion.lift u.hom f.hom hr),
    InducedCategory.Hom.ext (IsOpenImmersion.lift_fac u.hom f.hom hr)⟩

private theorem cancel_comp_of_isOpenImmersion {Z' U Y' : AdicSpace.{u}}
    (u : U ⟶ Y') [PreAdicSpace.IsOpenImmersion u.hom] {l₁ l₂ : Z' ⟶ U} (h : l₁ ≫ u = l₂ ≫ u) :
    l₁ = l₂ := by
  apply InducedCategory.Hom.ext
  rw [← cancel_mono u.hom]
  exact congrArg InducedCategory.Hom.hom h

private theorem eq_pairHom_of_sqZero_quotient
    {A B C : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B]
    [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsHuberRing C]
    {S : Pair A} {T : Pair B} {R : Pair C} {ψ : Pair.Hom S T} (hψ : ψ.IsFiniteEtale)
    {I : Ideal C} (hI : I ^ 2 = ⊥) {σ₁ σ₂ : Pair.Hom T R}
    (hψ_eq : σ₁.comp ψ = σ₂.comp ψ)
    (hq_eq : (Pair.quotientHom R I).comp σ₁ = (Pair.quotientHom R I).comp σ₂) :
    σ₁ = σ₂ := by
  let _ : Algebra A B := ψ.toRingHom.toAlgebra
  let _ : Algebra A C := (σ₁.toRingHom.comp ψ.toRingHom).toAlgebra
  have _ : Algebra.Etale A B := hψ.etale
  have hring : σ₂.toRingHom.comp ψ.toRingHom = σ₁.toRingHom.comp ψ.toRingHom := by
    simpa only [Pair.Hom.toRingHom_comp] using congrArg Pair.Hom.toRingHom hψ_eq.symm
  let f₁ : B →ₐ[A] C := { σ₁.toRingHom with commutes' := fun _ ↦ rfl }
  let f₂ : B →ₐ[A] C := { σ₂.toRingHom with commutes' := fun a ↦ RingHom.congr_fun hring a }
  have hmk : (Ideal.Quotient.mkₐ A I).comp f₁ = (Ideal.Quotient.mkₐ A I).comp f₂ := by
    ext b
    have hb := RingHom.congr_fun (congrArg Pair.Hom.toRingHom hq_eq) b
    simp only [Pair.Hom.toRingHom_comp, Pair.Hom.toRingHom_quotientHom, RingHom.comp_apply] at hb
    exact hb
  have hf : f₁ = f₂ := (Algebra.FormallyEtale.comp_bijective A B I hI).injective hmk
  exact Pair.Hom.ext (RingHom.ext fun b ↦ AlgHom.congr_fun hf b)

private theorem exists_pairHom_of_sqZero_quotient
    {A B C : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B]
    [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsHuberRing C]
    {S : Pair A} {T : Pair B} {R : Pair C} {ψ : Pair.Hom S T} (hψ : ψ.IsFiniteEtale)
    {I : Ideal C} (hI : I ^ 2 = ⊥) (α : Pair.Hom S R) (β₀ : Pair.Hom T (R.quotient I))
    (hcomm : β₀.comp ψ = (Pair.quotientHom R I).comp α) :
    ∃ β : Pair.Hom T R, β.comp ψ = α ∧ (Pair.quotientHom R I).comp β = β₀ := by
  let _ : Algebra A B := ψ.toRingHom.toAlgebra
  let _ : Algebra A C := α.toRingHom.toAlgebra
  have _ : Algebra.Etale A B := hψ.etale
  have hring : β₀.toRingHom.comp ψ.toRingHom = (Ideal.Quotient.mk I).comp α.toRingHom := by
    simpa only [Pair.Hom.toRingHom_comp, Pair.Hom.toRingHom_quotientHom] using
      congrArg Pair.Hom.toRingHom hcomm
  let β₀_alg : B →ₐ[A] C ⧸ I :=
    { β₀.toRingHom with commutes' := fun a ↦ RingHom.congr_fun hring a }
  obtain ⟨β_alg, hβ_alg⟩ := (Algebra.FormallyEtale.comp_bijective A B I hI).surjective β₀_alg
  obtain ⟨β, hβ⟩ := hψ.exists_hom α β_alg.toRingHom β_alg.comp_algebraMap
  refine ⟨β, Pair.Hom.ext (by rw [Pair.Hom.toRingHom_comp, hβ]; exact β_alg.comp_algebraMap), ?_⟩
  refine Pair.Hom.ext (RingHom.ext fun b ↦ ?_)
  have hb := AlgHom.congr_fun hβ_alg b
  rw [Pair.Hom.toRingHom_comp, Pair.Hom.toRingHom_quotientHom, hβ, RingHom.comp_apply]
  exact hb

/-- **Formal unramifiedness of étale morphisms along square-zero quotients.** Let `f : Y ⟶ X`
satisfy `IsEtaleLocalDescription`, and let `(C, R)` be a complete Hausdorff sheafy Huber pair with
singleton spectrum and `I : Ideal C` a closed square-zero ideal (`I ^ 2 = ⊥`) whose quotient Huber
pair is sheafy with nonempty spectrum. Any two morphisms `g₁, g₂ : Spa(C, R⁺) ⟶ Y` that agree after
composing with `f` and after restricting to `Spa(C ⧸ I, (R.quotient I)⁺)` are equal. -/
theorem IsEtaleLocalDescription.eq_of_sqZero_quotient {f : Y ⟶ X}
    (hf : IsEtaleLocalDescription f)
    {C : Type u} [CommRing C] [UniformSpace C] [IsUniformAddGroup C] [IsTopologicalRing C]
    [CompleteSpace C] [T0Space C] [IsHuberRing C]
    (R : Pair C) (hR : IsSheafyForEveryPresentation R.plus) [Subsingleton (ofPair R hR).obj]
    (I : Ideal C) (hI : I ^ 2 = ⊥) (hI_closed : IsClosed (I : Set C))
    (hRI : IsSheafyForEveryPresentation (R.quotient I).plus)
    (z₀ : (ofPair (R.quotient I) hRI).obj)
    {g₁ g₂ : ofPair R hR ⟶ Y} (hf_eq : g₁ ≫ f = g₂ ≫ f)
    (hι_eq : comapOfPair hR hRI (Pair.quotientHom R I) ≫ g₁ =
      comapOfPair hR hRI (Pair.quotientHom R I) ≫ g₂) :
    g₁ = g₂ := by
  let _ : UniformSpace (C ⧸ I) := IsTopologicalAddGroup.rightUniformSpace (C ⧸ I)
  have _ : IsUniformAddGroup (C ⧸ I) := isUniformAddGroup_of_addCommGroup
  have _ : CompleteSpace (C ⧸ I) := QuotientAddGroup.completeSpace_right _ I.toAddSubgroup
  have _ : T1Space (C ⧸ I) := (Ideal.Quotient.t1Space_iff I).mpr hI_closed
  let ι := comapOfPair hR hRI (Pair.quotientHom R I)
  let r₀ : (ofPair R hR).obj := ι.hom.base z₀
  have hg_pt : g₁.hom.base r₀ = g₂.hom.base r₀ :=
    congrArg (fun k : ofPair (R.quotient I) hRI ⟶ Y ↦ k.hom.base z₀) hι_eq
  obtain ⟨A, _, _, _, _, _, _, _, S, P, hP, hsheafS, B, _, _, _, _, _, _, _, T, P', hP',
    hsheafT, ψ, hψ, U, u, j, i, hu, hy_mem, hj, hi, hfac⟩ :=
    hf.exists_affinoid_factorisation (g₁.hom.base r₀)
  obtain ⟨l₁, hl₁⟩ := exists_lift_of_subsingleton u g₁ r₀ hy_mem
  obtain ⟨l₂, hl₂⟩ := exists_lift_of_subsingleton u g₂ r₀ (hg_pt ▸ hy_mem)
  have hk_f : (l₁ ≫ j) ≫ AdicSpace.comapOfPresentation S P hP hsheafS T P' hP' hsheafT ψ =
      (l₂ ≫ j) ≫ AdicSpace.comapOfPresentation S P hP hsheafS T P' hP' hsheafT ψ := by
    refine cancel_comp_of_isOpenImmersion i ?_
    simpa only [Category.assoc, ← hfac] using
      (congrArg (· ≫ f) hl₁).trans (hf_eq.trans (congrArg (· ≫ f) hl₂).symm)
  have hl_ι : ι ≫ l₁ = ι ≫ l₂ :=
    cancel_comp_of_isOpenImmersion u (by rw [Category.assoc, Category.assoc, hl₁, hl₂, hι_eq])
  have hσ_ψ := congrArg (ofPairToOfPresentationHomEquiv S P hP hsheafS R hR) hk_f
  rw [ofPairToOfPresentationHomEquiv_comp_right, ofPairToOfPresentationHomEquiv_comp_right] at hσ_ψ
  have hσ_q := congrArg (ofPairToOfPresentationHomEquiv T P' hP' hsheafT (R.quotient I) hRI)
    (show ι ≫ l₁ ≫ j = ι ≫ l₂ ≫ j by rw [← Category.assoc, hl_ι, Category.assoc])
  rw [ofPairToOfPresentationHomEquiv_comp_left, ofPairToOfPresentationHomEquiv_comp_left] at hσ_q
  have hk := (ofPairToOfPresentationHomEquiv T P' hP' hsheafT R hR).injective
    (eq_pairHom_of_sqZero_quotient hψ hI hσ_ψ hσ_q)
  rw [← hl₁, ← hl₂, cancel_comp_of_isOpenImmersion j hk]

/-- **Infinitesimal lifting (existence) for étale morphisms along square-zero quotients.** -/
theorem IsEtaleLocalDescription.exists_of_sqZero_quotient {f : Y ⟶ X}
    (hf : IsEtaleLocalDescription f)
    {C : Type u} [CommRing C] [UniformSpace C] [IsUniformAddGroup C] [IsTopologicalRing C]
    [CompleteSpace C] [T0Space C] [IsHuberRing C]
    (R : Pair C) (hR : IsSheafyForEveryPresentation R.plus) [Subsingleton (ofPair R hR).obj]
    (I : Ideal C) (hI : I ^ 2 = ⊥) (hI_closed : IsClosed (I : Set C))
    (hRI : IsSheafyForEveryPresentation (R.quotient I).plus)
    (z₀ : (ofPair (R.quotient I) hRI).obj)
    (g₀ : ofPair (R.quotient I) hRI ⟶ Y) (h : ofPair R hR ⟶ X)
    (hsq : g₀ ≫ f = comapOfPair hR hRI (Pair.quotientHom R I) ≫ h) :
    ∃ g : ofPair R hR ⟶ Y,
      comapOfPair hR hRI (Pair.quotientHom R I) ≫ g = g₀ ∧ g ≫ f = h := by
  let _ : UniformSpace (C ⧸ I) := IsTopologicalAddGroup.rightUniformSpace (C ⧸ I)
  have _ : IsUniformAddGroup (C ⧸ I) := isUniformAddGroup_of_addCommGroup
  have _ : CompleteSpace (C ⧸ I) := QuotientAddGroup.completeSpace_right _ I.toAddSubgroup
  have _ : T1Space (C ⧸ I) := (Ideal.Quotient.t1Space_iff I).mpr hI_closed
  let ι := comapOfPair hR hRI (Pair.quotientHom R I)
  have _ : Subsingleton (ofPair (R.quotient I) hRI).obj := subsingleton_ofPair_quotient R I hR hRI
  obtain ⟨A, _, _, _, _, _, _, _, S, P, hP, hsheafS, B, _, _, _, _, _, _, _, T, P', hP',
    hsheafT, ψ, hψ, U, u, j, i, hu, ⟨u₀, hu₀⟩, hj, hi, hfac⟩ :=
    hf.exists_affinoid_factorisation (g₀.hom.base z₀)
  obtain ⟨g₀', hg₀'⟩ := exists_lift_of_subsingleton u g₀ z₀ ⟨u₀, hu₀⟩
  have hh_mem : h.hom.base (ι.hom.base z₀) ∈ Set.range i.hom.base := by
    have hpt := congrArg (fun m : ofPair (R.quotient I) hRI ⟶ X ↦ m.hom.base z₀) hsq.symm
    have hpt' := congrArg (fun m : U ⟶ X ↦ m.hom.base u₀) hfac
    simp only [ObjectProperty.FullSubcategory.comp_hom, comp_base, TopCat.coe_comp,
      Function.comp_apply] at hpt hpt'
    exact ⟨_, (hu₀ ▸ hpt').symm.trans hpt.symm⟩
  obtain ⟨h', hh'⟩ := exists_lift_of_subsingleton i h (ι.hom.base z₀) hh_mem
  have hcomm_space : (g₀' ≫ j) ≫ AdicSpace.comapOfPresentation S P hP hsheafS T P' hP' hsheafT ψ =
      ι ≫ h' :=
    cancel_comp_of_isOpenImmersion i
      (by rw [Category.assoc, Category.assoc, ← hfac, ← Category.assoc, hg₀', hsq, Category.assoc,
        hh'])
  have hcomm_pair := congrArg (ofPairToOfPresentationHomEquiv S P hP hsheafS (R.quotient I) hRI)
    hcomm_space
  rw [ofPairToOfPresentationHomEquiv_comp_right, ofPairToOfPresentationHomEquiv_comp_left]
    at hcomm_pair
  obtain ⟨β, hβ_ψ, hβ_q⟩ := exists_pairHom_of_sqZero_quotient hψ hI _ _ hcomm_pair
  let k := (ofPairToOfPresentationHomEquiv T P' hP' hsheafT R hR).symm β
  have hk_ι : ι ≫ k = g₀' ≫ j :=
    (ofPairToOfPresentationHomEquiv T P' hP' hsheafT (R.quotient I) hRI).injective
      (by rw [ofPairToOfPresentationHomEquiv_comp_left, Equiv.apply_symm_apply, hβ_q])
  have hk_ψ : k ≫ AdicSpace.comapOfPresentation S P hP hsheafS T P' hP' hsheafT ψ = h' :=
    (ofPairToOfPresentationHomEquiv S P hP hsheafS R hR).injective
      (by rw [ofPairToOfPresentationHomEquiv_comp_right, Equiv.apply_symm_apply, hβ_ψ])
  obtain ⟨l, hl⟩ := exists_lift_of_subsingleton j k (ι.hom.base z₀)
    ⟨g₀'.hom.base z₀, (congrArg (fun m : ofPair (R.quotient I) hRI ⟶ _ ↦ m.hom.base z₀) hk_ι).symm⟩
  refine ⟨l ≫ u, ?_, ?_⟩
  · have hl_ι : ι ≫ l = g₀' :=
      cancel_comp_of_isOpenImmersion j (by rw [Category.assoc, hl, hk_ι])
    rw [← Category.assoc, hl_ι, hg₀']
  · rw [Category.assoc, hfac, ← Category.assoc, hl, ← Category.assoc, hk_ψ, hh']

/-- **Full infinitesimal lifting property for étale morphisms of analytic adic spaces** along
square-zero quotients by closed ideals of complete Hausdorff sheafy Huber pairs with singleton
spectrum. -/
theorem IsEtaleLocalDescription.existsUnique_of_sqZero_quotient {f : Y ⟶ X}
    (hf : IsEtaleLocalDescription f)
    {C : Type u} [CommRing C] [UniformSpace C] [IsUniformAddGroup C] [IsTopologicalRing C]
    [CompleteSpace C] [T0Space C] [IsHuberRing C]
    (R : Pair C) (hR : IsSheafyForEveryPresentation R.plus) [Subsingleton (ofPair R hR).obj]
    (I : Ideal C) (hI : I ^ 2 = ⊥) (hI_closed : IsClosed (I : Set C))
    (hRI : IsSheafyForEveryPresentation (R.quotient I).plus)
    (z₀ : (ofPair (R.quotient I) hRI).obj)
    (g₀ : ofPair (R.quotient I) hRI ⟶ Y) (h : ofPair R hR ⟶ X)
    (hsq : g₀ ≫ f = comapOfPair hR hRI (Pair.quotientHom R I) ≫ h) :
    ∃! g : ofPair R hR ⟶ Y,
      comapOfPair hR hRI (Pair.quotientHom R I) ≫ g = g₀ ∧ g ≫ f = h := by
  obtain ⟨g, hg₁, hg₂⟩ := hf.exists_of_sqZero_quotient R hR I hI hI_closed hRI z₀ g₀ h hsq
  exact ⟨g, ⟨hg₁, hg₂⟩, fun g' ⟨hg'₁, hg'₂⟩ ↦
    hf.eq_of_sqZero_quotient R hR I hI hI_closed hRI z₀ (hg'₂.trans hg₂.symm)
      (hg'₁.trans hg₁.symm)⟩

end InfinitesimalLifting

end AdicSpace

end TauCeti
