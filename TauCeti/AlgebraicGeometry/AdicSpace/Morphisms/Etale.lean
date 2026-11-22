/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Morphisms.Finite.Etale

import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.GlueMorphisms
import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.LocallyOfFiniteType.Local
import TauCeti.RingTheory.Huber.ModuleTopology.FiniteEtale

/-!
# Étale morphisms of analytic adic spaces

A morphism `f : Y ⟶ X` of analytic adic spaces is *étale* in the local-factorization sense of
Kedlaya–Liu and Scholze (`TauCeti.AdicSpace.IsEtaleLocalDescription`) when `X` and `Y` are analytic
and every point of `Y` has an open neighbourhood `U` over which `f` factors as an open immersion
`j : U ⟶ W`, followed by a finite étale morphism `g : W ⟶ V`, followed by an open immersion
`i : V ⟶ X`. Neither locally noetherian hypotheses nor separatedness are imposed; the name
`IsEtaleLocalDescription` distinguishes this notion from Huber's infinitesimal criterion on locally
noetherian spaces.

## Main definitions and results

* `TauCeti.AdicSpace.IsEtaleLocalDescription`, `IsEtaleLocalDescription.of_isFiniteEtale`,
  `IsEtaleLocalDescription.of_isOpenImmersion` (into analytic targets), and characterizations of
  `𝟙 X`, isomorphisms, and empty sources.
* `IsEtaleLocalDescription.respectsIso`, `IsEtaleLocalDescription.isOpenImmersion_comp`,
  `IsEtaleLocalDescription.comp_isOpenImmersion` (into analytic targets), source locality
  (`isEtaleLocalDescription_iff_of_jointly_surjective`,
  `isEtaleLocalDescription_iff_of_iSup_eq_top_source`, into analytic targets), and target-cover
  descent (`IsEtaleLocalDescription.of_iSup_eq_top`).
* `IsEtaleLocalDescription.AffinoidFactorization` and
  `IsEtaleLocalDescription.exists_affinoid_factorization`: refinement of the middle finite étale
  factor to complete Hausdorff Tate affinoid charts via `comapOfPair`.
* `IsEtaleLocalDescription.locallyOfFiniteType`,
  `IsEtaleLocalDescription.isLocallyNoetherianAnalytic_source`.
* `IsEtaleLocalDescription.eq_of_sqZero_quotient`,
  `IsEtaleLocalDescription.exists_of_sqZero_quotient`,
  `IsEtaleLocalDescription.existsUnique_of_sqZero_quotient`: unique infinitesimal lifting along
  square-zero quotients (`I ^ 2 = ⊥`) of sheafy Huber pairs `(C, R)` with sheafy quotient pair
  `R.quotient I`.

## References

* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory: foundations*, Astérisque 371 (2015),
  §8.2, Definition 8.2.16.
* P. Scholze, *Perfectoid spaces*, Publ. Math. IHÉS 116 (2012), §7, Definition 7.1(iii).
* P. Scholze, *Étale cohomology of diamonds*, arXiv:1709.07343, §6, Definition 6.2(ii).
* R. Huber, *Étale cohomology of rigid analytic varieties and adic spaces*, Aspects of Mathematics
  E30 (1996), §1.6–1.7.
-/

public section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Topology

namespace TauCeti.AdicSpace

open Huber PreAdicSpace ValuationSpectrum

universe u

variable {X Y Z : AdicSpace.{u}}

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
theorem isEtaleLocalDescription_iff (f : Y ⟶ X) : IsEtaleLocalDescription f ↔
    X.IsAnalytic ∧ Y.IsAnalytic ∧ ∀ y : Y.obj,
      ∃ (U V W : AdicSpace.{u}) (u : U ⟶ Y) (i : V ⟶ X) (j : U ⟶ W) (g : W ⟶ V),
        PreAdicSpace.IsOpenImmersion u.hom ∧ y ∈ Set.range u.hom.base ∧
          PreAdicSpace.IsOpenImmersion i.hom ∧ PreAdicSpace.IsOpenImmersion j.hom ∧
          IsFiniteEtale g ∧ u ≫ f = j ≫ g ≫ i := Iff.rfl

/-- The target of an étale morphism is analytic. -/
theorem IsEtaleLocalDescription.isAnalytic_target {f : Y ⟶ X} (hf : IsEtaleLocalDescription f) :
    X.IsAnalytic := hf.1

/-- The source of an étale morphism is analytic. -/
theorem IsEtaleLocalDescription.isAnalytic_source {f : Y ⟶ X} (hf : IsEtaleLocalDescription f) :
    Y.IsAnalytic := hf.2.1

/-- **Every finite étale morphism is étale.** -/
theorem IsEtaleLocalDescription.of_isFiniteEtale {f : Y ⟶ X} (hf : IsFiniteEtale f) :
    IsEtaleLocalDescription f :=
  ⟨hf.isAnalytic_target, hf.isAnalytic_source, fun y ↦
    ⟨Y, X, Y, 𝟙 Y, 𝟙 X, 𝟙 Y, f, inferInstance, ⟨y, rfl⟩, inferInstance, inferInstance, hf, by simp⟩⟩

/-- **Every open immersion into an analytic adic space is étale.** -/
theorem IsEtaleLocalDescription.of_isOpenImmersion (f : Y ⟶ X)
    [PreAdicSpace.IsOpenImmersion f.hom] (hX : X.IsAnalytic) : IsEtaleLocalDescription f :=
  ⟨hX, hX.of_isOpenImmersion f, fun y ↦ ⟨Y, X, X, 𝟙 Y, 𝟙 X, f, 𝟙 X, inferInstance, ⟨y, rfl⟩,
    inferInstance, inferInstance, isFiniteEtale_id hX, by simp⟩⟩

/-- **An open immersion in `AdicSpace` is étale if and only if its target is analytic.** -/
theorem isEtaleLocalDescription_iff_of_isOpenImmersion (f : Y ⟶ X)
    [PreAdicSpace.IsOpenImmersion f.hom] : IsEtaleLocalDescription f ↔ X.IsAnalytic :=
  ⟨IsEtaleLocalDescription.isAnalytic_target, IsEtaleLocalDescription.of_isOpenImmersion f⟩

/-- **The identity of an analytic adic space is étale.** -/
theorem IsEtaleLocalDescription.id {X : AdicSpace.{u}} (hX : X.IsAnalytic) :
    IsEtaleLocalDescription (𝟙 X) := .of_isFiniteEtale (isFiniteEtale_id hX)

/-- **The identity of an adic space `X` is étale if and only if `X` is analytic.** -/
@[simp] theorem isEtaleLocalDescription_id_iff {X : AdicSpace.{u}} :
    IsEtaleLocalDescription (𝟙 X) ↔ X.IsAnalytic :=
  ⟨IsEtaleLocalDescription.isAnalytic_target, IsEtaleLocalDescription.id⟩

/-- **An isomorphism onto an analytic adic space is étale.** -/
theorem IsEtaleLocalDescription.of_isIso (f : Y ⟶ X) [IsIso f] (hX : X.IsAnalytic) :
    IsEtaleLocalDescription f := .of_isFiniteEtale (isFiniteEtale_of_isIso f hX)

/-- **An isomorphism in `AdicSpace` is étale if and only if its target is analytic.** -/
theorem isEtaleLocalDescription_iff_of_isIso (f : Y ⟶ X) [IsIso f] :
    IsEtaleLocalDescription f ↔ X.IsAnalytic :=
  ⟨IsEtaleLocalDescription.isAnalytic_target, IsEtaleLocalDescription.of_isIso f⟩

/-- **Every morphism from an empty adic space into an analytic adic space is étale.** -/
theorem IsEtaleLocalDescription.of_isEmpty (f : Y ⟶ X) [IsEmpty Y.obj] (hX : X.IsAnalytic) :
    IsEtaleLocalDescription f := .of_isFiniteEtale (IsFiniteEtale.of_isEmpty f hX)

/-- **A morphism from an empty adic space into `X` is étale if and only if `X` is analytic.** -/
theorem isEtaleLocalDescription_iff_of_isEmpty (f : Y ⟶ X) [IsEmpty Y.obj] :
    IsEtaleLocalDescription f ↔ X.IsAnalytic :=
  ⟨IsEtaleLocalDescription.isAnalytic_target, IsEtaleLocalDescription.of_isEmpty f⟩

/-! ### Stability under open immersions, isomorphisms, and covers -/

/-- **Precomposing an étale morphism with an open immersion gives an étale morphism.** -/
theorem IsEtaleLocalDescription.isOpenImmersion_comp {f : Y ⟶ X}
    (hf : IsEtaleLocalDescription f) (v : Z ⟶ Y) [PreAdicSpace.IsOpenImmersion v.hom] :
    IsEtaleLocalDescription (v ≫ f) := by
  refine ⟨hf.isAnalytic_target, hf.isAnalytic_source.of_isOpenImmersion v, fun z ↦ ?_⟩
  obtain ⟨U, V, W, u, i, j, g, hu, ⟨u₀, hu₀⟩, hi, hj, hg, hfac⟩ := hf.2.2 (v.hom.base z)
  let U' : AdicSpace.{u} :=
    ⟨pullback u.hom v.hom, isAdic_of_isOpenImmersion Z.property (pullback.snd u.hom v.hom)⟩
  let u' : U' ⟶ Z := ObjectProperty.homMk (pullback.snd u.hom v.hom)
  let l : U' ⟶ U := ObjectProperty.homMk (pullback.fst u.hom v.hom)
  have hz : z ∈ Set.range u'.hom.base := by
    rw [ObjectProperty.homMk_hom, IsOpenImmersion.range_pullback_snd_of_left]; exact ⟨u₀, hu₀⟩
  refine ⟨U', V, W, u', i, l ≫ j, g, inferInstance, hz, hi, ?_, hg, ?_⟩
  · rw [ObjectProperty.FullSubcategory.comp_hom]; infer_instance
  · have huv : u' ≫ v = l ≫ u := by
      ext1
      simp only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom, u', l]
      exact pullback.condition.symm
    simp only [reassoc_of% huv, hfac, Category.assoc]

/-- **Postcomposing an étale morphism with an open immersion into an analytic target gives an étale
morphism.** -/
theorem IsEtaleLocalDescription.comp_isOpenImmersion {f : Y ⟶ X} (hf : IsEtaleLocalDescription f)
    (v : X ⟶ Z) [PreAdicSpace.IsOpenImmersion v.hom] (hZ : Z.IsAnalytic) :
    IsEtaleLocalDescription (f ≫ v) := by
  refine ⟨hZ, hf.isAnalytic_source, fun y ↦ ?_⟩
  obtain ⟨U, V, W, u, i, j, g, hu, hy, hi, hj, hg, hfac⟩ := hf.2.2 y
  refine ⟨U, V, W, u, i ≫ v, j, g, hu, hy, ?_, hj, hg, ?_⟩
  · rw [ObjectProperty.FullSubcategory.comp_hom]; infer_instance
  · simp only [reassoc_of% hfac]

/-- Being étale (`IsEtaleLocalDescription`) is invariant under isomorphisms of source and target. -/
instance IsEtaleLocalDescription.respectsIso :
    MorphismProperty.RespectsIso (@IsEtaleLocalDescription.{u}) :=
  MorphismProperty.RespectsIso.mk _
    (fun e _ hf ↦ have := (ObjectProperty.ι isAdic).map_isIso e.hom; hf.isOpenImmersion_comp e.hom)
    (fun e _ hf ↦ have := (ObjectProperty.ι isAdic).map_isIso e.hom
      hf.comp_isOpenImmersion e.hom (hf.isAnalytic_target.of_iso e.symm))

/-- **Source locality of étale morphisms.** Let `f : Y ⟶ X` be a morphism into an analytic adic
space `X`. If open immersions `u k : U k ⟶ Y` jointly cover `Y` and every composite `u k ≫ f`
satisfies `IsEtaleLocalDescription`, then `f` satisfies `IsEtaleLocalDescription`. -/
theorem IsEtaleLocalDescription.of_jointly_surjective {f : Y ⟶ X} (hX : X.IsAnalytic) {ι : Type*}
    {U : ι → AdicSpace.{u}} (u : ∀ k, U k ⟶ Y) [∀ k, PreAdicSpace.IsOpenImmersion (u k).hom]
    (hcov : ∀ y : Y.obj, ∃ (k : ι) (z : (U k).obj), (u k).hom.base z = y)
    (hf : ∀ k, IsEtaleLocalDescription (u k ≫ f)) : IsEtaleLocalDescription f := by
  refine ⟨hX, .of_jointly_surjective u (fun k ↦ (hf k).isAnalytic_source) hcov, fun y ↦ ?_⟩
  obtain ⟨k, z, rfl⟩ := hcov y
  obtain ⟨U', V', W', u', i, j, g, hu', ⟨q, hq⟩, hi, hj, hg, hfac⟩ := (hf k).2.2 z
  refine ⟨U', V', W', u' ≫ u k, i, j, g, ?_, ⟨q, by simp [hq]⟩, hi, hj, hg, ?_⟩
  · rw [ObjectProperty.FullSubcategory.comp_hom]; infer_instance
  · rw [Category.assoc, hfac]

/-- Being étale (`IsEtaleLocalDescription`) can be tested on any jointly surjective family of open
immersions into the source, provided the target `X` is analytic. -/
theorem isEtaleLocalDescription_iff_of_jointly_surjective {f : Y ⟶ X} (hX : X.IsAnalytic)
    {ι : Type*} {U : ι → AdicSpace.{u}} (u : ∀ k, U k ⟶ Y)
    [∀ k, PreAdicSpace.IsOpenImmersion (u k).hom]
    (hcov : ∀ y : Y.obj, ∃ (k : ι) (z : (U k).obj), (u k).hom.base z = y) :
    IsEtaleLocalDescription f ↔ ∀ k, IsEtaleLocalDescription (u k ≫ f) :=
  ⟨fun hf k ↦ hf.isOpenImmersion_comp (u k), .of_jointly_surjective hX u hcov⟩

/-- **Source-cover descent along opens of `Y`.** If `X` is analytic, `U : ι → Opens Y.obj` covers
`Y`, and the restriction of `f : Y ⟶ X` to each `U k` satisfies `IsEtaleLocalDescription`, then `f`
satisfies `IsEtaleLocalDescription`. -/
theorem IsEtaleLocalDescription.of_iSup_eq_top_source {f : Y ⟶ X} (hX : X.IsAnalytic) {ι : Type*}
    (U : ι → Opens Y.obj) (hU : iSup U = ⊤)
    (hf : ∀ k, IsEtaleLocalDescription (Y.ofRestrict (U k) ≫ f)) :
    IsEtaleLocalDescription f :=
  .of_jointly_surjective hX (fun k ↦ Y.ofRestrict (U k))
    (fun y ↦ let ⟨k, hk⟩ := Opens.mem_iSup.mp (hU.symm ▸ trivial : y ∈ iSup U)
      ⟨k, ⟨y, hk⟩, Y.ofRestrict_base_apply (U k) ⟨y, hk⟩⟩)
    hf

/-- Being étale (`IsEtaleLocalDescription`) is local on the source for morphisms into an analytic
target `X`. -/
theorem isEtaleLocalDescription_iff_of_iSup_eq_top_source {f : Y ⟶ X} (hX : X.IsAnalytic)
    {ι : Type*} (U : ι → Opens Y.obj) (hU : iSup U = ⊤) :
    IsEtaleLocalDescription f ↔ ∀ k, IsEtaleLocalDescription (Y.ofRestrict (U k) ≫ f) :=
  ⟨fun hf _ ↦ hf.isOpenImmersion_comp _, .of_iSup_eq_top_source hX U hU⟩

/-- **Target-cover descent for étale morphisms.** If `V : ι → Opens X.obj` covers `X` and the
preimage restriction of `f : Y ⟶ X` over every `V k` satisfies `IsEtaleLocalDescription`, then `f`
satisfies `IsEtaleLocalDescription`. -/
theorem IsEtaleLocalDescription.of_iSup_eq_top {f : Y ⟶ X} {ι : Type*} (V : ι → Opens X.obj)
    (hV : iSup V = ⊤) (hf : ∀ k, IsEtaleLocalDescription (AdicSpace.restrictPreimage f (V k))) :
    IsEtaleLocalDescription f := by
  have hX : X.IsAnalytic := .of_jointly_surjective (fun k ↦ X.ofRestrict (V k))
    (fun k ↦ (hf k).isAnalytic_target)
    fun x ↦ let ⟨k, hx⟩ := Opens.mem_iSup.mp (hV.symm ▸ trivial : x ∈ iSup V)
      ⟨k, ⟨x, hx⟩, X.ofRestrict_base_apply (V k) ⟨x, hx⟩⟩
  let U : ι → Opens Y.obj := fun k ↦ (Opens.map f.hom.base).obj (V k)
  have hU : iSup U = ⊤ := eq_top_iff.mpr fun y _ ↦
    let ⟨k, hk⟩ := Opens.mem_iSup.mp (hV.symm ▸ trivial : f.hom.base y ∈ iSup V)
    Opens.mem_iSup.mpr ⟨k, hk⟩
  refine .of_iSup_eq_top_source hX U hU fun k ↦ ?_
  rw [← AdicSpace.restrictPreimage_ofRestrict f (V k)]
  exact (hf k).comp_isOpenImmersion (X.ofRestrict (V k)) hX

/-! ### Refinement to affinoid middle factors and finiteness properties -/

/-- A local factorization of an étale morphism `f : Y ⟶ X` around `y : Y.obj` through a finite
étale morphism `comapOfPair isSheafyTarget isSheafySource pairHom` of complete Hausdorff Tate
affinoid adic spaces. -/
structure IsEtaleLocalDescription.AffinoidFactorization {Y X : AdicSpace.{u}} (f : Y ⟶ X)
    (y : Y.obj) : Type (u + 1) where
  /-- Target coefficient ring of the middle affinoid factor. -/
  Target : Type u
  [commRingTarget : CommRing Target]
  [uniformSpaceTarget : UniformSpace Target]
  [isUniformAddGroupTarget : IsUniformAddGroup Target]
  [isTopologicalRingTarget : IsTopologicalRing Target]
  [completeSpaceTarget : CompleteSpace Target]
  [t2SpaceTarget : T2Space Target]
  [isTateRingTarget : IsTateRing Target]
  /-- Target Huber pair. -/
  targetPair : Pair Target
  /-- Sheafiness of `targetPair`. -/
  isSheafyTarget : IsSheafyForEveryPresentation targetPair.plus
  /-- Source coefficient ring of the middle affinoid factor. -/
  Source : Type u
  [commRingSource : CommRing Source]
  [uniformSpaceSource : UniformSpace Source]
  [isUniformAddGroupSource : IsUniformAddGroup Source]
  [isTopologicalRingSource : IsTopologicalRing Source]
  [completeSpaceSource : CompleteSpace Source]
  [t2SpaceSource : T2Space Source]
  [isTateRingSource : IsTateRing Source]
  /-- Source Huber pair. -/
  sourcePair : Pair Source
  /-- Sheafiness of `sourcePair`. -/
  isSheafySource : IsSheafyForEveryPresentation sourcePair.plus
  /-- Underlying finite étale morphism of Huber pairs. -/
  pairHom : Pair.Hom targetPair sourcePair
  /-- Proof that `pairHom` is finite étale. -/
  isFiniteEtale : pairHom.IsFiniteEtale
  /-- Open neighbourhood around `y`. -/
  U : AdicSpace.{u}
  /-- Open immersion from `U` into `Y`. -/
  u : U ⟶ Y
  /-- Open immersion from `U` into the middle source affinoid. -/
  j : U ⟶ ofPair sourcePair isSheafySource
  /-- Open immersion from the middle target affinoid into `X`. -/
  i : ofPair targetPair isSheafyTarget ⟶ X
  [isOpenImmersion_u : PreAdicSpace.IsOpenImmersion u.hom]
  /-- Membership of `y` in the image of `u`. -/
  mem : y ∈ Set.range u.hom.base
  [isOpenImmersion_j : PreAdicSpace.IsOpenImmersion j.hom]
  [isOpenImmersion_i : PreAdicSpace.IsOpenImmersion i.hom]
  /-- Factorization equation `u ≫ f = j ≫ comapOfPair ... ≫ i`. -/
  fac : u ≫ f = j ≫ comapOfPair isSheafyTarget isSheafySource pairHom ≫ i

attribute [instance] IsEtaleLocalDescription.AffinoidFactorization.commRingTarget
  IsEtaleLocalDescription.AffinoidFactorization.uniformSpaceTarget
  IsEtaleLocalDescription.AffinoidFactorization.isUniformAddGroupTarget
  IsEtaleLocalDescription.AffinoidFactorization.isTopologicalRingTarget
  IsEtaleLocalDescription.AffinoidFactorization.completeSpaceTarget
  IsEtaleLocalDescription.AffinoidFactorization.t2SpaceTarget
  IsEtaleLocalDescription.AffinoidFactorization.isTateRingTarget
  IsEtaleLocalDescription.AffinoidFactorization.commRingSource
  IsEtaleLocalDescription.AffinoidFactorization.uniformSpaceSource
  IsEtaleLocalDescription.AffinoidFactorization.isUniformAddGroupSource
  IsEtaleLocalDescription.AffinoidFactorization.isTopologicalRingSource
  IsEtaleLocalDescription.AffinoidFactorization.completeSpaceSource
  IsEtaleLocalDescription.AffinoidFactorization.t2SpaceSource
  IsEtaleLocalDescription.AffinoidFactorization.isTateRingSource
  IsEtaleLocalDescription.AffinoidFactorization.isOpenImmersion_u
  IsEtaleLocalDescription.AffinoidFactorization.isOpenImmersion_j
  IsEtaleLocalDescription.AffinoidFactorization.isOpenImmersion_i

/-- **Refinement of local factorizations of an étale morphism to complete Hausdorff Tate affinoid
middle factors** via `comapOfPair`. -/
theorem IsEtaleLocalDescription.exists_affinoid_factorization {f : Y ⟶ X}
    (hf : IsEtaleLocalDescription f) (y : Y.obj) :
    Nonempty (IsEtaleLocalDescription.AffinoidFactorization f y) := by
  obtain ⟨U₀, V₀, W₀, u₀, i₀, j₀, g₀, hu₀, ⟨p₀, hp₀⟩, hi₀, hj₀, hg₀, hfac₀⟩ := hf.2.2 y
  obtain ⟨c⟩ := hg₀.exists_ofPair_chart (g₀.hom.base (j₀.hom.base p₀))
  let w := W₀.obj.ofRestrict ((Opens.map g₀.hom.base).obj c.V).isOpenEmbedding
  let U : AdicSpace.{u} :=
    ⟨pullback w j₀.hom, isAdic_of_isOpenImmersion U₀.property (pullback.snd w j₀.hom)⟩
  let r : U ⟶ U₀ := ObjectProperty.homMk (pullback.snd w j₀.hom)
  let j : U ⟶ ofPair c.sourcePair c.isSheafySource :=
    ObjectProperty.homMk (pullback.fst w j₀.hom ≫ c.sourceIso.hom)
  let i : ofPair c.targetPair c.isSheafyTarget ⟶ X :=
    ObjectProperty.homMk (c.targetIso.inv ≫ V₀.obj.ofRestrict c.V.isOpenEmbedding ≫ i₀.hom)
  obtain ⟨q₀, hq₀⟩ : p₀ ∈ Set.range r.hom.base := by
    rw [ObjectProperty.homMk_hom, IsOpenImmersion.range_pullback_snd_of_left]
    exact ⟨⟨j₀.hom.base p₀, Opens.mem_map.mpr c.mem⟩, rfl⟩
  have _ : PreAdicSpace.IsOpenImmersion (r ≫ u₀).hom := by
    rw [ObjectProperty.FullSubcategory.comp_hom]; infer_instance
  refine ⟨{
    Target := c.Target
    targetPair := c.targetPair
    isSheafyTarget := c.isSheafyTarget
    Source := c.Source
    sourcePair := c.sourcePair
    isSheafySource := c.isSheafySource
    pairHom := c.pairHom
    isFiniteEtale := c.isFiniteEtale
    U := U
    u := r ≫ u₀
    j := j
    i := i
    mem := ⟨q₀, by simp [hq₀, hp₀]⟩
    fac := ?_ }⟩
  ext1
  have h1 := congrArg (r.hom ≫ InducedCategory.Hom.hom ·) hfac₀
  simp only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom, r, j, i,
    Category.assoc] at h1 ⊢
  rw [h1, ← pullback.condition_assoc]
  simp only [w, reassoc_of% c.fac]

/-- **An étale morphism of analytic adic spaces is locally of finite type.** -/
theorem IsEtaleLocalDescription.locallyOfFiniteType {f : Y ⟶ X} (hf : IsEtaleLocalDescription f) :
    PreAdicSpace.LocallyOfFiniteType f.hom := by
  choose U V W u i j g hu hy hi hj hg hfac using hf.2.2
  let O : Y.obj → Opens Y.obj := fun y ↦ ⟨Set.range (u y).hom.base, (hu y).base_open.isOpen_range⟩
  refine PreAdicSpace.LocallyOfFiniteType.of_iSup_eq_top O
    (eq_top_iff.mpr fun y _ ↦ Opens.mem_iSup.mpr ⟨y, hy y⟩) fun y ↦ ?_
  have huf : PreAdicSpace.LocallyOfFiniteType ((u y).hom ≫ f.hom) := by
    have hfac' : (u y).hom ≫ f.hom = ((j y).hom ≫ (g y).hom) ≫ (i y).hom := by
      simpa only [ObjectProperty.FullSubcategory.comp_hom, Category.assoc] using
        congrArg InducedCategory.Hom.hom (hfac y)
    rw [hfac']
    exact ((hg y).isFinite.locallyOfFiniteType.comp_of_isOpenImmersion _).isOpenImmersion_comp _
  rw [← IsOpenImmersion.isoOfRangeEq_inv_comp (u y).hom (Y.obj.ofRestrict (O y).isOpenEmbedding)
      (Opens.set_range_inclusion' (O y)).symm, Category.assoc,
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

section AffinoidChart

variable {f : Y ⟶ X} {A : Type u} [CommRing A] [UniformSpace A] [IsUniformAddGroup A]
  [IsTopologicalRing A] [CompleteSpace A] [T0Space A] [IsHuberRing A] {S : Pair A}
  (hS : IsSheafyForEveryPresentation S.plus) {B : Type u} [CommRing B] [UniformSpace B]
  [IsUniformAddGroup B] [IsTopologicalRing B] [CompleteSpace B] [T0Space B] [IsHuberRing B]
  {T : Pair B} (hT : IsSheafyForEveryPresentation T.plus) {ψ : Pair.Hom S T}
  {U : AdicSpace.{u}} {u : U ⟶ Y} {j : U ⟶ ofPair T hT} {i : ofPair S hS ⟶ X}
  [PreAdicSpace.IsOpenImmersion u.hom] [PreAdicSpace.IsOpenImmersion j.hom]
  [PreAdicSpace.IsOpenImmersion i.hom] {A₁ : Type u} [CommRing A₁] [UniformSpace A₁]
  [IsUniformAddGroup A₁] [IsTopologicalRing A₁] [CompleteSpace A₁] [T0Space A₁] [IsHuberRing A₁]
  {S₁ : Pair A₁} (hS₁ : IsSheafyForEveryPresentation S₁.plus) {K : Ideal A₁}
  (hSK : IsSheafyForEveryPresentation (S₁.quotient K).plus) [T0Space (A₁ ⧸ K)]

private theorem eq_of_affinoid_factorization (hψ : ψ.IsFiniteEtale)
    (hfac : u ≫ f = j ≫ comapOfPair hS hT ψ ≫ i)
    (hcompK : @CompleteSpace (A₁ ⧸ K) (IsTopologicalAddGroup.rightUniformSpace (A₁ ⧸ K)))
    (hK : K ^ 2 = ⊥) {g₁ g₂ : ofPair S₁ hS₁ ⟶ Y}
    (hr₁ : Set.range g₁.hom.base ⊆ Set.range u.hom.base)
    (hr₂ : Set.range g₂.hom.base ⊆ Set.range u.hom.base) (hf_eq : g₁ ≫ f = g₂ ≫ f)
    (hK_eq : comapOfPair hS₁ hSK (Pair.quotientHom S₁ K) ≫ g₁ =
      comapOfPair hS₁ hSK (Pair.quotientHom S₁ K) ≫ g₂) : g₁ = g₂ := by
  let _ : UniformSpace (A₁ ⧸ K) := IsTopologicalAddGroup.rightUniformSpace (A₁ ⧸ K)
  have _ : IsUniformAddGroup (A₁ ⧸ K) := isUniformAddGroup_of_addCommGroup
  have _ : CompleteSpace (A₁ ⧸ K) := hcompK
  let l₁ := liftOfIsOpenImmersion u g₁ hr₁
  let l₂ := liftOfIsOpenImmersion u g₂ hr₂
  have hk_f : (l₁ ≫ j) ≫ comapOfPair hS hT ψ = (l₂ ≫ j) ≫ comapOfPair hS hT ψ :=
    (cancel_mono i).mp (by
      simpa only [Category.assoc, ← hfac] using
        (congrArg (· ≫ f) (liftOfIsOpenImmersion_fac u g₁ hr₁)).trans
          (hf_eq.trans (congrArg (· ≫ f) (liftOfIsOpenImmersion_fac u g₂ hr₂)).symm))
  have hl_K : comapOfPair hS₁ hSK (Pair.quotientHom S₁ K) ≫ l₁ =
      comapOfPair hS₁ hSK (Pair.quotientHom S₁ K) ≫ l₂ :=
    (cancel_mono u).mp (by simp [l₁, l₂, Category.assoc, hK_eq])
  have hσ_ψ := congrArg (ofPairHomEquiv hS hS₁) hk_f
  have hσ_K := congrArg (ofPairHomEquiv hT hSK) ((reassoc_of% hl_K) j)
  simp only [ofPairHomEquiv_comp, ofPairHomEquiv_comapOfPair] at hσ_ψ hσ_K
  rw [← liftOfIsOpenImmersion_fac u g₁ hr₁, ← liftOfIsOpenImmersion_fac u g₂ hr₂]
  exact congrArg (· ≫ u)
    ((cancel_mono j).mp
      ((ofPairHomEquiv hT hS₁).injective (hψ.eq_of_sqZero_quotient hK hσ_ψ hσ_K)))

private theorem exists_of_affinoid_factorization (hψ : ψ.IsFiniteEtale)
    (hfac : u ≫ f = j ≫ comapOfPair hS hT ψ ≫ i)
    (hcompK : @CompleteSpace (A₁ ⧸ K) (IsTopologicalAddGroup.rightUniformSpace (A₁ ⧸ K)))
    (hK : K ^ 2 = ⊥) (g₀ : ofPair (S₁.quotient K) hSK ⟶ Y) (h : ofPair S₁ hS₁ ⟶ X)
    (hsq : g₀ ≫ f = comapOfPair hS₁ hSK (Pair.quotientHom S₁ K) ≫ h)
    (hr₀ : Set.range g₀.hom.base ⊆ Set.range u.hom.base) :
    ∃ g : ofPair S₁ hS₁ ⟶ Y, comapOfPair hS₁ hSK (Pair.quotientHom S₁ K) ≫ g = g₀ ∧ g ≫ f = h := by
  let _ : UniformSpace (A₁ ⧸ K) := IsTopologicalAddGroup.rightUniformSpace (A₁ ⧸ K)
  have _ : IsUniformAddGroup (A₁ ⧸ K) := isUniformAddGroup_of_addCommGroup
  have _ : CompleteSpace (A₁ ⧸ K) := hcompK
  let πK := comapOfPair hS₁ hSK (Pair.quotientHom S₁ K)
  have hsurj : Function.Surjective πK.hom.base :=
    (isHomeomorph_comapOfPair_quotientHom_base_of_isNilpotent S₁ hS₁ K hSK ⟨2, hK⟩).surjective
  -- Factor `g₀` through `u` and `h` through `i` via surjectivity of `πK`
  let g₀' := liftOfIsOpenImmersion u g₀ hr₀
  have hhr : Set.range h.hom.base ⊆ Set.range i.hom.base := by
    rintro _ ⟨z₁, rfl⟩; obtain ⟨z₂, rfl⟩ := hsurj z₁
    exact ⟨_, (congrArg (fun m : ofPair (S₁.quotient K) hSK ⟶ X ↦ m.hom.base z₂)
      (by rw [← hsq, ← liftOfIsOpenImmersion_fac u g₀ hr₀, Category.assoc, hfac] :
        πK ≫ h = g₀' ≫ j ≫ comapOfPair hS hT ψ ≫ i)).symm⟩
  let h' := liftOfIsOpenImmersion i h hhr
  -- Lift across the finite étale Huber-pair morphism `ψ` via `ofPairHomEquiv`
  have hcomm_space : (g₀' ≫ j) ≫ comapOfPair hS hT ψ = πK ≫ h' := by
    refine (cancel_mono i).mp ?_
    calc ((g₀' ≫ j) ≫ comapOfPair hS hT ψ) ≫ i
        = g₀' ≫ j ≫ comapOfPair hS hT ψ ≫ i := by simp only [Category.assoc]
      _ = g₀' ≫ u ≫ f := by rw [← hfac]
      _ = g₀ ≫ f := liftOfIsOpenImmersion_fac_assoc u g₀ hr₀ f
      _ = πK ≫ h := hsq
      _ = (πK ≫ h') ≫ i := by rw [Category.assoc, liftOfIsOpenImmersion_fac]
  have hcomm_pair := congrArg (ofPairHomEquiv hS hSK) hcomm_space
  simp only [πK, ofPairHomEquiv_comp, ofPairHomEquiv_comapOfPair] at hcomm_pair
  obtain ⟨β, hβ_ψ, hβ_K⟩ := hψ.exists_of_sqZero_quotient hK _ _ hcomm_pair
  let k : ofPair S₁ hS₁ ⟶ ofPair T hT := comapOfPair hT hS₁ β
  have hk_K : πK ≫ k = g₀' ≫ j := by rw [← comapOfPair_comp, hβ_K, comapOfPair_ofPairHomEquiv]
  have hk_ψ : k ≫ comapOfPair hS hT ψ = h' := by
    rw [← comapOfPair_comp, hβ_ψ, comapOfPair_ofPairHomEquiv]
  -- Factor `k` back through the open immersion `j : U ⟶ ofPair T hT`
  have hkr : Set.range k.hom.base ⊆ Set.range j.hom.base := by
    rintro _ ⟨z₁, rfl⟩; obtain ⟨z₂, rfl⟩ := hsurj z₁
    exact ⟨g₀'.hom.base z₂, (congrArg (fun m ↦ m.hom.base z₂) hk_K).symm⟩
  let l := liftOfIsOpenImmersion j k hkr
  refine ⟨l ≫ u, ?_, ?_⟩
  · have hlj : πK ≫ l = g₀' :=
      (cancel_mono j).mp (by rw [Category.assoc, liftOfIsOpenImmersion_fac, hk_K])
    rw [(reassoc_of% hlj) u, liftOfIsOpenImmersion_fac]
  · calc (l ≫ u) ≫ f
        = l ≫ u ≫ f := Category.assoc _ _ _
      _ = l ≫ j ≫ comapOfPair hS hT ψ ≫ i := by rw [hfac]
      _ = k ≫ comapOfPair hS hT ψ ≫ i := by rw [liftOfIsOpenImmersion_fac_assoc]
      _ = h' ≫ i := by rw [reassoc_of% hk_ψ]
      _ = h := liftOfIsOpenImmersion_fac _ _ _

end AffinoidChart

variable {C : Type u} [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsHuberRing C]

/-- **Formal unramifiedness of étale morphisms along square-zero quotients.** Let `f : Y ⟶ X`
satisfy `IsEtaleLocalDescription`, and let `(C, R)` be a sheafy Huber pair and `I : Ideal C` a
square-zero ideal (`I ^ 2 = ⊥`) whose quotient Huber pair `R.quotient I` is sheafy. Any two
morphisms `g₁, g₂ : Spa(C, R⁺) ⟶ Y` that agree after composing with `f` and after restricting to
`Spa(C ⧸ I, (R.quotient I)⁺)` are equal. -/
theorem IsEtaleLocalDescription.eq_of_sqZero_quotient {f : Y ⟶ X} (hf : IsEtaleLocalDescription f)
    (R : Pair C) (hR : IsSheafyForEveryPresentation R.plus) (I : Ideal C) (hI : I ^ 2 = ⊥)
    (hRI : IsSheafyForEveryPresentation (R.quotient I).plus) {g₁ g₂ : ofPair R hR ⟶ Y}
    (hf_eq : g₁ ≫ f = g₂ ≫ f)
    (hι_eq : comapOfPair hR hRI (Pair.quotientHom R I) ≫ g₁ =
      comapOfPair hR hRI (Pair.quotientHom R I) ≫ g₂) : g₁ = g₂ := by
  have hι := isHomeomorph_comapOfPair_quotientHom_base_of_isNilpotent R hR I hRI ⟨2, hI⟩
  have hbase_eq : g₁.hom.base = g₂.hom.base := by
    ext z; obtain ⟨z₀, rfl⟩ := hι.surjective z; exact congrArg (fun m ↦ m.hom.base z₀) hι_eq
  refine InducedCategory.Hom.ext (PreAdicSpace.hom_ext_of_forall_exists_isOpenImmersion
    (ofPair R hR).property.isSheafy fun z ↦ ?_)
  obtain ⟨fac⟩ := hf.exists_affinoid_factorization (g₁.hom.base z)
  let W : Opens (ofPair R hR).obj := ⟨g₁.hom.base ⁻¹' Set.range fac.u.hom.base,
    fac.isOpenImmersion_u.base_open.isOpen_range.preimage g₁.hom.base.hom.continuous⟩
  obtain ⟨sq⟩ := exists_ofPair_quotient_rational_square R hR I hRI W fac.mem
  have hr₁ : Set.range (sq.targetMap ≫ g₁).hom.base ⊆ Set.range fac.u.hom.base := by
    rintro _ ⟨q, rfl⟩
    exact sq.le (by rw [← SetLike.mem_coe, ← sq.range_targetMap]; exact ⟨q, rfl⟩)
  have hr₂ : Set.range (sq.targetMap ≫ g₂).hom.base ⊆ Set.range fac.u.hom.base := by
    rintro _ ⟨q, rfl⟩
    have hq : (sq.targetMap ≫ g₁).hom.base q ∈ Set.range fac.u.hom.base := hr₁ ⟨q, rfl⟩
    simpa [hbase_eq] using hq
  have hvg : sq.targetMap ≫ g₁ = sq.targetMap ≫ g₂ :=
    eq_of_affinoid_factorization fac.isSheafyTarget fac.isSheafySource
      sq.isSheafy sq.isSheafyQuotient
      fac.isFiniteEtale fac.fac sq.completeSpaceQuotient (sq.pow_eq_bot hI) hr₁ hr₂
      (by simp only [Category.assoc, hf_eq])
      (by simp only [reassoc_of% sq.comm, hι_eq])
  exact ⟨(ofPair sq.pair sq.isSheafy).obj, sq.targetMap.hom, inferInstance,
    sq.range_targetMap.symm ▸ sq.mem, congrArg InducedCategory.Hom.hom hvg⟩

section SqZeroLift

variable {f : Y ⟶ X} (R : Pair C) (hR : IsSheafyForEveryPresentation R.plus) (I : Ideal C)
  (hRI : IsSheafyForEveryPresentation (R.quotient I).plus)
  (g₀ : ofPair (R.quotient I) hRI ⟶ Y) (h : ofPair R hR ⟶ X)

private noncomputable abbrev sqZeroQuotHom : ofPair (R.quotient I) hRI ⟶ ofPair R hR :=
  comapOfPair hR hRI (Pair.quotientHom R I)

private theorem comm_restrictPreimage_of_square {W W₀ Z Z₀ : AdicSpace.{u}}
    {k : W₀ ⟶ W} {v : W ⟶ Z} {u : W₀ ⟶ Z₀} {ι : Z₀ ⟶ Z} (hsq : k ≫ v = u ≫ ι)
    (O : Opens Z.obj) {vO : W.obj ⟶ Z.obj.restrict O.isOpenEmbedding}
    (hvO : vO ≫ Z.obj.ofRestrict O.isOpenEmbedding = v.hom)
    {uO : W₀.obj ⟶ Z₀.obj.restrict ((Opens.map ι.hom.base).obj O).isOpenEmbedding}
    (huO : uO ≫ Z₀.obj.ofRestrict ((Opens.map ι.hom.base).obj O).isOpenEmbedding = u.hom) :
    k.hom ≫ vO = uO ≫ ι.hom.restrictPreimage O := by
  rw [← cancel_mono (Z.obj.ofRestrict O.isOpenEmbedding), Category.assoc, hvO,
    ← ObjectProperty.FullSubcategory.comp_hom, hsq, ObjectProperty.FullSubcategory.comp_hom,
    Category.assoc, Hom.restrictPreimage_ofRestrict, reassoc_of% huO]

section SquareComparison

variable {R hR I hRI} {W : Opens (ofPair R hR).obj} {z : (ofPair R hR).obj}
  (sq : OfPairQuotientRationalSquare R hR I hRI W z)

private noncomputable def sqTargetIso :
    (ofPair sq.pair sq.isSheafy).obj ≅ (ofPair R hR).obj.restrict sq.openSet.isOpenEmbedding :=
  IsOpenImmersion.isoOfRangeEq sq.targetMap.hom
    ((ofPair R hR).obj.ofRestrict sq.openSet.isOpenEmbedding)
    (sq.range_targetMap.trans (Opens.set_range_inclusion' sq.openSet).symm)

private theorem sqTargetIso_hom_ofRestrict :
    (sqTargetIso sq).hom ≫ (ofPair R hR).obj.ofRestrict sq.openSet.isOpenEmbedding =
      sq.targetMap.hom :=
  IsOpenImmersion.isoOfRangeEq_hom_comp _ _ _

private theorem sqTargetIso_inv_targetMap :
    (sqTargetIso sq).inv ≫ sq.targetMap.hom =
      (ofPair R hR).obj.ofRestrict sq.openSet.isOpenEmbedding :=
  IsOpenImmersion.isoOfRangeEq_inv_comp _ _ _

private noncomputable def sqQuotientIso :
    (ofPair (sq.pair.quotient sq.ideal) sq.isSheafyQuotient).obj ≅
      (ofPair (R.quotient I) hRI).obj.restrict
        ((Opens.map (sqZeroQuotHom R hR I hRI).hom.base).obj sq.openSet).isOpenEmbedding :=
  IsOpenImmersion.isoOfRangeEq sq.quotientMap.hom
    ((ofPair (R.quotient I) hRI).obj.ofRestrict
      ((Opens.map (sqZeroQuotHom R hR I hRI).hom.base).obj sq.openSet).isOpenEmbedding)
    (sq.range_quotientMap.trans
      (Opens.set_range_inclusion'
        ((Opens.map (sqZeroQuotHom R hR I hRI).hom.base).obj sq.openSet)).symm)

private theorem sqQuotientIso_hom_ofRestrict :
    (sqQuotientIso sq).hom ≫
      (ofPair (R.quotient I) hRI).obj.ofRestrict
        ((Opens.map (sqZeroQuotHom R hR I hRI).hom.base).obj sq.openSet).isOpenEmbedding =
      sq.quotientMap.hom :=
  IsOpenImmersion.isoOfRangeEq_hom_comp _ _ _

private theorem sqQuotientIso_inv_quotientMap :
    (sqQuotientIso sq).inv ≫ sq.quotientMap.hom =
      (ofPair (R.quotient I) hRI).obj.ofRestrict
        ((Opens.map (sqZeroQuotHom R hR I hRI).hom.base).obj sq.openSet).isOpenEmbedding :=
  IsOpenImmersion.isoOfRangeEq_inv_comp _ _ _

private theorem sqRestrictPreimage :
    (sqZeroQuotHom R hR I hRI).hom.restrictPreimage sq.openSet =
      (sqQuotientIso sq).inv ≫
        (comapOfPair sq.isSheafy sq.isSheafyQuotient (Pair.quotientHom sq.pair sq.ideal)).hom ≫
        (sqTargetIso sq).hom :=
  (Iso.eq_inv_comp (sqQuotientIso sq)).mpr
    (comm_restrictPreimage_of_square sq.comm sq.openSet (sqTargetIso_hom_ofRestrict sq)
      (sqQuotientIso_hom_ofRestrict sq)).symm

private noncomputable def sqTargetIncl {O : Opens (ofPair R hR).obj} (hO : sq.openSet ≤ O) :
    (ofPair sq.pair sq.isSheafy).obj ⟶ (ofPair R hR).obj.restrict O.isOpenEmbedding :=
  (sqTargetIso sq).hom ≫ Hom.liftRestrict (𝟙 (ofPair R hR).obj) (by simpa using hO)

private theorem sqTargetIncl_ofRestrict {O : Opens (ofPair R hR).obj} (hO : sq.openSet ≤ O) :
    sqTargetIncl sq hO ≫ (ofPair R hR).obj.ofRestrict O.isOpenEmbedding = sq.targetMap.hom := by
  rw [sqTargetIncl, Category.assoc, Hom.liftRestrict_ofRestrict, Category.comp_id,
    sqTargetIso_hom_ofRestrict]

private noncomputable def sqQuotientIncl {O : Opens (ofPair R hR).obj} (hO : sq.openSet ≤ O) :
    (ofPair (sq.pair.quotient sq.ideal) sq.isSheafyQuotient).obj ⟶
      (ofPair (R.quotient I) hRI).obj.restrict
        ((Opens.map (sqZeroQuotHom R hR I hRI).hom.base).obj O).isOpenEmbedding :=
  (sqQuotientIso sq).hom ≫
    Hom.liftRestrict (𝟙 (ofPair (R.quotient I) hRI).obj)
      (by simpa using ((Opens.map (sqZeroQuotHom R hR I hRI).hom.base).map (homOfLE hO)).le)

private theorem sqQuotientIncl_ofRestrict {O : Opens (ofPair R hR).obj} (hO : sq.openSet ≤ O) :
    sqQuotientIncl sq hO ≫
      (ofPair (R.quotient I) hRI).obj.ofRestrict
        ((Opens.map (sqZeroQuotHom R hR I hRI).hom.base).obj O).isOpenEmbedding =
      sq.quotientMap.hom := by
  rw [sqQuotientIncl, Category.assoc, Hom.liftRestrict_ofRestrict, Category.comp_id,
    sqQuotientIso_hom_ofRestrict]

private theorem sqIncl_restrictPreimage {O : Opens (ofPair R hR).obj} (hO : sq.openSet ≤ O) :
    (comapOfPair sq.isSheafy sq.isSheafyQuotient (Pair.quotientHom sq.pair sq.ideal)).hom ≫
        sqTargetIncl sq hO =
      sqQuotientIncl sq hO ≫ (sqZeroQuotHom R hR I hRI).hom.restrictPreimage O :=
  comm_restrictPreimage_of_square sq.comm O (sqTargetIncl_ofRestrict sq hO)
    (sqQuotientIncl_ofRestrict sq hO)

end SquareComparison

private theorem exists_local_lift_of_sqZero_quotient (hf : IsEtaleLocalDescription f)
    (hI : I ^ 2 = ⊥) (hsq : g₀ ≫ f = sqZeroQuotHom R hR I hRI ≫ h) (z : (ofPair R hR).obj) :
    ∃ (O : Opens (ofPair R hR).obj), z ∈ O ∧
      ∃ gO : (ofPair R hR).obj.restrict O.isOpenEmbedding ⟶ Y.obj,
        gO ≫ f.hom = (ofPair R hR).obj.ofRestrict O.isOpenEmbedding ≫ h.hom ∧
        (sqZeroQuotHom R hR I hRI).hom.restrictPreimage O ≫ gO =
          (ofPair (R.quotient I) hRI).obj.ofRestrict
            ((Opens.map (sqZeroQuotHom R hR I hRI).hom.base).obj O).isOpenEmbedding ≫ g₀.hom := by
  let Z := ofPair R hR; let ι := sqZeroQuotHom R hR I hRI
  have hι := isHomeomorph_comapOfPair_quotientHom_base_of_isNilpotent R hR I hRI ⟨2, hI⟩
  obtain ⟨z₀, hz₀⟩ := hι.surjective z
  -- Refine around `z` to a rational open `sq.openSet` where `g₀` lands in an affinoid chart
  obtain ⟨fac⟩ := hf.exists_affinoid_factorization (g₀.hom.base z₀)
  let W : Opens Z.obj := ⟨ι.hom.base '' (g₀.hom.base ⁻¹' Set.range fac.u.hom.base),
    hι.isOpenMap _ (fac.isOpenImmersion_u.base_open.isOpen_range.preimage
      g₀.hom.base.hom.continuous)⟩
  obtain ⟨sq⟩ := exists_ofPair_quotient_rational_square R hR I hRI W ⟨z₀, fac.mem, hz₀⟩
  have hr₀ : Set.range (sq.quotientMap ≫ g₀).hom.base ⊆ Set.range fac.u.hom.base := by
    rintro _ ⟨q, rfl⟩; exact hι.injective.mem_set_image.mp
      (sq.le (Set.mem_preimage.mp (by rw [← sq.range_quotientMap]; exact ⟨q, rfl⟩)))
  -- Lift over the complete affinoid rational localization `sq.pair` and transport back to `Z|_O`
  obtain ⟨gloc, hgloc_K, hgloc_f⟩ :=
    exists_of_affinoid_factorization fac.isSheafyTarget fac.isSheafySource sq.isSheafy
      sq.isSheafyQuotient fac.isFiniteEtale fac.fac sq.completeSpaceQuotient (sq.pow_eq_bot hI)
      (sq.quotientMap ≫ g₀) (sq.targetMap ≫ h)
      (by simp only [Category.assoc, hsq, ← reassoc_of% sq.comm]) hr₀
  have hgloc_f_hom : gloc.hom ≫ f.hom = sq.targetMap.hom ≫ h.hom := by
    simpa only [ObjectProperty.FullSubcategory.comp_hom] using
      congrArg InducedCategory.Hom.hom hgloc_f
  have hgloc_K_hom :
      (comapOfPair sq.isSheafy sq.isSheafyQuotient (Pair.quotientHom sq.pair sq.ideal)).hom ≫
          gloc.hom =
        sq.quotientMap.hom ≫ g₀.hom := by
    simpa only [ObjectProperty.FullSubcategory.comp_hom] using
      congrArg InducedCategory.Hom.hom hgloc_K
  refine ⟨sq.openSet, sq.mem, (sqTargetIso sq).inv ≫ gloc.hom, ?_, ?_⟩
  · simp only [Category.assoc, hgloc_f_hom, reassoc_of% (sqTargetIso_inv_targetMap sq)]
  · rw [sqRestrictPreimage]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, hgloc_K_hom,
      reassoc_of% (sqQuotientIso_inv_quotientMap sq)]

private theorem pullback_fst_comp_eq_of_sqZero_quotient (hf : IsEtaleLocalDescription f)
    (hI : I ^ 2 = ⊥) {O₁ O₂ : Opens (ofPair R hR).obj}
    {g₁ : (ofPair R hR).obj.restrict O₁.isOpenEmbedding ⟶ Y.obj}
    {g₂ : (ofPair R hR).obj.restrict O₂.isOpenEmbedding ⟶ Y.obj}
    (hg₁_f : g₁ ≫ f.hom = (ofPair R hR).obj.ofRestrict O₁.isOpenEmbedding ≫ h.hom)
    (hg₂_f : g₂ ≫ f.hom = (ofPair R hR).obj.ofRestrict O₂.isOpenEmbedding ≫ h.hom)
    (hg₁_ι : (sqZeroQuotHom R hR I hRI).hom.restrictPreimage O₁ ≫ g₁ =
      (ofPair (R.quotient I) hRI).obj.ofRestrict
        ((Opens.map (sqZeroQuotHom R hR I hRI).hom.base).obj O₁).isOpenEmbedding ≫ g₀.hom)
    (hg₂_ι : (sqZeroQuotHom R hR I hRI).hom.restrictPreimage O₂ ≫ g₂ =
      (ofPair (R.quotient I) hRI).obj.ofRestrict
        ((Opens.map (sqZeroQuotHom R hR I hRI).hom.base).obj O₂).isOpenEmbedding ≫ g₀.hom) :
    pullback.fst ((ofPair R hR).obj.ofRestrict O₁.isOpenEmbedding)
      ((ofPair R hR).obj.ofRestrict O₂.isOpenEmbedding) ≫ g₁ = pullback.snd _ _ ≫ g₂ := by
  let Z := ofPair R hR; let Z₀ := ofPair (R.quotient I) hRI; let ι := sqZeroQuotHom R hR I hRI
  let pZ := pullback.fst (Z.obj.ofRestrict O₁.isOpenEmbedding)
    (Z.obj.ofRestrict O₂.isOpenEmbedding) ≫ Z.obj.ofRestrict O₁.isOpenEmbedding
  have hrP : Set.range pZ.base = ((O₁ ⊓ O₂ : Opens Z.obj) : Set Z.obj) :=
    (IsOpenImmersion.range_pullback_to_base_of_left _ _).trans
      (congrArg₂ (· ∩ ·) (Opens.set_range_inclusion' O₁) (Opens.set_range_inclusion' O₂))
  -- Cover `O₁ ⊓ O₂` by rational opens `ofPair sq.pair sq.isSheafy` and invoke
  -- `eq_of_sqZero_quotient`
  refine PreAdicSpace.hom_ext_of_forall_exists_isOpenImmersion
    (isAdic_of_isOpenImmersion Z.property pZ).isSheafy fun p ↦ ?_
  obtain ⟨sq⟩ := exists_ofPair_quotient_rational_square R hR I hRI (O₁ ⊓ O₂)
    (by rw [← SetLike.mem_coe, ← hrP]; exact ⟨p, rfl⟩)
  have hvP_sub : Set.range sq.targetMap.hom.base ⊆ Set.range pZ.base := by
    rw [sq.range_targetMap, hrP]; exact sq.le
  let vP := IsOpenImmersion.lift pZ sq.targetMap.hom hvP_sub
  obtain ⟨q, hq⟩ : pZ.base p ∈ Set.range sq.targetMap.hom.base :=
    sq.range_targetMap.symm ▸ sq.mem
  have hp_mem : p ∈ Set.range vP.base := ⟨q,
    (inferInstance : PreAdicSpace.IsOpenImmersion pZ).base_open.injective
      ((congrArg (fun m ↦ m.base q) (IsOpenImmersion.lift_fac pZ sq.targetMap.hom hvP_sub)).trans
        hq)⟩
  let πK := comapOfPair sq.isSheafy sq.isSheafyQuotient (Pair.quotientHom sq.pair sq.ideal)
  have hπK_lift {O : Opens Z.obj} (hWO : sq.openSet ≤ O)
      {gO : Z.obj.restrict O.isOpenEmbedding ⟶ Y.obj}
      (hgO_ι : ι.hom.restrictPreimage O ≫ gO =
        Z₀.obj.ofRestrict ((Opens.map ι.hom.base).obj O).isOpenEmbedding ≫ g₀.hom) :
      πK.hom ≫ sqTargetIncl sq hWO ≫ gO = sq.quotientMap.hom ≫ g₀.hom := by
    rw [reassoc_of% (sqIncl_restrictPreimage sq hWO), hgO_ι,
      reassoc_of% (sqQuotientIncl_ofRestrict sq hWO)]
  have hv₁ : vP ≫ pullback.fst _ _ = sqTargetIncl sq (sq.le.trans inf_le_left) :=
    (cancel_mono (Z.obj.ofRestrict O₁.isOpenEmbedding)).mp
      (by rw [Category.assoc, IsOpenImmersion.lift_fac pZ _ hvP_sub, sqTargetIncl_ofRestrict])
  have hv₂ : vP ≫ pullback.snd _ _ = sqTargetIncl sq (sq.le.trans inf_le_right) :=
    (cancel_mono (Z.obj.ofRestrict O₂.isOpenEmbedding)).mp
      (by rw [Category.assoc, ← pullback.condition, IsOpenImmersion.lift_fac pZ _ hvP_sub,
        sqTargetIncl_ofRestrict])
  have hm_eq : (ObjectProperty.homMk (sqTargetIncl sq (sq.le.trans inf_le_left) ≫ g₁) :
        ofPair sq.pair sq.isSheafy ⟶ Y) =
      ObjectProperty.homMk (sqTargetIncl sq (sq.le.trans inf_le_right) ≫ g₂) :=
    hf.eq_of_sqZero_quotient sq.pair sq.isSheafy sq.ideal (sq.pow_eq_bot hI) sq.isSheafyQuotient
      (InducedCategory.Hom.ext (by
        simp only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom,
          Category.assoc, hg₁_f, hg₂_f, Z, reassoc_of% (sqTargetIncl_ofRestrict sq _)]))
      (InducedCategory.Hom.ext (by
        simp only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom]
        exact (hπK_lift _ hg₁_ι).trans (hπK_lift _ hg₂_ι).symm))
  refine ⟨(ofPair sq.pair sq.isSheafy).obj, vP, inferInstance, hp_mem, ?_⟩
  rw [reassoc_of% hv₁, reassoc_of% hv₂]
  simpa only [ObjectProperty.homMk_hom] using congrArg InducedCategory.Hom.hom hm_eq

end SqZeroLift

/-- **Infinitesimal lifting (existence) for étale morphisms along square-zero quotients**
(`I ^ 2 = ⊥`) of sheafy Huber pairs `(C, R)` whose quotient Huber pair `R.quotient I` is sheafy. -/
theorem IsEtaleLocalDescription.exists_of_sqZero_quotient {f : Y ⟶ X}
    (hf : IsEtaleLocalDescription f) (R : Pair C) (hR : IsSheafyForEveryPresentation R.plus)
    (I : Ideal C) (hI : I ^ 2 = ⊥) (hRI : IsSheafyForEveryPresentation (R.quotient I).plus)
    (g₀ : ofPair (R.quotient I) hRI ⟶ Y) (h : ofPair R hR ⟶ X)
    (hsq : g₀ ≫ f = comapOfPair hR hRI (Pair.quotientHom R I) ≫ h) :
    ∃ g : ofPair R hR ⟶ Y, comapOfPair hR hRI (Pair.quotientHom R I) ≫ g = g₀ ∧ g ≫ f = h := by
  let ι := comapOfPair hR hRI (Pair.quotientHom R I)
  choose O hzO gO hgO_f hgO_ι using exists_local_lift_of_sqZero_quotient R hR I hRI g₀ h hf hI hsq
  have hcov : ⨆ z, O z = ⊤ := eq_top_iff.mpr fun z _ ↦ Opens.mem_iSup.mpr ⟨z, hzO z⟩
  let g : ofPair R hR ⟶ Y := ObjectProperty.homMk
    (PreAdicSpace.glueMorphisms (ofPair R hR).property.isSheafy O hcov gO fun k l ↦
      pullback_fst_comp_eq_of_sqZero_quotient R hR I hRI g₀ h hf hI
        (hgO_f k) (hgO_f l) (hgO_ι k) (hgO_ι l))
  have hcov₀ : ⨆ z, (Opens.map ι.hom.base).obj (O z) = ⊤ := eq_top_iff.mpr fun w _ ↦
    let ⟨z, hz⟩ := Opens.mem_iSup.mp (hcov.symm ▸ trivial : ι.hom.base w ∈ ⨆ z, O z)
    Opens.mem_iSup.mpr ⟨z, hz⟩
  refine ⟨g, InducedCategory.Hom.ext (PreAdicSpace.hom_ext_of_ofRestrict
      (ofPair (R.quotient I) hRI).property.isSheafy _ hcov₀ fun z ↦ ?_),
    InducedCategory.Hom.ext (PreAdicSpace.hom_ext_of_ofRestrict
      (ofPair R hR).property.isSheafy O hcov fun z ↦ ?_)⟩
  · simp only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom, g]
    rw [← Hom.restrictPreimage_ofRestrict_assoc, PreAdicSpace.ofRestrict_glueMorphisms, hgO_ι]
  · simp [ObjectProperty.FullSubcategory.comp_hom, g,
      PreAdicSpace.ofRestrict_glueMorphisms_assoc, hgO_f]

/-- **Unique infinitesimal lifting for étale morphisms of analytic adic spaces** along square-zero
quotients (`I ^ 2 = ⊥`) of sheafy Huber pairs `(C, R)` with sheafy quotient pair `R.quotient I`. -/
theorem IsEtaleLocalDescription.existsUnique_of_sqZero_quotient {f : Y ⟶ X}
    (hf : IsEtaleLocalDescription f) (R : Pair C) (hR : IsSheafyForEveryPresentation R.plus)
    (I : Ideal C) (hI : I ^ 2 = ⊥) (hRI : IsSheafyForEveryPresentation (R.quotient I).plus)
    (g₀ : ofPair (R.quotient I) hRI ⟶ Y) (h : ofPair R hR ⟶ X)
    (hsq : g₀ ≫ f = comapOfPair hR hRI (Pair.quotientHom R I) ≫ h) :
    ∃! g : ofPair R hR ⟶ Y, comapOfPair hR hRI (Pair.quotientHom R I) ≫ g = g₀ ∧ g ≫ f = h := by
  obtain ⟨g, hg₁, hg₂⟩ := hf.exists_of_sqZero_quotient R hR I hI hRI g₀ h hsq
  exact ⟨g, ⟨hg₁, hg₂⟩, fun g' ⟨hg'₁, hg'₂⟩ ↦
    hf.eq_of_sqZero_quotient R hR I hI hRI (hg'₂.trans hg₂.symm) (hg'₁.trans hg₁.symm)⟩

end InfinitesimalLifting

end TauCeti.AdicSpace
