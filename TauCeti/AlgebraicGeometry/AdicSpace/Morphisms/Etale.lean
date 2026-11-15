/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Morphisms.FiniteEtale

import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.GlueMorphisms
import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.LocallyOfFiniteType.Local
import TauCeti.RingTheory.Huber.ModuleTopology.FiniteEtale

/-!
# Étale morphisms of analytic adic spaces

A morphism `f : Y ⟶ X` of analytic adic spaces is *étale* in the local-factorization sense of
Kedlaya–Liu and Scholze (`TauCeti.AdicSpace.IsEtaleLocalDescription`) when `X` and `Y` are analytic
and every point `y` of `Y` has an open neighbourhood `U` over which `f` factors as an open immersion
`j : U ⟶ W`, followed by a finite étale morphism `g : W ⟶ V`, followed by an open immersion
`i : V ⟶ X`. Neither locally noetherian hypotheses nor separatedness are imposed. The name
`IsEtaleLocalDescription` distinguishes this local-factorization notion on general analytic adic
spaces from Huber's infinitesimal criterion on locally noetherian spaces.

Finite étale morphisms (`IsEtaleLocalDescription.of_isFiniteEtale`) and open immersions into
analytic adic spaces (`IsEtaleLocalDescription.of_isOpenImmersion`) are étale. The property is
invariant under source and target isomorphisms, stable under precomposing with open immersions and
under postcomposing with open immersions into analytic targets, local on the source for morphisms
into an analytic target (`isEtaleLocalDescription_iff_of_jointly_surjective`,
`isEtaleLocalDescription_iff_of_iSup_eq_top_source`), and descends along open covers of the target
(`IsEtaleLocalDescription.of_iSup_eq_top`). Refining the middle finite étale factor to a complete
Hausdorff Tate affinoid chart expresses `f` locally through `AdicSpace.comapOfPair`
(`IsEtaleLocalDescription.exists_affinoid_factorization`).

Consequently, étale morphisms are locally of finite type
(`IsEtaleLocalDescription.locallyOfFiniteType`) and carry locally noetherian analytic structure from
target to source (`IsEtaleLocalDescription.isLocallyNoetherianAnalytic_source`). Moreover, they
satisfy unique infinitesimal lifting along square-zero quotients (`I ^ 2 = ⊥`) of arbitrary sheafy
Huber pairs `(C, R)` whose quotient pair `R.quotient I` is sheafy
(`IsEtaleLocalDescription.existsUnique_of_sqZero_quotient`): this obstructs both ramified finite
morphisms such as `T ↦ S²` (failure of uniqueness) and unramified closed immersions such as
`{T = 0}` into the closed unit disc (failure of existence).

## Main definitions

* `TauCeti.AdicSpace.IsEtaleLocalDescription`: étale morphisms of analytic adic spaces via local
  factorization through finite étale morphisms and open immersions.

## Main results

* `TauCeti.AdicSpace.IsEtaleLocalDescription.of_isFiniteEtale` and
  `TauCeti.AdicSpace.IsEtaleLocalDescription.of_isOpenImmersion`: finite étale morphisms and open
  immersions into analytic adic spaces are étale.
* `TauCeti.AdicSpace.IsEtaleLocalDescription.respectsIso`,
  `TauCeti.AdicSpace.IsEtaleLocalDescription.isOpenImmersion_comp`,
  `TauCeti.AdicSpace.IsEtaleLocalDescription.comp_isOpenImmersion`,
  `TauCeti.AdicSpace.isEtaleLocalDescription_iff_of_jointly_surjective`,
  `TauCeti.AdicSpace.isEtaleLocalDescription_iff_of_iSup_eq_top_source`, and
  `TauCeti.AdicSpace.IsEtaleLocalDescription.of_iSup_eq_top`: invariance under isomorphisms,
  stability under open immersions, source locality, and target-cover descent.
* `TauCeti.AdicSpace.IsEtaleLocalDescription.exists_affinoid_factorization`: refinement of the
  middle finite étale factor to complete Hausdorff Tate affinoid charts via `comapOfPair`.
* `TauCeti.AdicSpace.IsEtaleLocalDescription.locallyOfFiniteType` and
  `TauCeti.AdicSpace.IsEtaleLocalDescription.isLocallyNoetherianAnalytic_source`: finiteness and
  ascent of locally noetherian analytic structure.
* `TauCeti.AdicSpace.IsEtaleLocalDescription.eq_of_sqZero_quotient`,
  `TauCeti.AdicSpace.IsEtaleLocalDescription.exists_of_sqZero_quotient`, and
  `TauCeti.AdicSpace.IsEtaleLocalDescription.existsUnique_of_sqZero_quotient`: infinitesimal
  lifting along square-zero quotients of sheafy Huber pairs.

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

namespace TauCeti

open Huber PreAdicSpace ValuationSpectrum

universe u

namespace AdicSpace

variable {X Y Z : AdicSpace.{u}}

private instance {A B : AdicSpace.{u}} (m : A.obj ⟶ B.obj) [PreAdicSpace.IsOpenImmersion m] :
    PreAdicSpace.IsOpenImmersion (ObjectProperty.homMk m : A ⟶ B).hom := by
  rw [ObjectProperty.homMk_hom]
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
theorem isEtaleLocalDescription_iff_of_isOpenImmersion (f : Y ⟶ X)
    [PreAdicSpace.IsOpenImmersion f.hom] :
    IsEtaleLocalDescription f ↔ X.IsAnalytic :=
  ⟨IsEtaleLocalDescription.isAnalytic_target, IsEtaleLocalDescription.of_isOpenImmersion f⟩

/-- **The identity of an analytic adic space is étale.** -/
theorem IsEtaleLocalDescription.id {X : AdicSpace.{u}} (hX : X.IsAnalytic) :
    IsEtaleLocalDescription (𝟙 X) :=
  .of_isFiniteEtale (IsFiniteEtale.id hX)

/-- **The identity of an adic space `X` is étale if and only if `X` is analytic.** -/
@[simp]
theorem isEtaleLocalDescription_id_iff {X : AdicSpace.{u}} :
    IsEtaleLocalDescription (𝟙 X) ↔ X.IsAnalytic :=
  ⟨IsEtaleLocalDescription.isAnalytic_target, IsEtaleLocalDescription.id⟩

/-- **An isomorphism onto an analytic adic space is étale.** -/
theorem IsEtaleLocalDescription.of_isIso (f : Y ⟶ X) [IsIso f] (hX : X.IsAnalytic) :
    IsEtaleLocalDescription f :=
  .of_isFiniteEtale (IsFiniteEtale.of_isIso f hX)

/-- **An isomorphism in `AdicSpace` is étale if and only if its target is analytic.** -/
theorem isEtaleLocalDescription_iff_of_isIso (f : Y ⟶ X) [IsIso f] :
    IsEtaleLocalDescription f ↔ X.IsAnalytic :=
  ⟨IsEtaleLocalDescription.isAnalytic_target, IsEtaleLocalDescription.of_isIso f⟩

/-- **Every morphism from an empty adic space into an analytic adic space is étale.** -/
theorem IsEtaleLocalDescription.of_isEmpty (f : Y ⟶ X) [IsEmpty Y.obj] (hX : X.IsAnalytic) :
    IsEtaleLocalDescription f :=
  .of_isFiniteEtale (IsFiniteEtale.of_isEmpty f hX)

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
    rw [ObjectProperty.homMk_hom, IsOpenImmersion.range_pullback_snd_of_left]
    exact ⟨u₀, hu₀⟩
  have hcond : u' ≫ v = l ≫ u := InducedCategory.Hom.ext pullback.condition.symm
  refine ⟨U', V, W, u', i, l ≫ j, g, inferInstance, hz, hi, ?_, hg, ?_⟩
  · rw [ObjectProperty.FullSubcategory.comp_hom]
    infer_instance
  · rw [← Category.assoc, hcond, Category.assoc, hfac, Category.assoc]

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

/-- Being étale (`IsEtaleLocalDescription`) can be tested on any jointly surjective family of open
immersions into the source, provided the target `X` is analytic. -/
theorem isEtaleLocalDescription_iff_of_jointly_surjective {f : Y ⟶ X} (hX : X.IsAnalytic)
    {ι : Type*} {U : ι → AdicSpace.{u}} (u : ∀ k, U k ⟶ Y)
    [∀ k, PreAdicSpace.IsOpenImmersion (u k).hom]
    (hcov : ∀ y : Y.obj, ∃ (k : ι) (z : (U k).obj), (u k).hom.base z = y) :
    IsEtaleLocalDescription f ↔ ∀ k, IsEtaleLocalDescription (u k ≫ f) :=
  ⟨fun hf k ↦ hf.isOpenImmersion_comp (u k),
    IsEtaleLocalDescription.of_jointly_surjective hX u hcov⟩

/-- **Source-cover descent along opens of `Y`.** If `X` is analytic, `U : ι → Opens Y.obj` covers
`Y`, and the restriction of `f : Y ⟶ X` to each `U k` satisfies `IsEtaleLocalDescription`, then `f`
satisfies `IsEtaleLocalDescription`. -/
theorem IsEtaleLocalDescription.of_iSup_eq_top_source {f : Y ⟶ X} (hX : X.IsAnalytic) {ι : Type*}
    (U : ι → Opens Y.obj) (hU : iSup U = ⊤)
    (hf : ∀ k, IsEtaleLocalDescription
      ((ObjectProperty.homMk (Y.obj.ofRestrict (U k).isOpenEmbedding) :
        (⟨Y.obj.restrict (U k).isOpenEmbedding, isAdic_restrict _ Y.property⟩ :
          AdicSpace.{u}) ⟶ Y) ≫ f)) :
    IsEtaleLocalDescription f := by
  refine @IsEtaleLocalDescription.of_jointly_surjective _ _ _ hX _ _
    (fun k ↦ (ObjectProperty.homMk (Y.obj.ofRestrict (U k).isOpenEmbedding) :
      (⟨Y.obj.restrict (U k).isOpenEmbedding, isAdic_restrict _ Y.property⟩ :
        AdicSpace.{u}) ⟶ Y)) (fun _ ↦ inferInstance)
    (fun y ↦ ?_) hf
  obtain ⟨k, hk⟩ := Opens.mem_iSup.mp (by rw [hU]; trivial)
  exact ⟨k, ⟨y, hk⟩, rfl⟩

/-- Being étale (`IsEtaleLocalDescription`) is local on the source for morphisms into an analytic
target `X`. -/
theorem isEtaleLocalDescription_iff_of_iSup_eq_top_source {f : Y ⟶ X} (hX : X.IsAnalytic)
    {ι : Type*} (U : ι → Opens Y.obj) (hU : iSup U = ⊤) :
    IsEtaleLocalDescription f ↔ ∀ k, IsEtaleLocalDescription
      ((ObjectProperty.homMk (Y.obj.ofRestrict (U k).isOpenEmbedding) :
        (⟨Y.obj.restrict (U k).isOpenEmbedding, isAdic_restrict _ Y.property⟩ :
          AdicSpace.{u}) ⟶ Y) ≫ f) :=
  ⟨fun hf _ ↦ hf.isOpenImmersion_comp _, IsEtaleLocalDescription.of_iSup_eq_top_source hX U hU⟩

/-- **Target-cover descent for étale morphisms.** If `V : ι → Opens X.obj` covers `X` and the
preimage restriction of `f : Y ⟶ X` over every `V k` satisfies `IsEtaleLocalDescription`, then `f`
satisfies `IsEtaleLocalDescription`. -/
theorem IsEtaleLocalDescription.of_iSup_eq_top {f : Y ⟶ X} {ι : Type*} (V : ι → Opens X.obj)
    (hV : iSup V = ⊤)
    (hf : ∀ k, IsEtaleLocalDescription
      (ObjectProperty.homMk (f.hom.restrictPreimage (V k)) :
        (⟨Y.obj.restrict ((Opens.map f.hom.base).obj (V k)).isOpenEmbedding,
          isAdic_restrict _ Y.property⟩ : AdicSpace.{u}) ⟶
        ⟨X.obj.restrict (V k).isOpenEmbedding, isAdic_restrict _ X.property⟩)) :
    IsEtaleLocalDescription f := by
  have hX : X.IsAnalytic := by
    rw [isAnalytic_iff_analyticPoints_eq_univ, Set.eq_univ_iff_forall]
    intro x
    obtain ⟨k, hx⟩ := Opens.mem_iSup.mp (by rw [hV]; trivial)
    exact Set.mem_preimage.mp
      ((preimage_analyticPoints_of_isOpenImmersion (X.obj.ofRestrict (V k).isOpenEmbedding)).symm ▸
        (hf k).isAnalytic_target.mem_analyticPoints ⟨x, hx⟩)
  let U : ι → Opens Y.obj := fun k ↦ (Opens.map f.hom.base).obj (V k)
  have hU : iSup U = ⊤ := eq_top_iff.mpr fun y _ ↦ by
    obtain ⟨k, hk⟩ := Opens.mem_iSup.mp (show f.hom.base y ∈ iSup V by rw [hV]; trivial)
    exact Opens.mem_iSup.mpr ⟨k, hk⟩
  refine IsEtaleLocalDescription.of_iSup_eq_top_source hX U hU fun k ↦ ?_
  have hsq : (ObjectProperty.homMk (Y.obj.ofRestrict (U k).isOpenEmbedding) :
      (⟨Y.obj.restrict (U k).isOpenEmbedding, isAdic_restrict _ Y.property⟩ : AdicSpace.{u}) ⟶ Y) ≫
      f =
      ObjectProperty.homMk (f.hom.restrictPreimage (V k)) ≫
        (ObjectProperty.homMk (X.obj.ofRestrict (V k).isOpenEmbedding) :
          (⟨X.obj.restrict (V k).isOpenEmbedding, isAdic_restrict _ X.property⟩ :
            AdicSpace.{u}) ⟶ X) :=
    InducedCategory.Hom.ext (Hom.restrictPreimage_ofRestrict f.hom (V k)).symm
  rw [hsq]
  exact (hf k).comp_isOpenImmersion _ hX

/-! ### Refinement to affinoid middle factors and finiteness properties -/

/-- **Refinement of local factorizations of an étale morphism to complete Hausdorff Tate affinoid
charts.** Around any `y : Y.obj`, an étale morphism `f : Y ⟶ X` admits an open adic subspace `U`
with an open immersion `u : U ⟶ Y` whose image contains `y` such that `u ≫ f` factors as
`j ≫ comapOfPair hS hT ψ ≫ i`, where `(A, S)` and `(B, T)` are complete Hausdorff Tate sheafy Huber
pairs, `ψ : Pair.Hom S T` is finite étale, and `j` and `i` are open immersions. -/
theorem IsEtaleLocalDescription.exists_affinoid_factorization {f : Y ⟶ X}
    (hf : IsEtaleLocalDescription f) (y : Y.obj) :
    ∃ (A : Type u) (_ : CommRing A) (_ : UniformSpace A) (_ : IsUniformAddGroup A)
      (_ : IsTopologicalRing A) (_ : CompleteSpace A) (_ : T2Space A) (_ : IsTateRing A)
      (S : Pair A) (hS : IsSheafyForEveryPresentation S.plus)
      (B : Type u) (_ : CommRing B) (_ : UniformSpace B) (_ : IsUniformAddGroup B)
      (_ : IsTopologicalRing B) (_ : CompleteSpace B) (_ : T2Space B) (_ : IsTateRing B)
      (T : Pair B) (hT : IsSheafyForEveryPresentation T.plus)
      (ψ : Pair.Hom S T) (_ : ψ.IsFiniteEtale)
      (U : AdicSpace.{u}) (u : U ⟶ Y) (j : U ⟶ ofPair T hT) (i : ofPair S hS ⟶ X),
      PreAdicSpace.IsOpenImmersion u.hom ∧ y ∈ Set.range u.hom.base ∧
        PreAdicSpace.IsOpenImmersion j.hom ∧ PreAdicSpace.IsOpenImmersion i.hom ∧
        u ≫ f = j ≫ comapOfPair hS hT ψ ≫ i := by
  obtain ⟨U₀, V₀, W₀, u₀, i₀, j₀, g₀, hu₀, ⟨p₀, hp₀⟩, hi₀, hj₀, hg₀, hfac₀⟩ := hf.2.2 y
  obtain ⟨V', hv₀, A, _, _, _, _, _, _, _, S, hS, B, _, _, _, _, _, _, _, T, hT, ψ, hψ,
    eV, eW, hg_fac⟩ := hg₀.exists_ofPair_chart (g₀.hom.base (j₀.hom.base p₀))
  let w := W₀.obj.ofRestrict ((Opens.map g₀.hom.base).obj V').isOpenEmbedding
  let U : AdicSpace.{u} :=
    ⟨pullback w j₀.hom, isAdic_of_isOpenImmersion U₀.property (pullback.snd w j₀.hom)⟩
  let r : U ⟶ U₀ := ObjectProperty.homMk (pullback.snd w j₀.hom)
  let j : U ⟶ ofPair T hT := ObjectProperty.homMk (pullback.fst w j₀.hom ≫ eW.hom)
  let i : ofPair S hS ⟶ X :=
    ObjectProperty.homMk (eV.inv ≫ V₀.obj.ofRestrict V'.isOpenEmbedding ≫ i₀.hom)
  have hp₀_mem : p₀ ∈ Set.range r.hom.base := by
    rw [ObjectProperty.homMk_hom, IsOpenImmersion.range_pullback_snd_of_left]
    exact ⟨⟨j₀.hom.base p₀, Opens.mem_map.mpr hv₀⟩, rfl⟩
  obtain ⟨q₀, hq₀⟩ := hp₀_mem
  refine ⟨A, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, S, hS, B, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, T, hT, ψ, hψ, U, r ≫ u₀, j, i,
    ?_, ⟨q₀, by simp [hq₀, hp₀]⟩, inferInstance, inferInstance, ?_⟩
  · rw [ObjectProperty.FullSubcategory.comp_hom]
    infer_instance
  · ext1
    have h1 := congrArg (fun k ↦ r.hom ≫ k) (congrArg InducedCategory.Hom.hom hfac₀)
    simp only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom, r, j, i] at h1 ⊢
    rw [Category.assoc, h1, ← Category.assoc, ← Category.assoc, ← pullback.condition,
      Category.assoc, Category.assoc, reassoc_of% hg_fac]
    simp only [Category.assoc]

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

private theorem cancel_comp_of_isOpenImmersion {Z' U Y' : AdicSpace.{u}}
    (u : U ⟶ Y') [PreAdicSpace.IsOpenImmersion u.hom] {l₁ l₂ : Z' ⟶ U} (h : l₁ ≫ u = l₂ ≫ u) :
    l₁ = l₂ := by
  apply InducedCategory.Hom.ext
  rw [← cancel_mono u.hom]
  exact congrArg InducedCategory.Hom.hom h

private theorem lift_of_range_subset {Z' U Y' : AdicSpace.{u}}
    (u : U ⟶ Y') [PreAdicSpace.IsOpenImmersion u.hom] (f : Z' ⟶ Y')
    (hr : Set.range f.hom.base ⊆ Set.range u.hom.base) :
    ∃ l : Z' ⟶ U, l ≫ u = f :=
  ⟨ObjectProperty.homMk (IsOpenImmersion.lift u.hom f.hom hr),
    InducedCategory.Hom.ext (IsOpenImmersion.lift_fac u.hom f.hom hr)⟩

/-- Local uniqueness along a quotient mapping of complete Hausdorff sheafy Huber pairs with
square-zero kernel over a single affinoid factorization chart. -/
private theorem eq_of_isQuotientMapping_of_affinoid_factorization {f : Y ⟶ X}
    {A : Type u} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]
    [CompleteSpace A] [T0Space A] [IsHuberRing A] {S : Pair A}
    (hS : IsSheafyForEveryPresentation S.plus)
    {B : Type u} [CommRing B] [UniformSpace B] [IsUniformAddGroup B] [IsTopologicalRing B]
    [CompleteSpace B] [T0Space B] [IsHuberRing B] {T : Pair B}
    (hT : IsSheafyForEveryPresentation T.plus)
    {ψ : Pair.Hom S T} (hψ : ψ.IsFiniteEtale)
    {U : AdicSpace.{u}} {u : U ⟶ Y} {j : U ⟶ ofPair T hT} {i : ofPair S hS ⟶ X}
    [PreAdicSpace.IsOpenImmersion u.hom] [PreAdicSpace.IsOpenImmersion j.hom]
    [PreAdicSpace.IsOpenImmersion i.hom]
    (hfac : u ≫ f = j ≫ comapOfPair hS hT ψ ≫ i)
    {A₁ : Type u} [CommRing A₁] [UniformSpace A₁] [IsUniformAddGroup A₁] [IsTopologicalRing A₁]
    [CompleteSpace A₁] [T0Space A₁] [IsHuberRing A₁] {S₁ : Pair A₁}
    (hS₁ : IsSheafyForEveryPresentation S₁.plus)
    {A₂ : Type u} [CommRing A₂] [UniformSpace A₂] [IsUniformAddGroup A₂] [IsTopologicalRing A₂]
    [CompleteSpace A₂] [T0Space A₂] [IsHuberRing A₂] {S₂ : Pair A₂}
    (hS₂ : IsSheafyForEveryPresentation S₂.plus)
    {π : Pair.Hom S₁ S₂} (hπ : π.IsQuotientMapping) (hker : RingHom.ker π.toRingHom ^ 2 = ⊥)
    {g₁ g₂ : ofPair S₁ hS₁ ⟶ Y}
    (hr₁ : Set.range g₁.hom.base ⊆ Set.range u.hom.base)
    (hr₂ : Set.range g₂.hom.base ⊆ Set.range u.hom.base)
    (hf_eq : g₁ ≫ f = g₂ ≫ f)
    (hπ_eq : comapOfPair hS₁ hS₂ π ≫ g₁ = comapOfPair hS₁ hS₂ π ≫ g₂) :
    g₁ = g₂ := by
  obtain ⟨l₁, hl₁⟩ := lift_of_range_subset u g₁ hr₁
  obtain ⟨l₂, hl₂⟩ := lift_of_range_subset u g₂ hr₂
  have hk_f : (l₁ ≫ j) ≫ comapOfPair hS hT ψ = (l₂ ≫ j) ≫ comapOfPair hS hT ψ := by
    refine cancel_comp_of_isOpenImmersion i ?_
    simpa only [Category.assoc, ← hfac] using
      (congrArg (· ≫ f) hl₁).trans (hf_eq.trans (congrArg (· ≫ f) hl₂).symm)
  have hl_π : comapOfPair hS₁ hS₂ π ≫ l₁ = comapOfPair hS₁ hS₂ π ≫ l₂ :=
    cancel_comp_of_isOpenImmersion u (by rw [Category.assoc, Category.assoc, hl₁, hl₂, hπ_eq])
  have hσ_ψ := congrArg (ofPairHomEquiv hS hS₁) hk_f
  rw [ofPairHomEquiv_comp, ofPairHomEquiv_comp, ofPairHomEquiv_comapOfPair] at hσ_ψ
  have hσ_π := congrArg (ofPairHomEquiv hT hS₂) ((reassoc_of% hl_π) j)
  rw [ofPairHomEquiv_comp, ofPairHomEquiv_comp, ofPairHomEquiv_comapOfPair] at hσ_π
  have hk := (ofPairHomEquiv hT hS₁).injective
    (hψ.eq_of_isQuotientMapping_sqZero_ker hπ hker hσ_ψ hσ_π)
  rw [← hl₁, ← hl₂, cancel_comp_of_isOpenImmersion j hk]

/-- Local existence along a quotient mapping of complete Hausdorff sheafy Huber pairs with
square-zero kernel over a single affinoid factorization chart. -/
private theorem exists_of_isQuotientMapping_of_affinoid_factorization {f : Y ⟶ X}
    {A : Type u} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]
    [CompleteSpace A] [T0Space A] [IsHuberRing A] {S : Pair A}
    (hS : IsSheafyForEveryPresentation S.plus)
    {B : Type u} [CommRing B] [UniformSpace B] [IsUniformAddGroup B] [IsTopologicalRing B]
    [CompleteSpace B] [T0Space B] [IsHuberRing B] {T : Pair B}
    (hT : IsSheafyForEveryPresentation T.plus)
    {ψ : Pair.Hom S T} (hψ : ψ.IsFiniteEtale)
    {U : AdicSpace.{u}} {u : U ⟶ Y} {j : U ⟶ ofPair T hT} {i : ofPair S hS ⟶ X}
    [PreAdicSpace.IsOpenImmersion u.hom] [PreAdicSpace.IsOpenImmersion j.hom]
    [PreAdicSpace.IsOpenImmersion i.hom]
    (hfac : u ≫ f = j ≫ comapOfPair hS hT ψ ≫ i)
    {A₁ : Type u} [CommRing A₁] [UniformSpace A₁] [IsUniformAddGroup A₁] [IsTopologicalRing A₁]
    [CompleteSpace A₁] [T0Space A₁] [IsHuberRing A₁] {S₁ : Pair A₁}
    (hS₁ : IsSheafyForEveryPresentation S₁.plus)
    {A₂ : Type u} [CommRing A₂] [UniformSpace A₂] [IsUniformAddGroup A₂] [IsTopologicalRing A₂]
    [CompleteSpace A₂] [T0Space A₂] [IsHuberRing A₂] {S₂ : Pair A₂}
    (hS₂ : IsSheafyForEveryPresentation S₂.plus)
    {π : Pair.Hom S₁ S₂} (hπ : π.IsQuotientMapping) (hker : RingHom.ker π.toRingHom ^ 2 = ⊥)
    (g₀ : ofPair S₂ hS₂ ⟶ Y) (h : ofPair S₁ hS₁ ⟶ X)
    (hsq : g₀ ≫ f = comapOfPair hS₁ hS₂ π ≫ h)
    (hr₀ : Set.range g₀.hom.base ⊆ Set.range u.hom.base) :
    ∃ g : ofPair S₁ hS₁ ⟶ Y, comapOfPair hS₁ hS₂ π ≫ g = g₀ ∧ g ≫ f = h := by
  have hsurj : Function.Surjective (comapOfPair hS₁ hS₂ π).hom.base :=
    (isHomeomorph_comapOfPair_base_of_isQuotientMapping hS₁ hS₂ hπ fun a ha ↦
      ⟨2, by rw [← Ideal.mem_bot, ← hker]; exact Ideal.pow_mem_pow ha 2⟩).surjective
  obtain ⟨g₀', hg₀'⟩ := lift_of_range_subset u g₀ hr₀
  have hhr : Set.range h.hom.base ⊆ Set.range i.hom.base := by
    rintro _ ⟨z₁, rfl⟩
    obtain ⟨z₂, rfl⟩ := hsurj z₁
    have h1 := congrArg (fun m : ofPair S₂ hS₂ ⟶ X ↦ m.hom.base z₂)
      (by rw [← hsq, ← hg₀', Category.assoc, hfac] :
        comapOfPair hS₁ hS₂ π ≫ h = g₀' ≫ j ≫ comapOfPair hS hT ψ ≫ i)
    exact ⟨_, h1.symm⟩
  obtain ⟨h', hh'⟩ := lift_of_range_subset i h hhr
  have hcomm_space : (g₀' ≫ j) ≫ comapOfPair hS hT ψ = comapOfPair hS₁ hS₂ π ≫ h' :=
    cancel_comp_of_isOpenImmersion i
      (by rw [Category.assoc, Category.assoc, ← hfac, ← Category.assoc, hg₀', hsq,
        Category.assoc, hh'])
  have hcomm_pair := congrArg (ofPairHomEquiv hS hS₂) hcomm_space
  rw [ofPairHomEquiv_comp, ofPairHomEquiv_comp, ofPairHomEquiv_comapOfPair,
    ofPairHomEquiv_comapOfPair] at hcomm_pair
  obtain ⟨β, hβ_ψ, hβ_π⟩ := hψ.exists_of_isQuotientMapping_sqZero_ker hπ hker _ _ hcomm_pair
  let k : ofPair S₁ hS₁ ⟶ ofPair T hT := comapOfPair hT hS₁ β
  have hk_π : comapOfPair hS₁ hS₂ π ≫ k = g₀' ≫ j := by
    rw [← comapOfPair_comp, hβ_π, comapOfPair_ofPairHomEquiv]
  have hk_ψ : k ≫ comapOfPair hS hT ψ = h' := by
    rw [← comapOfPair_comp, hβ_ψ, comapOfPair_ofPairHomEquiv]
  have hkr : Set.range k.hom.base ⊆ Set.range j.hom.base := by
    rintro _ ⟨z₁, rfl⟩
    obtain ⟨z₂, rfl⟩ := hsurj z₁
    exact ⟨g₀'.hom.base z₂,
      (congrArg (fun m : ofPair S₂ hS₂ ⟶ ofPair T hT ↦ m.hom.base z₂) hk_π).symm⟩
  obtain ⟨l, hl⟩ := lift_of_range_subset j k hkr
  refine ⟨l ≫ u, ?_, ?_⟩
  · have hlj : comapOfPair hS₁ hS₂ π ≫ l = g₀' :=
      cancel_comp_of_isOpenImmersion j (by rw [Category.assoc, hl, hk_π])
    rw [← Category.assoc, hlj, hg₀']
  · rw [Category.assoc, hfac, ← Category.assoc, hl, ← Category.assoc, hk_ψ, hh']

private theorem range_lift_ofRestrict_eq_range_ofRestrict {V Z : AdicSpace.{u}} (v : V ⟶ Z)
    (W O_Z : Opens Z.obj) (hv_range : Set.range v.hom.base = O_Z)
    {vW : V ⟶ ⟨Z.obj.restrict W.isOpenEmbedding, isAdic_restrict _ Z.property⟩}
    (hvW : vW ≫ ObjectProperty.homMk (Z.obj.ofRestrict W.isOpenEmbedding) = v) :
    Set.range vW.hom.base =
      Set.range ((Z.obj.restrict W.isOpenEmbedding).ofRestrict
        ((Opens.map (Z.obj.ofRestrict W.isOpenEmbedding).base).obj O_Z).isOpenEmbedding).base := by
  ext w
  constructor
  · rintro ⟨q, rfl⟩
    have hv_mem : v.hom.base q ∈ (O_Z : Set Z.obj) := by rw [← hv_range]; exact ⟨q, rfl⟩
    have hv_eq := congrArg (fun m : V ⟶ Z ↦ m.hom.base q) hvW
    have hvq : (Z.obj.ofRestrict W.isOpenEmbedding).base (vW.hom.base q) ∈ O_Z :=
      hv_eq.symm ▸ hv_mem
    exact ⟨⟨vW.hom.base q, Opens.mem_map.mpr hvq⟩, rfl⟩
  · rintro ⟨⟨w, hw⟩, rfl⟩
    have hw' : (Z.obj.ofRestrict W.isOpenEmbedding).base w ∈ (O_Z : Set Z.obj) :=
      Opens.mem_map.mp hw
    rw [← hv_range] at hw'
    obtain ⟨q, hq⟩ := hw'
    exact ⟨q, Subtype.ext ((congrArg (fun m : V ⟶ Z ↦ m.hom.base q) hvW).trans hq)⟩

private theorem lift_comm_restrictPreimage {V V₀ Z Z₀ : AdicSpace.{u}}
    (π : V₀ ⟶ V) (v : V ⟶ Z) (u' : V₀ ⟶ Z₀) (ι : Z₀ ⟶ Z) (W : Opens Z.obj)
    (hπv : π ≫ v = u' ≫ ι)
    {vW : V ⟶ ⟨Z.obj.restrict W.isOpenEmbedding, isAdic_restrict _ Z.property⟩}
    (hvW : vW ≫ ObjectProperty.homMk (Z.obj.ofRestrict W.isOpenEmbedding) = v)
    {u'W : V₀ ⟶ ⟨Z₀.obj.restrict ((Opens.map ι.hom.base).obj W).isOpenEmbedding,
      isAdic_restrict _ Z₀.property⟩}
    (hu'W : u'W ≫ ObjectProperty.homMk
      (Z₀.obj.ofRestrict ((Opens.map ι.hom.base).obj W).isOpenEmbedding) = u') :
    π ≫ vW = u'W ≫ ObjectProperty.homMk (ι.hom.restrictPreimage W) := by
  refine cancel_comp_of_isOpenImmersion
    (ObjectProperty.homMk (Z.obj.ofRestrict W.isOpenEmbedding)) ?_
  ext1
  simpa only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom, Category.assoc,
    Hom.restrictPreimage_ofRestrict] using
    congrArg InducedCategory.Hom.hom
      (by rw [hvW, hπv, ← hu'W, Category.assoc] :
        π ≫ vW ≫ ObjectProperty.homMk (Z.obj.ofRestrict W.isOpenEmbedding) =
          u'W ≫ ObjectProperty.homMk (Z₀.obj.ofRestrict _) ≫ ι)

/-- Around each point `z` of an open subspace `W` of `ofPair R hR`, two morphisms `g₁, g₂` out of
`W` that agree over `X` and over the preimage of `W` in `ofPair (R.quotient I) hRI` agree on a
smaller open neighbourhood of `z`. -/
private theorem exists_open_eq_on_open_of_sqZero_quotient {f : Y ⟶ X}
    (hf : IsEtaleLocalDescription f)
    {C : Type u} [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsHuberRing C]
    (R : Pair C) (hR : IsSheafyForEveryPresentation R.plus)
    (I : Ideal C) (hI : I ^ 2 = ⊥)
    (hRI : IsSheafyForEveryPresentation (R.quotient I).plus)
    (W : Opens (ofPair R hR).obj)
    {g₁ g₂ : (⟨(ofPair R hR).obj.restrict W.isOpenEmbedding,
      isAdic_restrict _ (ofPair R hR).property⟩ : AdicSpace.{u}) ⟶ Y}
    (hbase_eq : g₁.hom.base = g₂.hom.base)
    (hf_eq : g₁ ≫ f = g₂ ≫ f)
    (hι_eq : (ObjectProperty.homMk
        ((comapOfPair hR hRI (Pair.quotientHom R I)).hom.restrictPreimage W) :
        (⟨(ofPair (R.quotient I) hRI).obj.restrict
            ((Opens.map (comapOfPair hR hRI (Pair.quotientHom R I)).hom.base).obj
              W).isOpenEmbedding,
          isAdic_restrict _ (ofPair (R.quotient I) hRI).property⟩ : AdicSpace.{u}) ⟶ _) ≫ g₁ =
      ObjectProperty.homMk
        ((comapOfPair hR hRI (Pair.quotientHom R I)).hom.restrictPreimage W) ≫ g₂)
    (z : W) :
    ∃ O : Opens ((ofPair R hR).obj.restrict W.isOpenEmbedding), z ∈ O ∧
      ((ofPair R hR).obj.restrict W.isOpenEmbedding).ofRestrict O.isOpenEmbedding ≫ g₁.hom =
        ((ofPair R hR).obj.restrict W.isOpenEmbedding).ofRestrict O.isOpenEmbedding ≫ g₂.hom := by
  let Z := ofPair R hR
  let Z₀ := ofPair (R.quotient I) hRI
  let ι := comapOfPair hR hRI (Pair.quotientHom R I)
  let ZW : AdicSpace.{u} := ⟨Z.obj.restrict W.isOpenEmbedding, isAdic_restrict _ Z.property⟩
  let Z₀W : AdicSpace.{u} :=
    ⟨Z₀.obj.restrict ((Opens.map ι.hom.base).obj W).isOpenEmbedding, isAdic_restrict _ Z₀.property⟩
  obtain ⟨A, _, _, _, _, _, _, _, S, hS, B, _, _, _, _, _, _, _, T, hT, ψ, hψ,
    U, u, j, i, hu, hz_mem, hj, hi, hfac⟩ := hf.exists_affinoid_factorization (g₁.hom.base z)
  let W_sub : Opens ZW.obj :=
    ⟨g₁.hom.base ⁻¹' Set.range u.hom.base,
      hu.base_open.isOpen_range.preimage g₁.hom.base.hom.continuous⟩
  let W' : Opens Z.obj := W.isOpenEmbedding.isOpenMap.functor.obj W_sub
  obtain ⟨O_Z, hzO, hOW', A₁, _, _, _, _, _, _, _, S₁, hS₁, A₂, _, _, _, _, _, _, _, S₂, hS₂,
    π, hπ, hker_pow, v, u', hv, hv_range, _, hu'_range, hπv⟩ :=
    exists_ofPair_quotient_rational_square R hR I hRI W' ⟨z, hz_mem, rfl⟩
  have hOW : (O_Z : Set Z.obj) ⊆ W := fun w hw ↦ by obtain ⟨q, _, rfl⟩ := hOW' hw; exact q.2
  let vW : ofPair S₁ hS₁ ⟶ ZW := ObjectProperty.homMk
    (IsOpenImmersion.lift (Z.obj.ofRestrict W.isOpenEmbedding) v.hom
      (Set.range_subset_iff.mpr fun q ↦ Set.mem_range.mpr
        ⟨⟨v.hom.base q, hOW (by rw [← hv_range]; exact ⟨q, rfl⟩)⟩, rfl⟩))
  have hvW : vW ≫ ObjectProperty.homMk (Z.obj.ofRestrict W.isOpenEmbedding) = v :=
    InducedCategory.Hom.ext (IsOpenImmersion.lift_fac _ _ _)
  obtain ⟨u'W, hu'W⟩ := lift_of_range_subset
    (ObjectProperty.homMk (Z₀.obj.ofRestrict _) : Z₀W ⟶ Z₀) u'
    (by rw [hu'_range, ObjectProperty.homMk_hom]; rintro w hw; exact ⟨⟨w, hOW hw⟩, rfl⟩)
  have hπvW := lift_comm_restrictPreimage (comapOfPair hS₁ hS₂ π) v u' ι W hπv hvW hu'W
  have hr₁ : Set.range (vW ≫ g₁).hom.base ⊆ Set.range u.hom.base := by
    rintro _ ⟨q, rfl⟩
    have hv_mem : v.hom.base q ∈ (O_Z : Set Z.obj) := by rw [← hv_range]; exact ⟨q, rfl⟩
    obtain ⟨w, hw, hweq⟩ := hOW' hv_mem
    have hqw : vW.hom.base q = w := Subtype.ext
      ((congrArg (fun m : ofPair S₁ hS₁ ⟶ Z ↦ m.hom.base q) hvW).trans hweq.symm)
    change g₁.hom.base (vW.hom.base q) ∈ Set.range u.hom.base
    exact hqw.symm ▸ hw
  have hr₂ : Set.range (vW ≫ g₂).hom.base ⊆ Set.range u.hom.base := by
    rintro _ ⟨q, rfl⟩
    change g₂.hom.base (vW.hom.base q) ∈ Set.range u.hom.base
    rw [← hbase_eq]
    exact hr₁ ⟨q, rfl⟩
  have hvg : vW ≫ g₁ = vW ≫ g₂ :=
    eq_of_isQuotientMapping_of_affinoid_factorization hS hT hψ hfac hS₁ hS₂ hπ (hker_pow hI)
      hr₁ hr₂ (by rw [Category.assoc, Category.assoc, hf_eq])
      (by rw [← Category.assoc, ← Category.assoc, hπvW, Category.assoc, Category.assoc, hι_eq])
  let O : Opens ZW.obj := (Opens.map (Z.obj.ofRestrict W.isOpenEmbedding).base).obj O_Z
  have hrO := range_lift_ofRestrict_eq_range_ofRestrict v W O_Z hv_range hvW
  have hvg_hom : vW.hom ≫ g₁.hom = vW.hom ≫ g₂.hom := congrArg InducedCategory.Hom.hom hvg
  refine ⟨O, Opens.mem_map.mpr hzO, ?_⟩
  rw [← IsOpenImmersion.isoOfRangeEq_inv_comp vW.hom
    (((ofPair R hR).obj.restrict W.isOpenEmbedding).ofRestrict O.isOpenEmbedding) hrO,
    Category.assoc, Category.assoc, hvg_hom]

/-- Uniqueness of square-zero lifts over an arbitrary open `W` of `ofPair R hR`. -/
private theorem eq_on_open_of_sqZero_quotient {f : Y ⟶ X}
    (hf : IsEtaleLocalDescription f)
    {C : Type u} [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsHuberRing C]
    (R : Pair C) (hR : IsSheafyForEveryPresentation R.plus)
    (I : Ideal C) (hI : I ^ 2 = ⊥)
    (hRI : IsSheafyForEveryPresentation (R.quotient I).plus)
    (W : Opens (ofPair R hR).obj)
    {g₁ g₂ : (⟨(ofPair R hR).obj.restrict W.isOpenEmbedding,
      isAdic_restrict _ (ofPair R hR).property⟩ : AdicSpace.{u}) ⟶ Y}
    (hf_eq : g₁ ≫ f = g₂ ≫ f)
    (hι_eq : (ObjectProperty.homMk
        ((comapOfPair hR hRI (Pair.quotientHom R I)).hom.restrictPreimage W) :
        (⟨(ofPair (R.quotient I) hRI).obj.restrict
            ((Opens.map (comapOfPair hR hRI (Pair.quotientHom R I)).hom.base).obj
              W).isOpenEmbedding,
          isAdic_restrict _ (ofPair (R.quotient I) hRI).property⟩ : AdicSpace.{u}) ⟶ _) ≫ g₁ =
      ObjectProperty.homMk
        ((comapOfPair hR hRI (Pair.quotientHom R I)).hom.restrictPreimage W) ≫ g₂) :
    g₁ = g₂ := by
  have hι := isHomeomorph_comapOfPair_quotientHom_base R hR I hRI fun a ha ↦
    ⟨2, by rw [← Ideal.mem_bot, ← hI]; exact Ideal.pow_mem_pow ha 2⟩
  have hbase_eq : g₁.hom.base = g₂.hom.base := by
    ext z
    obtain ⟨z₀, hz₀⟩ := hι.surjective z.1
    let z₀W : (ofPair (R.quotient I) hRI).obj.restrict
        ((Opens.map (comapOfPair hR hRI (Pair.quotientHom R I)).hom.base).obj W).isOpenEmbedding :=
      ⟨z₀, Opens.mem_map.mpr (hz₀.symm ▸ z.2)⟩
    have hz_apply : ((comapOfPair hR hRI (Pair.quotientHom R I)).hom.restrictPreimage W).base z₀W =
        z :=
      ((comapOfPair hR hRI (Pair.quotientHom R I)).hom.restrictPreimage_base_apply W z₀W).trans
        (Subtype.ext hz₀)
    simpa only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom, comp_base,
      TopCat.coe_comp, Function.comp_apply, hz_apply] using
      congrArg (fun m ↦ m.hom.base z₀W) hι_eq
  choose O hzO hO_eq using fun z ↦
    exists_open_eq_on_open_of_sqZero_quotient hf R hR I hI hRI W hbase_eq hf_eq hι_eq z
  have hcov : iSup O = ⊤ := eq_top_iff.mpr fun z _ ↦ Opens.mem_iSup.mpr ⟨z, hzO z⟩
  exact InducedCategory.Hom.ext
    (PreAdicSpace.hom_ext_of_ofRestrict
      (isAdic_restrict _ (ofPair R hR).property |> isAdic_iff.mp |>.1) O hcov hO_eq)

/-- **Formal unramifiedness of étale morphisms along square-zero quotients.** Let `f : Y ⟶ X`
satisfy `IsEtaleLocalDescription`, and let `(C, R)` be a sheafy Huber pair and `I : Ideal C` a
square-zero ideal (`I ^ 2 = ⊥`) whose quotient Huber pair `R.quotient I` is sheafy. Any two
morphisms `g₁, g₂ : Spa(C, R⁺) ⟶ Y` that agree after composing with `f` and after restricting to
`Spa(C ⧸ I, (R.quotient I)⁺)` are equal. -/
theorem IsEtaleLocalDescription.eq_of_sqZero_quotient {f : Y ⟶ X}
    (hf : IsEtaleLocalDescription f)
    {C : Type u} [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsHuberRing C]
    (R : Pair C) (hR : IsSheafyForEveryPresentation R.plus)
    (I : Ideal C) (hI : I ^ 2 = ⊥)
    (hRI : IsSheafyForEveryPresentation (R.quotient I).plus)
    {g₁ g₂ : ofPair R hR ⟶ Y} (hf_eq : g₁ ≫ f = g₂ ≫ f)
    (hι_eq : comapOfPair hR hRI (Pair.quotientHom R I) ≫ g₁ =
      comapOfPair hR hRI (Pair.quotientHom R I) ≫ g₂) :
    g₁ = g₂ := by
  let Z := ofPair R hR
  let Z₀ := ofPair (R.quotient I) hRI
  let ι := comapOfPair hR hRI (Pair.quotientHom R I)
  let rZ : (⟨Z.obj.restrict (⊤ : Opens Z.obj).isOpenEmbedding,
      isAdic_restrict _ Z.property⟩ : AdicSpace.{u}) ⟶ Z :=
    ObjectProperty.homMk (Z.obj.ofRestrict _)
  have : IsIso rZ.hom := by
    rw [ObjectProperty.homMk_hom, ← restrictTopIso_hom]
    infer_instance
  have hsq : (ObjectProperty.homMk (ι.hom.restrictPreimage ⊤) :
      (⟨Z₀.obj.restrict ((Opens.map ι.hom.base).obj ⊤).isOpenEmbedding,
        isAdic_restrict _ Z₀.property⟩ : AdicSpace.{u}) ⟶ _) ≫ rZ =
      ObjectProperty.homMk (Z₀.obj.ofRestrict _) ≫ ι :=
    InducedCategory.Hom.ext (Hom.restrictPreimage_ofRestrict ι.hom ⊤)
  have hr_eq : rZ ≫ g₁ = rZ ≫ g₂ :=
    eq_on_open_of_sqZero_quotient hf R hR I hI hRI ⊤
      (by rw [Category.assoc, Category.assoc, hf_eq])
      (by rw [← Category.assoc, ← Category.assoc, hsq, Category.assoc, Category.assoc, hι_eq])
  exact InducedCategory.Hom.ext ((cancel_epi rZ.hom).mp (congrArg InducedCategory.Hom.hom hr_eq))

/-- Around any point `z : (ofPair R hR).obj`, a square-zero lifting problem admits a local lift
over an open neighbourhood `O` of `z`. -/
private theorem exists_local_lift_of_sqZero_quotient {f : Y ⟶ X}
    (hf : IsEtaleLocalDescription f)
    {C : Type u} [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsHuberRing C]
    (R : Pair C) (hR : IsSheafyForEveryPresentation R.plus)
    (I : Ideal C) (hI : I ^ 2 = ⊥)
    (hRI : IsSheafyForEveryPresentation (R.quotient I).plus)
    (g₀ : ofPair (R.quotient I) hRI ⟶ Y) (h : ofPair R hR ⟶ X)
    (hsq : g₀ ≫ f = comapOfPair hR hRI (Pair.quotientHom R I) ≫ h)
    (z : (ofPair R hR).obj) :
    ∃ (O : Opens (ofPair R hR).obj), z ∈ O ∧
      ∃ gO : (ofPair R hR).obj.restrict O.isOpenEmbedding ⟶ Y.obj,
        gO ≫ f.hom = (ofPair R hR).obj.ofRestrict O.isOpenEmbedding ≫ h.hom ∧
        (comapOfPair hR hRI (Pair.quotientHom R I)).hom.restrictPreimage O ≫ gO =
          (ofPair (R.quotient I) hRI).obj.ofRestrict
            ((Opens.map (comapOfPair hR hRI (Pair.quotientHom R I)).hom.base).obj
              O).isOpenEmbedding ≫
            g₀.hom := by
  let Z := ofPair R hR
  let Z₀ := ofPair (R.quotient I) hRI
  let ι := comapOfPair hR hRI (Pair.quotientHom R I)
  have hι := isHomeomorph_comapOfPair_quotientHom_base R hR I hRI fun a ha ↦
    ⟨2, by rw [← Ideal.mem_bot, ← hI]; exact Ideal.pow_mem_pow ha 2⟩
  obtain ⟨z₀, hz₀⟩ := hι.surjective z
  obtain ⟨A, _, _, _, _, _, _, _, S, hS, B, _, _, _, _, _, _, _, T, hT, ψ, hψ,
    U, u, j, i, hu, hz₀_mem, hj, hi, hfac⟩ := hf.exists_affinoid_factorization (g₀.hom.base z₀)
  let W₀ : Set Z₀.obj := g₀.hom.base ⁻¹' Set.range u.hom.base
  let W : Opens Z.obj :=
    ⟨ι.hom.base '' W₀,
      hι.isOpenMap _ (hu.base_open.isOpen_range.preimage g₀.hom.base.hom.continuous)⟩
  obtain ⟨O, hzO, hOW, A₁, _, _, _, _, _, _, _, S₁, hS₁, A₂, _, _, _, _, _, _, _, S₂, hS₂,
    π, hπ, hker_pow, v, u', hv, hv_range, hu', hu'_range, hπv⟩ :=
    exists_ofPair_quotient_rational_square R hR I hRI W ⟨z₀, hz₀_mem, hz₀⟩
  have hr₀ : Set.range (u' ≫ g₀).hom.base ⊆ Set.range u.hom.base := by
    rintro _ ⟨q, rfl⟩
    have hq_mem : u'.hom.base q ∈ Set.range u'.hom.base := ⟨q, rfl⟩
    rw [hu'_range] at hq_mem
    exact hι.injective.mem_set_image.mp (hOW hq_mem)
  have hsq_loc : (u' ≫ g₀) ≫ f = comapOfPair hS₁ hS₂ π ≫ (v ≫ h) := by
    rw [Category.assoc, hsq, ← Category.assoc, ← hπv, Category.assoc]
  obtain ⟨gloc, hgloc_π, hgloc_f⟩ :=
    exists_of_isQuotientMapping_of_affinoid_factorization hS hT hψ hfac hS₁ hS₂ hπ (hker_pow hI)
      (u' ≫ g₀) (v ≫ h) hsq_loc hr₀
  have hrv : Set.range v.hom.base = Set.range (Z.obj.ofRestrict O.isOpenEmbedding).base := by
    rw [hv_range]
    ext w
    exact ⟨fun hw ↦ ⟨⟨w, hw⟩, rfl⟩, by rintro ⟨q, rfl⟩; exact q.2⟩
  have hru' : Set.range u'.hom.base =
      Set.range (Z₀.obj.ofRestrict ((Opens.map ι.hom.base).obj O).isOpenEmbedding).base := by
    rw [hu'_range]
    ext w
    exact ⟨fun hw ↦ ⟨⟨w, hw⟩, rfl⟩, by rintro ⟨q, rfl⟩; exact q.2⟩
  let ev := IsOpenImmersion.isoOfRangeEq v.hom (Z.obj.ofRestrict O.isOpenEmbedding) hrv
  let eu' := IsOpenImmersion.isoOfRangeEq u'.hom (Z₀.obj.ofRestrict _) hru'
  have hres_ι : ι.hom.restrictPreimage O = eu'.inv ≫ (comapOfPair hS₁ hS₂ π).hom ≫ ev.hom := by
    rw [← cancel_mono (Z.obj.ofRestrict O.isOpenEmbedding), Hom.restrictPreimage_ofRestrict,
      Category.assoc, Category.assoc, IsOpenImmersion.isoOfRangeEq_hom_comp]
    have hπv' := congrArg InducedCategory.Hom.hom hπv
    simp only [ObjectProperty.FullSubcategory.comp_hom] at hπv'
    rw [hπv', IsOpenImmersion.isoOfRangeEq_inv_comp_assoc]
  refine ⟨O, hzO, ev.inv ≫ gloc.hom, ?_, ?_⟩
  · rw [Category.assoc, ← ObjectProperty.FullSubcategory.comp_hom, hgloc_f,
      ObjectProperty.FullSubcategory.comp_hom, IsOpenImmersion.isoOfRangeEq_inv_comp_assoc]
  · rw [hres_ι, Category.assoc, Category.assoc, Iso.hom_inv_id_assoc,
      ← ObjectProperty.FullSubcategory.comp_hom, hgloc_π,
      ObjectProperty.FullSubcategory.comp_hom, IsOpenImmersion.isoOfRangeEq_inv_comp_assoc]

private theorem restrictPreimage_comp_lift_ofRestrict {Z Z₀ : PreAdicSpace.{u}} (ι : Z₀ ⟶ Z)
    {U V : Opens Z} (hUV : U ≤ V) :
    ι.restrictPreimage U ≫
      IsOpenImmersion.lift (Z.ofRestrict V.isOpenEmbedding) (Z.ofRestrict U.isOpenEmbedding)
        (Set.range_subset_iff.mpr fun q ↦ Set.mem_range.mpr ⟨⟨q.1, hUV q.2⟩, rfl⟩) =
    IsOpenImmersion.lift (Z₀.ofRestrict ((Opens.map ι.base).obj V).isOpenEmbedding)
      (Z₀.ofRestrict ((Opens.map ι.base).obj U).isOpenEmbedding)
      (Set.range_subset_iff.mpr fun q ↦ Set.mem_range.mpr ⟨⟨q.1, hUV q.2⟩, rfl⟩) ≫
      ι.restrictPreimage V := by
  rw [← cancel_mono (Z.ofRestrict V.isOpenEmbedding), Category.assoc, Category.assoc,
    IsOpenImmersion.lift_fac, Hom.restrictPreimage_ofRestrict,
    Hom.restrictPreimage_ofRestrict, IsOpenImmersion.lift_fac_assoc]

/-- Two local square-zero lifts over opens `O₁` and `O₂` agree on their pullback over `ofPair R hR`.
-/
private theorem pullback_fst_comp_eq_of_sqZero_quotient {f : Y ⟶ X}
    (hf : IsEtaleLocalDescription f)
    {C : Type u} [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsHuberRing C]
    (R : Pair C) (hR : IsSheafyForEveryPresentation R.plus)
    (I : Ideal C) (hI : I ^ 2 = ⊥)
    (hRI : IsSheafyForEveryPresentation (R.quotient I).plus)
    (g₀ : ofPair (R.quotient I) hRI ⟶ Y) (h : ofPair R hR ⟶ X)
    {O₁ O₂ : Opens (ofPair R hR).obj}
    {g₁ : (ofPair R hR).obj.restrict O₁.isOpenEmbedding ⟶ Y.obj}
    {g₂ : (ofPair R hR).obj.restrict O₂.isOpenEmbedding ⟶ Y.obj}
    (hg₁_f : g₁ ≫ f.hom = (ofPair R hR).obj.ofRestrict O₁.isOpenEmbedding ≫ h.hom)
    (hg₂_f : g₂ ≫ f.hom = (ofPair R hR).obj.ofRestrict O₂.isOpenEmbedding ≫ h.hom)
    (hg₁_ι : (comapOfPair hR hRI (Pair.quotientHom R I)).hom.restrictPreimage O₁ ≫ g₁ =
      (ofPair (R.quotient I) hRI).obj.ofRestrict
        ((Opens.map (comapOfPair hR hRI (Pair.quotientHom R I)).hom.base).obj
          O₁).isOpenEmbedding ≫ g₀.hom)
    (hg₂_ι : (comapOfPair hR hRI (Pair.quotientHom R I)).hom.restrictPreimage O₂ ≫ g₂ =
      (ofPair (R.quotient I) hRI).obj.ofRestrict
        ((Opens.map (comapOfPair hR hRI (Pair.quotientHom R I)).hom.base).obj
          O₂).isOpenEmbedding ≫ g₀.hom) :
    pullback.fst ((ofPair R hR).obj.ofRestrict O₁.isOpenEmbedding)
      ((ofPair R hR).obj.ofRestrict O₂.isOpenEmbedding) ≫ g₁ = pullback.snd _ _ ≫ g₂ := by
  let ι := comapOfPair hR hRI (Pair.quotientHom R I)
  let W : Opens (ofPair R hR).obj := O₁ ⊓ O₂
  let iW₁ := IsOpenImmersion.lift ((ofPair R hR).obj.ofRestrict O₁.isOpenEmbedding)
    ((ofPair R hR).obj.ofRestrict W.isOpenEmbedding)
    (Set.range_subset_iff.mpr fun q ↦ Set.mem_range.mpr ⟨⟨q.1, q.2.1⟩, rfl⟩)
  let iW₂ := IsOpenImmersion.lift ((ofPair R hR).obj.ofRestrict O₂.isOpenEmbedding)
    ((ofPair R hR).obj.ofRestrict W.isOpenEmbedding)
    (Set.range_subset_iff.mpr fun q ↦ Set.mem_range.mpr ⟨⟨q.1, q.2.2⟩, rfl⟩)
  have hm_eq : (ObjectProperty.homMk (iW₁ ≫ g₁) :
      (⟨(ofPair R hR).obj.restrict W.isOpenEmbedding,
        isAdic_restrict _ (ofPair R hR).property⟩ : AdicSpace.{u}) ⟶ Y) =
      ObjectProperty.homMk (iW₂ ≫ g₂) :=
    eq_on_open_of_sqZero_quotient hf R hR I hI hRI W
      (InducedCategory.Hom.ext (by
        simp only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom,
          Category.assoc, hg₁_f, hg₂_f]
        rw [IsOpenImmersion.lift_fac_assoc, IsOpenImmersion.lift_fac_assoc]))
      (InducedCategory.Hom.ext (by
        simp only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom]
        rw [reassoc_of% (restrictPreimage_comp_lift_ofRestrict ι.hom (inf_le_left : W ≤ O₁)),
          reassoc_of% (restrictPreimage_comp_lift_ofRestrict ι.hom (inf_le_right : W ≤ O₂)),
          hg₁_ι, hg₂_ι, IsOpenImmersion.lift_fac_assoc, IsOpenImmersion.lift_fac_assoc]))
  have hm_hom : iW₁ ≫ g₁ = iW₂ ≫ g₂ := congrArg InducedCategory.Hom.hom hm_eq
  let pZ := pullback.fst ((ofPair R hR).obj.ofRestrict O₁.isOpenEmbedding)
      ((ofPair R hR).obj.ofRestrict O₂.isOpenEmbedding) ≫
      (ofPair R hR).obj.ofRestrict O₁.isOpenEmbedding
  have hrP : Set.range pZ.base =
      Set.range ((ofPair R hR).obj.ofRestrict W.isOpenEmbedding).base := by
    rw [IsOpenImmersion.range_pullback_to_base_of_left]
    ext w
    exact ⟨fun ⟨⟨q₁, h₁⟩, ⟨q₂, h₂⟩⟩ ↦ ⟨⟨w, h₁ ▸ q₁.2, h₂ ▸ q₂.2⟩, rfl⟩,
      by rintro ⟨q, rfl⟩; exact ⟨⟨⟨q.1, q.2.1⟩, rfl⟩, ⟨⟨q.1, q.2.2⟩, rfl⟩⟩⟩
  let eP := IsOpenImmersion.isoOfRangeEq pZ ((ofPair R hR).obj.ofRestrict W.isOpenEmbedding) hrP
  have heP₁ : eP.hom ≫ iW₁ = pullback.fst _ _ := by
    rw [← cancel_mono ((ofPair R hR).obj.ofRestrict O₁.isOpenEmbedding), Category.assoc,
      IsOpenImmersion.lift_fac, IsOpenImmersion.isoOfRangeEq_hom_comp]
  have heP₂ : eP.hom ≫ iW₂ = pullback.snd _ _ := by
    rw [← cancel_mono ((ofPair R hR).obj.ofRestrict O₂.isOpenEmbedding), Category.assoc,
      IsOpenImmersion.lift_fac, IsOpenImmersion.isoOfRangeEq_hom_comp]
    exact pullback.condition
  rw [← heP₁, ← heP₂, Category.assoc, Category.assoc, hm_hom]

/-- **Infinitesimal lifting (existence) for étale morphisms along square-zero quotients.** Let
`f : Y ⟶ X` satisfy `IsEtaleLocalDescription`, and let `(C, R)` be a sheafy Huber pair and
`I : Ideal C` a square-zero ideal (`I ^ 2 = ⊥`) whose quotient Huber pair `R.quotient I` is sheafy.
Every commutative square from `Spa(C ⧸ I, (R.quotient I)⁺) ⟶ Spa(C, R⁺)` to `f : Y ⟶ X` admits a
diagonal lift `Spa(C, R⁺) ⟶ Y`. -/
theorem IsEtaleLocalDescription.exists_of_sqZero_quotient {f : Y ⟶ X}
    (hf : IsEtaleLocalDescription f)
    {C : Type u} [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsHuberRing C]
    (R : Pair C) (hR : IsSheafyForEveryPresentation R.plus)
    (I : Ideal C) (hI : I ^ 2 = ⊥)
    (hRI : IsSheafyForEveryPresentation (R.quotient I).plus)
    (g₀ : ofPair (R.quotient I) hRI ⟶ Y) (h : ofPair R hR ⟶ X)
    (hsq : g₀ ≫ f = comapOfPair hR hRI (Pair.quotientHom R I) ≫ h) :
    ∃ g : ofPair R hR ⟶ Y,
      comapOfPair hR hRI (Pair.quotientHom R I) ≫ g = g₀ ∧ g ≫ f = h := by
  let ι := comapOfPair hR hRI (Pair.quotientHom R I)
  choose O hzO gO hgO_f hgO_ι using
    exists_local_lift_of_sqZero_quotient hf R hR I hI hRI g₀ h hsq
  have hcov : ⨆ z, O z = ⊤ := eq_top_iff.mpr fun z _ ↦ Opens.mem_iSup.mpr ⟨z, hzO z⟩
  let g : ofPair R hR ⟶ Y := ObjectProperty.homMk
    (PreAdicSpace.glueMorphisms (isAdic_iff.mp (ofPair R hR).property).1 O hcov gO fun k l ↦
      pullback_fst_comp_eq_of_sqZero_quotient hf R hR I hI hRI g₀ h
        (hgO_f k) (hgO_f l) (hgO_ι k) (hgO_ι l))
  have hcov₀ : ⨆ z, (Opens.map ι.hom.base).obj (O z) = ⊤ := eq_top_iff.mpr fun w _ ↦ by
    obtain ⟨z, hz⟩ := Opens.mem_iSup.mp (show ι.hom.base w ∈ ⨆ z, O z by rw [hcov]; trivial)
    exact Opens.mem_iSup.mpr ⟨z, hz⟩
  refine ⟨g, ?_, ?_⟩
  · ext1
    refine PreAdicSpace.hom_ext_of_ofRestrict
      (isAdic_iff.mp (ofPair (R.quotient I) hRI).property).1 _ hcov₀ fun z ↦ ?_
    simp only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom, g]
    rw [← Category.assoc, ← Hom.restrictPreimage_ofRestrict, Category.assoc,
      PreAdicSpace.ofRestrict_glueMorphisms, hgO_ι]
  · ext1
    refine PreAdicSpace.hom_ext_of_ofRestrict
      (isAdic_iff.mp (ofPair R hR).property).1 O hcov fun z ↦ ?_
    simp only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom, g,
      PreAdicSpace.ofRestrict_glueMorphisms_assoc, hgO_f]

/-- **Unique infinitesimal lifting for étale morphisms of analytic adic spaces** along square-zero
quotients (`I ^ 2 = ⊥`) of sheafy Huber pairs `(C, R)` with sheafy quotient pair `R.quotient I`. -/
theorem IsEtaleLocalDescription.existsUnique_of_sqZero_quotient {f : Y ⟶ X}
    (hf : IsEtaleLocalDescription f)
    {C : Type u} [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsHuberRing C]
    (R : Pair C) (hR : IsSheafyForEveryPresentation R.plus)
    (I : Ideal C) (hI : I ^ 2 = ⊥)
    (hRI : IsSheafyForEveryPresentation (R.quotient I).plus)
    (g₀ : ofPair (R.quotient I) hRI ⟶ Y) (h : ofPair R hR ⟶ X)
    (hsq : g₀ ≫ f = comapOfPair hR hRI (Pair.quotientHom R I) ≫ h) :
    ∃! g : ofPair R hR ⟶ Y,
      comapOfPair hR hRI (Pair.quotientHom R I) ≫ g = g₀ ∧ g ≫ f = h := by
  obtain ⟨g, hg₁, hg₂⟩ := hf.exists_of_sqZero_quotient R hR I hI hRI g₀ h hsq
  exact ⟨g, ⟨hg₁, hg₂⟩, fun g' ⟨hg'₁, hg'₂⟩ ↦
    hf.eq_of_sqZero_quotient R hR I hI hRI (hg'₂.trans hg₂.symm) (hg'₁.trans hg₁.symm)⟩

end InfinitesimalLifting

end AdicSpace

end TauCeti
