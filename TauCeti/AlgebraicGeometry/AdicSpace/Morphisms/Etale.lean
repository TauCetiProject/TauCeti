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
* `IsEtaleLocalDescription.exists_affinoid_factorization`: refinement of the middle finite étale
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
    inferInstance, inferInstance, .id hX, by simp⟩⟩

/-- **An open immersion in `AdicSpace` is étale if and only if its target is analytic.** -/
theorem isEtaleLocalDescription_iff_of_isOpenImmersion (f : Y ⟶ X)
    [PreAdicSpace.IsOpenImmersion f.hom] : IsEtaleLocalDescription f ↔ X.IsAnalytic :=
  ⟨IsEtaleLocalDescription.isAnalytic_target, IsEtaleLocalDescription.of_isOpenImmersion f⟩

/-- **The identity of an analytic adic space is étale.** -/
theorem IsEtaleLocalDescription.id {X : AdicSpace.{u}} (hX : X.IsAnalytic) :
    IsEtaleLocalDescription (𝟙 X) := .of_isFiniteEtale (IsFiniteEtale.id hX)

/-- **The identity of an adic space `X` is étale if and only if `X` is analytic.** -/
@[simp] theorem isEtaleLocalDescription_id_iff {X : AdicSpace.{u}} :
    IsEtaleLocalDescription (𝟙 X) ↔ X.IsAnalytic :=
  ⟨IsEtaleLocalDescription.isAnalytic_target, IsEtaleLocalDescription.id⟩

/-- **An isomorphism onto an analytic adic space is étale.** -/
theorem IsEtaleLocalDescription.of_isIso (f : Y ⟶ X) [IsIso f] (hX : X.IsAnalytic) :
    IsEtaleLocalDescription f := .of_isFiniteEtale (IsFiniteEtale.of_isIso f hX)

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
    rw [← Category.assoc, huv, Category.assoc, hfac, Category.assoc]

/-- **Postcomposing an étale morphism with an open immersion into an analytic target gives an étale
morphism.** -/
theorem IsEtaleLocalDescription.comp_isOpenImmersion {f : Y ⟶ X} (hf : IsEtaleLocalDescription f)
    (v : X ⟶ Z) [PreAdicSpace.IsOpenImmersion v.hom] (hZ : Z.IsAnalytic) :
    IsEtaleLocalDescription (f ≫ v) := by
  refine ⟨hZ, hf.isAnalytic_source, fun y ↦ ?_⟩
  obtain ⟨U, V, W, u, i, j, g, hu, hy, hi, hj, hg, hfac⟩ := hf.2.2 y
  refine ⟨U, V, W, u, i ≫ v, j, g, hu, hy, ?_, hj, hg, ?_⟩
  · rw [ObjectProperty.FullSubcategory.comp_hom]; infer_instance
  · rw [← Category.assoc, hfac, Category.assoc, Category.assoc]

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
    (U : ι → Opens Y.obj) (hU : iSup U = ⊤) (hf : ∀ k, IsEtaleLocalDescription
      ((ObjectProperty.homMk (Y.obj.ofRestrict (U k).isOpenEmbedding) :
        (⟨Y.obj.restrict (U k).isOpenEmbedding, isAdic_restrict _ Y.property⟩ :
          AdicSpace.{u}) ⟶ Y) ≫ f)) : IsEtaleLocalDescription f := by
  let u : ∀ k, (⟨Y.obj.restrict (U k).isOpenEmbedding, isAdic_restrict _ Y.property⟩ :
      AdicSpace.{u}) ⟶ Y := fun k ↦ ObjectProperty.homMk (Y.obj.ofRestrict (U k).isOpenEmbedding)
  have _ (k) : PreAdicSpace.IsOpenImmersion (u k).hom := inferInstance
  exact .of_jointly_surjective hX u
    (fun y ↦ let ⟨k, hk⟩ := Opens.mem_iSup.mp (hU.symm ▸ trivial : y ∈ iSup U); ⟨k, ⟨y, hk⟩, rfl⟩)
    hf

/-- Being étale (`IsEtaleLocalDescription`) is local on the source for morphisms into an analytic
target `X`. -/
theorem isEtaleLocalDescription_iff_of_iSup_eq_top_source {f : Y ⟶ X} (hX : X.IsAnalytic)
    {ι : Type*} (U : ι → Opens Y.obj) (hU : iSup U = ⊤) :
    IsEtaleLocalDescription f ↔ ∀ k, IsEtaleLocalDescription
      ((ObjectProperty.homMk (Y.obj.ofRestrict (U k).isOpenEmbedding) :
        (⟨Y.obj.restrict (U k).isOpenEmbedding, isAdic_restrict _ Y.property⟩ :
          AdicSpace.{u}) ⟶ Y) ≫ f) :=
  ⟨fun hf _ ↦ hf.isOpenImmersion_comp _, .of_iSup_eq_top_source hX U hU⟩

/-- **Target-cover descent for étale morphisms.** If `V : ι → Opens X.obj` covers `X` and the
preimage restriction of `f : Y ⟶ X` over every `V k` satisfies `IsEtaleLocalDescription`, then `f`
satisfies `IsEtaleLocalDescription`. -/
theorem IsEtaleLocalDescription.of_iSup_eq_top {f : Y ⟶ X} {ι : Type*} (V : ι → Opens X.obj)
    (hV : iSup V = ⊤) (hf : ∀ k, IsEtaleLocalDescription
      (ObjectProperty.homMk (f.hom.restrictPreimage (V k)) :
        (⟨Y.obj.restrict ((Opens.map f.hom.base).obj (V k)).isOpenEmbedding,
          isAdic_restrict _ Y.property⟩ : AdicSpace.{u}) ⟶
        ⟨X.obj.restrict (V k).isOpenEmbedding, isAdic_restrict _ X.property⟩)) :
    IsEtaleLocalDescription f := by
  let v : ∀ k, X.restrict (V k) ⟶ X := fun k ↦ X.ofRestrict (V k)
  have _ (k) : PreAdicSpace.IsOpenImmersion (v k).hom := inferInstance
  have hX : X.IsAnalytic := .of_jointly_surjective v (fun k ↦ (hf k).isAnalytic_target)
    fun x ↦ let ⟨k, hx⟩ := Opens.mem_iSup.mp (hV.symm ▸ trivial : x ∈ iSup V)
      ⟨k, ⟨x, hx⟩, X.ofRestrict_base_apply (V k) ⟨x, hx⟩⟩
  let U : ι → Opens Y.obj := fun k ↦ (Opens.map f.hom.base).obj (V k)
  have hU : iSup U = ⊤ := eq_top_iff.mpr fun y _ ↦
    let ⟨k, hk⟩ := Opens.mem_iSup.mp (hV.symm ▸ trivial : f.hom.base y ∈ iSup V)
    Opens.mem_iSup.mpr ⟨k, hk⟩
  refine .of_iSup_eq_top_source hX U hU fun k ↦ ?_
  have hu_eq : (ObjectProperty.homMk (Y.obj.ofRestrict (U k).isOpenEmbedding) :
      Y.restrict (U k) ⟶ Y) = Y.ofRestrict (U k) :=
    InducedCategory.Hom.ext (Y.ofRestrict_hom (U k)).symm
  have hres_eq : (ObjectProperty.homMk (f.hom.restrictPreimage (V k)) :
      Y.restrict (U k) ⟶ X.restrict (V k)) = AdicSpace.restrictPreimage f (V k) :=
    InducedCategory.Hom.ext (AdicSpace.restrictPreimage_hom f (V k)).symm
  rw [hu_eq, ← AdicSpace.restrictPreimage_ofRestrict f (V k), ← hres_eq]
  exact (hf k).comp_isOpenImmersion (v k) hX

/-! ### Refinement to affinoid middle factors and finiteness properties -/

/-- **Refinement of local factorizations of an étale morphism to complete Hausdorff Tate affinoid
middle factors** via `comapOfPair`. -/
theorem IsEtaleLocalDescription.exists_affinoid_factorization {f : Y ⟶ X}
    (hf : IsEtaleLocalDescription f) (y : Y.obj) :
    ∃ (A : Type u) (_ : CommRing A) (_ : UniformSpace A) (_ : IsUniformAddGroup A)
      (_ : IsTopologicalRing A) (_ : CompleteSpace A) (_ : T2Space A) (_ : IsTateRing A)
      (S : Pair A) (hS : IsSheafyForEveryPresentation S.plus) (B : Type u) (_ : CommRing B)
      (_ : UniformSpace B) (_ : IsUniformAddGroup B) (_ : IsTopologicalRing B) (_ : CompleteSpace B)
      (_ : T2Space B) (_ : IsTateRing B) (T : Pair B) (hT : IsSheafyForEveryPresentation T.plus)
      (ψ : Pair.Hom S T) (_ : ψ.IsFiniteEtale) (U : AdicSpace.{u}) (u : U ⟶ Y)
      (j : U ⟶ ofPair T hT) (i : ofPair S hS ⟶ X),
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
  obtain ⟨q₀, hq₀⟩ : p₀ ∈ Set.range r.hom.base := by
    rw [ObjectProperty.homMk_hom, IsOpenImmersion.range_pullback_snd_of_left]
    exact ⟨⟨j₀.hom.base p₀, Opens.mem_map.mpr hv₀⟩, rfl⟩
  refine ⟨A, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, S, hS, B, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, T, hT, ψ, hψ, U, r ≫ u₀, j, i, ?_,
    ⟨q₀, by simp [hq₀, hp₀]⟩, inferInstance, inferInstance, ?_⟩
  · rw [ObjectProperty.FullSubcategory.comp_hom]; infer_instance
  · ext1; have h1 := congrArg (r.hom ≫ InducedCategory.Hom.hom ·) hfac₀
    simp only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom, r, j, i] at h1 ⊢
    rw [Category.assoc, h1, ← Category.assoc, ← Category.assoc, ← pullback.condition]
    simp only [Category.assoc, w, reassoc_of% hg_fac]

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
    exact ((hg y).locallyOfFiniteType.comp_of_isOpenImmersion _).isOpenImmersion_comp _
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
    ((cancel_mono j).mp ((ofPairHomEquiv hT hS₁).injective (hψ.eq_of_sqZero_quotient hK hσ_ψ hσ_K)))

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
  have hcomm_space : (g₀' ≫ j) ≫ comapOfPair hS hT ψ = πK ≫ h' :=
    (cancel_mono i).mp (by
      rw [Category.assoc, Category.assoc, ← hfac, ← Category.assoc,
        liftOfIsOpenImmersion_fac, hsq, Category.assoc, liftOfIsOpenImmersion_fac])
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
  · have hlj : πK ≫ l = g₀' := (cancel_mono j).mp (by rw [Category.assoc,
      liftOfIsOpenImmersion_fac, hk_K])
    rw [← Category.assoc, hlj, liftOfIsOpenImmersion_fac]
  · rw [Category.assoc, hfac, ← Category.assoc, liftOfIsOpenImmersion_fac, ← Category.assoc,
      hk_ψ, liftOfIsOpenImmersion_fac]

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
  obtain ⟨A, _, _, _, _, _, _, _, S, hS, B, _, _, _, _, _, _, _, T, hT, ψ, hψ,
    U, u, j, i, hu, hz_mem, hj, hi, hfac⟩ := hf.exists_affinoid_factorization (g₁.hom.base z)
  let W : Opens (ofPair R hR).obj := ⟨g₁.hom.base ⁻¹' Set.range u.hom.base,
    hu.base_open.isOpen_range.preimage g₁.hom.base.hom.continuous⟩
  obtain ⟨O, hzO, hOW, A₁, _, _, _, _, _, _, _, S₁, hS₁, K, hSK, _, hcompK, hK_pow,
    v, _, hv, hv_range, _, _, hKv⟩ := exists_ofPair_quotient_rational_square R hR I hRI W hz_mem
  have hr₁ : Set.range (v ≫ g₁).hom.base ⊆ Set.range u.hom.base := by
    rintro _ ⟨q, rfl⟩; exact hOW (by rw [← SetLike.mem_coe, ← hv_range]; exact ⟨q, rfl⟩)
  have hr₂ : Set.range (v ≫ g₂).hom.base ⊆ Set.range u.hom.base := by
    rintro _ ⟨q, rfl⟩
    have hq : g₁.hom.base (v.hom.base q) ∈ Set.range u.hom.base := hr₁ ⟨q, rfl⟩
    rwa [hbase_eq] at hq
  have hvg : v ≫ g₁ = v ≫ g₂ :=
    eq_of_affinoid_factorization hS hT hS₁ hSK hψ hfac hcompK (hK_pow hI) hr₁ hr₂
      (by rw [Category.assoc, Category.assoc, hf_eq])
      (by rw [← Category.assoc, ← Category.assoc, hKv, Category.assoc, Category.assoc, hι_eq])
  exact ⟨(ofPair S₁ hS₁).obj, v.hom, hv, hv_range.symm ▸ hzO, congrArg InducedCategory.Hom.hom hvg⟩

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

private theorem exists_local_lift_of_sqZero_quotient (hf : IsEtaleLocalDescription f)
    (hI : I ^ 2 = ⊥) (hsq : g₀ ≫ f = sqZeroQuotHom R hR I hRI ≫ h) (z : (ofPair R hR).obj) :
    ∃ (O : Opens (ofPair R hR).obj), z ∈ O ∧
      ∃ gO : (ofPair R hR).obj.restrict O.isOpenEmbedding ⟶ Y.obj,
        gO ≫ f.hom = (ofPair R hR).obj.ofRestrict O.isOpenEmbedding ≫ h.hom ∧
        (sqZeroQuotHom R hR I hRI).hom.restrictPreimage O ≫ gO =
          (ofPair (R.quotient I) hRI).obj.ofRestrict
            ((Opens.map (sqZeroQuotHom R hR I hRI).hom.base).obj O).isOpenEmbedding ≫ g₀.hom := by
  let Z := ofPair R hR; let Z₀ := ofPair (R.quotient I) hRI; let ι := sqZeroQuotHom R hR I hRI
  have hι := isHomeomorph_comapOfPair_quotientHom_base_of_isNilpotent R hR I hRI ⟨2, hI⟩
  obtain ⟨z₀, hz₀⟩ := hι.surjective z
  -- Refine around `z` to a rational open `O` where `g₀` lands in an affinoid chart `U` of `f`
  obtain ⟨A, _, _, _, _, _, _, _, S, hS, B, _, _, _, _, _, _, _, T, hT, ψ, hψ,
    U, u, j, i, hu, hz₀_mem, hj, hi, hfac⟩ := hf.exists_affinoid_factorization (g₀.hom.base z₀)
  let W : Opens Z.obj := ⟨ι.hom.base '' (g₀.hom.base ⁻¹' Set.range u.hom.base),
    hι.isOpenMap _ (hu.base_open.isOpen_range.preimage g₀.hom.base.hom.continuous)⟩
  obtain ⟨O, hzO, hOW, A₁, _, _, _, _, _, _, _, S₁, hS₁, K, hSK, _, hcompK, hK_pow,
    v, u', hv, hv_range, hu', hu'_range, hKv⟩ :=
    exists_ofPair_quotient_rational_square R hR I hRI W ⟨z₀, hz₀_mem, hz₀⟩
  have hr₀ : Set.range (u' ≫ g₀).hom.base ⊆ Set.range u.hom.base := by
    rintro _ ⟨q, rfl⟩; exact hι.injective.mem_set_image.mp
      (hOW (Set.mem_preimage.mp (by rw [← hu'_range]; exact ⟨q, rfl⟩)))
  -- Lift over the complete affinoid rational localization `S₁` and transport back to `Z|_O`
  obtain ⟨gloc, hgloc_K, hgloc_f⟩ :=
    exists_of_affinoid_factorization hS hT hS₁ hSK hψ hfac hcompK (hK_pow hI) (u' ≫ g₀) (v ≫ h)
      (by rw [Category.assoc, hsq, ← Category.assoc, ← hKv, Category.assoc]) hr₀
  have hrv : Set.range v.hom.base = Set.range (Z.obj.ofRestrict O.isOpenEmbedding).base :=
    hv_range.trans (Opens.set_range_inclusion' O).symm
  have hru' : Set.range u'.hom.base =
      Set.range (Z₀.obj.ofRestrict ((Opens.map ι.hom.base).obj O).isOpenEmbedding).base :=
    hu'_range.trans (Opens.set_range_inclusion' ((Opens.map ι.hom.base).obj O)).symm
  let ev := IsOpenImmersion.isoOfRangeEq v.hom (Z.obj.ofRestrict O.isOpenEmbedding) hrv
  let eu' := IsOpenImmersion.isoOfRangeEq u'.hom (Z₀.obj.ofRestrict _) hru'
  have hres_ι : ι.hom.restrictPreimage O =
      eu'.inv ≫ (comapOfPair hS₁ hSK (Pair.quotientHom S₁ K)).hom ≫ ev.hom :=
    (Iso.eq_inv_comp eu').mpr (comm_restrictPreimage_of_square hKv O
      (IsOpenImmersion.isoOfRangeEq_hom_comp _ _ hrv)
      (IsOpenImmersion.isoOfRangeEq_hom_comp _ _ hru')).symm
  refine ⟨O, hzO, ev.inv ≫ gloc.hom, ?_, ?_⟩
  · rw [Category.assoc, ← ObjectProperty.FullSubcategory.comp_hom, hgloc_f,
      ObjectProperty.FullSubcategory.comp_hom, IsOpenImmersion.isoOfRangeEq_inv_comp_assoc]
  · rw [hres_ι, Category.assoc, Category.assoc, Iso.hom_inv_id_assoc,
      ← ObjectProperty.FullSubcategory.comp_hom, hgloc_K,
      ObjectProperty.FullSubcategory.comp_hom, IsOpenImmersion.isoOfRangeEq_inv_comp_assoc]

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
  -- Cover `O₁ ⊓ O₂` by rational opens `ofPair S₁ hS₁` and invoke `eq_of_sqZero_quotient`
  refine PreAdicSpace.hom_ext_of_forall_exists_isOpenImmersion
    (isAdic_of_isOpenImmersion Z.property pZ).isSheafy fun p ↦ ?_
  obtain ⟨O_z, hzO, hOW, A₁, _, _, _, _, _, _, _, S₁, hS₁, K, hSK, _, _, hK_pow,
    v, u', hv, hv_range, _, hu'_range, hKv⟩ :=
    exists_ofPair_quotient_rational_square R hR I hRI (O₁ ⊓ O₂)
      (by rw [← SetLike.mem_coe, ← hrP]; exact ⟨p, rfl⟩)
  have hvP_sub : Set.range v.hom.base ⊆ Set.range pZ.base := by rw [hv_range, hrP]; exact hOW
  let vP := IsOpenImmersion.lift pZ v.hom hvP_sub
  obtain ⟨q, hq⟩ : pZ.base p ∈ Set.range v.hom.base := hv_range.symm ▸ hzO
  have hp_mem : p ∈ Set.range vP.base := ⟨q,
    (inferInstance : PreAdicSpace.IsOpenImmersion pZ).base_open.injective
      ((congrArg (fun m ↦ m.base q) (IsOpenImmersion.lift_fac pZ v.hom hvP_sub)).trans hq)⟩
  let πK := comapOfPair hS₁ hSK (Pair.quotientHom S₁ K)
  have hπK_lift {O : Opens Z.obj} (hWO : O₁ ⊓ O₂ ≤ O)
      {vO : (ofPair S₁ hS₁).obj ⟶ Z.obj.restrict O.isOpenEmbedding}
      (hvO : vO ≫ Z.obj.ofRestrict O.isOpenEmbedding = v.hom)
      {gO : Z.obj.restrict O.isOpenEmbedding ⟶ Y.obj}
      (hgO_ι : ι.hom.restrictPreimage O ≫ gO =
        Z₀.obj.ofRestrict ((Opens.map ι.hom.base).obj O).isOpenEmbedding ≫ g₀.hom) :
      πK.hom ≫ vO ≫ gO = u'.hom ≫ g₀.hom := by
    let u'O := IsOpenImmersion.lift
      (Z₀.obj.ofRestrict ((Opens.map ι.hom.base).obj O).isOpenEmbedding) u'.hom
      (Set.range_subset_iff.mpr fun r ↦ Set.mem_range.mpr
        ⟨⟨u'.hom.base r, hWO (hOW (Set.mem_preimage.mp (by rw [← hu'_range]; exact ⟨r, rfl⟩)))⟩,
          rfl⟩)
    have hcomm : πK.hom ≫ vO = u'O ≫ ι.hom.restrictPreimage O :=
      comm_restrictPreimage_of_square hKv O hvO (IsOpenImmersion.lift_fac _ _ _)
    rw [← Category.assoc, hcomm, Category.assoc, hgO_ι, IsOpenImmersion.lift_fac_assoc]
  have hv₁ : (vP ≫ pullback.fst _ _) ≫ Z.obj.ofRestrict O₁.isOpenEmbedding = v.hom := by
    rw [Category.assoc]; exact IsOpenImmersion.lift_fac pZ v.hom hvP_sub
  have hv₂ : (vP ≫ pullback.snd _ _) ≫ Z.obj.ofRestrict O₂.isOpenEmbedding = v.hom := by
    rw [Category.assoc, ← pullback.condition]; exact IsOpenImmersion.lift_fac pZ v.hom hvP_sub
  have hm_eq : (ObjectProperty.homMk ((vP ≫ pullback.fst _ _) ≫ g₁) : ofPair S₁ hS₁ ⟶ Y) =
      ObjectProperty.homMk ((vP ≫ pullback.snd _ _) ≫ g₂) :=
    hf.eq_of_sqZero_quotient S₁ hS₁ K (hK_pow hI) hSK
      (InducedCategory.Hom.ext (by
        simp only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom,
          Category.assoc, hg₁_f, hg₂_f, Z, reassoc_of% hv₁, reassoc_of% hv₂]))
      (InducedCategory.Hom.ext (by
        simp only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom]
        exact (hπK_lift inf_le_left hv₁ hg₁_ι).trans (hπK_lift inf_le_right hv₂ hg₂_ι).symm))
  refine ⟨(ofPair S₁ hS₁).obj, vP, inferInstance, hp_mem, ?_⟩
  simpa only [ObjectProperty.homMk_hom, Category.assoc] using congrArg InducedCategory.Hom.hom hm_eq

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
    rw [← Category.assoc, ← Hom.restrictPreimage_ofRestrict, Category.assoc,
      PreAdicSpace.ofRestrict_glueMorphisms, hgO_ι]
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
