/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Morphisms.FinitePresentation.Basic

import TauCeti.RingTheory.Huber.LocalizationTopology.Discrete
import TauCeti.RingTheory.Huber.LocalizationTopology.Noetherian
import TauCeti.RingTheory.Huber.NoetherianType.TopologicallyFiniteType
import TauCeti.RingTheory.Huber.TopologicallyFiniteType.Cancel

/-!
# Cancellation and open restriction for morphisms locally of finite presentation

Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of adic spaces such that `f ≫ g` is locally of finite
presentation and `g` is locally of finite type. Then `f` is locally of finite presentation (Huber
1996, Proposition 1.6.7(iii); Stacks Project, Lemma 02FV).

Around a point `x : X.obj`, one chooses a complete Hausdorff chart `χ : A → C₀` for `f ≫ g`,
refines `g` over a rational open `R(TA / sA)` of `Spa(A, A⁺)` via
`LocallyOfFiniteType.exists_openImmersion_over_rationalLocalization` to obtain a finite-type pair
morphism `ψ : A₁ → B`, base-changes `χ` along `R(TA / sA)` to `χ₁ : A₁ → C₁`, and shrinks `Spa(C₁)`
further to a rational open `Spa(C₂)` mapping into `Spa(B)`. On global sections, `φ ∘ ψ = ι ∘ χ₁`.
Pair-level right-cancellation (`TauCeti.Huber.Pair.Hom.IsTopologicallyFiniteType.of_comp`) gives
`φ.IsTopologicallyFiniteType`, while if `B` is discrete the standing-class dichotomy on `ψ : A₁ → B`
either makes `A₁` discrete (so `ψ.toRingHom.FiniteType` cancels via
`RingHom.FinitePresentation.of_comp_finiteType`) or makes `B` noetherian (so finite type upgrades
via `RingHom.FinitePresentation.of_finiteType`).

Restriction of morphisms locally of finite presentation along commuting squares of open immersions
follows immediately from right-cancellation and composition, without requiring any explicit
standing-class hypothesis on the spaces involved.

## Main results

* `TauCeti.AdicSpace.LocallyOfFinitePresentation.of_comp`: if `f ≫ g` is locally of finite
  presentation and `g` is locally of finite type, then `f` is locally of finite presentation.
* `TauCeti.AdicSpace.LocallyOfFinitePresentation.restrict`: restriction of morphisms locally of
  finite presentation along open immersions of source and target.

## References

* R. Huber, *Étale cohomology of rigid analytic varieties and adic spaces*, Aspects of
  Mathematics E30 (1996), Proposition 1.6.7(iii).
* [The Stacks Project, *Morphisms, Lemma 02FV (29.21.11)*][stacks-project].
-/

public section

open CategoryTheory TopologicalSpace Topology

namespace TauCeti.AdicSpace

open Huber Huber.PairOfDefinition PreAdicSpace ValuationSpectrum

universe u

variable {X Y Z : AdicSpace.{u}}

/-- **Right-cancellation of morphisms locally of finite presentation along morphisms locally of
finite type** (Huber 1996, Proposition 1.6.7(iii); Stacks 02FV): if `f ≫ g` is locally of finite
presentation and `g` is locally of finite type, then `f` is locally of finite presentation. -/
theorem LocallyOfFinitePresentation.of_comp {f : X ⟶ Y} {g : Y ⟶ Z}
    (hfg : LocallyOfFinitePresentation (f ≫ g)) (hg : LocallyOfFiniteType g) :
    LocallyOfFinitePresentation f := by
  classical
  rw [locallyOfFinitePresentation_iff]
  intro x
  -- 1. Choose a complete chart `(kX₀ : Spa(C₀) ⟶ X, kZ : Spa(A) ⟶ Z, χ : A → C₀)` for `f ≫ g`.
  obtain ⟨A, _, _, _, _, _, _, _, _, S, P, hP, hsheafA, C₀, _, _, _, _, _, _, _, U₀, PC₀, hPC₀,
    hsheafC₀, kX₀, hkX₀, kZ, hkZ, χ, hχ, hχ_fp, c₀₀, hc₀₀, hsq_fg⟩ :=
    hfg.exists_openImmersion_chart x
  -- 2. Refine `g : Y ⟶ Z` over `kZ : Spa(A) ⟶ Z` around `a₀ := Spa(χ)(c₀₀)`.
  let a₀ := (presentationLimitPreAdicSpacePairComap P PC₀ hP hPC₀ hsheafC₀ χ).base c₀₀
  have ha₀ : kZ.base a₀ = g.hom.base (f.hom.base x) := by
    have h1 := congrArg (fun m ↦ m.base c₀₀) hsq_fg
    simpa [a₀, hc₀₀] using h1
  obtain ⟨TA, sA, hTA, ha₀R, B, _, _, _, _, _, _, _, T, PB, hPB, hsheafB, kY, hkY, ψ, hψ, b₀,
    hb₀, hsq_g⟩ := hg.exists_openImmersion_over_rationalLocalization P hP hsheafA kZ
      (f.hom.base x) ha₀
  -- 3. Base-change `χ : S → U₀` along `R(TA / sA)`.
  let LA := Localization.Away sA
  have hdenA := P.hasDenominatorPower_of_isOpen_span TA sA LA hTA
  let _ := P.locUniformSpace TA sA LA hdenA
  have _ := P.isUniformAddGroup_locUniformSpace TA sA LA hdenA
  have _ := P.isTopologicalRing_locUniformSpace TA sA LA hdenA
  have _ := P.isHuberRing_completion_locTopology TA sA LA hdenA
  let S₁ := P.rationalLocalizationPair S hP TA sA LA hdenA
  let P₁ := P.completionLocalization TA sA LA hdenA
  have hP₁ : P₁.ringOfDefinition ≤ S₁.plus := by
    rw [rationalLocalizationPair_plus]
    exact P.completionLocalization_ringOfDefinition_le_completedPlusSubring S.plus hP TA sA LA hdenA
  have hsheafA₁ := isSheaf_presentationLimitPresheaf_rationalLocalizationPair P S hP TA sA LA
    hdenA hTA hsheafA
  let TC₀ : Finset C₀ := TA.image χ.toRingHom
  let sC₀ : C₀ := χ.toRingHom sA
  have hTC₀ : IsOpen (Ideal.span (TC₀ : Set C₀) : Set C₀) := by
    rw [Finset.coe_image, ← Ideal.map_span]
    exact hχ.isTopologicallyFiniteType_toRingHom.isOpen_map hTA
  let LC₀ := Localization.Away sC₀
  have hdenC₀ := PC₀.hasDenominatorPower_of_isOpen_span TC₀ sC₀ LC₀ hTC₀
  let _ := PC₀.locUniformSpace TC₀ sC₀ LC₀ hdenC₀
  have _ := PC₀.isUniformAddGroup_locUniformSpace TC₀ sC₀ LC₀ hdenC₀
  have _ := PC₀.isTopologicalRing_locUniformSpace TC₀ sC₀ LC₀ hdenC₀
  have _ := PC₀.isHuberRing_completion_locTopology TC₀ sC₀ LC₀ hdenC₀
  let U₁ := PC₀.rationalLocalizationPair U₀ hPC₀ TC₀ sC₀ LC₀ hdenC₀
  let PC₁ := PC₀.completionLocalization TC₀ sC₀ LC₀ hdenC₀
  have hPC₁ : PC₁.ringOfDefinition ≤ U₁.plus := by
    rw [rationalLocalizationPair_plus]
    exact PC₀.completionLocalization_ringOfDefinition_le_completedPlusSubring U₀.plus hPC₀ TC₀ sC₀
      LC₀ hdenC₀
  have hsheafC₁ := isSheaf_presentationLimitPresheaf_rationalLocalizationPair PC₀ U₀ hPC₀ TC₀ sC₀
    LC₀ hdenC₀ hTC₀ hsheafC₀
  let χ₁ := P.completionLocPairMap S hP TA sA LA hdenA PC₀ U₀ hPC₀ χ TC₀ sC₀ LC₀ hdenC₀ rfl
    (fun _ ht ↦ Finset.mem_image_of_mem _ ht)
  have hTA_ins : IsOpen (Ideal.span (insert sA (TA : Set A)) : Set A) :=
    Submodule.isOpen_mono (Ideal.span_mono (Set.subset_insert _ _)) hTA
  have hTC₀_ins : IsOpen (Ideal.span (insert sC₀ (TC₀ : Set C₀)) : Set C₀) :=
    Submodule.isOpen_mono (Ideal.span_mono (Set.subset_insert _ _)) hTC₀
  have hStdA₁ : IsHuberStandard (UniformSpace.Completion LA) :=
    isHuberStandard_completion_locTopology_of_isHuberStandard P hTA_ins LA hdenA
  have hχ₁ : χ₁.IsTopologicallyFiniteType :=
    P.isTopologicallyFiniteType_completionLocPairMap S hP TA sA LA hdenA PC₀ U₀ hPC₀ χ TC₀ sC₀
      LC₀ hdenC₀ rfl (fun _ ht ↦ Finset.mem_image_of_mem _ ht) hχ hTC₀_ins
  have hχ₁_fp :
      DiscreteTopology (UniformSpace.Completion LA) → χ₁.toRingHom.FinitePresentation := by
    rw [show χ₁.toRingHom = _ from toRingHom_completionLocPairMap ..]
    exact P.finitePresentation_completionLocMap_of_discreteTopology TA sA hTA_ins LA hdenA PC₀
      hχ.isTopologicallyFiniteType_toRingHom hχ_fp TC₀ sC₀ LC₀ hdenC₀ rfl
      (fun _ ht ↦ Finset.mem_image_of_mem _ ht) hTC₀_ins
  have hStdB : IsHuberStandard B := by
    have := hStdA₁
    exact .of_isTopologicallyFiniteType hψ.isTopologicallyFiniteType_toRingHom
  let ιA := presentationLimitPreAdicSpacePairComap P P₁ hP hP₁ hsheafA₁
    (P.toCompletionLocHom S hP TA sA LA hdenA)
  have hιA_imm : PreAdicSpace.IsOpenImmersion ιA := by
    rw [show ιA = _ from presentationLimitPreAdicSpacePairComap_def ..]
    exact isOpenImmersion_presentationLimitPreAdicSpaceComap_toCompletionLocHom P hP TA sA LA hdenA
      hTA hsheafA₁
  let ιC₀ := presentationLimitPreAdicSpacePairComap PC₀ PC₁ hPC₀ hPC₁ hsheafC₁
    (PC₀.toCompletionLocHom U₀ hPC₀ TC₀ sC₀ LC₀ hdenC₀)
  have hιC₀_imm : PreAdicSpace.IsOpenImmersion ιC₀ := by
    rw [show ιC₀ = _ from presentationLimitPreAdicSpacePairComap_def ..]
    exact isOpenImmersion_presentationLimitPreAdicSpaceComap_toCompletionLocHom PC₀ hPC₀ TC₀ sC₀
      LC₀ hdenC₀ hTC₀ hsheafC₁
  have hιC₀_range : Set.range ιC₀.base = (spaBasicOpen U₀.plus TC₀ sC₀ : Set (spa U₀.plus)) := by
    rw [show ιC₀ = _ from presentationLimitPreAdicSpacePairComap_def ..]
    exact range_presentationLimitPreAdicSpaceComap_toCompletionLocHom_base PC₀ hPC₀ TC₀ sC₀ LC₀
      hdenC₀ hsheafC₁
  let kX₁ := ιC₀ ≫ kX₀
  let kZ₁ := ιA ≫ kZ
  have hkX₁_imm : PreAdicSpace.IsOpenImmersion kX₁ := PreAdicSpace.IsOpenImmersion.comp ιC₀ kX₀
  have hkZ₁_imm : PreAdicSpace.IsOpenImmersion kZ₁ := PreAdicSpace.IsOpenImmersion.comp ιA kZ
  have hc₀₀R : (c₀₀ : spa U₀.plus) ∈ (spaBasicOpen U₀.plus TC₀ sC₀ : Set (spa U₀.plus)) := by
    have hmem : (χ.spaComap c₀₀).1 ∈ rationalSubset S.plus TA sA := by
      have ha' := mem_spaBasicOpen.mp ha₀R
      dsimp only [a₀] at ha'
      rwa [presentationLimitPreAdicSpacePairComap_base_apply P PC₀ hP hPC₀ hsheafC₀ χ c₀₀] at ha'
    have hpre := Set.ext_iff.mp (χ.spaComap_preimage_rationalSubset TA sA) c₀₀
    exact mem_spaBasicOpen.mpr (hpre.mp hmem)
  obtain ⟨c₁₀, hc₁₀⟩ : (c₀₀ : spa U₀.plus) ∈ Set.range ιC₀.base := hιC₀_range.symm ▸ hc₀₀R
  have hc₁₀_x : kX₁.base c₁₀ = x := by
    simpa [kX₁, ← hc₀₀] using congrArg kX₀.base hc₁₀
  have hsq_fg₁ :
      presentationLimitPreAdicSpacePairComap P₁ PC₁ hP₁ hPC₁ hsheafC₁ χ₁ ≫ kZ₁ =
        kX₁ ≫ (f ≫ g).hom := by
    have hcomm := presentationLimitPreAdicSpaceComap_completionLocPairMap_comp P PC₀ hP hPC₀ χ
      hsheafC₀ TA sA LA hdenA LC₀ hdenC₀ hsheafA₁ hsheafC₁
    dsimp only [kZ₁, kX₁, ιA, ιC₀, χ₁, TC₀, sC₀]
    rw [presentationLimitPreAdicSpacePairComap_def, presentationLimitPreAdicSpacePairComap_def,
      presentationLimitPreAdicSpacePairComap_def, ← Category.assoc, hcomm, Category.assoc]
    rw [← presentationLimitPreAdicSpacePairComap_def P PC₀ hP hPC₀ hsheafC₀ χ, hsq_fg,
      Category.assoc]
  -- 4. Shrink `Spa(C₁)` around `c₁₀` to `R(TC₁ / sC₁)` mapping into `Set.range kY`.
  let OC₁ : Opens (presentationLimitPreAdicSpace PC₁ U₁.plus
      U₁.isRingOfIntegralElements.isPowerBounded_of_mem hPC₁) :=
    ⟨(kX₁ ≫ f.hom).base ⁻¹' Set.range kY.base,
      kY.isOpenEmbedding.isOpen_range.preimage (kX₁ ≫ f.hom).base.hom.2⟩
  have hc₁₀O : c₁₀ ∈ OC₁ := ⟨b₀, by simpa [hc₁₀_x] using hb₀⟩
  obtain ⟨RC₁, hRC₁, hc₁₀R, hRC₁O⟩ :=
    Opens.isBasis_iff_nbhd.mp (isBasis_spaRationalOpens U₁.plus) hc₁₀O
  obtain ⟨TC₁, sC₁, hTC₁, rfl⟩ := mem_spaRationalOpens_iff_exists_spaBasicOpen.mp hRC₁
  let LC₁ := Localization.Away sC₁
  have hdenC₁ := PC₁.hasDenominatorPower_of_isOpen_span TC₁ sC₁ LC₁ hTC₁
  let _ := PC₁.locUniformSpace TC₁ sC₁ LC₁ hdenC₁
  have _ := PC₁.isUniformAddGroup_locUniformSpace TC₁ sC₁ LC₁ hdenC₁
  have _ := PC₁.isTopologicalRing_locUniformSpace TC₁ sC₁ LC₁ hdenC₁
  have _ := PC₁.isHuberRing_completion_locTopology TC₁ sC₁ LC₁ hdenC₁
  let U₂ := PC₁.rationalLocalizationPair U₁ hPC₁ TC₁ sC₁ LC₁ hdenC₁
  let PC₂ := PC₁.completionLocalization TC₁ sC₁ LC₁ hdenC₁
  have hPC₂ : PC₂.ringOfDefinition ≤ U₂.plus := by
    rw [rationalLocalizationPair_plus]
    exact PC₁.completionLocalization_ringOfDefinition_le_completedPlusSubring U₁.plus hPC₁ TC₁ sC₁
      LC₁ hdenC₁
  have hsheafC₂ := isSheaf_presentationLimitPresheaf_rationalLocalizationPair PC₁ U₁ hPC₁ TC₁ sC₁
    LC₁ hdenC₁ hTC₁ hsheafC₁
  let ιC₁ := presentationLimitPreAdicSpacePairComap PC₁ PC₂ hPC₁ hPC₂ hsheafC₂
    (PC₁.toCompletionLocHom U₁ hPC₁ TC₁ sC₁ LC₁ hdenC₁)
  have hιC₁_imm : PreAdicSpace.IsOpenImmersion ιC₁ := by
    rw [show ιC₁ = _ from presentationLimitPreAdicSpacePairComap_def ..]
    exact isOpenImmersion_presentationLimitPreAdicSpaceComap_toCompletionLocHom PC₁ hPC₁ TC₁ sC₁
      LC₁ hdenC₁ hTC₁ hsheafC₂
  have hιC₁_range : Set.range ιC₁.base = (spaBasicOpen U₁.plus TC₁ sC₁ : Set (spa U₁.plus)) := by
    rw [show ιC₁ = _ from presentationLimitPreAdicSpacePairComap_def ..]
    exact range_presentationLimitPreAdicSpaceComap_toCompletionLocHom_base PC₁ hPC₁ TC₁ sC₁ LC₁
      hdenC₁ hsheafC₂
  let kX₂ := ιC₁ ≫ kX₁
  have hkX₂_imm : PreAdicSpace.IsOpenImmersion kX₂ := PreAdicSpace.IsOpenImmersion.comp ιC₁ kX₁
  obtain ⟨c₂, hc₂⟩ : (c₁₀ : spa U₁.plus) ∈ Set.range ιC₁.base :=
    hιC₁_range.symm ▸
      (hc₁₀R : (c₁₀ : spa U₁.plus) ∈ (spaBasicOpen U₁.plus TC₁ sC₁ : Set (spa U₁.plus)))
  have hrangeC₂ : Set.range (kX₂ ≫ f.hom).base ⊆ Set.range kY.base := by
    rintro _ ⟨z, rfl⟩
    have hz : (ιC₁.base z : spa U₁.plus) ∈ (spaBasicOpen U₁.plus TC₁ sC₁ : Set (spa U₁.plus)) :=
      hιC₁_range ▸ ⟨z, rfl⟩
    exact hRC₁O hz
  let q := PreAdicSpace.IsOpenImmersion.lift kY (kX₂ ≫ f.hom) hrangeC₂
  have hq_fac : q ≫ kY = kX₂ ≫ f.hom :=
    PreAdicSpace.IsOpenImmersion.lift_fac kY (kX₂ ≫ f.hom) hrangeC₂
  let φ := presentationLimitHomPairHom PB PC₂ T U₂ hPB hPC₂ q
  have hqψ : q ≫ presentationLimitPreAdicSpacePairComap P₁ PB hP₁ hPB hsheafB ψ =
      ιC₁ ≫ presentationLimitPreAdicSpacePairComap P₁ PC₁ hP₁ hPC₁ hsheafC₁ χ₁ := by
    rw [← cancel_mono kZ₁, Category.assoc]
    have hg' : presentationLimitPreAdicSpacePairComap P₁ PB hP₁ hPB hsheafB ψ ≫ kZ₁ =
        kY ≫ g.hom := hsq_g
    rw [hg', ← Category.assoc q, hq_fac]
    dsimp only [kX₂]
    rw [Category.assoc, Category.assoc,
      ← ObjectProperty.FullSubcategory.comp_hom (f := f) (g := g), ← hsq_fg₁, Category.assoc]
  have hφψ : φ.comp ψ = (PC₁.toCompletionLocHom U₁ hPC₁ TC₁ sC₁ LC₁ hdenC₁).comp χ₁ := by
    have h := congrArg (presentationLimitHomPairHom P₁ PC₂ S₁ U₂ hP₁ hPC₂) hqψ
    rwa [presentationLimitHomPairHom_comp P₁ PB PC₂ S₁ T U₂ hP₁ hPB hPC₂,
      presentationLimitHomPairHom_presentationLimitPreAdicSpacePairComap P₁ PB S₁ T hP₁ hPB
        hsheafB,
      ← presentationLimitPreAdicSpacePairComap_comp P₁ PC₁ PC₂ hP₁ hPC₁ hPC₂ hsheafC₁ hsheafC₂,
      presentationLimitHomPairHom_presentationLimitPreAdicSpacePairComap P₁ PC₂ S₁ U₂ hP₁ hPC₂
        hsheafC₂] at h
  have hχ'₁_tft :
      ((PC₁.toCompletionLocHom U₁ hPC₁ TC₁ sC₁ LC₁ hdenC₁).comp χ₁).IsTopologicallyFiniteType :=
    PC₁.isTopologicallyFiniteType_toCompletionLocHom_comp U₁ hPC₁ TC₁ sC₁ LC₁ hdenC₁ χ₁ hχ₁
      (Submodule.isOpen_mono (Ideal.span_mono (Set.subset_insert _ _)) hTC₁)
  have hφ_tft : φ.IsTopologicallyFiniteType :=
    Pair.Hom.IsTopologicallyFiniteType.of_comp (hφψ ▸ hχ'₁_tft)
  have hφ_fp : DiscreteTopology B → φ.toRingHom.FinitePresentation := by
    intro hDiscB
    have : IsHuberStandard (UniformSpace.Completion LA) := hStdA₁
    rcases IsHuberStandard.discreteTopology_or_isNoetherianRing_of_isTopologicallyFiniteType
        hψ.isTopologicallyFiniteType_toRingHom with hDiscA₁ | hNoethB
    · have : DiscreteTopology (UniformSpace.Completion LC₀) :=
        hχ₁.isTopologicallyFiniteType_toRingHom.discreteTopology
      have hcomp_fp : (φ.toRingHom.comp ψ.toRingHom).FinitePresentation := by
        rw [← Pair.Hom.toRingHom_comp, hφψ, Pair.Hom.toRingHom_comp, toRingHom_toCompletionLocHom]
        exact (PC₁.finitePresentation_toCompletionLoc_of_discreteTopology (TC₁ : Set _) sC₁ LC₁
          hdenC₁).comp (hχ₁_fp hDiscA₁)
      exact RingHom.FinitePresentation.of_comp_finiteType ψ.toRingHom hcomp_fp
        hψ.isTopologicallyFiniteType_toRingHom.finiteType
    · have : DiscreteTopology (UniformSpace.Completion LC₁) :=
        hφ_tft.isTopologicallyFiniteType_toRingHom.discreteTopology
      exact RingHom.FinitePresentation.of_finiteType.mp
        hφ_tft.isTopologicallyFiniteType_toRingHom.finiteType
  refine exists_locallyOfFinitePresentation_chart_of_openImmersion_sq hPB hPC₂ hsheafC₂ kX₂ kY φ
    hφ_tft hφ_fp (b₀ := c₂) ?_ ?_
  · simpa [kX₂, ← hc₁₀_x] using congrArg kX₁.base hc₂
  · rw [presentationLimitPreAdicSpacePairComap_presentationLimitHomPairHom PB PC₂ T U₂ hPB hPC₂
      hsheafC₂]
    exact hq_fac

/-- **Restriction of morphisms locally of finite presentation along open immersions**: if
`g ≫ iV = iU ≫ f` for open immersions `iU : U ⟶ X` and `iV : V ⟶ Y` and `f` is locally of finite
presentation, then `g` is locally of finite presentation. No standing-class assumption on `U`, `V`,
`X`, or `Y` is needed explicitly, as `X.IsLocallyHuberStandard` follows from `hf`. -/
theorem LocallyOfFinitePresentation.restrict {U V : AdicSpace.{u}} {iU : U ⟶ X} {iV : V ⟶ Y}
    {f : X ⟶ Y} {g : U ⟶ V} [PreAdicSpace.IsOpenImmersion iU.hom]
    [PreAdicSpace.IsOpenImmersion iV.hom] (hcomm : g ≫ iV = iU ≫ f)
    (hf : LocallyOfFinitePresentation f) : LocallyOfFinitePresentation g :=
  LocallyOfFinitePresentation.of_comp
    (hcomm ▸ (LocallyOfFinitePresentation.of_isOpenImmersion iU
      hf.isLocallyHuberStandard_source).comp hf)
    (LocallyOfFiniteType.of_isOpenImmersion iV)

end TauCeti.AdicSpace
