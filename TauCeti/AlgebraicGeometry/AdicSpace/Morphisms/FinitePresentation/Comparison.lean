/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Morphisms.AnalyticLocus
public import TauCeti.AlgebraicGeometry.AdicSpace.Morphisms.FinitePresentation.Cancel

import Mathlib.RingTheory.RingHom.FinitePresentation
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.RationalSubset.Discrete
import TauCeti.RingTheory.Huber.LocalizationTopology.Discrete
import TauCeti.RingTheory.Huber.LocalizationTopology.Noetherian
import TauCeti.RingTheory.Huber.NoetherianType.TopologicallyFiniteType

/-!
# Analytic, noetherian, and discrete affinoid comparisons for `LocallyOfFinitePresentation`

Huber's definition of morphisms locally of finite presentation (Huber 1996, Definition 1.2.1(ii))
augments `LocallyOfFiniteType` with two features: charts over Huber's standing class
(`IsHuberStandard`) and algebraic finite presentation (`RingHom.FinitePresentation`) on discrete
target charts. This file establishes how those two features specialize across the main classes of
bases:

* **Analytic and locally noetherian bases:** over an analytic adic space `Y` locally of Huber's
  standing class (equivalently, locally noetherian), every inhabited open affinoid has an analytic
  point and is therefore non-discrete, so `LocallyOfFinitePresentation` and `LocallyOfFiniteType`
  coincide (`locallyOfFinitePresentation_iff_locallyOfFiniteType_of_analyticPoints_eq_univ`). In
  particular, every morphism locally of finite type into a locally noetherian adic space restricts
  to a morphism locally of finite presentation on analytic loci
  (`LocallyOfFiniteType.locallyOfFinitePresentation_analyticLocusMap`).
* **Locally noetherian discrete bases:** when `Y` is locally of Huber's standing class and every
  discrete complete Hausdorff affinoid open of `Y` is noetherian, `LocallyOfFinitePresentation` and
  `LocallyOfFiniteType` again coincide
  (`locallyOfFinitePresentation_iff_locallyOfFiniteType_of_forall_discrete_isNoetherianRing`).
* **Affinoid and strongly noetherian Tate bases:** a morphism of Huber pairs `φ : (A, A⁺) → (B, B⁺)`
  satisfying Huber's pair-level condition induces a morphism locally of finite presentation on
  `Spa` (`locallyOfFinitePresentation_comapOfPair`), and over a strongly noetherian Tate ring `A`
  neither completeness nor Hausdorffness of `A` is needed
  (`locallyOfFinitePresentation_comapOfPair_of_isTateRing`).
* **Discrete affinoids:** between discrete commutative rings `A` and `B` with trivial plus rings
  `Pair.discrete A = (A, A)` and `Pair.discrete B = (B, B)`, `Spa(B, B) ⟶ Spa(A, A)` is locally of
  finite presentation if and only if `φ.toRingHom : A →+* B` is algebraically of finite presentation
  (`locallyOfFinitePresentation_comapOfPair_discrete_iff`).

## Main results

* `locallyOfFinitePresentation_iff_locallyOfFiniteType_of_analyticPoints_eq_univ`,
  `LocallyOfFiniteType.locallyOfFinitePresentation_analyticLocusMap`: equivalence with
  `LocallyOfFiniteType` over analytic targets locally of Huber's standing class, and upgrade on
  analytic loci.
* `locallyOfFinitePresentation_iff_locallyOfFiniteType_of_forall_discrete_isNoetherianRing`:
  equivalence with `LocallyOfFiniteType` when all discrete affinoid opens of the target are
  noetherian.
* `locallyOfFinitePresentation_comapOfPair`,
  `locallyOfFinitePresentation_comapOfPair_of_isTateRing`: affinoid and strongly noetherian Tate
  affinoid criteria.
* `LocallyOfFinitePresentation.finitePresentation_of_discreteTopology`,
  `locallyOfFinitePresentation_comapOfPair_discrete_iff`: discrete affinoid characterization via
  `RingHom.FinitePresentation`.

## References

* R. Huber, *Étale cohomology of rigid analytic varieties and adic spaces*, Aspects of
  Mathematics E30 (1996), (1.1.1) and Definition 1.2.1(ii).
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Remark 6.37 and Definition 8.48.
-/

public section

open CategoryTheory TopologicalSpace Topology

namespace TauCeti.AdicSpace

open Huber Huber.PairOfDefinition PreAdicSpace ValuationSpectrum

universe u

variable {X Y : AdicSpace.{u}}

/-! ### Analytic and noetherian comparisons -/

section AnalyticAndNoetherian

/-- **Over an analytic target locally of Huber's standing class, `LocallyOfFinitePresentation` and
`LocallyOfFiniteType` coincide** (Huber 1996, §1.2): an inhabited discrete affinoid open has no
analytic points, so the discrete finite-presentation side-condition is vacuous on every refined
chart covering a point of the source. -/
theorem locallyOfFinitePresentation_iff_locallyOfFiniteType_of_analyticPoints_eq_univ
    {f : X ⟶ Y} (hY : Y.IsLocallyHuberStandard) (ha : Y.obj.analyticPoints = Set.univ) :
    LocallyOfFinitePresentation f ↔ LocallyOfFiniteType f := by
  refine ⟨LocallyOfFinitePresentation.locallyOfFiniteType,
    fun hf ↦ (locallyOfFinitePresentation_iff _).mpr fun x ↦ ?_⟩
  obtain ⟨V, hV, hfxV⟩ := isLocallyHuberStandard_iff.mp hY (f.hom.base x)
  obtain ⟨A, _, _, _, _, _, _, _, _, S, P, hP, ⟨eV⟩⟩ :=
    (isHuberStandardAffinoid_iff _).mp ((mem_propOpens_iff _).mp hV)
  have hsheafA : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa S.plus))
      (presentationLimitPresheaf P S.plus) :=
    ObjectProperty.prop_of_iso isSheafy eV (isSheafy_restrict _ Y.property.isSheafy)
  let kY := eV.inv ≫ Y.obj.ofRestrict V.isOpenEmbedding
  have hkY : PreAdicSpace.IsOpenImmersion kY := PreAdicSpace.IsOpenImmersion.comp _ _
  let a₀ := eV.hom.base ⟨f.hom.base x, hfxV⟩
  have ha₀ : kY.base a₀ = f.hom.base x := by
    have hb : (eV.hom ≫ eV.inv).base ⟨f.hom.base x, hfxV⟩ = ⟨f.hom.base x, hfxV⟩ := by
      simp
      rfl
    exact congrArg (Y.obj.ofRestrict V.isOpenEmbedding).base hb
  obtain ⟨TA, sA, hTA, -, C, _, _, _, _, _, _, _, U, PC, hPC, hsheafC, kX, hkX, β, hβ, c₀, hc₀,
    hsq⟩ := hf.exists_openImmersion_over_rationalLocalization P hP hsheafA kY x ha₀
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
  have hStdA₁ : IsHuberStandard (UniformSpace.Completion LA) :=
    isHuberStandard_completion_locTopology_of_isHuberStandard P
      (Submodule.isOpen_mono (Ideal.span_mono (Set.subset_insert _ _)) hTA) LA hdenA
  let ιA := presentationLimitPreAdicSpacePairComap P P₁ hP hP₁ hsheafA₁
    (P.toCompletionLocHom S hP TA sA LA hdenA)
  have hιA_imm : PreAdicSpace.IsOpenImmersion ιA := by
    rw [show ιA = _ from presentationLimitPreAdicSpacePairComap_def ..]
    exact isOpenImmersion_presentationLimitPreAdicSpaceComap_toCompletionLocHom P hP TA sA LA hdenA
      hTA hsheafA₁
  let kY₁ := ιA ≫ kY
  have hkY₁_imm : PreAdicSpace.IsOpenImmersion kY₁ := PreAdicSpace.IsOpenImmersion.comp ιA kY
  have hβ_fp : DiscreteTopology (UniformSpace.Completion LA) → β.toRingHom.FinitePresentation := by
    intro hDiscA₁
    let a₁ := (presentationLimitPreAdicSpacePairComap P₁ PC hP₁ hPC hsheafC β).base c₀
    have ha₁_an : a₁ ∈ (presentationLimitPreAdicSpace P₁ S₁.plus
        S₁.isRingOfIntegralElements.isPowerBounded_of_mem hP₁).analyticPoints := by
      rw [← preimage_analyticPoints_of_isOpenImmersion kY₁, ha]
      exact Set.mem_univ _
    rw [analyticPoints_presentationLimitPreAdicSpace] at ha₁_an
    exact False.elim
      ((isAnalyticPoint_def _).mp ((mem_spaAnalytic_iff S₁.plus _).mp ha₁_an).2 (isOpen_discrete _))
  exact exists_locallyOfFinitePresentation_chart_of_openImmersion_sq hP₁ hPC hsheafC kX kY₁ β hβ
    hβ_fp hc₀ hsq

namespace IsLocallyNoetherian

/-- **Over an analytic locally noetherian target, `LocallyOfFinitePresentation` and
`LocallyOfFiniteType` coincide.** -/
theorem locallyOfFinitePresentation_iff_locallyOfFiniteType_of_analyticPoints_eq_univ
    {f : X ⟶ Y} (hY : Y.IsLocallyNoetherian) (ha : Y.obj.analyticPoints = Set.univ) :
    LocallyOfFinitePresentation f ↔ LocallyOfFiniteType f :=
  AdicSpace.locallyOfFinitePresentation_iff_locallyOfFiniteType_of_analyticPoints_eq_univ
    (hY.isLocallyHuberStandard_of_analyticPoints_eq_univ ha) ha

end IsLocallyNoetherian

/-- **Every morphism locally of finite type into a locally noetherian adic space restricts to a
morphism locally of finite presentation on analytic loci.** -/
theorem LocallyOfFiniteType.locallyOfFinitePresentation_analyticLocusMap {f : X ⟶ Y}
    (hf : LocallyOfFiniteType f) (hY : Y.IsLocallyNoetherian) :
    LocallyOfFinitePresentation hf.isAdic.analyticLocusMap := by
  have hft : LocallyOfFiniteType hf.isAdic.analyticLocusMap :=
    hf.restrict hf.isAdic.analyticLocusMap_ι
  have haY : Y.analyticLocus.obj.analyticPoints = Set.univ := by
    rw [analyticLocus_obj, analyticPoints_analyticLocus]
  exact (locallyOfFinitePresentation_iff_locallyOfFiniteType_of_analyticPoints_eq_univ
    hY.isLocallyHuberStandard_analyticLocus haY).mpr hft

/-- **Over a target locally of Huber's standing class whose discrete affinoid opens are noetherian,
`LocallyOfFinitePresentation` and `LocallyOfFiniteType` coincide.** -/
theorem locallyOfFinitePresentation_iff_locallyOfFiniteType_of_forall_discrete_isNoetherianRing
    {f : X ⟶ Y} (hY : Y.IsLocallyHuberStandard)
    (hnoeth : ∀ (A : Type u) [CommRing A] [UniformSpace A] [IsUniformAddGroup A]
      [IsTopologicalRing A] [CompleteSpace A] [T2Space A] [IsHuberRing A] [DiscreteTopology A]
      (S : Pair A) (P : PairOfDefinition A) (hP : P.ringOfDefinition ≤ S.plus)
      (k : presentationLimitPreAdicSpace P S.plus
        S.isRingOfIntegralElements.isPowerBounded_of_mem hP ⟶ Y.obj),
      PreAdicSpace.IsOpenImmersion k → IsNoetherianRing A) :
    LocallyOfFinitePresentation f ↔ LocallyOfFiniteType f := by
  refine ⟨LocallyOfFinitePresentation.locallyOfFiniteType,
    fun hf ↦ (locallyOfFinitePresentation_iff _).mpr fun x ↦ ?_⟩
  obtain ⟨V, hV, hfxV⟩ := isLocallyHuberStandard_iff.mp hY (f.hom.base x)
  obtain ⟨A, _, _, _, _, _, _, _, _, S, P, hP, ⟨eV⟩⟩ :=
    (isHuberStandardAffinoid_iff _).mp ((mem_propOpens_iff _).mp hV)
  have hsheafA : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa S.plus))
      (presentationLimitPresheaf P S.plus) :=
    ObjectProperty.prop_of_iso isSheafy eV (isSheafy_restrict _ Y.property.isSheafy)
  let kY := eV.inv ≫ Y.obj.ofRestrict V.isOpenEmbedding
  have hkY : PreAdicSpace.IsOpenImmersion kY := PreAdicSpace.IsOpenImmersion.comp _ _
  let a₀ := eV.hom.base ⟨f.hom.base x, hfxV⟩
  have ha₀ : kY.base a₀ = f.hom.base x := by
    have hb : (eV.hom ≫ eV.inv).base ⟨f.hom.base x, hfxV⟩ = ⟨f.hom.base x, hfxV⟩ := by
      simp
      rfl
    exact congrArg (Y.obj.ofRestrict V.isOpenEmbedding).base hb
  obtain ⟨TA, sA, hTA, -, C, _, _, _, _, _, _, _, U, PC, hPC, hsheafC, kX, hkX, β, hβ, c₀, hc₀,
    hsq⟩ := hf.exists_openImmersion_over_rationalLocalization P hP hsheafA kY x ha₀
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
  have hStdA₁ : IsHuberStandard (UniformSpace.Completion LA) :=
    isHuberStandard_completion_locTopology_of_isHuberStandard P
      (Submodule.isOpen_mono (Ideal.span_mono (Set.subset_insert _ _)) hTA) LA hdenA
  let ιA := presentationLimitPreAdicSpacePairComap P P₁ hP hP₁ hsheafA₁
    (P.toCompletionLocHom S hP TA sA LA hdenA)
  have hιA_imm : PreAdicSpace.IsOpenImmersion ιA := by
    rw [show ιA = _ from presentationLimitPreAdicSpacePairComap_def ..]
    exact isOpenImmersion_presentationLimitPreAdicSpaceComap_toCompletionLocHom P hP TA sA LA hdenA
      hTA hsheafA₁
  let kY₁ := ιA ≫ kY
  have hkY₁_imm : PreAdicSpace.IsOpenImmersion kY₁ := PreAdicSpace.IsOpenImmersion.comp ιA kY
  have hβ_fp : DiscreteTopology (UniformSpace.Completion LA) → β.toRingHom.FinitePresentation := by
    intro hDiscA₁
    have : IsNoetherianRing (UniformSpace.Completion LA) :=
      hnoeth (UniformSpace.Completion LA) S₁ P₁ hP₁ kY₁ hkY₁_imm
    have : DiscreteTopology C := hβ.isTopologicallyFiniteType_toRingHom.discreteTopology
    exact RingHom.FinitePresentation.of_finiteType.mp
      hβ.isTopologicallyFiniteType_toRingHom.finiteType
  exact exists_locallyOfFinitePresentation_chart_of_openImmersion_sq hP₁ hPC hsheafC kX kY₁ β hβ
    hβ_fp hc₀ hsq

end AnalyticAndNoetherian

/-! ### Affinoid, Tate affinoid, and discrete affinoid morphisms -/

section Affinoid

/-- **Affinoid morphisms**: for complete Hausdorff Huber pairs `S = (A, A⁺)` and `T = (B, B⁺)` with
`A` in Huber's standing class and sheafy adic spectra, a morphism `φ : S → T` topologically of
finite type satisfying `DiscreteTopology A → φ.toRingHom.FinitePresentation` induces a morphism
locally of finite presentation in `AdicSpace`. -/
theorem locallyOfFinitePresentation_presentationLimitPreAdicSpaceComap {A : Type u} [CommRing A]
    [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A] [CompleteSpace A] [T2Space A]
    [IsHuberRing A] [IsHuberStandard A] {B : Type u} [CommRing B] [UniformSpace B]
    [IsUniformAddGroup B] [IsTopologicalRing B] [CompleteSpace B] [T2Space B] [IsHuberRing B]
    {S : Pair A} {T : Pair B} (P : PairOfDefinition A) (P' : PairOfDefinition B)
    (hP : P.ringOfDefinition ≤ S.plus) (hP' : P'.ringOfDefinition ≤ T.plus)
    (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa T.plus))
      (presentationLimitPresheaf P' T.plus))
    (hA : PreAdicSpace.isAdic (presentationLimitPreAdicSpace P S.plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem hP))
    (φ : Pair.Hom S T) (hφ : φ.IsTopologicallyFiniteType)
    (hfp : DiscreteTopology A → φ.toRingHom.FinitePresentation) :
    LocallyOfFinitePresentation (X := ⟨_, isAdic_presentationLimitPreAdicSpace P' T.plus
        T.isRingOfIntegralElements.isPowerBounded_of_mem hP' hsheaf⟩) (Y := ⟨_, hA⟩)
      (ObjectProperty.homMk (presentationLimitPreAdicSpaceComap φ.toRingHom
        φ.continuous_toRingHom φ.map_mem_plus S.isRingOfIntegralElements.isPowerBounded_of_mem
        T.isRingOfIntegralElements.isPowerBounded_of_mem hP hP' hsheaf)) := by
  rw [locallyOfFinitePresentation_iff]
  intro x
  exact exists_locallyOfFinitePresentation_chart_of_openImmersion_sq hP hP' hsheaf (𝟙 _) (𝟙 _) φ hφ
    hfp (b₀ := x) rfl (by simp [presentationLimitPreAdicSpacePairComap_def])

/-- For complete Hausdorff `A` (`[IsHuberStandard A]`) and `B`, `comapOfPresentation` is locally of
finite presentation whenever `φ` is topologically of finite type and satisfies
`DiscreteTopology A → φ.toRingHom.FinitePresentation`. -/
theorem locallyOfFinitePresentation_comapOfPresentation {A : Type u} [CommRing A] [UniformSpace A]
    [IsUniformAddGroup A] [IsTopologicalRing A] [CompleteSpace A] [T2Space A] [IsHuberRing A]
    [IsHuberStandard A] {B : Type u} [CommRing B] [UniformSpace B] [IsUniformAddGroup B]
    [IsTopologicalRing B] [CompleteSpace B] [T2Space B] [IsHuberRing B]
    (S : Pair A) (P : PairOfDefinition A) (hS : P.ringOfDefinition ≤ S.plus)
    (hsheafS : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa S.plus))
      (presentationLimitPresheaf P S.plus))
    (T : Pair B) (P' : PairOfDefinition B) (hT : P'.ringOfDefinition ≤ T.plus)
    (hsheafT : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa T.plus))
      (presentationLimitPresheaf P' T.plus))
    (φ : Pair.Hom S T) (hφ : φ.IsTopologicallyFiniteType)
    (hfp : DiscreteTopology A → φ.toRingHom.FinitePresentation) :
    LocallyOfFinitePresentation (comapOfPresentation S P hS hsheafS T P' hT hsheafT φ) := by
  rw [comapOfPresentation_eq_homMk_presentationLimitPreAdicSpaceComap]
  exact locallyOfFinitePresentation_presentationLimitPreAdicSpaceComap P P' hS hT hsheafT
    (ofPresentation S P hS hsheafS).property φ hφ hfp

/-- Comparing `LocallyOfFinitePresentation` on `comapOfPair` with `comapOfPresentation` for any
compatible pairs of definition. -/
theorem locallyOfFinitePresentation_comapOfPair_iff_comapOfPresentation {A : Type u} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A] {B : Type u} [CommRing B]
    [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B] {S : Pair A} {T : Pair B}
    (hS : IsSheafyForEveryPresentation S.plus) (hT : IsSheafyForEveryPresentation T.plus)
    (P : PairOfDefinition A) (hP : P.ringOfDefinition ≤ S.plus)
    (P' : PairOfDefinition B) (hP' : P'.ringOfDefinition ≤ T.plus) (φ : Pair.Hom S T) :
    LocallyOfFinitePresentation (comapOfPair hS hT φ) ↔
      LocallyOfFinitePresentation
        (comapOfPresentation S P hP (hS.isSheaf P hP) T P' hP' (hT.isSheaf P' hP') φ) := by
  rw [← MorphismProperty.cancel_right_of_respectsIso (@LocallyOfFinitePresentation.{u}) _
      (ofPairIsoOfPresentation S hS P hP).hom,
    ← ofPairIsoOfPresentation_hom_comapOfPresentation hS hT P hP P' hP' φ,
    MorphismProperty.cancel_left_of_respectsIso (@LocallyOfFinitePresentation.{u})]

/-- For complete Hausdorff `A` (`[IsHuberStandard A]`) and `B`, `comapOfPair` is locally of finite
presentation whenever `φ` is topologically of finite type and satisfies
`DiscreteTopology A → φ.toRingHom.FinitePresentation`. -/
theorem locallyOfFinitePresentation_comapOfPair {A : Type u} [CommRing A] [UniformSpace A]
    [IsUniformAddGroup A] [IsTopologicalRing A] [CompleteSpace A] [T2Space A] [IsHuberRing A]
    [IsHuberStandard A] {B : Type u} [CommRing B] [UniformSpace B] [IsUniformAddGroup B]
    [IsTopologicalRing B] [CompleteSpace B] [T2Space B] [IsHuberRing B] {S : Pair A} {T : Pair B}
    (hS : IsSheafyForEveryPresentation S.plus) (hT : IsSheafyForEveryPresentation T.plus)
    (φ : Pair.Hom S T) (hφ : φ.IsTopologicallyFiniteType)
    (hfp : DiscreteTopology A → φ.toRingHom.FinitePresentation) :
    LocallyOfFinitePresentation (comapOfPair hS hT φ) := by
  obtain ⟨P, hP, _⟩ := hS.exists_compatible_isSheaf
  obtain ⟨P', hP', _⟩ := hT.exists_compatible_isSheaf
  exact (locallyOfFinitePresentation_comapOfPair_iff_comapOfPresentation hS hT P hP P' hP' φ).mpr
    (locallyOfFinitePresentation_comapOfPresentation S P hP (hS.isSheaf P hP) T P' hP'
      (hT.isSheaf P' hP') φ hφ hfp)

/-- **Over a strongly noetherian Tate ring, every pair morphism topologically of finite type into a
complete Hausdorff pair induces a morphism locally of finite presentation**, with no completeness or
Hausdorffness required of the base ring `A`. -/
theorem locallyOfFinitePresentation_comapOfPair_of_isTateRing {A : Type u} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [IsTateRing A] [IsStronglyNoetherian A]
    {B : Type u} [CommRing B] [UniformSpace B] [IsUniformAddGroup B] [IsTopologicalRing B]
    [CompleteSpace B] [T2Space B] [IsHuberRing B] {S : Pair A} {T : Pair B}
    (hS : IsSheafyForEveryPresentation S.plus) (hT : IsSheafyForEveryPresentation T.plus)
    (φ : Pair.Hom S T) (hφ : φ.IsTopologicallyFiniteType) :
    LocallyOfFinitePresentation (comapOfPair hS hT φ) := by
  obtain ⟨P, hP, _⟩ := hS.exists_compatible_isSheaf
  obtain ⟨P', hP', _⟩ := hT.exists_compatible_isSheaf
  rw [locallyOfFinitePresentation_comapOfPair_iff_comapOfPresentation hS hT P hP P' hP' φ]
  have hY : (ofPresentation S P hP (hS.isSheaf P hP)).IsLocallyHuberStandard :=
    IsLocallyHuberStandard.spa P S.plus S.isRingOfIntegralElements.isPowerBounded_of_mem hP
      (hS.isSheaf P hP)
  have ha : (ofPresentation S P hP (hS.isSheaf P hP)).obj.analyticPoints = Set.univ :=
    analyticPoints_presentationLimitPreAdicSpace_of_isTateRing P S.plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem hP
  exact (locallyOfFinitePresentation_iff_locallyOfFiniteType_of_analyticPoints_eq_univ hY ha).mpr
    (locallyOfFiniteType_comapOfPresentation S P hP (hS.isSheaf P hP) T P' hP' (hT.isSheaf P' hP')
      φ hφ)

/-- **Discrete affinoid morphisms locally of finite presentation have finitely presented ring
homomorphisms**: if `A` and `B` carry the discrete topology and
`comapOfPair hS hT φ : Spa(B, B⁺) ⟶ Spa(A, A⁺)` is locally of finite presentation, then
`φ.toRingHom : A →+* B` is algebraically of finite presentation (`RingHom.FinitePresentation`). -/
theorem LocallyOfFinitePresentation.finitePresentation_of_discreteTopology {A : Type u} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [DiscreteTopology A] {B : Type u} [CommRing B]
    [TopologicalSpace B] [IsTopologicalRing B] [DiscreteTopology B] {S : Pair A} {T : Pair B}
    {hS : IsSheafyForEveryPresentation S.plus} {hT : IsSheafyForEveryPresentation T.plus}
    {φ : Pair.Hom S T} (hf : LocallyOfFinitePresentation (comapOfPair hS hT φ)) :
    φ.toRingHom.FinitePresentation := by
  classical
  let _ : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
  have : IsUniformAddGroup A := isUniformAddGroup_of_addCommGroup
  have : DiscreteUniformity A := IsRightUniformAddGroup.discreteUniformity
  let _ : UniformSpace B := IsTopologicalAddGroup.rightUniformSpace B
  have : IsUniformAddGroup B := isUniformAddGroup_of_addCommGroup
  have : DiscreteUniformity B := IsRightUniformAddGroup.discreteUniformity
  obtain ⟨P, hP, _⟩ := hS.exists_compatible_isSheaf
  obtain ⟨P', hP', _⟩ := hT.exists_compatible_isSheaf
  have hsheafA := hS.isSheaf P hP
  have hsheafB := hT.isSheaf P' hP'
  let q := comapOfPresentation S P hP hsheafA T P' hP' hsheafB φ
  have hq : LocallyOfFinitePresentation q :=
    (locallyOfFinitePresentation_comapOfPair_iff_comapOfPresentation hS hT P hP P' hP' φ).mp hf
  -- For each `y : spa T.plus`, find a rational open `R(TB y / sB y)` around `y` whose coordinate
  -- ring `B_{sB y}` is finitely presented over `A`.
  have hloc : ∀ y : spa T.plus, ∃ (TB : Finset B) (sB : B),
      y.1 ∈ rationalSubset T.plus TB sB ∧
      ((algebraMap B (Localization.Away sB)).comp φ.toRingHom).FinitePresentation := by
    intro y
    let y₀ : presentationLimitPreAdicSpace P' T.plus
      T.isRingOfIntegralElements.isPowerBounded_of_mem hP' := y
    let kA : presentationLimitPreAdicSpace P S.plus
        S.isRingOfIntegralElements.isPowerBounded_of_mem hP ⟶
        (ofPresentation S P hP hsheafA).obj := 𝟙 _
    obtain ⟨TA, sA, hTA, -, -, C, _, _, _, _, _, _, _, U, PC, hPC, hsheafC, kX, hkX, β, hβ,
      hβ_fp, c₀, hc₀, hsq⟩ :=
      hq.exists_openImmersion_over_rationalLocalization P hP hsheafA kA y₀ rfl
    -- Shrink `Spa(B, B⁺)` around `y₀` into `Set.range kX.base`.
    let OB : Opens (presentationLimitPreAdicSpace P' T.plus
        T.isRingOfIntegralElements.isPowerBounded_of_mem hP') :=
      ⟨Set.range kX.base, kX.isOpenEmbedding.isOpen_range⟩
    have hyO : y₀ ∈ OB := ⟨c₀, hc₀⟩
    obtain ⟨RB, hRB, hyR, hRBO⟩ :=
      Opens.isBasis_iff_nbhd.mp (isBasis_spaRationalOpens T.plus) hyO
    obtain ⟨TB, sB, hTB, rfl⟩ := mem_spaRationalOpens_iff_exists_spaBasicOpen.mp hRB
    refine ⟨TB, sB, mem_spaBasicOpen.mp hyR, ?_⟩
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
      exact P.completionLocalization_ringOfDefinition_le_completedPlusSubring S.plus hP TA sA LA
        hdenA
    have hsheafA₁ := isSheaf_presentationLimitPresheaf_rationalLocalizationPair P S hP TA sA LA
      hdenA hTA hsheafA
    have hDiscA₁ : DiscreteTopology (UniformSpace.Completion LA) :=
      (P.isTopologicallyFiniteType_toCompletionLoc TA sA LA hdenA
        (Submodule.isOpen_mono (Ideal.span_mono (Set.subset_insert _ _)) hTA)).discreteTopology
    have hDiscC : DiscreteTopology C := hβ.isTopologicallyFiniteType_toRingHom.discreteTopology
    let LB := Localization.Away sB
    have hdenB := P'.hasDenominatorPower_of_isOpen_span TB sB LB hTB
    let _ := P'.locUniformSpace TB sB LB hdenB
    have _ := P'.isUniformAddGroup_locUniformSpace TB sB LB hdenB
    have _ := P'.isTopologicalRing_locUniformSpace TB sB LB hdenB
    have _ := P'.isHuberRing_completion_locTopology TB sB LB hdenB
    let T₁ := P'.rationalLocalizationPair T hP' TB sB LB hdenB
    let P₁' := P'.completionLocalization TB sB LB hdenB
    have hP₁' : P₁'.ringOfDefinition ≤ T₁.plus := by
      rw [rationalLocalizationPair_plus]
      exact P'.completionLocalization_ringOfDefinition_le_completedPlusSubring T.plus hP' TB sB LB
        hdenB
    have hsheafB₁ := isSheaf_presentationLimitPresheaf_rationalLocalizationPair P' T hP' TB sB LB
      hdenB hTB hsheafB
    let ιB := presentationLimitPreAdicSpacePairComap P' P₁' hP' hP₁' hsheafB₁
      (P'.toCompletionLocHom T hP' TB sB LB hdenB)
    have hιB_imm : PreAdicSpace.IsOpenImmersion ιB := by
      rw [show ιB = _ from presentationLimitPreAdicSpacePairComap_def ..]
      exact isOpenImmersion_presentationLimitPreAdicSpaceComap_toCompletionLocHom P' hP' TB sB LB
        hdenB hTB hsheafB₁
    have hιB_range : Set.range ιB.base = (spaBasicOpen T.plus TB sB : Set (spa T.plus)) := by
      rw [show ιB = _ from presentationLimitPreAdicSpacePairComap_def ..]
      exact range_presentationLimitPreAdicSpaceComap_toCompletionLocHom_base P' hP' TB sB LB hdenB
        hsheafB₁
    -- Pull `R(TB / sB)` back to `Spa(C, C⁺)` along `kX` so both open immersions into `Spa(B, B⁺)`
    -- have the exact same range `spaBasicOpen T.plus TB sB`.
    let δ := presentationLimitHomPairHom P' PC T U hP' hPC kX
    have hkX_eq : kX = presentationLimitPreAdicSpacePairComap P' PC hP' hPC hsheafC δ :=
      (presentationLimitPreAdicSpacePairComap_presentationLimitHomPairHom P' PC T U hP' hPC
        hsheafC kX).symm
    let TC : Finset C := TB.image δ.toRingHom
    let sC : C := δ.toRingHom sB
    have hTC : IsOpen (Ideal.span (TC : Set C) : Set C) := isOpen_discrete _
    let LC := Localization.Away sC
    have hdenC := PC.hasDenominatorPower_of_isOpen_span TC sC LC hTC
    let _ := PC.locUniformSpace TC sC LC hdenC
    have _ := PC.isUniformAddGroup_locUniformSpace TC sC LC hdenC
    have _ := PC.isTopologicalRing_locUniformSpace TC sC LC hdenC
    have _ := PC.isHuberRing_completion_locTopology TC sC LC hdenC
    let U₁ := PC.rationalLocalizationPair U hPC TC sC LC hdenC
    let PC₁ := PC.completionLocalization TC sC LC hdenC
    have hPC₁ : PC₁.ringOfDefinition ≤ U₁.plus := by
      rw [rationalLocalizationPair_plus]
      exact PC.completionLocalization_ringOfDefinition_le_completedPlusSubring U.plus hPC TC sC LC
        hdenC
    have hsheafC₁ := isSheaf_presentationLimitPresheaf_rationalLocalizationPair PC U hPC TC sC LC
      hdenC hTC hsheafC
    let ιC := presentationLimitPreAdicSpacePairComap PC PC₁ hPC hPC₁ hsheafC₁
      (PC.toCompletionLocHom U hPC TC sC LC hdenC)
    have hιC_imm : PreAdicSpace.IsOpenImmersion ιC := by
      rw [show ιC = _ from presentationLimitPreAdicSpacePairComap_def ..]
      exact isOpenImmersion_presentationLimitPreAdicSpaceComap_toCompletionLocHom PC hPC TC sC LC
        hdenC hTC hsheafC₁
    have hιC_range : Set.range ιC.base = (spaBasicOpen U.plus TC sC : Set (spa U.plus)) := by
      rw [show ιC = _ from presentationLimitPreAdicSpacePairComap_def ..]
      exact range_presentationLimitPreAdicSpaceComap_toCompletionLocHom_base PC hPC TC sC LC hdenC
        hsheafC₁
    have hpre_eq : (spaBasicOpen U.plus TC sC : Set (spa U.plus)) =
        kX.base ⁻¹' (spaBasicOpen T.plus TB sB : Set (spa T.plus)) := by
      ext c
      have hpre := Set.ext_iff.mp (δ.spaComap_preimage_rationalSubset TB sB) c
      have hc_eq : (kX.base c : spa T.plus) = δ.spaComap c := by
        rw [hkX_eq]
        exact presentationLimitPreAdicSpacePairComap_base_apply P' PC hP' hPC hsheafC δ c
      constructor
      · intro hc
        have h1 : (c : spa U.plus).1 ∈ rationalSubset U.plus TC sC := mem_spaBasicOpen.mp hc
        have h2 : (δ.spaComap c).1 ∈ rationalSubset T.plus TB sB := hpre.mpr h1
        have h3 : δ.spaComap c ∈ (spaBasicOpen T.plus TB sB : Set (spa T.plus)) :=
          mem_spaBasicOpen.mpr h2
        exact Set.mem_preimage.mpr (hc_eq.symm ▸ h3)
      · intro hc
        have hc' : δ.spaComap c ∈ (spaBasicOpen T.plus TB sB : Set (spa T.plus)) :=
          hc_eq ▸ Set.mem_preimage.mp hc
        have h2 : (δ.spaComap c).1 ∈ rationalSubset T.plus TB sB := mem_spaBasicOpen.mp hc'
        exact mem_spaBasicOpen.mpr (hpre.mp h2)
    have hrange_eq : Set.range (ιC ≫ kX).base = Set.range ιB.base := by
      rw [PreAdicSpace.comp_base, TopCat.coe_comp, Set.range_comp, hιC_range, hpre_eq, hιB_range]
      exact Set.image_preimage_eq_iff.mpr hRBO
    have hιCkX_imm : PreAdicSpace.IsOpenImmersion (ιC ≫ kX) :=
      PreAdicSpace.IsOpenImmersion.comp ιC kX
    let eCB := PreAdicSpace.IsOpenImmersion.isoOfRangeEq (ιC ≫ kX) ιB hrange_eq
    have heCB_inv : eCB.inv ≫ ιC ≫ kX = ιB :=
      PreAdicSpace.IsOpenImmersion.isoOfRangeEq_inv_comp (ιC ≫ kX) ιB hrange_eq
    let γ₁ := presentationLimitHomPairHom PC₁ P₁' U₁ T₁ hPC₁ hP₁' eCB.inv
    let γ₂ := presentationLimitHomPairHom P₁' PC₁ T₁ U₁ hP₁' hPC₁ eCB.hom
    have hγ₁₂ : γ₁.comp γ₂ = Pair.Hom.id T₁ := by
      rw [← presentationLimitHomPairHom_comp P₁' PC₁ P₁' T₁ U₁ T₁ hP₁' hPC₁ hP₁', eCB.inv_hom_id,
        presentationLimitHomPairHom_id P₁' T₁ hP₁']
    have hγ₂₁ : γ₂.comp γ₁ = Pair.Hom.id U₁ := by
      rw [← presentationLimitHomPairHom_comp PC₁ P₁' PC₁ U₁ T₁ U₁ hPC₁ hP₁' hPC₁, eCB.hom_inv_id,
        presentationLimitHomPairHom_id PC₁ U₁ hPC₁]
    have hγ₁_bij : Function.Bijective γ₁.toRingHom := by
      refine Function.bijective_iff_has_inverse.mpr ⟨γ₂.toRingHom, fun x ↦ ?_, fun x ↦ ?_⟩
      · have h := congrArg Pair.Hom.toRingHom hγ₂₁
        rw [Pair.Hom.toRingHom_comp, Pair.Hom.toRingHom_id] at h
        exact RingHom.congr_fun h x
      · have h := congrArg Pair.Hom.toRingHom hγ₁₂
        rw [Pair.Hom.toRingHom_comp, Pair.Hom.toRingHom_id] at h
        exact RingHom.congr_fun h x
    -- Compare the two paths `A → A₁ → C → C₁ → B₁` and `A → B → B₁` on global sections.
    have hpath :
        γ₁.comp ((PC.toCompletionLocHom U hPC TC sC LC hdenC).comp
          (β.comp (P.toCompletionLocHom S hP TA sA LA hdenA))) =
        (P'.toCompletionLocHom T hP' TB sB LB hdenB).comp φ := by
      have hsq₁ : presentationLimitPreAdicSpacePairComap P₁ PC hP₁ hPC hsheafC β ≫
          presentationLimitPreAdicSpacePairComap P P₁ hP hP₁ hsheafA₁
            (P.toCompletionLocHom S hP TA sA LA hdenA) =
          kX ≫ presentationLimitPreAdicSpacePairComap P P' hP hP' hsheafB φ := by
        simpa [kA, q] using hsq
      have hsq' : eCB.inv ≫ ιC ≫
          (presentationLimitPreAdicSpacePairComap P₁ PC hP₁ hPC hsheafC β ≫
            presentationLimitPreAdicSpacePairComap P P₁ hP hP₁ hsheafA₁
              (P.toCompletionLocHom S hP TA sA LA hdenA)) =
          ιB ≫ presentationLimitPreAdicSpacePairComap P P' hP hP' hsheafB φ := by
        rw [hsq₁, ← Category.assoc ιC, ← Category.assoc eCB.inv, heCB_inv]
      have h := congrArg (presentationLimitHomPairHom P P₁' S T₁ hP hP₁') hsq'
      dsimp only [γ₁, ιC] at h ⊢
      rwa [← presentationLimitPreAdicSpacePairComap_comp P P₁ PC hP hP₁ hPC hsheafA₁ hsheafC,
        ← presentationLimitPreAdicSpacePairComap_comp P PC PC₁ hP hPC hPC₁ hsheafC hsheafC₁,
        presentationLimitHomPairHom_comp P PC₁ P₁' S U₁ T₁ hP hPC₁ hP₁',
        presentationLimitHomPairHom_presentationLimitPreAdicSpacePairComap P PC₁ S U₁ hP hPC₁
          hsheafC₁,
        ← presentationLimitPreAdicSpacePairComap_comp P P' P₁' hP hP' hP₁' hsheafB hsheafB₁,
        presentationLimitHomPairHom_presentationLimitPreAdicSpacePairComap P P₁' S T₁ hP hP₁'
          hsheafB₁] at h
    have hfpA : (P.toCompletionLocHom S hP TA sA LA hdenA).toRingHom.FinitePresentation := by
      rw [toRingHom_toCompletionLocHom]
      exact P.finitePresentation_toCompletionLoc_of_discreteTopology (TA : Set A) sA LA hdenA
    have hfpC : (PC.toCompletionLocHom U hPC TC sC LC hdenC).toRingHom.FinitePresentation := by
      rw [toRingHom_toCompletionLocHom]
      exact PC.finitePresentation_toCompletionLoc_of_discreteTopology (TC : Set C) sC LC hdenC
    have hcomp_fp : ((P'.toCompletionLocHom T hP' TB sB LB hdenB).toRingHom.comp
        φ.toRingHom).FinitePresentation := by
      rw [← Pair.Hom.toRingHom_comp, ← hpath]
      simp only [Pair.Hom.toRingHom_comp]
      exact (RingHom.FinitePresentation.of_bijective hγ₁_bij).comp
        (hfpC.comp ((hβ_fp hDiscA₁).comp hfpA))
    let eB := P'.completionLocEquivOfDiscreteTopology (TB : Set B) sB LB hdenB
    have heq : (algebraMap B LB).comp φ.toRingHom =
        eB.symm.toRingHom.comp
          ((P'.toCompletionLocHom T hP' TB sB LB hdenB).toRingHom.comp φ.toRingHom) := by
      ext a
      simp [eB, toRingHom_toCompletionLocHom, toCompletionLoc_apply]
    rw [heq]
    exact (RingHom.FinitePresentation.of_bijective eB.symm.bijective).comp hcomp_fp
  choose TB sB hyR hfp using hloc
  have : IsLocalization.Away (1 : B) B :=
    IsLocalization.self (by rintro _ ⟨n, rfl⟩; simp)
  have hcov : rationalSubset T.plus ({1} : Finset B) 1 ⊆
      ⋃ y : spa T.plus, rationalSubset T.plus (TB y) (sB y) := by
    intro v hv
    rw [rationalSubset_singleton_one] at hv
    exact Set.mem_iUnion.mpr ⟨⟨v, hv⟩, hyR ⟨v, hv⟩⟩
  have hspan : Ideal.span (Set.range sB) = ⊤ := by
    simpa using span_eq_top_of_rationalSubset_subset_iUnion (Aplus := T.plus) (T := {1}) (s := 1) B
      (fun _ _ ↦ isOpen_discrete _) hcov
  refine RingHom.finitePresentation_ofLocalizationSpanTarget φ.toRingHom (Set.range sB) hspan ?_
  rintro ⟨_, y, rfl⟩
  exact hfp y

/-- **Discrete affinoid comparison for `LocallyOfFinitePresentation`**: for discrete commutative
rings `A` and `B` with trivial plus rings `Pair.discrete A = (A, A)` and `Pair.discrete B = (B, B)`,
the induced morphism `Spa(B, B) ⟶ Spa(A, A)` is locally of finite presentation if and only if
`φ.toRingHom` is algebraically of finite presentation (`RingHom.FinitePresentation`). -/
theorem locallyOfFinitePresentation_comapOfPair_discrete_iff {A : Type u} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [DiscreteTopology A] {B : Type u} [CommRing B]
    [TopologicalSpace B] [IsTopologicalRing B] [DiscreteTopology B]
    (hS : IsSheafyForEveryPresentation (Pair.discrete A).plus)
    (hT : IsSheafyForEveryPresentation (Pair.discrete B).plus)
    (φ : Pair.Hom (Pair.discrete A) (Pair.discrete B)) :
    LocallyOfFinitePresentation (comapOfPair hS hT φ) ↔ φ.toRingHom.FinitePresentation := by
  refine ⟨fun hf ↦ hf.finitePresentation_of_discreteTopology, fun hφ ↦ ?_⟩
  let _ : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
  have : IsUniformAddGroup A := isUniformAddGroup_of_addCommGroup
  have : DiscreteUniformity A := IsRightUniformAddGroup.discreteUniformity
  let _ : UniformSpace B := IsTopologicalAddGroup.rightUniformSpace B
  have : IsUniformAddGroup B := isUniformAddGroup_of_addCommGroup
  have : DiscreteUniformity B := IsRightUniformAddGroup.discreteUniformity
  exact locallyOfFinitePresentation_comapOfPair hS hT φ
    ((Pair.Hom.isTopologicallyFiniteType_iff_finiteType_of_plus_eq_top
      Pair.discrete_plus Pair.discrete_plus).mpr (RingHom.FiniteType.of_finitePresentation hφ))
    fun _ ↦ hφ

end Affinoid

end TauCeti.AdicSpace
