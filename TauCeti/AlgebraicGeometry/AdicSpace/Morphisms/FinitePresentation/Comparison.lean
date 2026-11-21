/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Morphisms.AnalyticLocus
public import TauCeti.AlgebraicGeometry.AdicSpace.Morphisms.FinitePresentation.Cancel

import Mathlib.RingTheory.RingHom.FinitePresentation
import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.Affinoid.CompleteChart
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Emptiness
import TauCeti.RingTheory.Huber.NoetherianType.TopologicallyFiniteType

/-!
# Analytic, noetherian, and discrete affinoid comparisons for `LocallyOfFinitePresentation`

This file compares `TauCeti.AdicSpace.LocallyOfFinitePresentation` with
`TauCeti.AdicSpace.LocallyOfFiniteType` and gives affinoid criteria:

* **Discrete-noetherian and analytic equivalence**: over `Y.IsLocallyHuberStandard`, the two
  properties coincide when every discrete complete affinoid open of `Y` is noetherian, and in
  particular whenever `Y` is analytic.
* **Affinoid criteria**: `comapOfPresentation` and `comapOfPair` are locally of finite
  presentation under `IsHuberStandard A` and `DiscreteTopology A → φ.toRingHom.FinitePresentation`
  (automatically satisfied over strongly noetherian Tate bases).
* **Discrete affinoid comparison**: for discrete rings with `Pair.discrete`,
  `LocallyOfFinitePresentation (comapOfPair hS hT φ) ↔ φ.toRingHom.FinitePresentation`.

## Main results

* `locallyOfFinitePresentation_iff_locallyOfFiniteType_of_forall_discrete_isNoetherianRing`,
  `locallyOfFinitePresentation_iff_locallyOfFiniteType_of_analyticPoints_eq_univ`,
  `locallyOfFinitePresentation_iff_of_isAnalytic`, and `IsLocallyNoetherian` counterparts.
* `LocallyOfFiniteType.locallyOfFinitePresentation_analyticLocusMap`.
* `locallyOfFinitePresentation_comapOfPresentation`, `locallyOfFinitePresentation_comapOfPair`,
  `locallyOfFinitePresentation_comapOfPair_of_isStronglyNoetherian`.
* `LocallyOfFinitePresentation.finitePresentation_of_discreteTopology`,
  `locallyOfFinitePresentation_comapOfPair_discrete_iff`.

## References

* R. Huber, *Étale cohomology of rigid analytic varieties and adic spaces*, Aspects of
  Mathematics E30 (1996), §1.1–1.2.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Remark 6.37 and Definition 8.48.
-/

public section

open CategoryTheory TopologicalSpace Topology

namespace TauCeti.AdicSpace

open Huber PreAdicSpace ValuationSpectrum CompleteAffinoidOpen

universe u

variable {X Y : AdicSpace.{u}}

/-- **Discrete-noetherian criterion comparing `LocallyOfFinitePresentation` and
`LocallyOfFiniteType`**: if `Y` is locally of Huber's standing class and every discrete complete
Hausdorff affinoid open of `Y` has a noetherian coordinate ring, then `f : X ⟶ Y` is locally of
finite presentation if and only if it is locally of finite type (since algebraic finite type over
a noetherian ring is automatically of finite presentation). -/
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
    fun hf ↦ (locallyOfFinitePresentation_iff f).mpr fun x ↦ ?_⟩
  obtain ⟨V, hV, hfxV⟩ := isLocallyHuberStandard_iff.mp hY (f.hom.base x)
  obtain ⟨A, _, _, _, _, _, _, _, _, S, P, hP, ⟨eV⟩⟩ :=
    (isHuberStandardAffinoid_iff _).mp ((mem_propOpens_iff _).mp hV)
  have hsheafA := isSheaf_of_restrict_iso P hP eV
  let CY := ofRestrictIso S P hP hsheafA eV
  have ha₀ : CY.hom.base (eV.hom.base ⟨f.hom.base x, hfxV⟩) = f.hom.base x :=
    ofRestrictIso_hom_base S P hP hsheafA eV hfxV
  obtain ⟨TA, sA, hTA, -, CX, β, hβ, c₀, hc₀, hsq⟩ :=
    hf.exists_openImmersion_over_rationalLocalization CY x ha₀
  let CY₁ := CY.rationalLocalization TA sA hTA
  have : IsHuberStandard CY.Ring := (inferInstance : IsHuberStandard A)
  have : IsHuberStandard CY₁.Ring := .of_isTopologicallyFiniteType
    (CY.isTopologicallyFiniteType_rationalLocalizationHom TA sA
      hTA).isTopologicallyFiniteType_toRingHom
  refine locallyOfFinitePresentationAt_of_openImmersion_sq CY₁ CX β hβ (fun _ ↦ ?_) hc₀ hsq
  have : IsNoetherianRing CY₁.Ring := hnoeth CY₁.Ring CY₁.pair CY₁.pairOfDefinition CY₁.le_plus
    CY₁.hom CY₁.isOpenImmersion
  have : DiscreteTopology CX.Ring := hβ.isTopologicallyFiniteType_toRingHom.discreteTopology
  exact RingHom.FinitePresentation.of_finiteType.mp
    hβ.isTopologicallyFiniteType_toRingHom.finiteType

/-- **Over an analytic target locally of Huber's standing class, `LocallyOfFinitePresentation` and
`LocallyOfFiniteType` coincide** (Huber 1996, §1.2): every discrete complete affinoid open of `Y`
is empty, hence has subsingleton (therefore noetherian) coordinate ring. -/
theorem locallyOfFinitePresentation_iff_locallyOfFiniteType_of_analyticPoints_eq_univ
    {f : X ⟶ Y} (hY : Y.IsLocallyHuberStandard) (ha : Y.obj.analyticPoints = Set.univ) :
    LocallyOfFinitePresentation f ↔ LocallyOfFiniteType f := by
  refine locallyOfFinitePresentation_iff_locallyOfFiniteType_of_forall_discrete_isNoetherianRing hY
    fun A _ _ _ _ _ _ _ _ S P hP k hk ↦ ?_
  have := hk
  rcases (spa S.plus).eq_empty_or_nonempty with hemp | ⟨a₁, ha₁⟩
  · have : Subsingleton A :=
      (spa_eq_empty_iff_subsingleton S.plus S.isRingOfIntegralElements).mp hemp
    infer_instance
  · let a₀ : presentationLimitPreAdicSpace P S.plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem hP := ⟨a₁, ha₁⟩
    have ha₀ : a₀ ∈ (presentationLimitPreAdicSpace P S.plus
        S.isRingOfIntegralElements.isPowerBounded_of_mem hP).analyticPoints := by
      rw [← preimage_analyticPoints_of_isOpenImmersion k, ha]; exact Set.mem_univ _
    rw [analyticPoints_presentationLimitPreAdicSpace] at ha₀
    exact ((isAnalyticPoint_def _).mp ((mem_spaAnalytic_iff S.plus _).mp ha₀).2
      (isOpen_discrete _)).elim

/-- **Over an analytic target locally of Huber's standing class (`Y.IsAnalytic`),
`LocallyOfFinitePresentation` and `LocallyOfFiniteType` coincide** (Huber 1996, §1.2). -/
theorem locallyOfFinitePresentation_iff_of_isAnalytic {f : X ⟶ Y}
    (hY : Y.IsLocallyHuberStandard) (ha : Y.IsAnalytic) :
    LocallyOfFinitePresentation f ↔ LocallyOfFiniteType f :=
  locallyOfFinitePresentation_iff_locallyOfFiniteType_of_analyticPoints_eq_univ hY
    ha.analyticPoints_eq_univ

namespace IsLocallyNoetherian

/-- **Over a locally noetherian target whose points are all analytic, `LocallyOfFinitePresentation`
and `LocallyOfFiniteType` coincide**: locally noetherian analytic adic spaces automatically lie in
Huber's standing class. -/
theorem locallyOfFinitePresentation_iff_locallyOfFiniteType_of_analyticPoints_eq_univ
    {f : X ⟶ Y} (hY : Y.IsLocallyNoetherian) (ha : Y.obj.analyticPoints = Set.univ) :
    LocallyOfFinitePresentation f ↔ LocallyOfFiniteType f :=
  AdicSpace.locallyOfFinitePresentation_iff_locallyOfFiniteType_of_analyticPoints_eq_univ
    (hY.isLocallyHuberStandard_of_analyticPoints_eq_univ ha) ha

/-- **Over a locally noetherian analytic target (`Y.IsAnalytic`), `LocallyOfFinitePresentation` and
`LocallyOfFiniteType` coincide.** -/
theorem locallyOfFinitePresentation_iff_of_isAnalytic {f : X ⟶ Y}
    (hY : Y.IsLocallyNoetherian) (ha : Y.IsAnalytic) :
    LocallyOfFinitePresentation f ↔ LocallyOfFiniteType f :=
  hY.locallyOfFinitePresentation_iff_locallyOfFiniteType_of_analyticPoints_eq_univ
    ha.analyticPoints_eq_univ

end IsLocallyNoetherian

/-- **Analytic-locus upgrade**: if `f : X ⟶ Y` is locally of finite type and `Y` is locally
noetherian, then the induced morphism `hf.isAdic.analyticLocusMap` between analytic loci is
locally of finite presentation. -/
theorem LocallyOfFiniteType.locallyOfFinitePresentation_analyticLocusMap {f : X ⟶ Y}
    (hf : LocallyOfFiniteType f) (hY : Y.IsLocallyNoetherian) :
    LocallyOfFinitePresentation hf.isAdic.analyticLocusMap :=
  (locallyOfFinitePresentation_iff_locallyOfFiniteType_of_analyticPoints_eq_univ
    hY.isLocallyHuberStandard_analyticLocus
    (by rw [analyticLocus_obj, analyticPoints_analyticLocus])).mpr
    (hf.restrict hf.isAdic.analyticLocusMap_ι)

section Affinoid

/-- **Affinoid sufficient condition (presentation level)**: if `φ : S → T` is a morphism of Huber
pairs topologically of finite type between sheafy presentations with `IsHuberStandard A` and
`DiscreteTopology A → φ.toRingHom.FinitePresentation`, then
`comapOfPresentation S P hS hsheafS T P' hT hsheafT φ` is locally of finite presentation. No
completeness or Hausdorffness assumption on `A` or `B` is needed. -/
theorem locallyOfFinitePresentation_comapOfPresentation {A B : Type u} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A] [IsHuberStandard A] [CommRing B]
    [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B]
    (S : Pair A) (P : PairOfDefinition A) (hS : P.ringOfDefinition ≤ S.plus)
    (hsheafS : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa S.plus))
      (presentationLimitPresheaf P S.plus))
    (T : Pair B) (P' : PairOfDefinition B) (hT : P'.ringOfDefinition ≤ T.plus)
    (hsheafT : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa T.plus))
      (presentationLimitPresheaf P' T.plus))
    (φ : Pair.Hom S T) (hφ : φ.IsTopologicallyFiniteType)
    (hfp : DiscreteTopology A → φ.toRingHom.FinitePresentation) :
    LocallyOfFinitePresentation (comapOfPresentation S P hS hsheafS T P' hT hsheafT φ) := by
  let CY := ofCompletion P hS hsheafS
  let CX := ofCompletion P' hT hsheafT
  let φ₁ := ofCompletionMap P hS hsheafS P' hT hsheafT φ
  have hιA := isTopologicallyFiniteType_toCompletionHom P hS hsheafS
  have : IsHuberStandard CY.Ring :=
    .of_isTopologicallyFiniteType hιA.isTopologicallyFiniteType_toRingHom
  have hφ₁ : φ₁.IsTopologicallyFiniteType :=
    isTopologicallyFiniteType_ofCompletionMap P hS hsheafS P' hT hsheafT φ hφ
  have hfp₁ : DiscreteTopology CY.Ring → φ₁.toRingHom.FinitePresentation := fun _ ↦
    hιA.isTopologicallyFiniteType_toRingHom.finitePresentation_of_comp
      hφ₁.isTopologicallyFiniteType_toRingHom fun hDiscA ↦ by
        have : DiscreteTopology B := hφ.isTopologicallyFiniteType_toRingHom.discreteTopology
        rw [← Pair.Hom.toRingHom_comp, ofCompletionMap_comp_toCompletionHom,
          Pair.Hom.toRingHom_comp]
        exact (finitePresentation_toCompletionHom P' hT hsheafT).comp (hfp hDiscA)
  refine (locallyOfFinitePresentation_iff _).mpr fun x ↦ ?_
  obtain ⟨b₀, hb₀⟩ : x ∈ Set.range CX.hom.base :=
    range_ofCompletion_hom_base P' hT hsheafT ▸ Set.mem_univ _
  refine locallyOfFinitePresentationAt_of_openImmersion_sq CY CX φ₁ hφ₁ hfp₁ hb₀ ?_
  rw [comapOfPresentation_hom]; exact pairComap_ofCompletionMap_comp_hom P _ _ P' _ _ φ

/-- Comparing `LocallyOfFinitePresentation` on `comapOfPair` with `comapOfPresentation` via the
canonical isomorphisms `ofPairIsoOfPresentation`. -/
theorem locallyOfFinitePresentation_comapOfPair_iff_comapOfPresentation {A B : Type u} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A] [CommRing B] [TopologicalSpace B]
    [IsTopologicalRing B] [IsHuberRing B] {S : Pair A} {T : Pair B}
    (hS : IsSheafyForEveryPresentation S.plus) (hT : IsSheafyForEveryPresentation T.plus)
    (P : PairOfDefinition A) (hP : P.ringOfDefinition ≤ S.plus) (P' : PairOfDefinition B)
    (hP' : P'.ringOfDefinition ≤ T.plus) (φ : Pair.Hom S T) :
    LocallyOfFinitePresentation (comapOfPair hS hT φ) ↔
      LocallyOfFinitePresentation
        (comapOfPresentation S P hP (hS.isSheaf P hP) T P' hP' (hT.isSheaf P' hP') φ) := by
  rw [← MorphismProperty.cancel_right_of_respectsIso (@LocallyOfFinitePresentation.{u}) _
      (ofPairIsoOfPresentation S hS P hP).hom,
    ← ofPairIsoOfPresentation_hom_comapOfPresentation hS hT P hP P' hP' φ,
    MorphismProperty.cancel_left_of_respectsIso (@LocallyOfFinitePresentation.{u})]

/-- **Affinoid sufficient condition**: if `φ : S → T` is a morphism of Huber pairs topologically of
finite type between sheafy pairs with `IsHuberStandard A` and
`DiscreteTopology A → φ.toRingHom.FinitePresentation`, then `comapOfPair hS hT φ` is locally of
finite presentation. No completeness or Hausdorffness assumption on `A` or `B` is needed. -/
theorem locallyOfFinitePresentation_comapOfPair {A B : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsHuberRing A] [IsHuberStandard A] [CommRing B] [TopologicalSpace B]
    [IsTopologicalRing B] [IsHuberRing B] {S : Pair A} {T : Pair B}
    (hS : IsSheafyForEveryPresentation S.plus) (hT : IsSheafyForEveryPresentation T.plus)
    (φ : Pair.Hom S T) (hφ : φ.IsTopologicallyFiniteType)
    (hfp : DiscreteTopology A → φ.toRingHom.FinitePresentation) :
    LocallyOfFinitePresentation (comapOfPair hS hT φ) := by
  obtain ⟨P, hP, _⟩ := hS.exists_compatible_isSheaf
  obtain ⟨P', hP', _⟩ := hT.exists_compatible_isSheaf
  exact (locallyOfFinitePresentation_comapOfPair_iff_comapOfPresentation hS hT P hP P' hP' φ).mpr
    (locallyOfFinitePresentation_comapOfPresentation _ _ _ _ _ _ _ _ φ hφ hfp)

/-- **Affinoid sufficient condition over a strongly noetherian Tate ring**: if `A` is a strongly
noetherian Tate ring and `φ : S → T` is topologically of finite type between sheafy Huber pairs,
then `comapOfPair hS hT φ` is automatically locally of finite presentation (no discrete
finite-presentation hypothesis or completeness/Hausdorffness assumption is required). -/
theorem locallyOfFinitePresentation_comapOfPair_of_isStronglyNoetherian {A B : Type u} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [IsTateRing A] [IsStronglyNoetherian A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B]
    {S : Pair A} {T : Pair B}
    (hS : IsSheafyForEveryPresentation S.plus) (hT : IsSheafyForEveryPresentation T.plus)
    (φ : Pair.Hom S T) (hφ : φ.IsTopologicallyFiniteType) :
    LocallyOfFinitePresentation (comapOfPair hS hT φ) := by
  obtain ⟨P, hP, _⟩ := hS.exists_compatible_isSheaf
  obtain ⟨P', hP', _⟩ := hT.exists_compatible_isSheaf
  rw [locallyOfFinitePresentation_comapOfPair_iff_comapOfPresentation hS hT P hP P' hP' φ]
  exact (locallyOfFinitePresentation_iff_locallyOfFiniteType_of_analyticPoints_eq_univ
    (IsLocallyHuberStandard.spa P S.plus S.isRingOfIntegralElements.isPowerBounded_of_mem hP
      (hS.isSheaf P hP))
    (analyticPoints_presentationLimitPreAdicSpace_of_isTateRing P S.plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem hP)).mpr
    (locallyOfFiniteType_comapOfPresentation S P hP (hS.isSheaf P hP) T P' hP' (hT.isSheaf P' hP')
      φ hφ)

/-- **Discrete descent for `LocallyOfFinitePresentation`**: if `φ : S → T` is a morphism of Huber
pairs with discrete underlying rings and `comapOfPair hS hT φ` is locally of finite presentation,
then the underlying ring homomorphism `φ.toRingHom` is algebraically of finite presentation
(`RingHom.FinitePresentation`). -/
theorem LocallyOfFinitePresentation.finitePresentation_of_discreteTopology {A B : Type u}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [DiscreteTopology A] [CommRing B]
    [TopologicalSpace B] [IsTopologicalRing B] [DiscreteTopology B] {S : Pair A} {T : Pair B}
    {hS : IsSheafyForEveryPresentation S.plus} {hT : IsSheafyForEveryPresentation T.plus}
    {φ : Pair.Hom S T} (hf : LocallyOfFinitePresentation (comapOfPair hS hT φ)) :
    φ.toRingHom.FinitePresentation := by
  obtain ⟨P, hP, _⟩ := hS.exists_compatible_isSheaf
  obtain ⟨P', hP', _⟩ := hT.exists_compatible_isSheaf
  have hsheafA := hS.isSheaf P hP
  have hq := (locallyOfFinitePresentation_comapOfPair_iff_comapOfPresentation hS hT P hP P' hP'
    φ).mp hf
  let CA := ofDiscrete S P hP hsheafA
  refine PreAdicSpace.ringHom_prop_of_forall_rational_chart_discrete
    RingHom.finitePresentation_stableUnderComposition RingHom.finitePresentation_respectsIso
    RingHom.finitePresentation_holdsForLocalizationAway
    RingHom.finitePresentation_ofLocalizationSpanTarget
    P hP hsheafA P' hP' (hT.isSheaf P' hP') φ fun y ↦ ?_
  obtain ⟨TA, sA, hTA, -, -, CX, β, hβ, hβ_fp, c₀, hc₀, hsq⟩ :=
    hq.exists_openImmersion_over_rationalLocalization CA y rfl
  have hDisc₁ : DiscreteTopology (CA.rationalLocalization TA sA hTA).Ring :=
    (CA.isTopologicallyFiniteType_rationalLocalizationHom TA sA
      hTA).isTopologicallyFiniteType_toRingHom.discreteTopology
  have hDiscC : DiscreteTopology CX.Ring := hβ.isTopologicallyFiniteType_toRingHom.discreteTopology
  rw [comapOfPresentation_hom] at hsq
  exact ⟨TA, sA, hTA, CX, hDiscC, β, hβ_fp hDisc₁, c₀, hc₀, hsq⟩

/-- **Discrete affinoid comparison for `LocallyOfFinitePresentation`**: for discrete rings `A, B`
with maximal plus subrings `Pair.discrete A` and `Pair.discrete B`, the affinoid morphism
`Spa(B, B) ⟶ Spa(A, A)` induced by `φ` is locally of finite presentation if and only if the
underlying ring homomorphism `φ.toRingHom : A →+* B` is algebraically of finite presentation
(`RingHom.FinitePresentation`). -/
theorem locallyOfFinitePresentation_comapOfPair_discrete_iff {A B : Type u} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [DiscreteTopology A] [CommRing B]
    [TopologicalSpace B] [IsTopologicalRing B] [DiscreteTopology B]
    (hS : IsSheafyForEveryPresentation (Pair.discrete A).plus)
    (hT : IsSheafyForEveryPresentation (Pair.discrete B).plus)
    (φ : Pair.Hom (Pair.discrete A) (Pair.discrete B)) :
    LocallyOfFinitePresentation (comapOfPair hS hT φ) ↔ φ.toRingHom.FinitePresentation :=
  ⟨fun hf ↦ hf.finitePresentation_of_discreteTopology, fun hφ ↦
    locallyOfFinitePresentation_comapOfPair hS hT φ
      ((Pair.Hom.isTopologicallyFiniteType_iff_finiteType_of_plus_eq_top
        Pair.discrete_plus Pair.discrete_plus).mpr (RingHom.FiniteType.of_finitePresentation hφ))
      fun _ ↦ hφ⟩

end Affinoid

end TauCeti.AdicSpace
