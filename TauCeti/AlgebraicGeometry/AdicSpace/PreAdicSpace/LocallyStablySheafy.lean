/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.LocallyStronglySheafy
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.StablySheafy

/-!
# Locally stably sheafy adic spaces

An object of `𝒱^pre` is a *stably sheafy affinoid* (`TauCeti.PreAdicSpace.isStablySheafyAffinoid`)
when it is isomorphic to the presentation-limit pre-adic space `Spa(A, A⁺)` of a complete Hausdorff
Huber pair `(A, A⁺)` whose coordinate ring `A` is stably sheafy (`TauCeti.Huber.IsStablySheafyRing`,
Wedhorn, Definition 8.26), and an adic space `X` is *locally stably sheafy*
(`TauCeti.AdicSpace.IsLocallyStablySheafy`) when every point of `X` has an open stably sheafy
affinoid neighbourhood (`TauCeti.PreAdicSpace.stablySheafyAffinoidOpens`). Unlike
`TauCeti.AdicSpace.IsLocallyStronglySheafy`, neither `IsTateRing` nor analyticity is required on the
coordinate rings, so formal schemes and discrete adic spaces covered by stably sheafy affinoids are
included alongside analytic spaces.

Since completed rational localisations preserve stable sheafiness
(`TauCeti.Huber.PairOfDefinition.isStablySheafyRing_completion_locTopology`), the open stably sheafy
affinoids form a basis of `Spa(A, A⁺)` for any stably sheafy Huber pair `(A, A⁺)` without
completeness or Hausdorffness hypotheses on `A`, and therefore form a basis of every locally stably
sheafy adic space (`TauCeti.AdicSpace.IsLocallyStablySheafy.isBasis_stablySheafyAffinoidOpens`).
Open subspaces of locally stably sheafy adic spaces remain locally stably sheafy
(`TauCeti.AdicSpace.IsLocallyStablySheafy.of_isOpenImmersion`).

Locally stably sheafy adic spaces serve as the base-change factors for fibre products of adic spaces
along morphisms locally of weakly finite type and adic base-change morphisms (Wedhorn, Theorem 8.56
and Remark 8.57(1)). Every locally noetherian analytic adic space is locally stably sheafy
(`TauCeti.AdicSpace.IsLocallyNoetherianAnalytic.isLocallyStablySheafy`), and conversely any analytic
locally stably sheafy adic space is locally strongly sheafy
(`TauCeti.AdicSpace.IsLocallyStablySheafy.isLocallyStronglySheafy_of_isAnalytic`).

## Main definitions

* `TauCeti.PreAdicSpace.isStablySheafyAffinoid`: objects of `𝒱^pre` isomorphic to `Spa(A, A⁺)` for a
  complete Hausdorff Huber pair with `A` stably sheafy.
* `TauCeti.PreAdicSpace.stablySheafyAffinoidOpens`: the open stably sheafy affinoids.
* `TauCeti.AdicSpace.IsLocallyStablySheafy`: locally stably sheafy adic spaces.

## Main results

* `TauCeti.ValuationSpectrum.spaBasicOpen_mem_stablySheafyAffinoidOpens` and
  `TauCeti.ValuationSpectrum.isBasis_stablySheafyAffinoidOpens_presentationLimitPreAdicSpace`: for a
  stably sheafy Huber ring `A`, rational subsets of `Spa(A, A⁺)` are open stably sheafy affinoids
  and the open stably sheafy affinoids form a basis of `Spa(A, A⁺)`.
* `spaBasicOpen_mem_stronglySheafyAffinoidOpens_of_isTopologicallyNilpotent` (in
  `TauCeti.ValuationSpectrum`): rational subsets of `Spa(A, A⁺)` at a topologically nilpotent
  denominator over a stably sheafy Huber ring `A` are open strongly sheafy Tate affinoids.
* `TauCeti.PreAdicSpace.isStablySheafyAffinoid_presentationLimitPreAdicSpace`: for any stably sheafy
  Huber pair `(A, A⁺)`, `Spa(A, A⁺)` is a stably sheafy affinoid, without completeness or
  Hausdorffness hypotheses on `A`.
* `TauCeti.AdicSpace.IsLocallyStablySheafy.isBasis_stablySheafyAffinoidOpens` and
  `TauCeti.AdicSpace.isLocallyStablySheafy_iff_isBasis_stablySheafyAffinoidOpens`: on a locally
  stably sheafy adic space, the open stably sheafy affinoids form a basis of the topology, and
  conversely.
* `TauCeti.AdicSpace.IsLocallyStablySheafy.of_isOpenImmersion`: open immersions into locally stably
  sheafy adic spaces have locally stably sheafy sources.
* `TauCeti.AdicSpace.IsLocallyStablySheafy.spa`: `Spa(A, A⁺)` is locally stably sheafy for any
  stably sheafy Huber pair `(A, A⁺)`.
* `TauCeti.AdicSpace.IsLocallyNoetherianAnalytic.isLocallyStablySheafy` and
  `TauCeti.AdicSpace.IsLocallyNoetherian.isLocallyStablySheafy_analyticLocus`: locally noetherian
  analytic adic spaces, and the analytic locus of any locally noetherian adic space, are locally
  stably sheafy.
* `TauCeti.AdicSpace.IsLocallyStablySheafy.isLocallyStronglySheafy_of_isAnalytic` and
  `TauCeti.AdicSpace.IsLocallyStablySheafy.isLocallyStronglySheafy_analyticLocus`: an analytic
  locally stably sheafy adic space (in particular, the analytic locus of any locally stably sheafy
  adic space) is locally strongly sheafy.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Definition 8.26, Remark 8.27,
  Corollary 8.35, Definition 8.54, Theorem 8.56, and Remark 8.57(1).
-/

public section

open CategoryTheory TopologicalSpace Topology

namespace TauCeti

open Huber ValuationSpectrum

universe u

namespace PreAdicSpace

/-! ### Stably sheafy affinoids -/

/-- An object of `𝒱^pre` is a *stably sheafy affinoid* when it is isomorphic to the
presentation-limit pre-adic space `Spa(A, A⁺)` of a complete Hausdorff Huber pair `(A, A⁺)` whose
coordinate ring `A` is stably sheafy (`TauCeti.Huber.IsStablySheafyRing`). -/
def isStablySheafyAffinoid : ObjectProperty PreAdicSpace.{u} := fun X ↦
  ∃ (A : Type u) (_ : CommRing A) (_ : UniformSpace A) (_ : IsUniformAddGroup A)
    (_ : IsTopologicalRing A) (_ : CompleteSpace A) (_ : T2Space A) (_ : IsHuberRing A)
    (_ : IsStablySheafyRing.{u, u} A) (S : Pair A) (P : PairOfDefinition A)
    (hP : P.ringOfDefinition ≤ S.plus),
    Nonempty (X ≅ presentationLimitPreAdicSpace P S.plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem hP)

/-- Unfolding lemma for `TauCeti.PreAdicSpace.isStablySheafyAffinoid`. -/
theorem isStablySheafyAffinoid_iff (X : PreAdicSpace.{u}) :
    isStablySheafyAffinoid X ↔
      ∃ (A : Type u) (_ : CommRing A) (_ : UniformSpace A) (_ : IsUniformAddGroup A)
        (_ : IsTopologicalRing A) (_ : CompleteSpace A) (_ : T2Space A) (_ : IsHuberRing A)
        (_ : IsStablySheafyRing.{u, u} A) (S : Pair A) (P : PairOfDefinition A)
        (hP : P.ringOfDefinition ≤ S.plus),
        Nonempty (X ≅ presentationLimitPreAdicSpace P S.plus
          S.isRingOfIntegralElements.isPowerBounded_of_mem hP) :=
  (Iff.rfl)

/-- Being a stably sheafy affinoid is invariant under isomorphism in `𝒱^pre`. -/
instance isStablySheafyAffinoid.instIsClosedUnderIsomorphisms :
    isStablySheafyAffinoid.{u}.IsClosedUnderIsomorphisms where
  of_iso e := fun ⟨A, iA, uA, hgA, htA, hcA, h2A, hA, hssA, S, P, hP, ⟨e'⟩⟩ ↦
    ⟨A, iA, uA, hgA, htA, hcA, h2A, hA, hssA, S, P, hP, ⟨e.symm ≪≫ e'⟩⟩

/-- A stably sheafy affinoid is affinoid. -/
theorem isStablySheafyAffinoid.isAffinoid {X : PreAdicSpace.{u}}
    (hX : isStablySheafyAffinoid X) : isAffinoid X := by
  obtain ⟨A, _, _, _, _, _, _, _, _, S, P, hP, e⟩ := hX
  exact (isAffinoid_iff_exists_complete X).mpr
    ⟨A, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, S, P, hP, e⟩

/-- Every stably sheafy affinoid is an adic space (`isAdic`). -/
theorem isStablySheafyAffinoid.isAdic {X : PreAdicSpace.{u}}
    (hX : isStablySheafyAffinoid X) : isAdic X := by
  obtain ⟨_, _, _, _, _, _, _, _, hA, S, P, hP, ⟨e⟩⟩ := hX
  exact ObjectProperty.prop_of_iso PreAdicSpace.isAdic e.symm
    (isAdic_presentationLimitPreAdicSpace_of_isSheafyRing P S.isRingOfIntegralElements hP
      hA.isSheafyRing)

/-- A strongly noetherian Tate affinoid is a stably sheafy affinoid
(`TauCeti.Huber.isStablySheafyRing_of_isStronglyNoetherian`). -/
theorem isStronglyNoetherianAffinoid.isStablySheafyAffinoid {X : PreAdicSpace.{u}}
    (hX : isStronglyNoetherianAffinoid X) : isStablySheafyAffinoid X := by
  obtain ⟨A, _, _, _, _, _, _, _, _, S, P, hP, e⟩ := (isStronglyNoetherianAffinoid_iff X).mp hX
  exact ⟨A, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, isStablySheafyRing_of_isStronglyNoetherian, S, P, hP, e⟩

private theorem isStablySheafyAffinoid_presentationLimitPreAdicSpace_of_completeSpace {A : Type u}
    [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A] [CompleteSpace A]
    [T2Space A] [IsHuberRing A] (hA : IsStablySheafyRing.{u, u} A) (S : Pair A)
    (P : PairOfDefinition A) (hP : P.ringOfDefinition ≤ S.plus) :
    isStablySheafyAffinoid (presentationLimitPreAdicSpace P S.plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem hP) :=
  ⟨A, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, hA, S, P, hP, ⟨Iso.refl _⟩⟩

variable (X : PreAdicSpace.{u})

/-- The *open stably sheafy affinoids* of an object `X` of `𝒱^pre`: the opens `U` such that `X`
restricted to `U` is a stably sheafy affinoid. -/
abbrev stablySheafyAffinoidOpens : Set (Opens X) :=
  X.propOpens isStablySheafyAffinoid

variable {X}

/-- An open stably sheafy affinoid is an open affinoid subspace. -/
theorem stablySheafyAffinoidOpens_subset_affinoidOpens :
    X.stablySheafyAffinoidOpens ⊆ X.affinoidOpens :=
  fun _ hU ↦ (mem_propOpens_iff _).mpr
    (isStablySheafyAffinoid.isAffinoid ((mem_propOpens_iff _).mp hU))

/-- An open strongly noetherian Tate affinoid is an open stably sheafy affinoid. -/
theorem stronglyNoetherianAffinoidOpens_subset_stablySheafyAffinoidOpens :
    X.stronglyNoetherianAffinoidOpens ⊆ X.stablySheafyAffinoidOpens :=
  fun _ hU ↦ (mem_propOpens_iff _).mpr
    (isStronglyNoetherianAffinoid.isStablySheafyAffinoid ((mem_propOpens_iff _).mp hU))

end PreAdicSpace

namespace ValuationSpectrum

open PairOfDefinition

variable {A : Type u} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]
  [IsHuberRing A] (P : PairOfDefinition A) (Aplus : Subring A)
  (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) (hP : P.ringOfDefinition ≤ Aplus)

/-- **Rational subsets of `Spa(A, A⁺)` over a stably sheafy Huber ring `A` are open stably sheafy
affinoids.** For `T` spanning an open ideal, the restriction of `Spa(A, A⁺)` to `R(T/s)` is
`Spa(A⟨T/s⟩, A_U⁺)` (`restrictSpaBasicOpenIso`), and `A⟨T/s⟩` is a complete Hausdorff stably sheafy
Huber ring (`isStablySheafyRing_completion_locTopology`). Neither completeness nor Hausdorffness of
`A` is required. -/
theorem spaBasicOpen_mem_stablySheafyAffinoidOpens (hA : IsStablySheafyRing.{u, u} A)
    {T : Finset A} {s : A} (hT : IsOpen (Ideal.span (T : Set A) : Set A)) :
    spaBasicOpen Aplus T s ∈
      (presentationLimitPreAdicSpace P Aplus hAplus hP).stablySheafyAffinoidOpens := by
  refine spaBasicOpen_mem_propOpens P Aplus hAplus hP PreAdicSpace.isStablySheafyAffinoid hT ?_
  intro _ _ _
  let hden := hasDenominatorPower_of_isOpen_span P T s (Localization.Away s) hT
  have hss := isStablySheafyRing_completion_locTopology P
    (Ideal.isOpen_of_isOpen_subideal (Ideal.span_mono (Set.subset_insert _ _)) hT) _ hden hA
  exact PreAdicSpace.isStablySheafyAffinoid_presentationLimitPreAdicSpace_of_completeSpace hss _ _
    (completionLocalization_ringOfDefinition_le_completedPlusPair P Aplus hAplus hP T s _ hden)

/-- **The open stably sheafy affinoids form a basis of `Spa(A, A⁺)`** when `A` is stably sheafy,
since the rational opens do. -/
theorem isBasis_stablySheafyAffinoidOpens_presentationLimitPreAdicSpace
    (hA : IsStablySheafyRing.{u, u} A) :
    Opens.IsBasis (presentationLimitPreAdicSpace P Aplus hAplus hP).stablySheafyAffinoidOpens :=
  isBasis_propOpens_presentationLimitPreAdicSpace P Aplus hAplus hP
    PreAdicSpace.isStablySheafyAffinoid
    fun hT ↦ spaBasicOpen_mem_stablySheafyAffinoidOpens P Aplus hAplus hP hA hT

/-- **Rational subsets at a topologically nilpotent denominator over a stably sheafy Huber ring `A`
are open strongly sheafy Tate affinoids.** If `T` spans an open ideal and `s` is topologically
nilpotent, `A⟨T/s⟩` is both Tate (`isTateRing_completion_locTopology_of_isTopologicallyNilpotent`)
and stably sheafy (`isStablySheafyRing_completion_locTopology`), hence strongly sheafy
(`IsStronglySheafy.of_isStablySheafyRing`). -/
theorem spaBasicOpen_mem_stronglySheafyAffinoidOpens_of_isTopologicallyNilpotent
    (hA : IsStablySheafyRing.{u, u} A) {T : Finset A} {s : A}
    (hT : IsOpen (Ideal.span (T : Set A) : Set A)) (hs : IsTopologicallyNilpotent s) :
    spaBasicOpen Aplus T s ∈
      (presentationLimitPreAdicSpace P Aplus hAplus hP).stronglySheafyAffinoidOpens := by
  refine spaBasicOpen_mem_propOpens P Aplus hAplus hP PreAdicSpace.isStronglySheafyAffinoid hT ?_
  intro _ _ _
  let hden := P.hasDenominatorPower_of_isOpen_span T s (Localization.Away s) hT
  let _ := locUniformSpace P T s (Localization.Away s) hden
  have := isUniformAddGroup_locUniformSpace P T s (Localization.Away s) hden
  have := isTopologicalRing_locUniformSpace P T s (Localization.Away s) hden
  have := isTateRing_completion_locTopology_of_isTopologicallyNilpotent P T s _ hden hs
  have hss := isStablySheafyRing_completion_locTopology P
    (Ideal.isOpen_of_isOpen_subideal (Ideal.span_mono (Set.subset_insert _ _)) hT) _ hden hA
  exact PreAdicSpace.isStronglySheafyAffinoid_presentationLimitPreAdicSpace
    (.of_isStablySheafyRing hss) _ _
    (completionLocalization_ringOfDefinition_le_completedPlusPair P Aplus hAplus hP T s _ hden)

/-- **Every analytic point of `Spa(A, A⁺)` over a stably sheafy Huber ring `A` has an open strongly
sheafy Tate affinoid neighbourhood.** An analytic point lies in a rational subset `R(T/g)` with `g`
topologically nilpotent, so `A⟨T/g⟩` is both Tate and stably sheafy, hence strongly sheafy
(`IsStronglySheafy.of_isStablySheafyRing`). -/
theorem exists_mem_stronglySheafyAffinoidOpens_of_mem_analyticPoints_presentationLimitPreAdicSpace
    (hA : IsStablySheafyRing.{u, u} A)
    {x : presentationLimitPreAdicSpace P Aplus hAplus hP}
    (hx : x ∈ (presentationLimitPreAdicSpace P Aplus hAplus hP).analyticPoints) :
    ∃ U ∈ (presentationLimitPreAdicSpace P Aplus hAplus hP).stronglySheafyAffinoidOpens,
      x ∈ U :=
  ValuationSpectrum.exists_mem_propOpens_of_mem_analyticPoints P Aplus hAplus hP
    PreAdicSpace.isStronglySheafyAffinoid
    (fun hT hs ↦ spaBasicOpen_mem_stronglySheafyAffinoidOpens_of_isTopologicallyNilpotent
      P Aplus hAplus hP hA hT hs) hx

end ValuationSpectrum

namespace PreAdicSpace

/-- **Complete-model invariance for stably sheafy Huber pairs**: the presentation-limit pre-adic
space of any stably sheafy Huber pair `(A, A⁺)` is a stably sheafy affinoid, without completeness or
Hausdorffness hypotheses on `A`. -/
theorem isStablySheafyAffinoid_presentationLimitPreAdicSpace {A : Type u} [CommRing A]
    [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A] [IsHuberRing A]
    (hA : IsStablySheafyRing.{u, u} A) (S : Pair A) (P : PairOfDefinition A)
    (hP : P.ringOfDefinition ≤ S.plus) :
    isStablySheafyAffinoid (presentationLimitPreAdicSpace P S.plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem hP) :=
  (top_mem_propOpens_iff _ isStablySheafyAffinoid).mp <|
    top_mem_propOpens_presentationLimitPreAdicSpace P S.plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem hP isStablySheafyAffinoid
      fun hT ↦ spaBasicOpen_mem_stablySheafyAffinoidOpens P S.plus _ hP hA hT

/-- **On a stably sheafy affinoid the open stably sheafy affinoids form a basis.** -/
theorem isStablySheafyAffinoid.isBasis_stablySheafyAffinoidOpens {X : PreAdicSpace.{u}}
    (hX : isStablySheafyAffinoid X) : Opens.IsBasis X.stablySheafyAffinoidOpens :=
  let ⟨_, _, _, _, _, _, _, _, hA, S, P, hP, ⟨e⟩⟩ := hX
  isBasis_propOpens_of_iso isStablySheafyAffinoid e
    (isBasis_stablySheafyAffinoidOpens_presentationLimitPreAdicSpace P S.plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem hP hA)

end PreAdicSpace

/-! ### Locally stably sheafy adic spaces -/

namespace AdicSpace

open PreAdicSpace

/-- **Locally stably sheafy adic spaces** (Wedhorn, Definition 8.26, Definition 8.54, Theorem 8.56,
and Remark 8.57(1)): an adic space `X` is *locally stably sheafy* when every point has an open
stably sheafy affinoid neighbourhood, that is, an open `U` with `X|_U ≅ Spa(A, A⁺)` for a complete
Hausdorff Huber pair `(A, A⁺)` with `A` stably sheafy (`TauCeti.Huber.IsStablySheafyRing`). -/
def IsLocallyStablySheafy (X : AdicSpace.{u}) : Prop :=
  ∀ x : X.obj, ∃ U ∈ X.obj.stablySheafyAffinoidOpens, x ∈ U

variable {X Y : AdicSpace.{u}}

/-- Unfolding lemma for `TauCeti.AdicSpace.IsLocallyStablySheafy`. -/
theorem isLocallyStablySheafy_iff :
    X.IsLocallyStablySheafy ↔ ∀ x : X.obj, ∃ U ∈ X.obj.stablySheafyAffinoidOpens, x ∈ U :=
  (Iff.rfl)

/-- **The open stably sheafy affinoids form a basis of the topology** on a locally stably sheafy
adic space. -/
theorem IsLocallyStablySheafy.isBasis_stablySheafyAffinoidOpens (hX : X.IsLocallyStablySheafy) :
    Opens.IsBasis X.obj.stablySheafyAffinoidOpens :=
  isBasis_propOpens isStablySheafyAffinoid
    (fun _ ↦ isStablySheafyAffinoid.isBasis_stablySheafyAffinoidOpens) hX

/-- An adic space is locally stably sheafy exactly when its open stably sheafy affinoids form a
basis of its topology. -/
theorem isLocallyStablySheafy_iff_isBasis_stablySheafyAffinoidOpens :
    X.IsLocallyStablySheafy ↔ Opens.IsBasis X.obj.stablySheafyAffinoidOpens :=
  ⟨IsLocallyStablySheafy.isBasis_stablySheafyAffinoidOpens, exists_mem_propOpens_of_isBasis⟩

/-- **Open subspaces of locally stably sheafy adic spaces are locally stably sheafy**: the source of
an open immersion into a locally stably sheafy adic space is locally stably sheafy. -/
theorem IsLocallyStablySheafy.of_isOpenImmersion (f : Y ⟶ X) [IsOpenImmersion f.hom]
    (hX : X.IsLocallyStablySheafy) : Y.IsLocallyStablySheafy :=
  exists_mem_propOpens_of_iso isStablySheafyAffinoid (IsOpenImmersion.isoRestrict f.hom)
    (exists_mem_propOpens_restrict f.hom.isOpenEmbedding isStablySheafyAffinoid
      hX.isBasis_stablySheafyAffinoidOpens)

/-- Being locally stably sheafy is carried back along an isomorphism of adic spaces. -/
theorem IsLocallyStablySheafy.of_iso (e : Y ≅ X) (hX : X.IsLocallyStablySheafy) :
    Y.IsLocallyStablySheafy :=
  hX.of_isOpenImmersion e.hom

/-- Isomorphic adic spaces are locally stably sheafy together. -/
theorem isLocallyStablySheafy_iff_of_iso (e : Y ≅ X) :
    Y.IsLocallyStablySheafy ↔ X.IsLocallyStablySheafy :=
  ⟨fun hY ↦ hY.of_iso e.symm, fun hX ↦ hX.of_iso e⟩

/-- Any adic space with no points is locally stably sheafy. -/
theorem isLocallyStablySheafy_of_isEmpty (X : AdicSpace.{u}) [IsEmpty X.obj] :
    X.IsLocallyStablySheafy :=
  fun x ↦ IsEmpty.elim ‹IsEmpty X.obj› x

/-- **`Spa(A, A⁺)` is locally stably sheafy** for every stably sheafy Huber pair `(A, A⁺)`. Neither
completeness nor Hausdorffness of `A` is required. -/
theorem IsLocallyStablySheafy.spa {A : Type u} [CommRing A] [UniformSpace A] [IsUniformAddGroup A]
    [IsTopologicalRing A] [IsHuberRing A] (hA : IsStablySheafyRing.{u, u} A) (S : Pair A)
    (P : PairOfDefinition A) (hP : P.ringOfDefinition ≤ S.plus) :
    IsLocallyStablySheafy ⟨presentationLimitPreAdicSpace P S.plus
        S.isRingOfIntegralElements.isPowerBounded_of_mem hP,
      isAdic_presentationLimitPreAdicSpace_of_isSheafyRing P S.isRingOfIntegralElements hP
        hA.isSheafyRing⟩ :=
  isLocallyStablySheafy_iff_isBasis_stablySheafyAffinoidOpens.mpr
    (isBasis_stablySheafyAffinoidOpens_presentationLimitPreAdicSpace P S.plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem hP hA)

/-! ### Comparison with locally noetherian analytic and locally strongly sheafy adic spaces -/

/-- **Locally noetherian analytic adic spaces are locally stably sheafy**: every strongly noetherian
Tate ring is stably sheafy (`TauCeti.Huber.isStablySheafyRing_of_isStronglyNoetherian`). -/
theorem IsLocallyNoetherianAnalytic.isLocallyStablySheafy
    (h : X.IsLocallyNoetherianAnalytic) : X.IsLocallyStablySheafy :=
  fun x ↦ let ⟨U, hU, hxU⟩ := isLocallyNoetherianAnalytic_def.mp h x
    ⟨U, stronglyNoetherianAffinoidOpens_subset_stablySheafyAffinoidOpens hU, hxU⟩

/-- **The analytic locus of a locally noetherian adic space is locally stably sheafy.** -/
theorem IsLocallyNoetherian.isLocallyStablySheafy_analyticLocus (hX : X.IsLocallyNoetherian) :
    X.analyticLocus.IsLocallyStablySheafy :=
  hX.isLocallyNoetherianAnalytic_analyticLocus.isLocallyStablySheafy

/-- **Every analytic point of a locally stably sheafy adic space has an open strongly sheafy Tate
affinoid neighbourhood.** -/
theorem IsLocallyStablySheafy.exists_mem_stronglySheafyAffinoidOpens_of_mem_analyticPoints
    (hX : X.IsLocallyStablySheafy) {x : X.obj} (hx : x ∈ X.obj.analyticPoints) :
    ∃ V ∈ X.obj.stronglySheafyAffinoidOpens, x ∈ V := by
  obtain ⟨U, hU, hxU⟩ := isLocallyStablySheafy_iff.mp hX x
  obtain ⟨_, _, _, _, _, _, _, _, hA, S, P, hP, ⟨e⟩⟩ :=
    (isStablySheafyAffinoid_iff _).mp ((mem_propOpens_iff _).mp hU)
  exact PreAdicSpace.exists_mem_propOpens_of_mem_analyticPoints isStronglySheafyAffinoid hx hxU
    P S.plus S.isRingOfIntegralElements.isPowerBounded_of_mem hP e fun hT hs ↦
      spaBasicOpen_mem_stronglySheafyAffinoidOpens_of_isTopologicallyNilpotent P S.plus _ hP hA hT
        hs

/-- **An analytic locally stably sheafy adic space is locally strongly sheafy**: every point is
analytic and therefore admits a strongly sheafy Tate affinoid neighbourhood. -/
theorem IsLocallyStablySheafy.isLocallyStronglySheafy_of_isAnalytic
    (ha : X.IsAnalytic) (hX : X.IsLocallyStablySheafy) : X.IsLocallyStronglySheafy :=
  isLocallyStronglySheafy_iff.mpr fun x ↦
    hX.exists_mem_stronglySheafyAffinoidOpens_of_mem_analyticPoints (ha.mem_analyticPoints x)

/-- **The analytic locus of a locally stably sheafy adic space is locally strongly sheafy.** -/
theorem IsLocallyStablySheafy.isLocallyStronglySheafy_analyticLocus
    (hX : X.IsLocallyStablySheafy) : X.analyticLocus.IsLocallyStronglySheafy :=
  (hX.of_isOpenImmersion (analyticLocus.ι X)).isLocallyStronglySheafy_of_isAnalytic
    (isAnalytic_analyticLocus X)

end AdicSpace

end TauCeti
