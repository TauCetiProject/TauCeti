/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.LocallyNoetherian
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.StronglySheafy

/-!
# Locally strongly sheafy adic spaces

An adic space is *locally strongly sheafy* (`TauCeti.AdicSpace.IsLocallyStronglySheafy`) when every
point has an open Tate affinoid neighbourhood `Spa(A, A⁺)` whose coordinate ring `A` is a complete
Hausdorff strongly sheafy Tate ring (`TauCeti.PreAdicSpace.stronglySheafyAffinoidOpens`,
Hansen–Kedlaya, Definition 4.1), so that its coordinate ring remains sheafy under restricted
power-series extensions.

Since strongly noetherian Tate rings are strongly sheafy
(`TauCeti.Huber.IsStronglySheafy.of_isStronglyNoetherian`), every strongly noetherian Tate affinoid
is a strongly sheafy Tate affinoid and every locally noetherian analytic adic space
(`TauCeti.AdicSpace.IsLocallyNoetherianAnalytic`) is locally strongly sheafy
(`TauCeti.AdicSpace.IsLocallyNoetherianAnalytic.isLocallyStronglySheafy`). Conversely, every locally
strongly sheafy adic space is analytic (`TauCeti.AdicSpace.IsLocallyStronglySheafy.isAnalytic`).
Moreover, by complete-model invariance
(`TauCeti.PreAdicSpace.isStronglySheafyAffinoid_presentationLimitPreAdicSpace`), for any strongly
sheafy Tate Huber pair `(A, A⁺)` (without completeness or Hausdorffness hypotheses on `A`),
`Spa(A, A⁺)` is an adic space and is locally strongly sheafy
(`TauCeti.AdicSpace.IsLocallyStronglySheafy.spa`).

## Main definitions

* `TauCeti.PreAdicSpace.isStronglySheafyAffinoid`,
  `TauCeti.PreAdicSpace.stronglySheafyAffinoidOpens`: strongly sheafy Tate affinoids and open
  subspaces.
* `TauCeti.AdicSpace.IsLocallyStronglySheafy`: locally strongly sheafy analytic adic spaces.

## Main results

* `TauCeti.PreAdicSpace.isStronglySheafyAffinoid_presentationLimitPreAdicSpace`: for any strongly
  sheafy Tate Huber pair `(A, A⁺)`, `Spa(A, A⁺)` is a strongly sheafy Tate affinoid, without
  completeness or Hausdorffness hypotheses on `A`.
* `TauCeti.AdicSpace.IsLocallyNoetherianAnalytic.isLocallyStronglySheafy`: locally noetherian
  analytic adic spaces are locally strongly sheafy.
* `TauCeti.AdicSpace.IsLocallyStronglySheafy.isAnalytic`: locally strongly sheafy adic spaces are
  analytic.
* `TauCeti.AdicSpace.IsLocallyStronglySheafy.spa`: for any strongly sheafy Tate Huber pair
  `(A, A⁺)`, `Spa(A, A⁺)` is locally strongly sheafy, without completeness or Hausdorffness
  hypotheses on `A`.

## References

* [D. Hansen and K. S. Kedlaya, *Sheafiness criteria for Huber rings*], §4, Definition 4.1.
* [K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory: foundations*], §8.2, Remark 8.2.18.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Definition 8.26 and
  Corollary 8.35.
-/

public section

open CategoryTheory TopologicalSpace Topology

namespace TauCeti

open Huber ValuationSpectrum

universe u

/-! ### Strongly sheafy Tate affinoids and locally strongly sheafy adic spaces -/

namespace PreAdicSpace

/-- An object of `𝒱^pre` is a *strongly sheafy Tate affinoid* when it is isomorphic to the
presentation-limit pre-adic space `Spa(A, A⁺)` of a complete Hausdorff Tate Huber pair `(A, A⁺)`
whose ring `A` is strongly sheafy (`TauCeti.Huber.IsStronglySheafy`). -/
def isStronglySheafyAffinoid : ObjectProperty PreAdicSpace.{u} := fun X ↦
  ∃ (A : Type u) (_ : CommRing A) (_ : UniformSpace A) (_ : IsUniformAddGroup A)
    (_ : IsTopologicalRing A) (_ : CompleteSpace A) (_ : T2Space A) (_ : IsTateRing A)
    (_ : IsStronglySheafy A) (S : Pair A) (P : PairOfDefinition A)
    (hP : P.ringOfDefinition ≤ S.plus),
    Nonempty (X ≅ presentationLimitPreAdicSpace P S.plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem hP)

/-- Unfolding lemma for `TauCeti.PreAdicSpace.isStronglySheafyAffinoid`. -/
theorem isStronglySheafyAffinoid_iff (X : PreAdicSpace.{u}) :
    isStronglySheafyAffinoid X ↔
      ∃ (A : Type u) (_ : CommRing A) (_ : UniformSpace A) (_ : IsUniformAddGroup A)
        (_ : IsTopologicalRing A) (_ : CompleteSpace A) (_ : T2Space A) (_ : IsTateRing A)
        (_ : IsStronglySheafy A) (S : Pair A) (P : PairOfDefinition A)
        (hP : P.ringOfDefinition ≤ S.plus),
        Nonempty (X ≅ presentationLimitPreAdicSpace P S.plus
          S.isRingOfIntegralElements.isPowerBounded_of_mem hP) :=
  (Iff.rfl)

/-- Being a strongly sheafy Tate affinoid is invariant under isomorphism in `𝒱^pre`. -/
instance isStronglySheafyAffinoid.instIsClosedUnderIsomorphisms :
    isStronglySheafyAffinoid.{u}.IsClosedUnderIsomorphisms where
  of_iso e := fun ⟨A, iA, uA, hgA, htA, hcA, h2A, hA, hssA, S, P, hP, ⟨e'⟩⟩ ↦
    ⟨A, iA, uA, hgA, htA, hcA, h2A, hA, hssA, S, P, hP, ⟨e.symm ≪≫ e'⟩⟩

/-- A strongly sheafy Tate affinoid is a Tate affinoid. -/
theorem isStronglySheafyAffinoid.isTateAffinoid {X : PreAdicSpace.{u}}
    (hX : isStronglySheafyAffinoid X) : isTateAffinoid X := by
  obtain ⟨A, _, _, _, _, _, _, _, _, S, P, hP, e⟩ := hX
  exact (isTateAffinoid_iff X).mpr ⟨A, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, S, P, hP, e⟩

/-- A strongly sheafy Tate affinoid is affinoid. -/
theorem isStronglySheafyAffinoid.isAffinoid {X : PreAdicSpace.{u}}
    (hX : isStronglySheafyAffinoid X) : isAffinoid X :=
  hX.isTateAffinoid.isAffinoid

/-- A strongly noetherian Tate affinoid is a strongly sheafy Tate affinoid
(`TauCeti.Huber.IsStronglySheafy.of_isStronglyNoetherian`). -/
theorem isStronglyNoetherianAffinoid.isStronglySheafyAffinoid {X : PreAdicSpace.{u}}
    (hX : isStronglyNoetherianAffinoid X) : isStronglySheafyAffinoid X := by
  obtain ⟨A, _, _, _, _, _, _, _, _, S, P, hP, e⟩ := (isStronglyNoetherianAffinoid_iff X).mp hX
  exact ⟨A, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, IsStronglySheafy.of_isStronglyNoetherian, S, P, hP, e⟩

private theorem isStronglySheafyAffinoid_presentationLimitPreAdicSpace_of_completeSpace {A : Type u}
    [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A] [CompleteSpace A]
    [T2Space A] [IsTateRing A] (hA : IsStronglySheafy A) (S : Pair A) (P : PairOfDefinition A)
    (hP : P.ringOfDefinition ≤ S.plus) :
    isStronglySheafyAffinoid (presentationLimitPreAdicSpace P S.plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem hP) :=
  ⟨A, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, hA, S, P, hP, ⟨Iso.refl _⟩⟩

/-- **Complete-model invariance for strongly sheafy Tate pairs**: the presentation-limit pre-adic
space of any strongly sheafy Tate Huber pair `(A, A⁺)` is a strongly sheafy Tate affinoid, without
completeness or Hausdorffness hypotheses on `A`. -/
theorem isStronglySheafyAffinoid_presentationLimitPreAdicSpace {A : Type u} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [IsTateRing A] (hA : IsStronglySheafy A)
    (S : Pair A) (P : PairOfDefinition A) (hP : P.ringOfDefinition ≤ S.plus) :
    isStronglySheafyAffinoid (presentationLimitPreAdicSpace P S.plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem hP) := by
  let hden := P.hasDenominatorPower_denom_one ({1} : Finset A) A
  let _ := P.locUniformSpace ({1} : Finset A) 1 A hden
  have _ := P.isUniformAddGroup_locUniformSpace ({1} : Finset A) 1 A hden
  have _ := P.isTopologicalRing_locUniformSpace ({1} : Finset A) 1 A hden
  have _ := P.isTateRing_completion_locTopology_of_isTateRing ({1} : Finset A) 1 A hden
  have hcomp_ss := P.isStronglySheafy_completion_locTopology_denom_one ({1} : Finset A)
    (by simp [isPowerBounded_one]) hA
  have hmodel :=
    isStronglySheafyAffinoid_presentationLimitPreAdicSpace_of_completeSpace hcomp_ss
      (P.rationalLocalizationPair S hP ({1} : Finset A) 1 A hden)
      (P.completionLocalization ({1} : Finset A) 1 A hden)
      (P.completionLocalization_ringOfDefinition_le_rationalLocalizationPair S hP
        ({1} : Finset A) 1 A hden)
  -- `rationalLocalizationPair` is sealed outside `Pair.lean`, and the `Prop` arguments of
  -- `presentationLimitPreAdicSpace` depend on its `.plus` subring, so rewrite via `simp`.
  simp only [PairOfDefinition.rationalLocalizationPair_plus] at hmodel
  exact ObjectProperty.prop_of_iso isStronglySheafyAffinoid
    (presentationLimitPreAdicSpaceCompleteIso P S.plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem hP A hden).symm hmodel

variable (X : PreAdicSpace.{u})

/-- The *open strongly sheafy Tate affinoids* of an object `X` of `𝒱^pre`: the opens `U` such that
`X` restricted to `U` is a strongly sheafy Tate affinoid. -/
abbrev stronglySheafyAffinoidOpens : Set (Opens X) :=
  X.propOpens isStronglySheafyAffinoid

variable {X}

/-- An open strongly sheafy Tate affinoid is an open Tate affinoid subspace. -/
theorem stronglySheafyAffinoidOpens_subset_tateAffinoidOpens :
    X.stronglySheafyAffinoidOpens ⊆ X.tateAffinoidOpens :=
  fun _ hU ↦ (mem_propOpens_iff _).mpr
    (isStronglySheafyAffinoid.isTateAffinoid ((mem_propOpens_iff _).mp hU))

/-- An open strongly noetherian Tate affinoid is an open strongly sheafy Tate affinoid. -/
theorem stronglyNoetherianAffinoidOpens_subset_stronglySheafyAffinoidOpens :
    X.stronglyNoetherianAffinoidOpens ⊆ X.stronglySheafyAffinoidOpens :=
  fun _ hU ↦ (mem_propOpens_iff _).mpr
    (isStronglyNoetherianAffinoid.isStronglySheafyAffinoid ((mem_propOpens_iff _).mp hU))

end PreAdicSpace

namespace AdicSpace

open PreAdicSpace

/-- **Locally strongly sheafy analytic adic spaces** (Hansen–Kedlaya, §4): an adic space `X` is
*locally strongly sheafy* when every point has an open strongly sheafy Tate affinoid neighbourhood,
that is, an open `U` with `X|_U ≅ Spa(A, A⁺)` for a complete Hausdorff Tate Huber pair `(A, A⁺)`
with `A` strongly sheafy. -/
def IsLocallyStronglySheafy (X : AdicSpace.{u}) : Prop :=
  ∀ x : X.obj, ∃ U ∈ X.obj.stronglySheafyAffinoidOpens, x ∈ U

variable {X Y : AdicSpace.{u}}

/-- Unfolding lemma for `TauCeti.AdicSpace.IsLocallyStronglySheafy`. -/
theorem isLocallyStronglySheafy_iff :
    X.IsLocallyStronglySheafy ↔ ∀ x : X.obj, ∃ U ∈ X.obj.stronglySheafyAffinoidOpens, x ∈ U :=
  (Iff.rfl)

/-- **Locally noetherian analytic adic spaces are locally strongly sheafy**: every strongly
noetherian Tate ring is strongly sheafy (`TauCeti.Huber.IsStronglySheafy.of_isStronglyNoetherian`).
-/
theorem IsLocallyNoetherianAnalytic.isLocallyStronglySheafy
    (h : X.IsLocallyNoetherianAnalytic) : X.IsLocallyStronglySheafy :=
  fun x ↦ let ⟨U, hU, hxU⟩ := isLocallyNoetherianAnalytic_def.mp h x
    ⟨U, stronglyNoetherianAffinoidOpens_subset_stronglySheafyAffinoidOpens hU, hxU⟩

/-- Every locally strongly sheafy adic space is analytic. -/
theorem IsLocallyStronglySheafy.isAnalytic (h : X.IsLocallyStronglySheafy) : X.IsAnalytic :=
  isAnalytic_iff.mpr fun x ↦ let ⟨U, hU, hxU⟩ := h x
    ⟨U, stronglySheafyAffinoidOpens_subset_tateAffinoidOpens hU, hxU⟩

/-- Being locally strongly sheafy is carried back along an isomorphism of adic spaces. -/
theorem IsLocallyStronglySheafy.of_iso (e : Y ≅ X) (hX : X.IsLocallyStronglySheafy) :
    Y.IsLocallyStronglySheafy :=
  exists_mem_propOpens_of_iso isStronglySheafyAffinoid ((ObjectProperty.ι _).mapIso e) hX

/-- Isomorphic adic spaces are locally strongly sheafy together. -/
theorem isLocallyStronglySheafy_iff_of_iso (e : Y ≅ X) :
    Y.IsLocallyStronglySheafy ↔ X.IsLocallyStronglySheafy :=
  ⟨fun hY ↦ hY.of_iso e.symm, fun hX ↦ hX.of_iso e⟩

/-- Any adic space with no points is locally strongly sheafy. -/
theorem isLocallyStronglySheafy_of_isEmpty (X : AdicSpace.{u}) [IsEmpty X.obj] :
    X.IsLocallyStronglySheafy :=
  fun x ↦ IsEmpty.elim ‹IsEmpty X.obj› x

/-- **`Spa(A, A⁺)` is locally strongly sheafy** for every strongly sheafy Tate Huber pair
`(A, A⁺)`. Neither completeness nor Hausdorffness of `A` is required. -/
theorem IsLocallyStronglySheafy.spa {A : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsTateRing A] (hA : IsStronglySheafy A) (S : Pair A)
    (P : PairOfDefinition A) (hP : P.ringOfDefinition ≤ S.plus) :
    IsLocallyStronglySheafy ⟨presentationLimitPreAdicSpace P S.plus
        S.isRingOfIntegralElements.isPowerBounded_of_mem hP,
      letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
      haveI : IsUniformAddGroup A := isUniformAddGroup_of_addCommGroup
      isAdic_presentationLimitPreAdicSpace_of_isSheafyRing P S.isRingOfIntegralElements hP
        hA.isSheafyRing⟩ :=
  fun _ ↦ ⟨⊤, (top_mem_propOpens_iff _ isStronglySheafyAffinoid).mpr
    (isStronglySheafyAffinoid_presentationLimitPreAdicSpace hA S P hP),
    trivial⟩

end AdicSpace

end TauCeti
