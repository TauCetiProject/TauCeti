/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.LocallyNoetherian
public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.LocallyTate
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.StronglySheafy
import TauCeti.RingTheory.Huber.LocalizationTopology.Noetherian
import TauCeti.RingTheory.Huber.LocalizationTopology.Trivial
import TauCeti.RingTheory.Huber.NoetherianType.Tate

/-!
# Locally noetherian analytic and locally strongly sheafy adic spaces

Étale geometry on adic spaces requires open Tate affinoid charts whose coordinate rings remain
sheafy after passing to finite étale and restricted power-series extensions. Two space-level
classes provide these charts:

* `TauCeti.AdicSpace.IsLocallyNoetherianAnalytic`: every point has an open affinoid neighbourhood
  `Spa(A, A⁺)` whose coordinate ring `A` is a complete Hausdorff strongly noetherian Tate ring
  (`TauCeti.PreAdicSpace.stronglyNoetherianAffinoidOpens`). This is the analytic subclass of
  Huber's locally noetherian adic spaces (`TauCeti.AdicSpace.IsLocallyNoetherian`).
* `TauCeti.AdicSpace.IsLocallyStronglySheafy`: every point has an open affinoid neighbourhood
  `Spa(A, A⁺)` whose coordinate ring `A` is a complete Hausdorff strongly sheafy Tate ring
  (`TauCeti.PreAdicSpace.stronglySheafyAffinoidOpens`, Hansen–Kedlaya, Definition 4.1).

The central comparison theorem (`TauCeti.AdicSpace.isLocallyNoetherianAnalytic_iff`) identifies
`IsLocallyNoetherianAnalytic X` with the conjunction `X.IsLocallyNoetherian ∧ X.IsAnalytic`. A
strongly noetherian Tate chart is both Tate and of noetherian type, giving the forward implication.
Conversely, if `X` is locally noetherian and analytic, every point `x` is analytic and lies in an
open affinoid `V ≅ Spa(A, A⁺)` with `A` of noetherian type; refining inside `V` to a standard
analytic rational open `R(G/g)` with `g` topologically nilpotent yields a complete Hausdorff
coordinate ring `A⟨G/g⟩` that is simultaneously Tate and of noetherian type, hence strongly
noetherian (`TauCeti.Huber.IsNoetherianType.isStronglyNoetherian`). Consequently open subspaces of
locally noetherian analytic spaces are locally noetherian analytic, and the analytic locus
`X.analyticLocus` of any locally noetherian adic space `X` is locally noetherian analytic.

Since strongly noetherian Tate rings are strongly sheafy
(`TauCeti.Huber.IsStronglySheafy.of_isStronglyNoetherian`), every locally noetherian analytic adic
space is locally strongly sheafy
(`TauCeti.AdicSpace.IsLocallyNoetherianAnalytic.isLocallyStronglySheafy`), and every locally
strongly sheafy adic space is analytic (`TauCeti.AdicSpace.IsLocallyStronglySheafy.isAnalytic`).
Moreover, for any strongly sheafy Tate Huber pair `(A, A⁺)` (without completeness or Hausdorffness
hypotheses on `A`), `Spa(A, A⁺)` is an adic space and is locally strongly sheafy.

## Main definitions

* `TauCeti.PreAdicSpace.isStronglyNoetherianAffinoid`,
  `TauCeti.PreAdicSpace.stronglyNoetherianAffinoidOpens`: strongly noetherian Tate affinoids and
  open subspaces.
* `TauCeti.AdicSpace.IsLocallyNoetherianAnalytic`: locally noetherian analytic adic spaces.
* `TauCeti.PreAdicSpace.isStronglySheafyAffinoid`,
  `TauCeti.PreAdicSpace.stronglySheafyAffinoidOpens`: strongly sheafy Tate affinoids and open
  subspaces.
* `TauCeti.AdicSpace.IsLocallyStronglySheafy`: locally strongly sheafy analytic adic spaces.

## Main results

* `TauCeti.AdicSpace.isLocallyNoetherianAnalytic_iff`: `X` is locally noetherian analytic if and
  only if `X` is locally noetherian and analytic, with projections
  `TauCeti.AdicSpace.IsLocallyNoetherianAnalytic.isLocallyNoetherian`,
  `TauCeti.AdicSpace.IsLocallyNoetherianAnalytic.isAnalytic` and constructor
  `TauCeti.AdicSpace.IsLocallyNoetherianAnalytic.of_isLocallyNoetherian_of_isAnalytic`.
* `TauCeti.AdicSpace.IsLocallyNoetherianAnalytic.of_isOpenImmersion` and
  `TauCeti.AdicSpace.IsLocallyNoetherian.isLocallyNoetherianAnalytic_analyticLocus`: open
  immersions and the analytic locus of a locally noetherian adic space.
* `TauCeti.AdicSpace.IsLocallyNoetherianAnalytic.isLocallyStronglySheafy`: locally noetherian
  analytic adic spaces are locally strongly sheafy.
* `TauCeti.ValuationSpectrum.isAdic_presentationLimitPreAdicSpace_of_isStronglySheafy` and
  `TauCeti.AdicSpace.IsLocallyStronglySheafy.spa`: the adic spectrum of a strongly sheafy Tate
  Huber pair is an adic space and is locally strongly sheafy.

## References

* [D. Hansen and K. S. Kedlaya, *Sheafiness criteria for Huber rings*], §4, Definition 4.1.
* R. Huber, *A generalization of formal schemes and rigid analytic varieties*, Math. Z. 217
  (1994), §3, Corollary 3.4 and Propositions 3.6 to 3.8.
* R. Huber, *Étale cohomology of rigid analytic varieties and adic spaces*, Aspects of
  Mathematics E30 (1996), §1.1.
* [K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory: foundations*], §8.2, Remark 8.2.18.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Remark 6.37, Definition 8.26
  and Corollary 8.35.
-/

public section

open CategoryTheory TopologicalSpace Topology

namespace TauCeti

open Huber ValuationSpectrum

universe u

/-! ### Strongly noetherian Tate affinoids -/

namespace PreAdicSpace

/-- An object of `𝒱^pre` is a *strongly noetherian Tate affinoid* when it is isomorphic to the
presentation-limit pre-adic space `Spa(A, A⁺)` of a complete Hausdorff strongly noetherian Tate
Huber pair `(A, A⁺)`. -/
def isStronglyNoetherianAffinoid : ObjectProperty PreAdicSpace.{u} := fun X ↦
  ∃ (A : Type u) (_ : CommRing A) (_ : UniformSpace A) (_ : IsUniformAddGroup A)
    (_ : IsTopologicalRing A) (_ : CompleteSpace A) (_ : T2Space A) (_ : IsTateRing A)
    (_ : IsStronglyNoetherian A) (S : Pair A) (P : PairOfDefinition A)
    (hP : P.ringOfDefinition ≤ S.plus),
    Nonempty (X ≅ presentationLimitPreAdicSpace P S.plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem hP)

/-- Unfolding lemma for `TauCeti.PreAdicSpace.isStronglyNoetherianAffinoid`. -/
theorem isStronglyNoetherianAffinoid_iff (X : PreAdicSpace.{u}) :
    isStronglyNoetherianAffinoid X ↔
      ∃ (A : Type u) (_ : CommRing A) (_ : UniformSpace A) (_ : IsUniformAddGroup A)
        (_ : IsTopologicalRing A) (_ : CompleteSpace A) (_ : T2Space A) (_ : IsTateRing A)
        (_ : IsStronglyNoetherian A) (S : Pair A) (P : PairOfDefinition A)
        (hP : P.ringOfDefinition ≤ S.plus),
        Nonempty (X ≅ presentationLimitPreAdicSpace P S.plus
          S.isRingOfIntegralElements.isPowerBounded_of_mem hP) :=
  (Iff.rfl)

/-- Being a strongly noetherian Tate affinoid is invariant under isomorphism in `𝒱^pre`. -/
instance isStronglyNoetherianAffinoid.instIsClosedUnderIsomorphisms :
    isStronglyNoetherianAffinoid.{u}.IsClosedUnderIsomorphisms where
  of_iso e := fun ⟨A, iA, uA, hgA, htA, hcA, h2A, hA, hsnA, S, P, hP, ⟨e'⟩⟩ ↦
    ⟨A, iA, uA, hgA, htA, hcA, h2A, hA, hsnA, S, P, hP, ⟨e.symm ≪≫ e'⟩⟩

/-- A strongly noetherian Tate affinoid is a Tate affinoid. -/
theorem isStronglyNoetherianAffinoid.isTateAffinoid {X : PreAdicSpace.{u}}
    (hX : isStronglyNoetherianAffinoid X) : isTateAffinoid X := by
  obtain ⟨A, _, _, _, _, _, _, _, _, S, P, hP, e⟩ := hX
  exact (isTateAffinoid_iff X).mpr ⟨A, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, S, P, hP, e⟩

/-- A strongly noetherian Tate affinoid is an affinoid of noetherian type. -/
theorem isStronglyNoetherianAffinoid.isNoetherianAffinoid {X : PreAdicSpace.{u}}
    (hX : isStronglyNoetherianAffinoid X) : isNoetherianAffinoid X := by
  obtain ⟨A, _, _, _, _, _, _, _, _, S, P, hP, e⟩ := hX
  exact (isNoetherianAffinoid_iff X).mpr ⟨A, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, S, P, hP, e⟩

/-- A strongly noetherian Tate affinoid is affinoid. -/
theorem isStronglyNoetherianAffinoid.isAffinoid {X : PreAdicSpace.{u}}
    (hX : isStronglyNoetherianAffinoid X) : isAffinoid X :=
  hX.isTateAffinoid.isAffinoid

/-- The presentation-limit pre-adic space of a complete Hausdorff Tate Huber pair of noetherian
type (in particular, of a complete Hausdorff strongly noetherian Tate pair) is a strongly
noetherian Tate affinoid: on Tate rings, noetherian type is strong noetherianness
(`TauCeti.Huber.IsNoetherianType.isStronglyNoetherian`). -/
theorem isStronglyNoetherianAffinoid_presentationLimitPreAdicSpace {A : Type u} [CommRing A]
    [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A] [CompleteSpace A] [T2Space A]
    [IsTateRing A] [IsNoetherianType A] (S : Pair A) (P : PairOfDefinition A)
    (hP : P.ringOfDefinition ≤ S.plus) :
    isStronglyNoetherianAffinoid (presentationLimitPreAdicSpace P S.plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem hP) :=
  have := IsNoetherianType.isStronglyNoetherian (A := A)
  ⟨A, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, S, P, hP, ⟨Iso.refl _⟩⟩

variable (X : PreAdicSpace.{u})

/-- The *open strongly noetherian Tate affinoids* of an object `X` of `𝒱^pre`: the opens `U` such
that `X` restricted to `U` is a strongly noetherian Tate affinoid. -/
abbrev stronglyNoetherianAffinoidOpens : Set (Opens X) :=
  X.propOpens isStronglyNoetherianAffinoid

variable {X}

/-- An open strongly noetherian Tate affinoid is an open Tate affinoid subspace. -/
theorem stronglyNoetherianAffinoidOpens_subset_tateAffinoidOpens :
    X.stronglyNoetherianAffinoidOpens ⊆ X.tateAffinoidOpens :=
  fun _ hU ↦ (mem_propOpens_iff _).mpr
    (isStronglyNoetherianAffinoid.isTateAffinoid ((mem_propOpens_iff _).mp hU))

/-- An open strongly noetherian Tate affinoid is an open affinoid of noetherian type. -/
theorem stronglyNoetherianAffinoidOpens_subset_noetherianAffinoidOpens :
    X.stronglyNoetherianAffinoidOpens ⊆ X.noetherianAffinoidOpens :=
  fun _ hU ↦ (mem_propOpens_iff _).mpr
    (isStronglyNoetherianAffinoid.isNoetherianAffinoid ((mem_propOpens_iff _).mp hU))

end PreAdicSpace

namespace ValuationSpectrum

open PairOfDefinition

section NoetherianBase

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
  [IsNoetherianType A] (P : PairOfDefinition A) (Aplus : Subring A)
  (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) (hP : P.ringOfDefinition ≤ Aplus)

/-- Common rational-open transport over a ring of noetherian type: if `T` spans an open ideal and
`A⟨T/s⟩` is Tate, then `A⟨T/s⟩` is of noetherian type and Tate, hence strongly noetherian, so
`R(T/s)` is an open strongly noetherian Tate affinoid of `Spa(A, A⁺)`. -/
private theorem spaBasicOpen_mem_stronglyNoetherianAffinoidOpens_of_isTateRing_completion
    {T : Finset A} {s : A} (hT : IsOpen (Ideal.span (T : Set A) : Set A))
    (htate :
      letI hden := hasDenominatorPower_of_isOpen_span P T s (Localization.Away s) hT
      letI := locUniformSpace P T s (Localization.Away s) hden
      letI := isUniformAddGroup_locUniformSpace P T s (Localization.Away s) hden
      letI := isTopologicalRing_locUniformSpace P T s (Localization.Away s) hden
      IsTateRing (UniformSpace.Completion (Localization.Away s))) :
    spaBasicOpen Aplus T s ∈
      (presentationLimitPreAdicSpace P Aplus hAplus hP).stronglyNoetherianAffinoidOpens := by
  let hden := hasDenominatorPower_of_isOpen_span P T s (Localization.Away s) hT
  let _ := locUniformSpace P T s _ hden
  have _ := isUniformAddGroup_locUniformSpace P T s _ hden
  have _ := isTopologicalRing_locUniformSpace P T s _ hden
  have _ : IsTateRing (UniformSpace.Completion (Localization.Away s)) := htate
  have _ := isNoetherianType_completion_locTopology_of_isNoetherianType P
    (Ideal.isOpen_of_isOpen_subideal (Ideal.span_mono (Set.subset_insert _ _)) hT) _ hden
  let S' : Pair (UniformSpace.Completion (Localization.Away s)) :=
    ⟨completedPlusSubring P Aplus T s _ hden, isRingOfIntegralElements_completedPlusSubring P
      Aplus (fun j _ ↦ hP j.2) hAplus T s _ hden⟩
  exact (PreAdicSpace.mem_propOpens_iff _).mpr <|
    ObjectProperty.prop_of_iso PreAdicSpace.isStronglyNoetherianAffinoid
      (restrictSpaBasicOpenIso P Aplus T s _ hden hAplus hP hT).symm
      (PreAdicSpace.isStronglyNoetherianAffinoid_presentationLimitPreAdicSpace S'
        (completionLocalization P T s _ hden)
        (completionLocalization_ringOfDefinition_le_completedPlusSubring P Aplus hP T s _ hden))

/-- **Rational subsets at a topologically nilpotent denominator over a noetherian-type base are
open strongly noetherian Tate affinoids.** For `A` of noetherian type (not necessarily Tate or
complete), if `T` spans an open ideal and `s` is topologically nilpotent, `A⟨T/s⟩` is both Tate
and of noetherian type, hence strongly noetherian. -/
theorem spaBasicOpen_mem_stronglyNoetherianAffinoidOpens_of_isTopologicallyNilpotent
    {T : Finset A} {s : A} (hT : IsOpen (Ideal.span (T : Set A) : Set A))
    (hs : IsTopologicallyNilpotent s) :
    spaBasicOpen Aplus T s ∈
      (presentationLimitPreAdicSpace P Aplus hAplus hP).stronglyNoetherianAffinoidOpens :=
  spaBasicOpen_mem_stronglyNoetherianAffinoidOpens_of_isTateRing_completion P Aplus hAplus hP hT
    (isTateRing_completion_locTopology_of_isTopologicallyNilpotent P T s _ _ hs)

end NoetherianBase

section StronglyNoetherianTateBase

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsTateRing A]
  [IsNoetherianType A] (P : PairOfDefinition A) (Aplus : Subring A)
  (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) (hP : P.ringOfDefinition ≤ Aplus)

/-- **Rational subsets of a strongly noetherian Tate `Spa(A, A⁺)` are open strongly noetherian
Tate affinoids.** This applies whenever `A` is Tate and of noetherian type (in particular, when `A`
is a strongly noetherian Tate ring, via `IsNoetherianType.of_isStronglyNoetherian`); `A` need not
be complete or Hausdorff. -/
theorem spaBasicOpen_mem_stronglyNoetherianAffinoidOpens {T : Finset A} {s : A}
    (hT : IsOpen (Ideal.span (T : Set A) : Set A)) :
    spaBasicOpen Aplus T s ∈
      (presentationLimitPreAdicSpace P Aplus hAplus hP).stronglyNoetherianAffinoidOpens :=
  spaBasicOpen_mem_stronglyNoetherianAffinoidOpens_of_isTateRing_completion P Aplus hAplus hP hT
    (isTateRing_completion_locTopology_of_isTateRing P T s _ _)

/-- **The open strongly noetherian Tate affinoids form a basis of `Spa(A, A⁺)`** when `A` is a
Tate ring of noetherian type (equivalently, a strongly noetherian Tate ring). -/
theorem isBasis_stronglyNoetherianAffinoidOpens_presentationLimitPreAdicSpace :
    Opens.IsBasis
      (presentationLimitPreAdicSpace P Aplus hAplus hP).stronglyNoetherianAffinoidOpens := by
  refine Opens.isBasis_iff_nbhd.mpr fun {U x} hx ↦ ?_
  obtain ⟨V, hV, hxV, hVU⟩ := Opens.isBasis_iff_nbhd.mp (isBasis_spaRationalOpens Aplus) hx
  obtain ⟨T, s, hT, rfl⟩ := mem_spaRationalOpens_iff_exists_spaBasicOpen.mp hV
  exact ⟨_, spaBasicOpen_mem_stronglyNoetherianAffinoidOpens P Aplus hAplus hP hT, hxV, hVU⟩

end StronglyNoetherianTateBase

end ValuationSpectrum

namespace PreAdicSpace

/-- The presentation-limit pre-adic space of any Tate Huber pair of noetherian type (in particular,
of any strongly noetherian Tate Huber pair) is a strongly noetherian Tate affinoid, without
completeness or Hausdorffness hypotheses on `A`. -/
theorem isStronglyNoetherianAffinoid_presentationLimitPreAdicSpace_of_isNoetherianType
    {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsTateRing A]
    [IsNoetherianType A] (S : Pair A) (P : PairOfDefinition A) (hP : P.ringOfDefinition ≤ S.plus) :
    isStronglyNoetherianAffinoid (presentationLimitPreAdicSpace P S.plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem hP) := by
  rw [← top_mem_propOpens_iff _ isStronglyNoetherianAffinoid]
  have htop : spaBasicOpen S.plus ({1} : Finset A) 1 = ⊤ := by
    ext x
    simp [mem_spaBasicOpen, rationalSubset_singleton_one]
  exact htop ▸ spaBasicOpen_mem_stronglyNoetherianAffinoidOpens P S.plus
    S.isRingOfIntegralElements.isPowerBounded_of_mem hP (by simp)

/-- **On a strongly noetherian Tate affinoid the open strongly noetherian Tate affinoids form a
basis.** -/
theorem isStronglyNoetherianAffinoid.isBasis_stronglyNoetherianAffinoidOpens
    {X : PreAdicSpace.{u}} (hX : isStronglyNoetherianAffinoid X) :
    Opens.IsBasis X.stronglyNoetherianAffinoidOpens :=
  let ⟨_, _, _, _, _, _, _, _, _, S, P, hP, ⟨e⟩⟩ := hX
  isBasis_propOpens_of_iso isStronglyNoetherianAffinoid e
    (isBasis_stronglyNoetherianAffinoidOpens_presentationLimitPreAdicSpace P S.plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem hP)

end PreAdicSpace

/-! ### Locally noetherian analytic adic spaces and the bridge -/

namespace AdicSpace

open PreAdicSpace

/-- **Locally noetherian analytic adic spaces** (Huber 1996, §1.1): an adic space `X` is *locally
noetherian analytic* when every point has an open strongly noetherian Tate affinoid neighbourhood,
that is, an open `U` with `X|_U ≅ Spa(A, A⁺)` for a complete Hausdorff strongly noetherian Tate
Huber pair `(A, A⁺)`. By `TauCeti.AdicSpace.isLocallyNoetherianAnalytic_iff` this is equivalent to
being both locally noetherian and analytic. -/
def IsLocallyNoetherianAnalytic (X : AdicSpace.{u}) : Prop :=
  ∀ x : X.obj, ∃ U ∈ X.obj.stronglyNoetherianAffinoidOpens, x ∈ U

variable {X Y : AdicSpace.{u}}

/-- Unfolding lemma for `TauCeti.AdicSpace.IsLocallyNoetherianAnalytic`. -/
theorem isLocallyNoetherianAnalytic_def :
    X.IsLocallyNoetherianAnalytic ↔
      ∀ x : X.obj, ∃ U ∈ X.obj.stronglyNoetherianAffinoidOpens, x ∈ U :=
  (Iff.rfl)

/-- **The open strongly noetherian Tate affinoids of a locally noetherian analytic adic space form
a basis of its topology.** -/
theorem IsLocallyNoetherianAnalytic.isBasis_stronglyNoetherianAffinoidOpens
    (hX : X.IsLocallyNoetherianAnalytic) :
    Opens.IsBasis X.obj.stronglyNoetherianAffinoidOpens :=
  isBasis_propOpens isStronglyNoetherianAffinoid
    (fun _ ↦ isStronglyNoetherianAffinoid.isBasis_stronglyNoetherianAffinoidOpens) hX

/-- An adic space is locally noetherian analytic if and only if its open strongly noetherian Tate
affinoids form a basis of its topology. -/
theorem isLocallyNoetherianAnalytic_iff_isBasis_stronglyNoetherianAffinoidOpens :
    X.IsLocallyNoetherianAnalytic ↔ Opens.IsBasis X.obj.stronglyNoetherianAffinoidOpens :=
  ⟨IsLocallyNoetherianAnalytic.isBasis_stronglyNoetherianAffinoidOpens,
    exists_mem_propOpens_of_isBasis⟩

/-- A locally noetherian analytic adic space is locally noetherian. -/
theorem IsLocallyNoetherianAnalytic.isLocallyNoetherian (h : X.IsLocallyNoetherianAnalytic) :
    X.IsLocallyNoetherian :=
  isLocallyNoetherian_iff.mpr fun x ↦ let ⟨U, hU, hxU⟩ := h x
    ⟨U, stronglyNoetherianAffinoidOpens_subset_noetherianAffinoidOpens hU, hxU⟩

/-- A locally noetherian analytic adic space is analytic. -/
theorem IsLocallyNoetherianAnalytic.isAnalytic (h : X.IsLocallyNoetherianAnalytic) :
    X.IsAnalytic :=
  isAnalytic_iff.mpr fun x ↦ let ⟨U, hU, hxU⟩ := h x
    ⟨U, stronglyNoetherianAffinoidOpens_subset_tateAffinoidOpens hU, hxU⟩

/-- **Locally noetherian and analytic implies locally noetherian analytic**: every point `x` of `X`
is analytic and lies in an open affinoid `V ≅ Spa(A, A⁺)` of noetherian type, so `x` lies in a
standard analytic rational open `R(G/g)` inside `V` whose completed localisation `A⟨G/g⟩` is both
Tate and of noetherian type, hence strongly noetherian. -/
theorem IsLocallyNoetherianAnalytic.of_isLocallyNoetherian_of_isAnalytic
    (hN : X.IsLocallyNoetherian) (hA : X.IsAnalytic) : X.IsLocallyNoetherianAnalytic := by
  intro x
  obtain ⟨V, hV, hxV⟩ := isLocallyNoetherian_iff.mp hN x
  obtain ⟨A, _, _, _, _, _, _, _, _, S, P, hP, ⟨e⟩⟩ :=
    (isNoetherianAffinoid_iff _).mp ((mem_propOpens_iff _).mp hV)
  exact exists_mem_propOpens_of_mem_analyticPoints isStronglyNoetherianAffinoid
    (hA.mem_analyticPoints x) hxV P S.plus
    S.isRingOfIntegralElements.isPowerBounded_of_mem hP e fun hT hs ↦
      spaBasicOpen_mem_stronglyNoetherianAffinoidOpens_of_isTopologicallyNilpotent P S.plus _ hP
        hT hs

/-- **Bridge between strongly noetherian Tate charts and `IsLocallyNoetherian ∧ IsAnalytic`**: an
adic space has an open cover by strongly noetherian Tate affinoids if and only if it is locally
noetherian and analytic. -/
theorem isLocallyNoetherianAnalytic_iff :
    X.IsLocallyNoetherianAnalytic ↔ X.IsLocallyNoetherian ∧ X.IsAnalytic :=
  ⟨fun h ↦ ⟨h.isLocallyNoetherian, h.isAnalytic⟩,
    fun ⟨hN, hA⟩ ↦ .of_isLocallyNoetherian_of_isAnalytic hN hA⟩

/-- **Open subspaces of locally noetherian analytic adic spaces are locally noetherian analytic.**
-/
theorem IsLocallyNoetherianAnalytic.of_isOpenImmersion (f : Y ⟶ X) [IsOpenImmersion f.hom]
    (hX : X.IsLocallyNoetherianAnalytic) : Y.IsLocallyNoetherianAnalytic :=
  .of_isLocallyNoetherian_of_isAnalytic
    (hX.isLocallyNoetherian.of_isOpenImmersion f) (hX.isAnalytic.of_isOpenImmersion f)

/-- Being locally noetherian analytic is carried back along an isomorphism of adic spaces. -/
theorem IsLocallyNoetherianAnalytic.of_iso (e : Y ≅ X) (hX : X.IsLocallyNoetherianAnalytic) :
    Y.IsLocallyNoetherianAnalytic :=
  have : IsIso e.hom.hom := ((ObjectProperty.ι _).mapIso e).isIso_hom
  hX.of_isOpenImmersion e.hom

/-- Isomorphic adic spaces are locally noetherian analytic together. -/
theorem isLocallyNoetherianAnalytic_iff_of_iso (e : Y ≅ X) :
    Y.IsLocallyNoetherianAnalytic ↔ X.IsLocallyNoetherianAnalytic :=
  ⟨fun hY ↦ hY.of_iso e.symm, fun hX ↦ hX.of_iso e⟩

/-- **The analytic locus of a locally noetherian adic space is locally noetherian analytic.** -/
theorem IsLocallyNoetherian.isLocallyNoetherianAnalytic_analyticLocus
    (hX : X.IsLocallyNoetherian) : X.analyticLocus.IsLocallyNoetherianAnalytic :=
  .of_isLocallyNoetherian_of_isAnalytic
    (hX.of_isOpenImmersion (analyticLocus.ι X)) (isAnalytic_analyticLocus X)

/-- Any adic space with no points is locally noetherian analytic. -/
theorem isLocallyNoetherianAnalytic_of_isEmpty (X : AdicSpace.{u}) [IsEmpty X.obj] :
    X.IsLocallyNoetherianAnalytic :=
  fun x ↦ IsEmpty.elim ‹IsEmpty X.obj› x

/-- **`Spa(A, A⁺)` is locally noetherian analytic** when `A` is a Tate ring of noetherian type
(equivalently, a strongly noetherian Tate ring) and the structure presheaf is a sheaf. Neither
completeness nor Hausdorffness of `A` is required. -/
theorem IsLocallyNoetherianAnalytic.spa {A : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsTateRing A] [IsNoetherianType A] (P : PairOfDefinition A)
    (Aplus : Subring A) (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a)
    (hP : P.ringOfDefinition ≤ Aplus)
    (hs : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa Aplus))
      (presentationLimitPresheaf P Aplus)) :
    IsLocallyNoetherianAnalytic ⟨presentationLimitPreAdicSpace P Aplus hAplus hP,
      isAdic_presentationLimitPreAdicSpace P Aplus hAplus hP hs⟩ :=
  .of_isLocallyNoetherian_of_isAnalytic
    (IsLocallyNoetherian.spa P Aplus hAplus hP hs) (IsAnalytic.spa P Aplus hAplus hP hs)

end AdicSpace

/-! ### Strongly sheafy Tate affinoids and locally strongly sheafy adic spaces -/

namespace ValuationSpectrum

/-- **The structure presheaf of `Spa(A, A⁺)` is a sheaf when `A` is strongly sheafy** and `A⁺` is
a ring of integral elements: a strongly sheafy Huber ring is sheafy
(`TauCeti.Huber.IsStronglySheafy.isSheafyRing`), so every ring of integral elements satisfies
`TauCeti.Huber.IsSheafyForEveryPresentation`. Neither completeness nor a Tate hypothesis on `A` is
required. -/
theorem isSheaf_presentationLimitPresheaf_of_isStronglySheafy {A : Type u} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A] (P : PairOfDefinition A)
    {Aplus : Subring A} (hAplus : IsRingOfIntegralElements Aplus)
    (hP : P.ringOfDefinition ≤ Aplus) (hA : IsStronglySheafy A) :
    Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa Aplus))
      (presentationLimitPresheaf P Aplus) := by
  let _ : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
  have _ : IsUniformAddGroup A := isUniformAddGroup_of_addCommGroup
  exact (hA.isSheafyRing.isSheafyForEveryPresentation hAplus).isSheaf P hP

/-- **The adic spectrum of a strongly sheafy Huber pair is an affinoid adic space.** The ring need
not be complete, Hausdorff, or Tate. -/
theorem isAdic_presentationLimitPreAdicSpace_of_isStronglySheafy {A : Type u} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A] (P : PairOfDefinition A)
    {Aplus : Subring A} (hAplus : IsRingOfIntegralElements Aplus)
    (hP : P.ringOfDefinition ≤ Aplus) (hA : IsStronglySheafy A) :
    PreAdicSpace.isAdic
      (presentationLimitPreAdicSpace P Aplus hAplus.isPowerBounded_of_mem hP) :=
  isAdic_presentationLimitPreAdicSpace P Aplus hAplus.isPowerBounded_of_mem hP
    (isSheaf_presentationLimitPresheaf_of_isStronglySheafy P hAplus hP hA)

end ValuationSpectrum

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
  obtain ⟨A, _, _, _, _, _, _, _, _, S, P, hP, e⟩ := hX
  exact ⟨A, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, IsStronglySheafy.of_isStronglyNoetherian, S, P, hP, e⟩

/-- The presentation-limit pre-adic space of a complete Hausdorff strongly sheafy Tate Huber pair
is a strongly sheafy Tate affinoid. For a general strongly sheafy Tate pair whose ring need not be
complete or Hausdorff, see
`TauCeti.PreAdicSpace.isStronglySheafyAffinoid_presentationLimitPreAdicSpace_of_isStronglySheafy`.
-/
theorem isStronglySheafyAffinoid_presentationLimitPreAdicSpace {A : Type u} [CommRing A]
    [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A] [CompleteSpace A] [T2Space A]
    [IsTateRing A] (hA : IsStronglySheafy A) (S : Pair A) (P : PairOfDefinition A)
    (hP : P.ringOfDefinition ≤ S.plus) :
    isStronglySheafyAffinoid (presentationLimitPreAdicSpace P S.plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem hP) :=
  ⟨A, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, hA, S, P, hP, ⟨Iso.refl _⟩⟩

/-- **Complete-model invariance for strongly sheafy Tate pairs**: the presentation-limit pre-adic
space of any strongly sheafy Tate Huber pair `(A, A⁺)` is a strongly sheafy Tate affinoid, without
completeness or Hausdorffness hypotheses on `A`. At the trivial presentation `({1}, 1)` carried by
`A` itself, the localisation topology agrees with the topology of `A`
(`TauCeti.Huber.PairOfDefinition.locTopology_denom_one`), so the completed model is the completion
`Â`, which is strongly sheafy by `TauCeti.Huber.isStronglySheafy_completion_iff`. -/
theorem isStronglySheafyAffinoid_presentationLimitPreAdicSpace_of_isStronglySheafy
    {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsTateRing A]
    (hA : IsStronglySheafy A) (S : Pair A) (P : PairOfDefinition A)
    (hP : P.ringOfDefinition ≤ S.plus) :
    isStronglySheafyAffinoid (presentationLimitPreAdicSpace P S.plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem hP) := by
  have hden := PairOfDefinition.hasDenominatorPower_denom_one P ({1} : Finset A) A
  let u := PairOfDefinition.locUniformSpace P ({1} : Finset A) 1 A hden
  have hu_grp := PairOfDefinition.isUniformAddGroup_locUniformSpace P ({1} : Finset A) 1 A hden
  have hu_ring := PairOfDefinition.isTopologicalRing_locUniformSpace P ({1} : Finset A) 1 A hden
  have htop : u.toTopologicalSpace = ‹TopologicalSpace A› :=
    (PairOfDefinition.locUniformSpace_toTopologicalSpace P ({1} : Finset A) 1 A hden).trans
      (PairOfDefinition.locTopology_denom_one P ({1} : Finset A) (by simp [isPowerBounded_one]))
  have hu_huber : @IsHuberRing A _ u.toTopologicalSpace hu_ring :=
    PairOfDefinition.isHuberRing_locUniformSpace P ({1} : Finset A) 1 A hden
  have hu_ss : @IsStronglySheafy A _ u.toTopologicalSpace hu_ring hu_huber := by
    refine (@isStronglySheafy_congr A A _ ‹TopologicalSpace A› _ _ _
      u.toTopologicalSpace hu_ring hu_huber (RingEquiv.refl A) ?_ ?_).mp hA
    · exact continuous_def.mpr fun _ hs ↦ htop ▸ hs
    · exact continuous_def.mpr fun _ hs ↦ htop.symm ▸ hs
  let _ : UniformSpace A := u
  have _ : IsUniformAddGroup A := hu_grp
  have _ : @IsTopologicalRing (UniformSpace.Completion A) _ _ := inferInstance
  have _ := PairOfDefinition.isTateRing_completion_locTopology_of_isTateRing P
    ({1} : Finset A) 1 A hden
  have hcomp_ss : IsStronglySheafy (UniformSpace.Completion A) :=
    (@isStronglySheafy_completion_iff A _ u hu_grp hu_ring hu_huber).mpr hu_ss
  let S' : Pair (UniformSpace.Completion A) :=
    PairOfDefinition.rationalLocalizationPair P S hP ({1} : Finset A) 1 A hden
  have hP' :
      (PairOfDefinition.completionLocalization P ({1} : Finset A) 1 A hden).ringOfDefinition ≤
        S'.plus := by
    simpa only [S', PairOfDefinition.rationalLocalizationPair_plus] using
      PairOfDefinition.completionLocalization_ringOfDefinition_le_completedPlusSubring P S.plus hP
        ({1} : Finset A) 1 A hden
  refine ⟨UniformSpace.Completion A, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, hcomp_ss, S',
    PairOfDefinition.completionLocalization P ({1} : Finset A) 1 A hden, hP', ⟨?_⟩⟩
  simpa only [S', PairOfDefinition.rationalLocalizationPair_plus] using
    presentationLimitPreAdicSpaceCompleteIso P S.plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem hP A hden

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
  fun x ↦ let ⟨U, hU, hxU⟩ := h x
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

/-- **`Spa(A, A⁺)` is locally strongly sheafy** for every strongly sheafy Tate Huber pair `(A, A⁺)`
(the whole space `⊤` is an open strongly sheafy Tate affinoid). Neither completeness nor
Hausdorffness of `A` is required. -/
theorem IsLocallyStronglySheafy.spa {A : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsTateRing A] (hA : IsStronglySheafy A) (S : Pair A)
    (P : PairOfDefinition A) (hP : P.ringOfDefinition ≤ S.plus) :
    IsLocallyStronglySheafy ⟨presentationLimitPreAdicSpace P S.plus
        S.isRingOfIntegralElements.isPowerBounded_of_mem hP,
      isAdic_presentationLimitPreAdicSpace_of_isStronglySheafy P S.isRingOfIntegralElements hP
        hA⟩ :=
  fun _ ↦ ⟨⊤, (top_mem_propOpens_iff _ isStronglySheafyAffinoid).mpr
    (isStronglySheafyAffinoid_presentationLimitPreAdicSpace_of_isStronglySheafy hA S P hP),
    trivial⟩

end AdicSpace

end TauCeti
