/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.Affinoid.Complete
public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.Analytic

/-!
# Open Tate affinoid subspaces and analytic adic spaces

An object of `𝒱^pre` is a *Tate affinoid* when it is isomorphic to the presentation-limit pre-adic
space `Spa(A, A⁺)` of a complete Hausdorff Tate Huber pair `(A, A⁺)`. The *open Tate affinoid
subspaces* of `X` (`TauCeti.PreAdicSpace.tateAffinoidOpens`) are the opens `U` on which the
restriction `X|_U` is a Tate affinoid, defined through `TauCeti.PreAdicSpace.propOpens`.

On any `Spa(A, A⁺)`, a rational open `R(T/s)` with `T` spanning an open ideal and `s` topologically
nilpotent has coordinate ring `A⟨T/s⟩`, in which the image of `s` is a pseudouniformiser, so
`R(T/s)` is an open Tate affinoid subspace even when `A` itself is neither Tate nor complete. Since
the standard rational cover of the analytic locus `Spa(A, A⁺)ᵃ` is formed by such rational opens as
`s` runs over finite generators of an ideal of definition, every analytic point of a locally
affinoid object of `𝒱^pre` has an open Tate affinoid neighbourhood. Together with the converse that
every point of a Tate affinoid is analytic, this identifies the intrinsic analytic points of a
locally affinoid space (`TauCeti.PreAdicSpace.analyticPoints`, existence of a local
pseudouniformiser) with the points admitting an open Tate affinoid neighbourhood
(`TauCeti.PreAdicSpace.isLocallyAffinoid.mem_analyticPoints_iff_exists_mem_tateAffinoidOpens`,
Wedhorn, Proposition and Definition 8.36).

An adic space `X` is *analytic* (`TauCeti.AdicSpace.IsAnalytic`) when every point lies in an open
Tate affinoid subspace. Equivalently:

* the open Tate affinoid subspaces form a basis of the topology of `X`
  (`TauCeti.AdicSpace.isAnalytic_iff_isBasis_tateAffinoidOpens`);
* every point of `X` is analytic (`TauCeti.AdicSpace.isAnalytic_iff_analyticPoints_eq_univ`);
* the inclusion `X_a ⟶ X` of the analytic locus is an isomorphism
  (`TauCeti.AdicSpace.isIso_analyticLocus_ι_iff`).

Analyticity passes to sources of open immersions, holds unconditionally for the analytic locus
`X.analyticLocus` of any adic space and for empty adic spaces, and on an affinoid adic space
`Spa(A, A⁺)` reduces to `spaAnalytic A⁺ = spa A⁺` (`TauCeti.AdicSpace.isAnalytic_spa_iff`), hence
holds whenever `A` is a Tate ring (`TauCeti.AdicSpace.IsAnalytic.spa`).

## Main definitions

* `TauCeti.PreAdicSpace.isTateAffinoid`: objects of `𝒱^pre` isomorphic to `Spa(A, A⁺)` for a
  complete Hausdorff Tate Huber pair.
* `TauCeti.PreAdicSpace.tateAffinoidOpens`: the open Tate affinoid subspaces of an object of
  `𝒱^pre`.
* `TauCeti.AdicSpace.IsAnalytic`: analytic adic spaces, covered by open Tate affinoid subspaces.

## Main results

* `TauCeti.ValuationSpectrum.spaBasicOpen_mem_tateAffinoidOpens_of_isTopologicallyNilpotent` and
  `TauCeti.ValuationSpectrum.spaBasicOpen_mem_tateAffinoidOpens`: rational subsets with
  topologically nilpotent denominator, and all rational subsets over a Tate ring, are open Tate
  affinoid subspaces.
* `TauCeti.PreAdicSpace.isLocallyAffinoid.mem_analyticPoints_iff_exists_mem_tateAffinoidOpens`: on a
  locally affinoid object of `𝒱^pre`, a point is analytic if and only if it has an open Tate
  affinoid neighbourhood.
* `TauCeti.AdicSpace.isAnalytic_iff_isBasis_tateAffinoidOpens`: an adic space is analytic if and
  only if its open Tate affinoid subspaces form a basis.
* `TauCeti.AdicSpace.isAnalytic_iff_analyticPoints_eq_univ`: an adic space is analytic if and only
  if all of its points are analytic.
* `TauCeti.AdicSpace.isAnalytic_analyticLocus` and `TauCeti.AdicSpace.isIso_analyticLocus_ι_iff`:
  the analytic locus `X_a` is analytic, and `X_a ⟶ X` is an isomorphism if and only if `X` is
  analytic.
* `TauCeti.AdicSpace.IsAnalytic.of_isOpenImmersion`, `TauCeti.AdicSpace.isAnalytic_spa_iff` and
  `TauCeti.AdicSpace.IsAnalytic.spa`: open immersions, general affinoid spectra and Tate affinoid
  spectra.

## References

* R. Huber, *A generalization of formal schemes and rigid analytic varieties*, Math. Z. 217
  (1994), §3.
* R. Huber, *Étale cohomology of rigid analytic varieties and adic spaces*, Aspects of
  Mathematics E30 (1996), §1.1.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Proposition and Definition 8.36
  and Remark 8.37.
-/

public section

open CategoryTheory TopologicalSpace Topology

namespace TauCeti

open Huber ValuationSpectrum

universe u

namespace PreAdicSpace

/-! ### Tate affinoids -/

/-- An object of `𝒱^pre` is a *Tate affinoid* when it is isomorphic to the presentation-limit
pre-adic space `Spa(A, A⁺)` of a complete Hausdorff Tate Huber pair `(A, A⁺)`. -/
def isTateAffinoid : ObjectProperty PreAdicSpace.{u} := fun X ↦
  ∃ (A : Type u) (_ : CommRing A) (_ : UniformSpace A) (_ : IsUniformAddGroup A)
    (_ : IsTopologicalRing A) (_ : CompleteSpace A) (_ : T2Space A) (_ : IsTateRing A)
    (S : Pair A) (P : PairOfDefinition A) (hP : P.ringOfDefinition ≤ S.plus),
    Nonempty (X ≅ presentationLimitPreAdicSpace P S.plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem hP)

/-- Unfolding lemma for `TauCeti.PreAdicSpace.isTateAffinoid`. -/
theorem isTateAffinoid_iff (X : PreAdicSpace.{u}) : isTateAffinoid X ↔
    ∃ (A : Type u) (_ : CommRing A) (_ : UniformSpace A) (_ : IsUniformAddGroup A)
      (_ : IsTopologicalRing A) (_ : CompleteSpace A) (_ : T2Space A) (_ : IsTateRing A)
      (S : Pair A) (P : PairOfDefinition A) (hP : P.ringOfDefinition ≤ S.plus),
      Nonempty (X ≅ presentationLimitPreAdicSpace P S.plus
        S.isRingOfIntegralElements.isPowerBounded_of_mem hP) :=
  (Iff.rfl)

/-- Being a Tate affinoid is invariant under isomorphism in `𝒱^pre`. -/
instance isTateAffinoid.instIsClosedUnderIsomorphisms :
    isTateAffinoid.{u}.IsClosedUnderIsomorphisms where
  of_iso e := fun ⟨A, iA, uA, hgA, htA, hcA, h2A, hA, S, P, hP, ⟨e'⟩⟩ ↦
    ⟨A, iA, uA, hgA, htA, hcA, h2A, hA, S, P, hP, ⟨e.symm ≪≫ e'⟩⟩

/-- A Tate affinoid is affinoid. -/
theorem isTateAffinoid.isAffinoid {X : PreAdicSpace.{u}} (hX : isTateAffinoid X) :
    isAffinoid X := by
  obtain ⟨A, _, _, _, _, _, _, _, S, P, hP, e⟩ := hX
  exact (isAffinoid_iff_exists_complete X).mpr
    ⟨A, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, S, P, hP, e⟩

private theorem isTateAffinoid_presentationLimitPreAdicSpace_of_completeSpace {A : Type u}
    [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A] [CompleteSpace A]
    [T2Space A] [IsTateRing A] (S : Pair A) (P : PairOfDefinition A)
    (hP : P.ringOfDefinition ≤ S.plus) :
    isTateAffinoid (presentationLimitPreAdicSpace P S.plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem hP) :=
  ⟨A, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, S, P, hP, ⟨Iso.refl _⟩⟩

/-- Every point of a Tate affinoid is analytic. -/
theorem isTateAffinoid.analyticPoints_eq_univ {X : PreAdicSpace.{u}} (hX : isTateAffinoid X) :
    X.analyticPoints = Set.univ := by
  obtain ⟨_, _, _, _, _, _, _, _, S, P, hP, ⟨e⟩⟩ := hX
  rw [← preimage_analyticPoints_of_isOpenImmersion e.hom,
    analyticPoints_presentationLimitPreAdicSpace_of_isTateRing, Set.preimage_univ]

variable (X : PreAdicSpace.{u})

/-- The *open Tate affinoid subspaces* of an object `X` of `𝒱^pre`: the opens `U` such that `X`
restricted to `U` is a Tate affinoid. -/
abbrev tateAffinoidOpens : Set (Opens X) :=
  X.propOpens isTateAffinoid

variable {X}

/-- An open Tate affinoid subspace is an open affinoid subspace. -/
theorem tateAffinoidOpens_subset_affinoidOpens :
    X.tateAffinoidOpens ⊆ X.affinoidOpens :=
  fun _ hU ↦
    (mem_propOpens_iff _).mpr (isTateAffinoid.isAffinoid ((mem_propOpens_iff _).mp hU))

/-- Every point of an open Tate affinoid subspace of `X` is an analytic point of `X`. -/
theorem subset_analyticPoints_of_mem_tateAffinoidOpens {U : Opens X}
    (hU : U ∈ X.tateAffinoidOpens) : (U : Set X) ⊆ X.analyticPoints := by
  intro x hxU
  have hx : (⟨x, hxU⟩ : X.restrict U.isOpenEmbedding) ∈
      (X.restrict U.isOpenEmbedding).analyticPoints := by
    rw [((mem_propOpens_iff _).mp hU).analyticPoints_eq_univ]
    trivial
  rwa [analyticPoints_restrict] at hx

end PreAdicSpace

namespace ValuationSpectrum

open PairOfDefinition

section ArbitraryBase

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  (P : PairOfDefinition A) (Aplus : Subring A)
  (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) (hP : P.ringOfDefinition ≤ Aplus)

/-- Common rational-open transport: if `T` spans an open ideal and `A⟨T/s⟩` is Tate for its
localisation uniformity, then `R(T/s)` is an open Tate affinoid subspace of `Spa(A, A⁺)`. -/
private theorem spaBasicOpen_mem_tateAffinoidOpens_of_isTateRing_completion {T : Finset A} {s : A}
    (hT : IsOpen (Ideal.span (T : Set A) : Set A))
    (htate :
      letI hden := hasDenominatorPower_of_isOpen_span P T s (Localization.Away s) hT
      letI := locUniformSpace P T s (Localization.Away s) hden
      letI := isUniformAddGroup_locUniformSpace P T s (Localization.Away s) hden
      letI := isTopologicalRing_locUniformSpace P T s (Localization.Away s) hden
      IsTateRing (UniformSpace.Completion (Localization.Away s))) :
    spaBasicOpen Aplus T s ∈
      (presentationLimitPreAdicSpace P Aplus hAplus hP).tateAffinoidOpens := by
  refine spaBasicOpen_mem_propOpens P Aplus hAplus hP PreAdicSpace.isTateAffinoid hT ?_
  intro _ _ _
  have : _ := htate
  exact PreAdicSpace.isTateAffinoid_presentationLimitPreAdicSpace_of_completeSpace _ _
    (completionLocalization_ringOfDefinition_le_completedPlusPair P Aplus hAplus hP T s _
      (hasDenominatorPower_of_isOpen_span P T s _ hT))

/-- **Rational subsets at a topologically nilpotent denominator are open Tate affinoids.** For any
Huber ring `A` (which need not be Tate or complete), if `T` spans an open ideal and `s` is
topologically nilpotent, the completed localisation `A⟨T/s⟩` has the image of `s` as a
pseudouniformiser (`isTateRing_completion_locTopology_of_isTopologicallyNilpotent`), so `R(T/s)` is
an open Tate affinoid subspace of `Spa(A, A⁺)`. -/
theorem spaBasicOpen_mem_tateAffinoidOpens_of_isTopologicallyNilpotent {T : Finset A} {s : A}
    (hT : IsOpen (Ideal.span (T : Set A) : Set A)) (hs : IsTopologicallyNilpotent s) :
    spaBasicOpen Aplus T s ∈
      (presentationLimitPreAdicSpace P Aplus hAplus hP).tateAffinoidOpens :=
  spaBasicOpen_mem_tateAffinoidOpens_of_isTateRing_completion P Aplus hAplus hP hT
    (isTateRing_completion_locTopology_of_isTopologicallyNilpotent P T s _ _ hs)

/-- **Covering analytic points of `Spa(A, A⁺)` by standard analytic rational opens.** Let `Q` be a
property of objects of `𝒱^pre` that holds on every rational open `R(T/s)` of `Spa(A, A⁺)` with `T`
spanning an open ideal and `s` topologically nilpotent. Then every analytic point of `Spa(A, A⁺)`
lies in an open of `propOpens Q`, namely one of the charts `R(G/g)` where `G` is a finite generating
set of `P.idealOfDefinition`. -/
theorem exists_mem_propOpens_of_mem_analyticPoints (Q : ObjectProperty PreAdicSpace.{u})
    (hQ : ∀ {T : Finset A} {s : A},
      IsOpen (Ideal.span (T : Set A) : Set A) → IsTopologicallyNilpotent s →
      spaBasicOpen Aplus T s ∈ (presentationLimitPreAdicSpace P Aplus hAplus hP).propOpens Q)
    {y : presentationLimitPreAdicSpace P Aplus hAplus hP}
    (hy : y ∈ (presentationLimitPreAdicSpace P Aplus hAplus hP).analyticPoints) :
    ∃ W ∈ (presentationLimitPreAdicSpace P Aplus hAplus hP).propOpens Q, y ∈ W := by
  classical
  obtain ⟨G, hG⟩ := P.fg_idealOfDefinition
  -- `presentationLimitPreAdicSpace` has underlying type `spa Aplus`, so `Set.mem_preimage`
  -- views `y` as an element of `spa Aplus`.
  have hy' : (y : spa Aplus).1 ∈ spaAnalytic Aplus :=
    Set.mem_preimage.mp (by rwa [analyticPoints_presentationLimitPreAdicSpace] at hy)
  rw [spaAnalytic_eq_biUnion_rationalSubset P Aplus G hG] at hy'
  obtain ⟨g, hg, hyg⟩ := Set.mem_iUnion₂.mp hy'
  refine ⟨spaBasicOpen Aplus (G.image (↑)) g, hQ ?_ ?_, mem_spaBasicOpen.mpr hyg⟩
  · exact P.span_image_eq_extendedIdealOfDefinition G hG ▸ P.isOpen_extendedIdealOfDefinition
  · exact P.isTopologicallyNilpotent_of_mem_idealOfDefinition
      (hG ▸ Ideal.subset_span (Finset.mem_coe.mpr hg))

end ArbitraryBase

section TateBase

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsTateRing A]
  (P : PairOfDefinition A) (Aplus : Subring A)
  (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) (hP : P.ringOfDefinition ≤ Aplus)

/-- **Rational subsets of a Tate `Spa(A, A⁺)` are open Tate affinoid subspaces.** Over a Tate ring
`A` (which need not be complete), every rational localisation `A⟨T/s⟩` with `T` spanning an open
ideal is a complete Hausdorff Tate ring (`isTateRing_completion_locTopology_of_isTateRing`). -/
theorem spaBasicOpen_mem_tateAffinoidOpens {T : Finset A} {s : A}
    (hT : IsOpen (Ideal.span (T : Set A) : Set A)) :
    spaBasicOpen Aplus T s ∈
      (presentationLimitPreAdicSpace P Aplus hAplus hP).tateAffinoidOpens :=
  spaBasicOpen_mem_tateAffinoidOpens_of_isTateRing_completion P Aplus hAplus hP hT
    (isTateRing_completion_locTopology_of_isTateRing P T s _ _)

/-- **The open Tate affinoid subspaces form a basis of `Spa(A, A⁺)`** when `A` is a Tate ring,
since the rational opens do. -/
theorem isBasis_tateAffinoidOpens_presentationLimitPreAdicSpace :
    Opens.IsBasis (presentationLimitPreAdicSpace P Aplus hAplus hP).tateAffinoidOpens :=
  isBasis_propOpens_presentationLimitPreAdicSpace P Aplus hAplus hP PreAdicSpace.isTateAffinoid
    fun hT ↦ spaBasicOpen_mem_tateAffinoidOpens P Aplus hAplus hP hT

end TateBase

end ValuationSpectrum

namespace PreAdicSpace

/-- The presentation-limit pre-adic space of any Tate Huber pair is a Tate affinoid, without
completeness or Hausdorffness hypotheses on `A`. -/
theorem isTateAffinoid_presentationLimitPreAdicSpace {A : Type u} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [IsTateRing A] (S : Pair A)
    (P : PairOfDefinition A) (hP : P.ringOfDefinition ≤ S.plus) :
    isTateAffinoid (presentationLimitPreAdicSpace P S.plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem hP) :=
  (top_mem_propOpens_iff _ isTateAffinoid).mp <|
    top_mem_propOpens_presentationLimitPreAdicSpace P S.plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem hP isTateAffinoid
      fun hT ↦ spaBasicOpen_mem_tateAffinoidOpens P S.plus _ hP hT

/-- **On a Tate affinoid the open Tate affinoid subspaces form a basis.** -/
theorem isTateAffinoid.isBasis_tateAffinoidOpens {X : PreAdicSpace.{u}} (hX : isTateAffinoid X) :
    Opens.IsBasis X.tateAffinoidOpens :=
  let ⟨_, _, _, _, _, _, _, _, S, P, hP, ⟨e⟩⟩ := hX
  isBasis_propOpens_of_iso isTateAffinoid e
    (isBasis_tateAffinoidOpens_presentationLimitPreAdicSpace P S.plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem hP)

/-- Transporting a standard analytic rational open from an affinoid chart `X|_V ≅ Spa(A, A⁺)` back
to `X`: if `x` is an analytic point of `X` lying in `V` and `Q` holds on rational opens of
`Spa(A, A⁺)` with topologically nilpotent denominator, then `x` lies in an open of `X.propOpens Q`.
-/
theorem exists_mem_propOpens_of_mem_analyticPoints {X : PreAdicSpace.{u}}
    (Q : ObjectProperty PreAdicSpace.{u}) [Q.IsClosedUnderIsomorphisms]
    {x : X} (hx : x ∈ X.analyticPoints) {V : Opens X} (hxV : x ∈ V)
    {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (P : PairOfDefinition A) (Aplus : Subring A)
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) (hP : P.ringOfDefinition ≤ Aplus)
    (e : X.restrict V.isOpenEmbedding ≅ presentationLimitPreAdicSpace P Aplus hAplus hP)
    (hQ : ∀ {T : Finset A} {s : A},
      IsOpen (Ideal.span (T : Set A) : Set A) → IsTopologicallyNilpotent s →
      spaBasicOpen Aplus T s ∈ (presentationLimitPreAdicSpace P Aplus hAplus hP).propOpens Q) :
    ∃ U ∈ X.propOpens Q, x ∈ U := by
  let x' : X.restrict V.isOpenEmbedding := ⟨x, hxV⟩
  have hx' : x' ∈ (X.restrict V.isOpenEmbedding).analyticPoints := by
    rwa [analyticPoints_restrict]
  obtain ⟨W, hW, hyW⟩ := ValuationSpectrum.exists_mem_propOpens_of_mem_analyticPoints
    P Aplus hAplus hP Q hQ (mapsTo_analyticPoints_of_isOpenImmersion e.hom hx')
  exact ⟨V.isOpenEmbedding.isOpenMap.functor.obj ((Opens.map e.hom.base).obj W),
    (mem_propOpens_restrict_iff X V.isOpenEmbedding Q _).mp
      ((map_hom_base_mem_propOpens_iff Q e).mpr hW),
    ⟨x', hyW, rfl⟩⟩

/-- **Tate-chart characterisation of analytic points** (Wedhorn, Proposition and Definition 8.36):
on a locally affinoid object `X` of `𝒱^pre`, a point is analytic if and only if it has an open Tate
affinoid neighbourhood. -/
theorem isLocallyAffinoid.mem_analyticPoints_iff_exists_mem_tateAffinoidOpens
    {X : PreAdicSpace.{u}} (hX : isLocallyAffinoid X) {x : X} :
    x ∈ X.analyticPoints ↔ ∃ U ∈ X.tateAffinoidOpens, x ∈ U := by
  refine ⟨fun hx ↦ ?_, fun ⟨U, hU, hxU⟩ ↦ subset_analyticPoints_of_mem_tateAffinoidOpens hU hxU⟩
  obtain ⟨V, hV, hxV⟩ := hX x
  obtain ⟨A, _, _, _, _, _, _, _, S, P, hP, ⟨e⟩⟩ :=
    (isAffinoid_iff_exists_complete _).mp ((mem_propOpens_iff _).mp hV)
  exact exists_mem_propOpens_of_mem_analyticPoints isTateAffinoid hx hxV P S.plus
    S.isRingOfIntegralElements.isPowerBounded_of_mem hP e
    fun hT hs ↦ spaBasicOpen_mem_tateAffinoidOpens_of_isTopologicallyNilpotent P S.plus _ hP hT hs

end PreAdicSpace

/-! ### Analytic adic spaces -/

namespace AdicSpace

open PreAdicSpace

/-- **Analytic adic spaces** (Huber 1996, §1.1; Wedhorn, Proposition and Definition 8.36): an adic
space `X` is *analytic* when every point has an open Tate affinoid neighbourhood, that is, an open
`U` with `X|_U ≅ Spa(A, A⁺)` for a complete Hausdorff Tate Huber pair `(A, A⁺)`. By
`TauCeti.AdicSpace.isAnalytic_iff_analyticPoints_eq_univ` these are precisely the adic spaces all
of whose points are analytic. -/
def IsAnalytic (X : AdicSpace.{u}) : Prop :=
  ∀ x : X.obj, ∃ U ∈ X.obj.tateAffinoidOpens, x ∈ U

variable {X Y : AdicSpace.{u}}

/-- Unfolding lemma for `TauCeti.AdicSpace.IsAnalytic`. -/
theorem isAnalytic_iff :
    X.IsAnalytic ↔ ∀ x : X.obj, ∃ U ∈ X.obj.tateAffinoidOpens, x ∈ U :=
  (Iff.rfl)

/-- **The open Tate affinoid subspaces of an analytic adic space form a basis of its topology.** -/
theorem IsAnalytic.isBasis_tateAffinoidOpens (hX : X.IsAnalytic) :
    Opens.IsBasis X.obj.tateAffinoidOpens :=
  isBasis_propOpens isTateAffinoid (fun _ ↦ isTateAffinoid.isBasis_tateAffinoidOpens) hX

/-- An adic space is analytic if and only if its open Tate affinoid subspaces form a basis of its
topology. -/
theorem isAnalytic_iff_isBasis_tateAffinoidOpens :
    X.IsAnalytic ↔ Opens.IsBasis X.obj.tateAffinoidOpens :=
  ⟨IsAnalytic.isBasis_tateAffinoidOpens, exists_mem_propOpens_of_isBasis⟩

/-- **Pointwise characterisation of analytic adic spaces** (Wedhorn, Proposition and
Definition 8.36): an adic space is covered by open Tate affinoids if and only if every point of `X`
is analytic. -/
theorem isAnalytic_iff_analyticPoints_eq_univ :
    X.IsAnalytic ↔ X.obj.analyticPoints = Set.univ := by
  rw [isAnalytic_iff, Set.eq_univ_iff_forall]
  exact forall_congr' fun x ↦
    (X.property.isLocallyAffinoid.mem_analyticPoints_iff_exists_mem_tateAffinoidOpens).symm

/-- Every point of an analytic adic space is analytic. -/
theorem IsAnalytic.analyticPoints_eq_univ (hX : X.IsAnalytic) :
    X.obj.analyticPoints = Set.univ :=
  isAnalytic_iff_analyticPoints_eq_univ.mp hX

/-- Every point of an analytic adic space belongs to its analytic locus. -/
theorem IsAnalytic.mem_analyticPoints (hX : X.IsAnalytic) (x : X.obj) :
    x ∈ X.obj.analyticPoints :=
  hX.analyticPoints_eq_univ.symm ▸ Set.mem_univ x

/-- **Open subspaces of analytic adic spaces are analytic**: the source of an open immersion into
an analytic adic space is analytic. -/
theorem IsAnalytic.of_isOpenImmersion (f : Y ⟶ X) [IsOpenImmersion f.hom] (hX : X.IsAnalytic) :
    Y.IsAnalytic :=
  exists_mem_propOpens_of_iso isTateAffinoid (IsOpenImmersion.isoRestrict f.hom)
    (exists_mem_propOpens_restrict f.hom.isOpenEmbedding isTateAffinoid
      hX.isBasis_tateAffinoidOpens)

/-- Analyticity is carried back along an isomorphism of adic spaces. -/
theorem IsAnalytic.of_iso (e : Y ≅ X) (hX : X.IsAnalytic) : Y.IsAnalytic :=
  have : IsIso e.hom.hom := ((ObjectProperty.ι _).mapIso e).isIso_hom
  hX.of_isOpenImmersion e.hom

/-- Isomorphic adic spaces are analytic together. -/
theorem isAnalytic_iff_of_iso (e : Y ≅ X) : Y.IsAnalytic ↔ X.IsAnalytic :=
  ⟨fun hY ↦ hY.of_iso e.symm, fun hX ↦ hX.of_iso e⟩

/-- **The analytic locus of any adic space is analytic.** -/
@[simp]
theorem isAnalytic_analyticLocus (X : AdicSpace.{u}) : X.analyticLocus.IsAnalytic := by
  rw [isAnalytic_iff_analyticPoints_eq_univ, analyticLocus_obj]
  exact PreAdicSpace.analyticPoints_analyticLocus X.obj

/-- **The inclusion `X_a ⟶ X` of the analytic locus is an isomorphism if and only if `X` is
analytic** (Wedhorn, Remark 8.37). -/
theorem isIso_analyticLocus_ι_iff (X : AdicSpace.{u}) :
    IsIso (analyticLocus.ι X) ↔ X.IsAnalytic := by
  rw [← ObjectProperty.isIso_hom_iff, analyticLocus.ι_hom,
    isAnalytic_iff_analyticPoints_eq_univ, ← PreAdicSpace.isIso_analyticLocus_ι_iff]
  exact ⟨fun _ ↦ IsIso.of_isIso_comp_left (eqToHom (analyticLocus_obj X)) _, fun _ ↦ inferInstance⟩

/-- Any adic space with no points is analytic. -/
theorem isAnalytic_of_isEmpty (X : AdicSpace.{u}) [IsEmpty X.obj] : X.IsAnalytic :=
  fun x ↦ IsEmpty.elim ‹IsEmpty X.obj› x

section Spa

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  (P : PairOfDefinition A) (Aplus : Subring A)
  (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) (hP : P.ringOfDefinition ≤ Aplus)

/-- **Analyticity of `Spa(A, A⁺)`**: a sheafy adic spectrum `Spa(A, A⁺)` is an analytic adic space
if and only if every point of `spa A⁺` lies in `spaAnalytic A⁺`, that is, has non-open support. -/
theorem isAnalytic_spa_iff
    (hs : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa Aplus))
      (presentationLimitPresheaf P Aplus)) :
    IsAnalytic ⟨presentationLimitPreAdicSpace P Aplus hAplus hP,
      isAdic_presentationLimitPreAdicSpace P Aplus hAplus hP hs⟩ ↔
      spaAnalytic Aplus = spa Aplus := by
  rw [isAnalytic_iff_analyticPoints_eq_univ, Set.eq_univ_iff_forall]
  refine ⟨fun h ↦ (spaAnalytic_subset_spa Aplus).antisymm fun v hv ↦ ?_, fun h x ↦ ?_⟩
  · have hx := h ⟨v, hv⟩
    rwa [analyticPoints_presentationLimitPreAdicSpace] at hx
  · rw [analyticPoints_presentationLimitPreAdicSpace]
    exact h.symm ▸ (x : spa Aplus).2

/-- **`Spa(A, A⁺)` is analytic when `A` is a Tate ring**: its rational opens are open Tate
affinoid subspaces. The ring `A` need not be complete or Hausdorff. -/
theorem IsAnalytic.spa [IsTateRing A]
    (hs : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa Aplus))
      (presentationLimitPresheaf P Aplus)) :
    IsAnalytic ⟨presentationLimitPreAdicSpace P Aplus hAplus hP,
      isAdic_presentationLimitPreAdicSpace P Aplus hAplus hP hs⟩ :=
  isAnalytic_iff_isBasis_tateAffinoidOpens.mpr
    (isBasis_tateAffinoidOpens_presentationLimitPreAdicSpace P Aplus hAplus hP)

end Spa

end AdicSpace

end TauCeti
