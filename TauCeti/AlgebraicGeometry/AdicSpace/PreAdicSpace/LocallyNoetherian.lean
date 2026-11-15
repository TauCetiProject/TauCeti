/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.LocallyTate
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.StronglyNoetherian
public import TauCeti.RingTheory.Huber.NoetherianType.Tate
import TauCeti.RingTheory.Huber.LocalizationTopology.Noetherian

/-!
# Locally noetherian and locally noetherian analytic adic spaces

An adic space is *locally noetherian* when every point has an open affinoid neighbourhood whose
coordinate ring is of noetherian type: a complete Hausdorff Huber ring that has a noetherian ring
of definition or is a strongly noetherian Tate ring (`TauCeti.Huber.IsNoetherianType`). These are
the ring hypotheses of Huber's sheafiness theorem, and the class of spaces on which Huber builds
fibre products and the theory of morphisms locally of finite type. A discrete ring is of noetherian
type, its prime subring being a noetherian ring of definition, whether or not it is noetherian. No
condition is placed on the plus rings.

The open affinoids of noetherian type are the opens `U` for which the restriction of `X` to `U` is
isomorphic to `Spa(A, A⁺)` for a complete Hausdorff Huber pair `(A, A⁺)` with `A` of noetherian
type (`TauCeti.PreAdicSpace.noetherianAffinoidOpens`). These are the opens
`TauCeti.PreAdicSpace.propOpens` for the isomorphism-closed property of being an affinoid of
noetherian type, so the transport, restriction and basis lemmas for `propOpens` apply to them as
they do to the open affinoid subspaces. Rational localisation preserves noetherian
type (`TauCeti.Huber.PairOfDefinition.isNoetherianType_completion_locTopology_of_isNoetherianType`)
and the restriction of `Spa(A, A⁺)` to a rational subset `R(T/s)` is `Spa(A⟨T/s⟩, A_U⁺)`, so every
rational open of `Spa(A, A⁺)` is an open affinoid of noetherian type when `A` is of noetherian
type. As the rational opens form a basis, so do the open affinoids of noetherian type, both on
`Spa(A, A⁺)` and on every locally noetherian adic space. Consequently open subspaces of locally
noetherian adic spaces are locally noetherian.

An adic space is *locally noetherian analytic* (`TauCeti.AdicSpace.IsLocallyNoetherianAnalytic`)
when every point has an open affinoid neighbourhood `Spa(A, A⁺)` whose coordinate ring `A` is a
complete Hausdorff strongly noetherian Tate ring
(`TauCeti.PreAdicSpace.stronglyNoetherianAffinoidOpens`). The comparison theorem
`TauCeti.AdicSpace.isLocallyNoetherianAnalytic_iff` identifies `IsLocallyNoetherianAnalytic X` with
the conjunction `X.IsLocallyNoetherian ∧ X.IsAnalytic`: a strongly noetherian Tate chart is both
Tate and of noetherian type, and conversely at an analytic point inside an open affinoid
`V ≅ Spa(A, A⁺)` of noetherian type one refines to a standard analytic rational open `R(G/g)` with
`g` topologically nilpotent, whose completed localisation `A⟨G/g⟩` is simultaneously Tate and of
noetherian type, hence strongly noetherian (`TauCeti.Huber.IsNoetherianType.isStronglyNoetherian`).
Consequently open subspaces of locally noetherian analytic adic spaces are locally noetherian
analytic, and the analytic locus `X.analyticLocus` of any locally noetherian adic space `X` is
locally noetherian analytic.

## Main definitions

* `TauCeti.PreAdicSpace.isNoetherianAffinoid`: the objects of `𝒱^pre` isomorphic to `Spa(A, A⁺)`
  for a complete Hausdorff Huber pair with `A` of noetherian type.
* `TauCeti.PreAdicSpace.noetherianAffinoidOpens`: the open affinoids of noetherian type.
* `TauCeti.AdicSpace.IsLocallyNoetherian`: locally noetherian adic spaces.
* `TauCeti.PreAdicSpace.isStronglyNoetherianAffinoid`,
  `TauCeti.PreAdicSpace.stronglyNoetherianAffinoidOpens`: strongly noetherian Tate affinoids and
  open subspaces.
* `TauCeti.AdicSpace.IsLocallyNoetherianAnalytic`: locally noetherian analytic adic spaces.

## Main results

* `TauCeti.ValuationSpectrum.isBasis_noetherianAffinoidOpens_presentationLimitPreAdicSpace`: for
  `A` of noetherian type, the open affinoids of noetherian type form a basis of `Spa(A, A⁺)`.
* `TauCeti.PreAdicSpace.isNoetherianAffinoid.isBasis_noetherianAffinoidOpens`: the same on every
  affinoid of noetherian type.
* `TauCeti.AdicSpace.IsLocallyNoetherian.isBasis_noetherianAffinoidOpens`: on a locally noetherian
  adic space the open affinoids of noetherian type form a basis of the topology, and
  `TauCeti.AdicSpace.isLocallyNoetherian_iff_isBasis_noetherianAffinoidOpens` is the converse.
* `TauCeti.AdicSpace.IsLocallyNoetherian.of_isOpenImmersion`: the source of an open immersion into
  a locally noetherian adic space is locally noetherian.
* `TauCeti.AdicSpace.IsLocallyNoetherian.spa`: `Spa(A, A⁺)` is locally noetherian when `A` is of
  noetherian type and the structure presheaf is a sheaf.
* `TauCeti.AdicSpace.isLocallyNoetherianAnalytic_iff`: `X` is locally noetherian analytic if and
  only if `X` is locally noetherian and analytic, with projections
  `TauCeti.AdicSpace.IsLocallyNoetherianAnalytic.isLocallyNoetherian`,
  `TauCeti.AdicSpace.IsLocallyNoetherianAnalytic.isAnalytic` and constructor
  `TauCeti.AdicSpace.IsLocallyNoetherianAnalytic.of_isLocallyNoetherian_of_isAnalytic`.
* `TauCeti.AdicSpace.IsLocallyNoetherianAnalytic.of_isOpenImmersion` and
  `TauCeti.AdicSpace.IsLocallyNoetherian.isLocallyNoetherianAnalytic_analyticLocus`: open
  immersions and the analytic locus of a locally noetherian adic space.
* `TauCeti.AdicSpace.IsLocallyNoetherianAnalytic.spa`: for a Tate ring of noetherian type,
  `Spa(A, A⁺)` is locally noetherian analytic, without completeness or Hausdorffness hypotheses on
  `A`.

## References

* R. Huber, *A generalization of formal schemes and rigid analytic varieties*, Math. Z. 217
  (1994), §2, Theorem 2.2, and §3, Corollary 3.4 and Propositions 3.6 to 3.8.
* R. Huber, *Étale cohomology of rigid analytic varieties and adic spaces*, Aspects of
  Mathematics E30 (1996), §1.1.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Remark 6.37, Remark 8.8,
  Corollary 8.35, and Proposition and Definition 8.36.
-/

public section

open CategoryTheory TopologicalSpace Topology

namespace TauCeti

open Huber ValuationSpectrum

universe u

namespace PreAdicSpace

/-! ### Affinoids of noetherian type -/

/-- An object of `𝒱^pre` is an *affinoid of noetherian type* when it is isomorphic to the
presentation-limit pre-adic space `Spa(A, A⁺)` of a complete Hausdorff Huber pair whose ring `A`
is of noetherian type: `A` has a noetherian ring of definition or is a strongly noetherian Tate
ring. -/
def isNoetherianAffinoid : ObjectProperty PreAdicSpace.{u} := fun X ↦
  ∃ (A : Type u) (_ : CommRing A) (_ : UniformSpace A) (_ : IsUniformAddGroup A)
    (_ : IsTopologicalRing A) (_ : CompleteSpace A) (_ : T2Space A) (_ : IsHuberRing A)
    (_ : IsNoetherianType A) (S : Pair A) (P : PairOfDefinition A)
    (hP : P.ringOfDefinition ≤ S.plus),
    Nonempty (X ≅ presentationLimitPreAdicSpace P S.plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem hP)

/-- Unfolding lemma for `TauCeti.PreAdicSpace.isNoetherianAffinoid`. -/
theorem isNoetherianAffinoid_iff (X : PreAdicSpace.{u}) : isNoetherianAffinoid X ↔
    ∃ (A : Type u) (_ : CommRing A) (_ : UniformSpace A) (_ : IsUniformAddGroup A)
      (_ : IsTopologicalRing A) (_ : CompleteSpace A) (_ : T2Space A) (_ : IsHuberRing A)
      (_ : IsNoetherianType A) (S : Pair A) (P : PairOfDefinition A)
      (hP : P.ringOfDefinition ≤ S.plus),
      Nonempty (X ≅ presentationLimitPreAdicSpace P S.plus
        S.isRingOfIntegralElements.isPowerBounded_of_mem hP) :=
  Iff.rfl

/-- Being an affinoid of noetherian type is invariant under isomorphism in `𝒱^pre`. -/
instance isNoetherianAffinoid.instIsClosedUnderIsomorphisms :
    isNoetherianAffinoid.{u}.IsClosedUnderIsomorphisms where
  of_iso e := fun ⟨A, iA, uA, hgA, htA, hcA, h2A, hA, hnA, S, P, hP, ⟨e'⟩⟩ ↦
    ⟨A, iA, uA, hgA, htA, hcA, h2A, hA, hnA, S, P, hP, ⟨e.symm ≪≫ e'⟩⟩

/-- An affinoid of noetherian type is affinoid. -/
theorem isNoetherianAffinoid.isAffinoid {X : PreAdicSpace.{u}} (hX : isNoetherianAffinoid X) :
    isAffinoid X := by
  obtain ⟨A, _, _, _, _, _, _, _, _, S, P, hP, e⟩ := hX
  exact (isAffinoid_iff_exists_complete X).mpr
    ⟨A, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, S, P, hP, e⟩

/-- The presentation-limit pre-adic space of a complete Hausdorff Huber pair whose ring is of
noetherian type is an affinoid of noetherian type. -/
theorem isNoetherianAffinoid_presentationLimitPreAdicSpace {A : Type u} [CommRing A]
    [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A] [CompleteSpace A] [T2Space A]
    [IsHuberRing A] [IsNoetherianType A] (S : Pair A) (P : PairOfDefinition A)
    (hP : P.ringOfDefinition ≤ S.plus) :
    isNoetherianAffinoid (presentationLimitPreAdicSpace P S.plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem hP) :=
  ⟨A, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, S, P, hP, ⟨Iso.refl _⟩⟩

variable (X : PreAdicSpace.{u})

/-- The *open affinoids of noetherian type* of an object `X` of `𝒱^pre`: the opens `U` such that
`X` restricted to `U` is an affinoid of noetherian type. -/
abbrev noetherianAffinoidOpens : Set (Opens X) :=
  X.propOpens isNoetherianAffinoid

variable {X}

/-- An open affinoid of noetherian type is an open affinoid subspace. -/
theorem noetherianAffinoidOpens_subset_affinoidOpens :
    X.noetherianAffinoidOpens ⊆ X.affinoidOpens :=
  fun _ hU ↦
    (mem_propOpens_iff _).mpr (isNoetherianAffinoid.isAffinoid ((mem_propOpens_iff _).mp hU))

end PreAdicSpace

namespace ValuationSpectrum

open PairOfDefinition

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
  [IsNoetherianType A] (P : PairOfDefinition A) (Aplus : Subring A)
  (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) (hP : P.ringOfDefinition ≤ Aplus)

/-- **Rational subsets of a noetherian-type `Spa(A, A⁺)` are open affinoids of noetherian type.**
For `T` spanning an open ideal, the restriction of `Spa(A, A⁺)` to `R(T/s)` is `Spa(A⟨T/s⟩, A_U⁺)`
(`restrictSpaBasicOpenIso`), and `A⟨T/s⟩` is a complete Hausdorff Huber ring of
noetherian type. The ring `A` itself need not be complete. -/
theorem spaBasicOpen_mem_noetherianAffinoidOpens {T : Finset A} {s : A}
    (hT : IsOpen (Ideal.span (T : Set A) : Set A)) :
    spaBasicOpen Aplus T s ∈
      (presentationLimitPreAdicSpace P Aplus hAplus hP).noetherianAffinoidOpens := by
  refine spaBasicOpen_mem_propOpens P Aplus hAplus hP PreAdicSpace.isNoetherianAffinoid hT ?_
  intro _ _ _
  let hden := hasDenominatorPower_of_isOpen_span P T s (Localization.Away s) hT
  have := isNoetherianType_completion_locTopology_of_isNoetherianType P
    (Ideal.isOpen_of_isOpen_subideal (Ideal.span_mono (Set.subset_insert _ _)) hT) _ hden
  exact PreAdicSpace.isNoetherianAffinoid_presentationLimitPreAdicSpace _ _
    (completionLocalization_ringOfDefinition_le_completedPlusPair P Aplus hAplus hP T s _ hden)

/-- **The open affinoids of noetherian type form a basis of `Spa(A, A⁺)`** when `A` is of noetherian
type, since the rational opens do. -/
theorem isBasis_noetherianAffinoidOpens_presentationLimitPreAdicSpace :
    Opens.IsBasis (presentationLimitPreAdicSpace P Aplus hAplus hP).noetherianAffinoidOpens :=
  isBasis_propOpens_presentationLimitPreAdicSpace P Aplus hAplus hP
    PreAdicSpace.isNoetherianAffinoid
    fun hT ↦ spaBasicOpen_mem_noetherianAffinoidOpens P Aplus hAplus hP hT

end ValuationSpectrum

namespace PreAdicSpace

/-- **On an affinoid of noetherian type the open affinoids of noetherian type form a basis.** -/
theorem isNoetherianAffinoid.isBasis_noetherianAffinoidOpens {X : PreAdicSpace.{u}}
    (hX : isNoetherianAffinoid X) : Opens.IsBasis X.noetherianAffinoidOpens :=
  let ⟨_, _, _, _, _, _, _, _, _, S, P, hP, ⟨e⟩⟩ := hX
  isBasis_propOpens_of_iso isNoetherianAffinoid e
    (isBasis_noetherianAffinoidOpens_presentationLimitPreAdicSpace P S.plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem hP)

end PreAdicSpace

/-! ### Locally noetherian adic spaces -/

namespace AdicSpace

open PreAdicSpace

/-- **Locally noetherian adic spaces** (Huber 1994, §3): an adic space `X` is *locally noetherian*
when every point has an open affinoid neighbourhood of noetherian type, that is, an open `U` with
`X|_U ≅ Spa(A, A⁺)` for a complete Hausdorff Huber pair with `A` of noetherian type. By
`TauCeti.AdicSpace.IsLocallyNoetherian.spa` this covers sheafy `Spa(A, A⁺)` with `A` discrete or a
strongly noetherian Tate ring; a discrete `A` need not be noetherian. -/
def IsLocallyNoetherian (X : AdicSpace.{u}) : Prop :=
  ∀ x : X.obj, ∃ U ∈ X.obj.noetherianAffinoidOpens, x ∈ U

variable {X Y : AdicSpace.{u}}

/-- Unfolding lemma for `TauCeti.AdicSpace.IsLocallyNoetherian`. -/
theorem isLocallyNoetherian_iff :
    X.IsLocallyNoetherian ↔ ∀ x : X.obj, ∃ U ∈ X.obj.noetherianAffinoidOpens, x ∈ U :=
  Iff.rfl

/-- **The open affinoids of noetherian type of a locally noetherian adic space form a basis of its
topology.** Every point `x` of an open `W` lies in an open affinoid of noetherian type
`U ≅ Spa(A, A⁺)`, whose own open affinoids of noetherian type form a basis
(`TauCeti.PreAdicSpace.isNoetherianAffinoid.isBasis_noetherianAffinoidOpens`); one of them between
`x` and `W ∩ U` is carried to an open affinoid of noetherian type of `X`. -/
theorem IsLocallyNoetherian.isBasis_noetherianAffinoidOpens (hX : X.IsLocallyNoetherian) :
    Opens.IsBasis X.obj.noetherianAffinoidOpens :=
  isBasis_propOpens isNoetherianAffinoid
    (fun _ ↦ isNoetherianAffinoid.isBasis_noetherianAffinoidOpens) hX

/-- An adic space is locally noetherian exactly when its open affinoids of noetherian type form a
basis of its topology. -/
theorem isLocallyNoetherian_iff_isBasis_noetherianAffinoidOpens :
    X.IsLocallyNoetherian ↔ Opens.IsBasis X.obj.noetherianAffinoidOpens :=
  ⟨IsLocallyNoetherian.isBasis_noetherianAffinoidOpens, exists_mem_propOpens_of_isBasis⟩

/-- **Open subspaces of locally noetherian adic spaces are locally noetherian**: the source of an
open immersion into a locally noetherian adic space is locally noetherian. A point `y` of `Y` has
an open affinoid neighbourhood of noetherian type in `X` inside the image of `f`, which `f`
identifies with an open affinoid of noetherian type of `Y`. Isomorphisms are open immersions, so
being locally noetherian is invariant under isomorphism. -/
theorem IsLocallyNoetherian.of_isOpenImmersion (f : Y ⟶ X) [IsOpenImmersion f.hom]
    (hX : X.IsLocallyNoetherian) : Y.IsLocallyNoetherian :=
  exists_mem_propOpens_of_iso isNoetherianAffinoid (IsOpenImmersion.isoRestrict f.hom)
    (exists_mem_propOpens_restrict f.hom.isOpenEmbedding isNoetherianAffinoid
      hX.isBasis_noetherianAffinoidOpens)

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
  [IsNoetherianType A] (P : PairOfDefinition A) (Aplus : Subring A)
  (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) (hP : P.ringOfDefinition ≤ Aplus)

/-- **`Spa(A, A⁺)` is locally noetherian** when `A` is a Huber ring of noetherian type and the
structure presheaf is a sheaf: its rational opens are open affinoids of noetherian type. Neither
completeness of `A` nor any condition on `A⁺` beyond being a plus ring of power-bounded elements
containing a ring of definition is needed. -/
theorem IsLocallyNoetherian.spa
    (hs : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa Aplus))
      (presentationLimitPresheaf P Aplus)) :
    IsLocallyNoetherian ⟨presentationLimitPreAdicSpace P Aplus hAplus hP,
      isAdic_presentationLimitPreAdicSpace P Aplus hAplus hP hs⟩ :=
  isLocallyNoetherian_iff_isBasis_noetherianAffinoidOpens.mpr
    (isBasis_noetherianAffinoidOpens_presentationLimitPreAdicSpace P Aplus hAplus hP)

end AdicSpace

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
  Iff.rfl

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

private theorem isStronglyNoetherianAffinoid_presentationLimitPreAdicSpace_of_completeSpace
    {A : Type u} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]
    [CompleteSpace A] [T2Space A] [IsTateRing A] [IsNoetherianType A] (S : Pair A)
    (P : PairOfDefinition A) (hP : P.ringOfDefinition ≤ S.plus) :
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
  refine spaBasicOpen_mem_propOpens P Aplus hAplus hP PreAdicSpace.isStronglyNoetherianAffinoid hT
    ?_
  intro _ _ _
  let hden := hasDenominatorPower_of_isOpen_span P T s (Localization.Away s) hT
  have : _ := htate
  have := isNoetherianType_completion_locTopology_of_isNoetherianType P
    (Ideal.isOpen_of_isOpen_subideal (Ideal.span_mono (Set.subset_insert _ _)) hT) _ hden
  exact PreAdicSpace.isStronglyNoetherianAffinoid_presentationLimitPreAdicSpace_of_completeSpace _ _
    (completionLocalization_ringOfDefinition_le_completedPlusPair P Aplus hAplus hP T s _ hden)

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
      (presentationLimitPreAdicSpace P Aplus hAplus hP).stronglyNoetherianAffinoidOpens :=
  isBasis_propOpens_presentationLimitPreAdicSpace P Aplus hAplus hP
    PreAdicSpace.isStronglyNoetherianAffinoid
    fun hT ↦ spaBasicOpen_mem_stronglyNoetherianAffinoidOpens P Aplus hAplus hP hT

end StronglyNoetherianTateBase

end ValuationSpectrum

namespace PreAdicSpace

/-- The presentation-limit pre-adic space of any Tate Huber pair of noetherian type (in particular,
of any strongly noetherian Tate Huber pair) is a strongly noetherian Tate affinoid, without
completeness or Hausdorffness hypotheses on `A`. -/
theorem isStronglyNoetherianAffinoid_presentationLimitPreAdicSpace {A : Type u} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [IsTateRing A] [IsNoetherianType A] (S : Pair A)
    (P : PairOfDefinition A) (hP : P.ringOfDefinition ≤ S.plus) :
    isStronglyNoetherianAffinoid (presentationLimitPreAdicSpace P S.plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem hP) :=
  (top_mem_propOpens_iff _ isStronglyNoetherianAffinoid).mp <|
    top_mem_propOpens_presentationLimitPreAdicSpace P S.plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem hP isStronglyNoetherianAffinoid
      fun hT ↦ spaBasicOpen_mem_stronglyNoetherianAffinoidOpens P S.plus _ hP hT

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
  Iff.rfl

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

/-- An adic space that is both locally noetherian and analytic is locally noetherian analytic. -/
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
(equivalently, a strongly noetherian Tate ring). Neither completeness nor Hausdorffness of `A` is
required. -/
theorem IsLocallyNoetherianAnalytic.spa {A : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsTateRing A] [IsNoetherianType A] (P : PairOfDefinition A)
    (Aplus : Subring A) (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a)
    (hP : P.ringOfDefinition ≤ Aplus) :
    IsLocallyNoetherianAnalytic ⟨presentationLimitPreAdicSpace P Aplus hAplus hP,
      letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
      haveI : IsStronglyNoetherian A := IsNoetherianType.isStronglyNoetherian
      isAdic_presentationLimitPreAdicSpace P Aplus hAplus hP
        (isSheaf_presentationLimitPresheaf_of_isStronglyNoetherian P hP hAplus)⟩ :=
  isLocallyNoetherianAnalytic_iff_isBasis_stronglyNoetherianAffinoidOpens.mpr
    (isBasis_stronglyNoetherianAffinoidOpens_presentationLimitPreAdicSpace P Aplus hAplus hP)

end AdicSpace

end TauCeti
