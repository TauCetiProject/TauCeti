/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.Adic
public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.Affinoid.Complete
public import TauCeti.RingTheory.Huber.NoetherianType.Basic
import TauCeti.RingTheory.Huber.LocalizationTopology.Noetherian

/-!
# Locally noetherian adic spaces

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

## Main definitions

* `TauCeti.PreAdicSpace.isNoetherianAffinoid`: the objects of `𝒱^pre` isomorphic to `Spa(A, A⁺)`
  for a complete Hausdorff Huber pair with `A` of noetherian type.
* `TauCeti.PreAdicSpace.noetherianAffinoidOpens`: the open affinoids of noetherian type.
* `TauCeti.AdicSpace.IsLocallyNoetherian`: locally noetherian adic spaces.

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

## References

* R. Huber, *A generalization of formal schemes and rigid analytic varieties*, Math. Z. 217
  (1994), §2, Theorem 2.2, and §3, Propositions 3.6 to 3.8.
* R. Huber, *Étale cohomology of rigid analytic varieties and adic spaces*, Aspects of
  Mathematics E30 (1996), §1.1.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Remark 6.37, Remark 8.8 and
  Corollary 8.35.
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
  have hden := hasDenominatorPower_of_isOpen_span P T s (Localization.Away s) hT
  let _ := locUniformSpace P T s _ hden
  have _ := isUniformAddGroup_locUniformSpace P T s _ hden
  have _ := isTopologicalRing_locUniformSpace P T s _ hden
  have _ := isHuberRing_completion_locTopology P T s _ hden
  have _ := isNoetherianType_completion_locTopology_of_isNoetherianType P
    (Ideal.isOpen_of_isOpen_subideal (Ideal.span_mono (Set.subset_insert _ _)) hT) _ hden
  let S' : Pair (UniformSpace.Completion (Localization.Away s)) :=
    ⟨completedPlusSubring P Aplus T s _ hden, isRingOfIntegralElements_completedPlusSubring P
      Aplus (fun j _ ↦ hP j.2) hAplus T s _ hden⟩
  exact (PreAdicSpace.mem_propOpens_iff _).mpr <|
    ObjectProperty.prop_of_iso PreAdicSpace.isNoetherianAffinoid
    (restrictSpaBasicOpenIso P Aplus T s _ hden hAplus hP hT).symm
    (PreAdicSpace.isNoetherianAffinoid_presentationLimitPreAdicSpace S'
      (completionLocalization P T s _ hden)
      (completionLocalization_ringOfDefinition_le_completedPlusSubring P Aplus hP T s _ hden))

/-- **The open affinoids of noetherian type form a basis of `Spa(A, A⁺)`** when `A` is of noetherian
type, since the rational opens do. -/
theorem isBasis_noetherianAffinoidOpens_presentationLimitPreAdicSpace :
    Opens.IsBasis (presentationLimitPreAdicSpace P Aplus hAplus hP).noetherianAffinoidOpens := by
  refine Opens.isBasis_iff_nbhd.mpr fun {U x} hx ↦ ?_
  obtain ⟨V, hV, hxV, hVU⟩ := Opens.isBasis_iff_nbhd.mp (isBasis_spaRationalOpens Aplus) hx
  obtain ⟨T, s, hT, rfl⟩ := mem_spaRationalOpens_iff_exists_spaBasicOpen.mp hV
  exact ⟨_, spaBasicOpen_mem_noetherianAffinoidOpens P Aplus hAplus hP hT, hxV, hVU⟩

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

end TauCeti
