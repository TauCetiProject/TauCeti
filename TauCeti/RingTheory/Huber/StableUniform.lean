/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.LocalizationTopology.CompleteSeparated.Basic
public import TauCeti.RingTheory.Huber.LocalizationTopology.Trivial
public import TauCeti.RingTheory.Huber.Uniform

/-!
# Stably uniform Tate rings

A Tate ring is *stably uniform* when each of its completed rational localizations is uniform.
A rational localization is represented by a finite numerator set `T`, a denominator `s`, and
the condition that the ideal spanned by `T` is open.  The coordinate ring is the separated
completion `A⟨T/s⟩` of the corresponding topological localization.  This is Wedhorn's
convention; a presentation in the convention where only `insert s T` must generate the unit ideal
is covered by the numerator set `insert s T`, which has the same ring `A₀[T/s]` by
`TauCeti.Huber.PairOfDefinition.locSubring_insert_eq_of_divBy_mem` (as `s/s = 1`).

The definition quantifies over pairs of definition because the current construction of
`A⟨T/s⟩` uses one to present its topology.  The ring `A⟨T/s⟩` does not depend on that choice
(`TauCeti.Huber.PairOfDefinition.completionLocObj_congr_pairOfDefinition`), so the rational
localizations over a single pair of definition already decide stable uniformity.  The definition
does not involve a ring of integral elements: stable uniformity is a property of the underlying
Tate ring, not of the choice of plus ring.

The definition needs no completeness or separation hypothesis on `A`, since each `A⟨T/s⟩` is
itself a separated completion.  When `A` is complete and Hausdorff, the trivial rational
localization `A⟨{1}/1⟩` is canonically isomorphic to `A`.  Consequently, stable uniformity then
implies uniformity of `A` itself; this is the first basic consequence needed by
the Buzzard–Verberkmoes sheafiness criterion.

## Main definitions

* `TauCeti.Huber.IsStablyUniform`: every completed rational localization of a Tate ring is
  uniform.

## Main results

* `TauCeti.Huber.isStablyUniform_iff`: the defining property, exposed as an equivalence.
* `TauCeti.Huber.isStablyUniform_iff_forall_isUniform_completionLocObj`: it suffices to check the
  rational localizations over one pair of definition.
* `TauCeti.Huber.IsStablyUniform.isUniform`: a stably uniform complete Hausdorff Tate ring is
  uniform.

## References

* D. Hansen, K. S. Kedlaya, *Sheafiness criteria for Huber rings*, Definitions 2.3 and 3.13.
* K. Buzzard, A. Verberkmoes, *Stably uniform affinoids are sheafy*, J. reine angew. Math. 740
  (2018), 25–39.
-/

public section

namespace TauCeti.Huber

open Topology

/-- A Tate ring is *stably uniform* when every completed rational localization `A⟨T/s⟩` is
uniform.  The openness of the ideal spanned by `T` is exactly the admissibility
condition for the rational localization; it supplies the denominator-power hypothesis needed to
construct its topology. -/
class IsStablyUniform (A : Type*) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsTateRing A] : Prop where
  /-- Every admissible completed rational localization is uniform. -/
  isUniform_rationalLocalization (P : PairOfDefinition A) (T : Finset A) (s : A)
      (hT : IsOpen (Ideal.span (T : Set A) : Set A)) :
    let hden := P.hasDenominatorPower_of_isOpen_span T s (Localization.Away s) hT
    letI := P.locUniformSpace T s (Localization.Away s) hden
    letI := P.isUniformAddGroup_locUniformSpace T s (Localization.Away s) hden
    letI := P.isTopologicalRing_locUniformSpace T s (Localization.Away s) hden
    IsUniform (UniformSpace.Completion (Localization.Away s))

variable (A : Type*) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsTateRing A]

/-- The defining property of stable uniformity: all admissible completed rational localizations
are uniform. -/
theorem isStablyUniform_iff : IsStablyUniform A ↔
    ∀ (P : PairOfDefinition A) (T : Finset A) (s : A)
      (hT : IsOpen (Ideal.span (T : Set A) : Set A)),
      let hden := P.hasDenominatorPower_of_isOpen_span T s (Localization.Away s) hT
      letI := P.locUniformSpace T s (Localization.Away s) hden
      letI := P.isUniformAddGroup_locUniformSpace T s (Localization.Away s) hden
      letI := P.isTopologicalRing_locUniformSpace T s (Localization.Away s) hden
      IsUniform (UniformSpace.Completion (Localization.Away s)) :=
  ⟨fun h ↦ h.isUniform_rationalLocalization,
    fun h ↦ ⟨fun P T s hT ↦ h P T s hT⟩⟩

variable {A} in
/-- **One pair of definition suffices**: for any fixed pair of definition `P`, a Tate ring is
stably uniform exactly when its admissible completed rational localizations `A⟨T/s⟩` over `P`
are uniform. Unlike `isStablyUniform_iff`, which ranges over all pairs of definition, the
localizations here are the bundled objects `P.completionLocObj` of
`CompleteSeparatedTopCommRingCat`, so uniformity can be moved along isomorphisms of these objects
with `CategoryTheory.Iso.isUniform_iff`. -/
theorem isStablyUniform_iff_forall_isUniform_completionLocObj (P : PairOfDefinition A) :
    IsStablyUniform A ↔ ∀ (T : Finset A) (s : A) (hT : IsOpen (Ideal.span (T : Set A) : Set A)),
      IsUniform (P.completionLocObj T s (Localization.Away s)
        (P.hasDenominatorPower_of_isOpen_span T s _ hT)) := by
  rw [isStablyUniform_iff]
  refine ⟨fun h T s hT ↦ P.completionLocObj_obj T s (Localization.Away s) _ ▸ h P T s hT,
    fun h P' T s hT ↦ ?_⟩
  -- the same rational localization, presented over `P`
  have hP := h T s hT
  rwa [P.completionLocObj_congr_pairOfDefinition P' _ _ _ _
    (P'.hasDenominatorPower_of_isOpen_span T s _ hT), P'.completionLocObj_obj] at hP

/-- A stably uniform complete Hausdorff Tate ring is uniform.  This is stable uniformity applied to
the trivial rational localization `A⟨{1}/1⟩`, transported back along its canonical topological
ring isomorphism with `A`. -/
theorem IsStablyUniform.isUniform {A : Type*} [CommRing A] [UniformSpace A]
    [IsUniformAddGroup A] [IsTopologicalRing A] [CompleteSpace A] [T0Space A] [IsTateRing A]
    [IsStablyUniform A] : IsUniform A := by
  obtain ⟨P⟩ := IsHuberRing.nonempty_pairOfDefinition (A := A)
  let T : Finset A := {1}
  have hT : IsOpen (Ideal.span (T : Set A) : Set A) := by
    simp [T]
  let S := Localization.Away (1 : A)
  let hden := P.hasDenominatorPower_of_isOpen_span T 1 S hT
  let _ := P.locUniformSpace T 1 S hden
  have _ := P.isUniformAddGroup_locUniformSpace T 1 S hden
  have _ := P.isTopologicalRing_locUniformSpace T 1 S hden
  have hloc : IsUniform (UniformSpace.Completion S) :=
    IsStablyUniform.isUniform_rationalLocalization P T 1 hT
  have hTpb : ∀ t ∈ T, IsPowerBounded t := by
    simp [T]
  let e : A ≃+* UniformSpace.Completion S :=
    P.toCompletionLocEquivDenomOne T hTpb S
  have he : Continuous e := by
    exact (P.continuous_toCompletionLoc T 1 S
      (P.hasDenominatorPower_denom_one T S)).congr fun a ↦
        (P.toCompletionLocEquivDenomOne_apply T hTpb S a).symm
  have he' : Continuous e.symm := by
    simpa only [e] using
      P.continuous_toCompletionLocEquivDenomOne_symm T hTpb S
  exact (isUniform_iff_of_ringEquiv e he he').mpr hloc

end TauCeti.Huber
