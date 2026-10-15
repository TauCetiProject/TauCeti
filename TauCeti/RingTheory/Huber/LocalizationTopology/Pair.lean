/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.LocalizationTopology.Plus

/-!
# Completed rational localisation as a Huber pair

Bundle the completed coordinate ring `A⟨T/s⟩` and its ring of integral elements `A_U⁺`
into a Huber pair, together with the structure morphism from `(A, A⁺)`. The plus ring is
the closure of the image of the integral closure of `A⁺[T/s]` in `A[1/s]`, as constructed
in `TauCeti.RingTheory.Huber.LocalizationTopology.Plus`.

This construction applies to arbitrary Huber rings, including non-Tate rings. It lets
statements about coordinate rings retain the plus-ring data used by the adic spectrum.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, §8.1 and Lemma 7.47.
-/

public section

open UniformSpace

namespace TauCeti.Huber.PairOfDefinition

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
  (P : PairOfDefinition A) (U : Pair A) (hP : P.ringOfDefinition ≤ U.plus)
  (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S]
  [IsLocalization.Away s S] (hden : HasDenominatorPower P T s S)

/-- The completed rational localisation pair `(A⟨T/s⟩, A_U⁺)`, with plus ring the closure
of the image of the integral closure of `A⁺[T/s]` in `A[1/s]`. -/
noncomputable def rationalLocalizationPair :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_completion_locTopology P T s S hden
    Pair (Completion S) :=
  letI := locUniformSpace P T s S hden
  letI := isUniformAddGroup_locUniformSpace P T s S hden
  letI := isTopologicalRing_locUniformSpace P T s S hden
  letI := isHuberRing_completion_locTopology P T s S hden
  ⟨completedPlusSubring P U.plus T s S hden,
    isRingOfIntegralElements_completedPlusSubring P U.plus (fun j _ ↦ hP j.2)
      U.isRingOfIntegralElements.isPowerBounded_of_mem T s S hden⟩

/-- The plus ring of the rational localisation pair is `completedPlusSubring`. -/
@[simp]
theorem rationalLocalizationPair_plus :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_completion_locTopology P T s S hden
    (rationalLocalizationPair P U hP T s S hden).plus =
      completedPlusSubring P U.plus T s S hden := (rfl)

/-- The structure map to a completed rational localisation as a morphism of Huber pairs. -/
noncomputable def toCompletionLocHom :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_completion_locTopology P T s S hden
    Pair.Hom U (rationalLocalizationPair P U hP T s S hden) :=
  letI := locUniformSpace P T s S hden
  letI := isUniformAddGroup_locUniformSpace P T s S hden
  letI := isTopologicalRing_locUniformSpace P T s S hden
  letI := isHuberRing_completion_locTopology P T s S hden
  { toRingHom := toCompletionLoc P T s S hden
    continuous_toRingHom := continuous_toCompletionLoc P T s S hden
    map_mem_plus := fun _ ha ↦ toCompletionLoc_mem_completedPlusSubring P U.plus T s S hden ha }

/-- The pair structure map has `toCompletionLoc` as its underlying ring homomorphism. -/
@[simp]
theorem toRingHom_toCompletionLocHom :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_completion_locTopology P T s S hden
    (toCompletionLocHom P U hP T s S hden).toRingHom = toCompletionLoc P T s S hden := (rfl)

end TauCeti.Huber.PairOfDefinition
