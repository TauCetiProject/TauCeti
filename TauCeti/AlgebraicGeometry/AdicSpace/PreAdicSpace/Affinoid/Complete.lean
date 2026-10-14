/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.RationalOpen
public import TauCeti.RingTheory.Huber.LocalizationTopology.Pair
public import TauCeti.RingTheory.Huber.LocalizationTopology.Trivial

/-!
# Complete models of affinoid pre-adic spaces

Every affinoid pre-adic space can be presented by a complete Hausdorff Huber pair,
with an isomorphism retaining the structure presheaf and stalk valuations.
Complete models allow local morphism properties to be checked using
maps of complete Huber pairs, even when the original affinoid presentation was incomplete.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Remarks 8.4 and 8.8.
-/

public section

open CategoryTheory TopologicalSpace Topology

namespace TauCeti.ValuationSpectrum

open Huber Huber.PairOfDefinition ValuationSpectrum

universe u

/-- The pre-adic space of a Huber pair is isomorphic to the pre-adic space of its
complete Hausdorff model, with the completed plus subring and pair of definition. -/
noncomputable def presentationLimitPreAdicSpaceCompleteIso
    {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (P : PairOfDefinition A) (Aplus : Subring A)
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) (hP : P.ringOfDefinition ≤ Aplus)
    (B : Type u) [CommRing B] [Algebra A B] [IsLocalization.Away (1 : A) B]
    (hden : HasDenominatorPower P {1} 1 B) :
    letI := locUniformSpace P {1} 1 B hden
    letI := isUniformAddGroup_locUniformSpace P {1} 1 B hden
    letI := isTopologicalRing_locUniformSpace P {1} 1 B hden
    presentationLimitPreAdicSpace P Aplus hAplus hP ≅
      presentationLimitPreAdicSpace (completionLocalization P {1} 1 B hden)
        (completedPlusSubring P Aplus {1} 1 B hden)
        (isPowerBounded_of_mem_completedPlusSubring P Aplus hAplus {1} 1 B hden)
        (completionLocalization_ringOfDefinition_le_completedPlusSubring P Aplus hP
          {1} 1 B hden) := by
  letI := locUniformSpace P {1} 1 B hden
  letI := isUniformAddGroup_locUniformSpace P {1} 1 B hden
  letI := isTopologicalRing_locUniformSpace P {1} 1 B hden
  let hj := isOpenEmbedding_spaComapLocHom P Aplus hP {1} 1 B hden
  -- The rational subset R({1}/1) is the whole space, so this restriction retains all of Spa.
  have hr : Set.range (spaComapLocHom P Aplus {1} 1 B hden) = Set.univ := by
    rw [coe_spaComapLocHom, range_spaComapLoc P Aplus hP {1} 1 B hden]
    ext x
    simp [mem_spaBasicOpen, rationalSubset_singleton_one]
  let M := presentationLimitPreAdicSpace P Aplus hAplus hP
  have hrange : Set.range (Opens.inclusion' (⊤ : Opens M)) =
      Set.range (spaComapLocHom P Aplus {1} 1 B hden) := by
    rw [Opens.set_range_inclusion', hr]
    exact Opens.coe_top
  exact M.restrictTopIso.symm ≪≫
    M.restrictIsoOfRangeEq (⊤ : Opens M).isOpenEmbedding hj hrange ≪≫
    presentationLimitPreAdicSpaceLocIso P Aplus {1} 1 B hden hAplus hP (by simp)

end TauCeti.ValuationSpectrum

namespace TauCeti.PreAdicSpace

open Huber Huber.PairOfDefinition ValuationSpectrum

/-- An affinoid pre-adic space admits a presentation by a complete Hausdorff Huber pair,
with an isomorphism of pre-adic spaces, including the stalk valuations. -/
theorem isAffinoid_iff_exists_complete (X : PreAdicSpace.{u}) : isAffinoid X ↔
    ∃ (A : Type u) (_ : CommRing A) (_ : UniformSpace A) (_ : IsUniformAddGroup A)
      (_ : IsTopologicalRing A) (_ : CompleteSpace A) (_ : T2Space A) (_ : IsHuberRing A)
      (S : Pair A) (P : PairOfDefinition A) (hP : P.ringOfDefinition ≤ S.plus),
      Nonempty (X ≅ presentationLimitPreAdicSpace P S.plus
        S.isRingOfIntegralElements.isPowerBounded_of_mem hP) := by
  classical
  constructor
  · intro hX
    obtain ⟨A, _, _, _, _, S, P, hP, ⟨e⟩⟩ := (isAffinoid_iff X).mp hX
    let B := Localization.Away (1 : A)
    have hden := hasDenominatorPower_denom_one P {1} B
    let _ := locUniformSpace P {1} 1 B hden
    have _ := isUniformAddGroup_locUniformSpace P {1} 1 B hden
    have _ := isTopologicalRing_locUniformSpace P {1} 1 B hden
    have _ := isHuberRing_completion_locTopology P {1} 1 B hden
    let S' : Pair (UniformSpace.Completion B) :=
      rationalLocalizationPair P S hP {1} 1 B hden
    have hP' : (completionLocalization P {1} 1 B hden).ringOfDefinition ≤ S'.plus := by
      simpa only [S', rationalLocalizationPair_plus] using
        completionLocalization_ringOfDefinition_le_completedPlusSubring P S.plus hP
          {1} 1 B hden
    refine ⟨UniformSpace.Completion B, inferInstance, inferInstance, inferInstance,
      inferInstance, inferInstance, inferInstance, inferInstance, S',
      completionLocalization P {1} 1 B hden, hP', ⟨?_⟩⟩
    simpa only [S', rationalLocalizationPair_plus] using
      e ≪≫ presentationLimitPreAdicSpaceCompleteIso P S.plus
        S.isRingOfIntegralElements.isPowerBounded_of_mem hP B hden
  · rintro ⟨A, _, _, _, _, _, _, _, S, P, hP, ⟨e⟩⟩
    exact (isAffinoid_iff X).mpr
      ⟨A, inferInstance, inferInstance, inferInstance, inferInstance, S, P, hP, ⟨e⟩⟩

end TauCeti.PreAdicSpace
