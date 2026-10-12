/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.RationalOpen

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

namespace TauCeti.PreAdicSpace

open Huber Huber.PairOfDefinition ValuationSpectrum

universe u

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
    let T : Finset A := {1}
    have hT : IsOpen (Ideal.span (T : Set A) : Set A) := by simp [T]
    let B := Localization.Away (1 : A)
    have hden := hasDenominatorPower_of_isOpen_span P T 1 B hT
    let _ := locUniformSpace P {1} 1 B hden
    have _ := isUniformAddGroup_locUniformSpace P {1} 1 B hden
    have _ := isTopologicalRing_locUniformSpace P {1} 1 B hden
    have _ := isHuberRing_completion_locTopology P {1} 1 B hden
    let S' : Pair (UniformSpace.Completion B) :=
      ⟨completedPlusSubring P S.plus {1} 1 B hden,
        isRingOfIntegralElements_completedPlusSubring P S.plus (fun a _ ↦ hP a.2)
          S.isRingOfIntegralElements.isPowerBounded_of_mem {1} 1 B hden⟩
    let hj := isOpenEmbedding_spaComapLocHom P S.plus hP {1} 1 B hden
    have hr : Set.range (spaComapLocHom P S.plus {1} 1 B hden) = Set.univ := by
      rw [coe_spaComapLocHom, range_spaComapLoc P S.plus hP {1} 1 B hden]
      ext x
      simp [mem_spaBasicOpen, rationalSubset_singleton_one]
    let M := presentationLimitPreAdicSpace P S.plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem hP
    have hrange : Set.range (Opens.inclusion' (⊤ : Opens M)) =
        Set.range (spaComapLocHom P S.plus {1} 1 B hden) := by
      rw [Opens.set_range_inclusion', hr]
      exact Opens.coe_top
    let e' := M.restrictTopIso.symm ≪≫
      M.restrictIsoOfRangeEq (⊤ : Opens M).isOpenEmbedding hj hrange
    exact ⟨UniformSpace.Completion B, inferInstance, inferInstance, inferInstance,
      inferInstance, inferInstance, inferInstance, inferInstance, S',
      completionLocalization P {1} 1 B hden,
      completionLocalization_ringOfDefinition_le_completedPlusSubring P S.plus hP {1} 1 B hden,
      ⟨e ≪≫ e' ≪≫ presentationLimitPreAdicSpaceLocIso P S.plus {1} 1 B hden
        S.isRingOfIntegralElements.isPowerBounded_of_mem hP hT⟩⟩
  · rintro ⟨A, _, _, _, _, _, _, _, S, P, hP, ⟨e⟩⟩
    exact (isAffinoid_iff X).mpr
      ⟨A, inferInstance, inferInstance, inferInstance, inferInstance, S, P, hP, ⟨e⟩⟩

end TauCeti.PreAdicSpace
