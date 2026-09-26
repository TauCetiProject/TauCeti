/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.StronglyNoetherian.Basic
import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Iterate

/-!
# Strong noetherianness and separated completion

A Huber ring is strongly noetherian if and only if its separated completion is strongly
noetherian. This permits reduction to complete Hausdorff rings in Tate acyclicity without
requiring the original ring to be Hausdorff.

The proof uses the existing topological identification `A⟨⟩ ≃ Â` and the iteration isomorphism
`A⟨X₁,…,Xₖ⟩ ≃ A⟨⟩⟨X₁,…,Xₖ⟩`. In particular it compares every restricted-series algebra,
rather than only the noetherianness of `Â` itself.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, §6.7 and Theorem 8.28.
-/

public section

namespace TauCeti.Huber

open UniformSpace

variable (A : Type*) [CommRing A] [UniformSpace A] [IsUniformAddGroup A]
  [IsTopologicalRing A] [IsHuberRing A]

/-- Strong noetherianness is unchanged by separated completion of a Huber ring.
Neither completeness nor separatedness of the original ring is required. -/
@[simp]
theorem isStronglyNoetherian_completion_iff :
    IsStronglyNoetherian (Completion A) ↔ IsStronglyNoetherian A := by
  -- Lift the zero-variable comparison using the given uniformity on `A`.
  -- The existing completed comparison fixes the canonical group uniformity instead.
  let e : restrictedMvPowerSeriesCompletion 0 A ≃+* Completion A :=
    Completion.mapRingEquiv
      (weightedRestrictedSubringFinZeroEquiv (fun _ : Fin 0 ↦ ({1} : Set A)))
      (continuous_weightedRestrictedSubringFinZeroEquiv _)
      (continuous_weightedRestrictedSubringFinZeroEquiv_symm _)
  have he : Continuous e :=
    Completion.continuous_map.congr fun x ↦ (Completion.mapRingEquiv_apply _ _ _ x).symm
  have he' : Continuous e.symm :=
    Completion.continuous_map.congr fun x ↦ (Completion.mapRingEquiv_symm_apply _ _ _ x).symm
  have h := isStronglyNoetherian_congr e he he'
  constructor
  · intro hA
    have : IsStronglyNoetherian (restrictedMvPowerSeriesCompletion 0 A) := h.mpr hA
    refine ⟨fun k ↦ ?_⟩
    have hk :=
      isNoetherianRing_of_ringEquiv _ (iterateRingEquiv 0 k A).symm
    rwa [Nat.zero_add] at hk
  · intro hA
    exact h.mp inferInstance

/-- The separated completion of a strongly noetherian Huber ring is strongly noetherian. -/
instance IsStronglyNoetherian.completion [IsStronglyNoetherian A] :
    IsStronglyNoetherian (Completion A) :=
  (isStronglyNoetherian_completion_iff A).mpr inferInstance

end TauCeti.Huber

end
