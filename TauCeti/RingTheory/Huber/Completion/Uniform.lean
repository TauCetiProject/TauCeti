/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Completion.Basic
public import TauCeti.RingTheory.Huber.Uniform

/-!
# Completions of uniform Huber rings

A Huber ring `A` is uniform exactly when its completion `Â` is. One direction holds because `A°`
is then a ring of definition, and `Â°`, the closure of the image of `A°`, is the ring of
definition of the completed pair. The other holds because `A°` is the preimage of `Â°`, and a set
whose image in `Â` is bounded was already bounded.

This is what makes the separated completion of a uniform ring uniform, as in the construction of
the uniformization of a Tate ring.

## Main results

* `TauCeti.Huber.isUniform_completion_iff`: `Â` is uniform if and only if `A` is.

## References

* [Wedhorn, *Adic Spaces*][wedhorn_adic], Remark 6.8 and Lemma 7.47.
-/

public section

open UniformSpace

namespace TauCeti.Huber

variable {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]
  [IsHuberRing A]

/-- **A Huber ring is uniform exactly when its completion is.** -/
theorem isUniform_completion_iff : IsUniform (Completion A) ↔ IsUniform A := by
  refine ⟨fun h ↦ isUniform_iff.mpr (isBounded_of_isBounded_image_completion_coe ?_),
    fun h ↦ ?_⟩
  · -- the image of `A°` lies in `Â°`
    refine (isUniform_iff.mp h).subset ?_
    rintro _ ⟨a, ha, rfl⟩
    exact isPowerBounded_completion_coe_iff.mpr ha
  · -- `A°` is a ring of definition, and the completed ring of definition is `Â°`
    obtain ⟨Q, hQ⟩ := isUniform_iff_exists_pairOfDefinition_ringOfDefinition_eq.mp h
    refine isUniform_iff_exists_pairOfDefinition_ringOfDefinition_eq.mpr ⟨Q.completion, ?_⟩
    rw [← topologicalClosure_map_coeRingHom_powerBoundedSubring, ← hQ]
    refine SetLike.coe_injective ?_
    rw [Q.completion_ringOfDefinition, Q.coe_completionRingOfDefinition,
      Subring.topologicalClosure_coe, Subring.coe_map]
    -- `Completion.coeRingHom` is the bundled coercion `A → Â`
    rfl

/-- The completion of a uniform Huber ring is uniform. -/
instance IsUniform.completion [IsUniform A] : IsUniform (Completion A) :=
  isUniform_completion_iff.mpr ‹_›

end TauCeti.Huber
