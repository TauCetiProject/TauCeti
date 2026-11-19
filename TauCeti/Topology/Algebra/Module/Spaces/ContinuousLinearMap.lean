/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

/-!
# Ranges of conjugated continuous linear maps

Conjugating an endomorphism `P` by a continuous linear equivalence `e`, via Mathlib's
`ContinuousLinearEquiv.conjContinuousAlgEquiv`, gives an endomorphism `e P e⁻¹` whose range is the
image under `e` of the range of `P`.

## Main results

* `ContinuousLinearEquiv.range_conjContinuousAlgEquiv`: `range (e P e⁻¹) = e (range P)`.
-/

public section

namespace ContinuousLinearEquiv

variable {𝕜 G H : Type*} [NormedField 𝕜] [AddCommGroup G] [AddCommGroup H] [Module 𝕜 G]
  [Module 𝕜 H] [TopologicalSpace G] [TopologicalSpace H] [IsTopologicalAddGroup G]
  [IsTopologicalAddGroup H] [ContinuousConstSMul 𝕜 G] [ContinuousConstSMul 𝕜 H]

/-- The range of the conjugate `e P e⁻¹` is the image under `e` of the range of `P`. -/
@[simp]
theorem range_conjContinuousAlgEquiv (e : G ≃L[𝕜] H) (P : G →L[𝕜] G) :
    (e.conjContinuousAlgEquiv P).range = P.range.map (e : G →ₗ[𝕜] H) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨P (e.symm x), ⟨e.symm x, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨e x, by simp⟩

end ContinuousLinearEquiv
