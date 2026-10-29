/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.StarProjection
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital

/-!
# Star projections from the continuous functional calculus

If a real function `f` takes only the values `0` and `1` on the spectrum of `a`, then `cfc f a` is
a star projection. When `f` is continuous on the spectrum and `a` is self-adjoint this follows
from multiplicativity of the functional calculus; otherwise `cfc f a` is the junk value `0`. In
particular the spectral projector `cfc (Ω.indicator 1) a` is a star projection for every set
`Ω ⊆ ℝ` and every `a`.

## Main results

* `TauCeti.isStarProjection_cfc` — `cfc f a` is a star projection when `f` is idempotent-valued on
  the spectrum of `a`;
* `TauCeti.isStarProjection_cfc_indicator` — the spectral projector `cfc (Ω.indicator 1) a` is a
  star projection.
-/

public section

namespace TauCeti

variable {A : Type*} [Ring A] [StarRing A] [TopologicalSpace A] [Algebra ℝ A]
  [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]

/-- If `f t` is idempotent (that is, `0` or `1`) at every point `t` of the spectrum of `a`, then
`cfc f a` is a star projection. -/
theorem isStarProjection_cfc {f : ℝ → ℝ} {a : A}
    (hf : ∀ t ∈ spectrum ℝ a, IsIdempotentElem (f t)) : IsStarProjection (cfc f a) := by
  by_cases h : IsSelfAdjoint a ∧ ContinuousOn f (spectrum ℝ a)
  · obtain ⟨ha, hcont⟩ := h
    refine ⟨?_, cfc_predicate f a⟩
    rw [IsIdempotentElem, ← cfc_mul f f a]
    exact cfc_congr hf
  · rcases not_and_or.1 h with ha | hcont
    · rw [cfc_apply_of_not_predicate a ha]
      exact .zero _
    · rw [cfc_apply_of_not_continuousOn a hcont]
      exact .zero _

/-- The spectral projector `cfc (Ω.indicator 1) a` is a star projection for every `Ω ⊆ ℝ`. (When
`a` is not self-adjoint, or the indicator is not continuous on its spectrum, it is the junk value
`0`.) -/
theorem isStarProjection_cfc_indicator (a : A) (Ω : Set ℝ) :
    IsStarProjection (cfc (Ω.indicator (1 : ℝ → ℝ)) a) :=
  isStarProjection_cfc fun t _ ↦ by by_cases ht : t ∈ Ω <;> simp [ht, IsIdempotentElem]

end TauCeti
