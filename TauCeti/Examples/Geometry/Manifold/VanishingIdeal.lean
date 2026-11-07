/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Geometry.Manifold.Algebra.VanishingIdeal.Basic

/-!
# Examples: the vanishing ideal and the cotangent space of `ℝ` at `0`

Write `t` for the coordinate function on `ℝ` and `I₀` for the ideal of smooth functions vanishing
at `0`. Then `t² = t · t` lies in `I₀²`, while `t` does not, since its derivative at `0` is `1`.
Under the identification `I₀ / I₀² ≃ T₀*ℝ` of `TauCeti.smoothCotangentEquiv`, the class of `t`
is the coordinate differential: it evaluates to `3` on the tangent vector `3`, whereas the class
of `t²` is zero and evaluates to `0`. The cotangent class therefore remembers the first-order
behaviour of a function, and nothing more.
-/

open TauCeti
open scoped Manifold ContDiff

-- `t² = t · t` lies in `I₀²`.
example (t : C^∞⟮𝓘(ℝ), ℝ; ℝ⟯) (ht : ∀ s, t s = s) :
    t ^ 2 ∈ smoothVanishingIdeal 𝓘(ℝ) (0 : ℝ) ^ 2 := by
  have h : t ∈ smoothVanishingIdeal 𝓘(ℝ) (0 : ℝ) := by simp [ht]
  simpa [sq] using Ideal.mul_mem_mul h h

-- `t` does not lie in `I₀²`: its derivative at `0` takes the value `1` on the tangent vector `1`.
example (t : C^∞⟮𝓘(ℝ), ℝ; ℝ⟯) (ht : ∀ s, t s = s) :
    t ∉ smoothVanishingIdeal 𝓘(ℝ) (0 : ℝ) ^ 2 := fun h ↦ by
  have hchart : (t : ℝ → ℝ) =ᶠ[nhds 0] extChartAt 𝓘(ℝ) (0 : ℝ) :=
    Filter.Eventually.of_forall fun s ↦ by simp [ht]
  have h₁ := congr($(mvfderiv_eq_zero_of_mem_smoothVanishingIdeal_sq h) 1)
  rw [mvfderiv_apply_of_eventuallyEq_extChartAt hchart] at h₁
  exact one_ne_zero h₁

-- The class of `t` evaluates to `3` on the tangent vector `3`.
example (t : C^∞⟮𝓘(ℝ), ℝ; ℝ⟯) (ht : ∀ s, t s = s)
    (h₀ : t ∈ smoothVanishingIdeal 𝓘(ℝ) (0 : ℝ)) :
    smoothCotangentEquiv BoundarylessManifold.isInteriorPoint
      ((smoothVanishingIdeal 𝓘(ℝ) (0 : ℝ)).toCotangent ⟨t, h₀⟩) (3 : ℝ) = 3 := by
  rw [smoothCotangentEquiv_toCotangent_of_eventuallyEq _ _ (ContinuousLinearMap.id ℝ ℝ)
    (Filter.Eventually.of_forall fun s ↦ by simp [ht])]
  exact ContinuousLinearMap.id_apply _

-- The class of `t²` is zero, so it evaluates to `0` on the tangent vector `3`.
example (t : C^∞⟮𝓘(ℝ), ℝ; ℝ⟯) (ht : ∀ s, t s = s)
    (h₀ : t ^ 2 ∈ smoothVanishingIdeal 𝓘(ℝ) (0 : ℝ)) :
    smoothCotangentEquiv BoundarylessManifold.isInteriorPoint
      ((smoothVanishingIdeal 𝓘(ℝ) (0 : ℝ)).toCotangent ⟨t ^ 2, h₀⟩) (3 : ℝ) = 0 := by
  have h : t ∈ smoothVanishingIdeal 𝓘(ℝ) (0 : ℝ) := by simp [ht]
  rw [(Ideal.toCotangent_eq_zero _ _).mpr (by simpa [sq] using Ideal.mul_mem_mul h h), map_zero]
  exact zero_apply _
