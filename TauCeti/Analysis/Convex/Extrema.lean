/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Extrema

/-!
# Local supporting hyperplanes of convex functions are global

A local minimum of a convex function on a convex set is a global minimum
(`IsMinOn.of_isLocalMinOn_of_convexOn`). Applied to `u - ℓ` for a linear functional `ℓ`, this
says that an affine function `x' ↦ u x + ℓ (x' - x)` lying below a convex function `u` near `x`
lies below it on the whole domain. In particular a subgradient of `u` relative to an open
neighbourhood of `x` in the domain is a subgradient relative to the whole domain.
-/

public section

open Filter

open scoped Topology

variable {E : Type*} [AddCommGroup E] [TopologicalSpace E] [Module ℝ E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] {s : Set E} {u : E → ℝ} {x : E}

/-- **Local supporting hyperplanes of a convex function are global.** If `u` is convex on `s`,
`x ∈ s`, and the affine function `x' ↦ u x + ℓ (x' - x)` lies below `u` at the points of `s`
near `x`, then it lies below `u` on all of `s`. -/
theorem ConvexOn.add_le_of_eventually_add_le (hu : ConvexOn ℝ s u) (hx : x ∈ s)
    (ℓ : E →ₗ[ℝ] ℝ) (h : ∀ᶠ x' in 𝓝[s] x, u x + ℓ (x' - x) ≤ u x') :
    ∀ x' ∈ s, u x + ℓ (x' - x) ≤ u x' := by
  have hmin : IsMinOn (fun y => u y - ℓ y) s x :=
    IsMinOn.of_isLocalMinOn_of_convexOn hx
      (h.mono fun x' hx' => by simp only [map_sub] at hx'; linarith)
      (hu.sub (ℓ.concaveOn hu.1))
  intro x' hx'
  have := isMinOn_iff.1 hmin x' hx'
  simp only [map_sub]
  linarith
