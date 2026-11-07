/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Extending primitives from a convex part of a disc

Mathlib's `DifferentiableOn.isExactOn_ball` gives every holomorphic function on a disc a
primitive there.  This file records the gluing consequence: a primitive of the same integrand on
a convex part of the disc extends to a primitive on the whole disc, because two primitives of one
function differ by a constant on a convex set.

## Main results

* `DifferentiableOn.exists_hasDerivAt_eqOn_ball_inter` -- a primitive of a holomorphic integrand
  on `ball c r ∩ U`, for convex `U`, is the restriction of a primitive on `ball c r`.
-/

public section

open Complex Metric Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- A holomorphic integrand `g` on a disc has a primitive on the disc agreeing with any given
primitive `f` of `g` on the intersection of the disc with a convex set `U`. -/
theorem DifferentiableOn.exists_hasDerivAt_eqOn_ball_inter {f g : ℂ → E} {c : ℂ} {r : ℝ}
    {U : Set ℂ} (hg : DifferentiableOn ℂ g (ball c r)) (hU : Convex ℝ U)
    (hf : ∀ z ∈ ball c r ∩ U, HasDerivAt f (g z) z) :
    ∃ G : ℂ → E, (∀ z ∈ ball c r, HasDerivAt G (g z) z) ∧ EqOn G f (ball c r ∩ U) := by
  obtain ⟨P, hP⟩ := hg.isExactOn_ball
  rcases (ball c r ∩ U).eq_empty_or_nonempty with hV | ⟨z₀, hz₀⟩
  · exact ⟨P, hP, by simp [hV]⟩
  refine ⟨fun z ↦ P z + (f z₀ - P z₀), fun z hz ↦ (hP z hz).add_const _, fun z hz ↦ ?_⟩
  have hderiv (w) (hw : w ∈ ball c r ∩ U) :
      HasDerivWithinAt (f - P) 0 (ball c r ∩ U) w := by
    simpa using ((hf w hw).sub (hP w hw.1)).hasDerivWithinAt
  have := ((convex_ball c r).inter hU).norm_image_sub_le_of_norm_hasDerivWithin_le hderiv
    (fun _ _ ↦ norm_zero.le) hz₀ hz
  rw [zero_mul, norm_le_zero_iff, sub_eq_zero, Pi.sub_apply, Pi.sub_apply] at this
  simp [← this]
