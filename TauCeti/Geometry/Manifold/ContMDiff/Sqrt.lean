/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Square roots of real functions on manifolds

The square root `x ↦ Real.sqrt (u x)` of a `C^n` real function `u` on a manifold is `C^n`
wherever `u` does not vanish, since `Real.sqrt` is smooth away from `0`.

## Main results

* `ContMDiffWithinAt.sqrt`, `ContMDiffAt.sqrt`, `ContMDiffOn.sqrt`, `ContMDiff.sqrt`:
  square-root composition preserves `C^n` regularity away from zeros.
-/

public section

open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {n : ℕ∞ω} {u : M → ℝ} {s : Set M} {x : M}

/-- The square root of a real function that is `C^n` within a set at a point where it does not
vanish is `C^n` within that set at that point. -/
theorem ContMDiffWithinAt.sqrt (hu : ContMDiffWithinAt I 𝓘(ℝ) n u s x) (hx : u x ≠ 0) :
    ContMDiffWithinAt I 𝓘(ℝ) n (fun y ↦ Real.sqrt (u y)) s x :=
  (Real.contDiffAt_sqrt hx).comp_contMDiffWithinAt hu

/-- The square root of a real function that is `C^n` at a point where it does not vanish is
`C^n` there. -/
theorem ContMDiffAt.sqrt (hu : ContMDiffAt I 𝓘(ℝ) n u x) (hx : u x ≠ 0) :
    ContMDiffAt I 𝓘(ℝ) n (fun y ↦ Real.sqrt (u y)) x :=
  (Real.contDiffAt_sqrt hx).comp_contMDiffAt hu

/-- The square root of a `C^n` real function that does not vanish on a set is `C^n` on that
set. -/
theorem ContMDiffOn.sqrt (hu : ContMDiffOn I 𝓘(ℝ) n u s) (hs : ∀ x ∈ s, u x ≠ 0) :
    ContMDiffOn I 𝓘(ℝ) n (fun y ↦ Real.sqrt (u y)) s :=
  fun x hx ↦ (hu x hx).sqrt (hs x hx)

/-- The square root of a nowhere-vanishing `C^n` real function is `C^n`. -/
theorem ContMDiff.sqrt (hu : ContMDiff I 𝓘(ℝ) n u) (h : ∀ x, u x ≠ 0) :
    ContMDiff I 𝓘(ℝ) n (fun y ↦ Real.sqrt (u y)) :=
  fun x ↦ (hu x).sqrt (h x)
