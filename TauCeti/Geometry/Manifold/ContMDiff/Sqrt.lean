/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.Algebra.Structures

/-!
# Smooth square-root regularization on manifolds

For a `C^n` real function `u` and a positive constant `ε`, the positive regularization
`x ↦ √(u x ^ 2 + ε)` is also `C^n`.
-/

public section

open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- Square-root regularization by a positive constant preserves `C^n` regularity. -/
theorem ContMDiff.sqrt_sq_add_const {n : ℕ∞ω} {u : M → ℝ}
    (hu : ContMDiff I 𝓘(ℝ) n u) {ε : ℝ} (hε : 0 < ε) :
    ContMDiff I 𝓘(ℝ) n (fun x ↦ Real.sqrt (u x ^ 2 + ε)) := fun x ↦
  (Real.contDiffAt_sqrt (by positivity)).comp_contMDiffAt ((hu.pow 2).add contMDiff_const x)
