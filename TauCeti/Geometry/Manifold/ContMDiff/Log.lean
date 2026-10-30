/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Logarithms of real functions on manifolds

The logarithm `x ↦ Real.log (u x)` of a `C^n` real function `u` on a manifold is `C^n` wherever
`u` does not vanish, since `Real.log` is smooth away from `0`. This is the manifold version of
`ContDiffAt.log`; it is used, for instance, to see that the exponent `φ` of a smooth conformal
factor `e^(2φ)` is smooth.

## Main results

* `ContMDiffAt.log`, `ContMDiff.log`: `x ↦ Real.log (u x)` is `C^n` where `u` does not vanish.
-/

public section

open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {n : ℕ∞ω} {u : M → ℝ} {x : M}

/-- The logarithm of a real function that is `C^n` at a point where it does not vanish is `C^n`
there. -/
theorem ContMDiffAt.log (hu : ContMDiffAt I 𝓘(ℝ) n u x) (h : u x ≠ 0) :
    ContMDiffAt I 𝓘(ℝ) n (fun y ↦ Real.log (u y)) x :=
  (Real.contDiffAt_log.2 h).contMDiffAt.comp x hu

/-- The logarithm of a nowhere-vanishing `C^n` real function is `C^n`. -/
theorem ContMDiff.log (hu : ContMDiff I 𝓘(ℝ) n u) (h : ∀ x, u x ≠ 0) :
    ContMDiff I 𝓘(ℝ) n (fun y ↦ Real.log (u y)) :=
  fun x ↦ (hu x).log (h x)
