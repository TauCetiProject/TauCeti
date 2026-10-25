/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Real powers of real functions on manifolds

A real power `x ↦ u x ^ p` of a `C^n` real function `u` on a manifold is `C^n` wherever `u` does
not vanish, since `t ↦ t ^ p` is analytic away from `0`. This is the manifold version of
`ContDiffAt.rpow_const_of_ne`; it is used, for instance, to rescale a Riemannian metric by a
real power `u ^ p` of a positive function.

## Main results

* `ContMDiffAt.rpow_const_of_ne`, `ContMDiff.rpow_const_of_ne`: `x ↦ u x ^ p` is `C^n` where `u`
  does not vanish.
-/

public section

open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {n : ℕ∞ω} {u : M → ℝ} {x : M}

/-- A real power of a real function that is `C^n` at a point where it does not vanish is `C^n`
there. -/
theorem ContMDiffAt.rpow_const_of_ne (hu : ContMDiffAt I 𝓘(ℝ) n u x) (h : u x ≠ 0) (p : ℝ) :
    ContMDiffAt I 𝓘(ℝ) n (fun y ↦ u y ^ p) x :=
  (Real.contDiffAt_rpow_const_of_ne (p := p) h).contMDiffAt.comp x hu

/-- A real power of a nowhere-vanishing `C^n` real function is `C^n`. -/
theorem ContMDiff.rpow_const_of_ne (hu : ContMDiff I 𝓘(ℝ) n u) (h : ∀ x, u x ≠ 0) (p : ℝ) :
    ContMDiff I 𝓘(ℝ) n (fun y ↦ u y ^ p) :=
  fun x ↦ (hu x).rpow_const_of_ne (h x) p
