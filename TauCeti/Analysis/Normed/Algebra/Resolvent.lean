/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Algebra.GelfandFormula

/-!
# Holomorphy of the resolvent

For an element `a` of a Banach algebra over a nontrivially normed field, Mathlib proves that the
resolvent `z ↦ (z1 - a)⁻¹` has a derivative at every point of the resolvent set. This file packages
that fact as differentiability on the resolvent set, the form in which it enters contour integrals
of the resolvent. It also records that a sphere enclosing the spectrum lies in the resolvent set,
which is how large circles serve as comparison contours for these integrals.
-/

public section

open Metric

namespace spectrum

/-- If the spectrum of `a` lies in the open ball of radius `R₀` about `0`, then every sphere about
`0` of radius at least `R₀` lies in the resolvent set. -/
theorem sphere_subset_resolventSet {𝕜 A : Type*} [NormedField 𝕜] [Ring A] [Algebra 𝕜 A] {a : A}
    {R₀ R : ℝ} (hR₀ : spectrum 𝕜 a ⊆ ball 0 R₀) (hR : R₀ ≤ R) :
    sphere (0 : 𝕜) R ⊆ resolventSet 𝕜 a := fun z hz ↦
  notMem_iff.mp fun hσ ↦
    (mem_ball_zero_iff.mp (hR₀ hσ)).not_ge (by rwa [mem_sphere_zero_iff_norm.mp hz])

variable {𝕜 A : Type*} [NontriviallyNormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A]
  [CompleteSpace A]

/-- The resolvent `z ↦ (z1 - a)⁻¹` is holomorphic on the resolvent set. -/
theorem differentiableOn_resolvent (a : A) : DifferentiableOn 𝕜 (resolvent a) (resolventSet 𝕜 a) :=
  fun _ hz ↦ (hasDerivAt_resolvent_const_left hz).differentiableAt.differentiableWithinAt

end spectrum
