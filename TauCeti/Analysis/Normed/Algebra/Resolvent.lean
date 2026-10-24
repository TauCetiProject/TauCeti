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
of the resolvent.
-/

public section

namespace spectrum

variable {𝕜 A : Type*} [NontriviallyNormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A]
  [CompleteSpace A]

/-- The resolvent `z ↦ (z1 - a)⁻¹` is holomorphic on the resolvent set. -/
theorem differentiableOn_resolvent (a : A) : DifferentiableOn 𝕜 (resolvent a) (resolventSet 𝕜 a) :=
  fun _ hz ↦ (hasDerivAt_resolvent_const_left hz).differentiableAt.differentiableWithinAt

end spectrum
