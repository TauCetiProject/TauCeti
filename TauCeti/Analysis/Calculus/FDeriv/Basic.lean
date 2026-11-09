/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic

/-!
# Differentiability from a nonzero derivative

The derivative `fderiv 𝕜 f` is totalized: it is `0` where `f` is not differentiable. So a
nonzero derivative certifies differentiability, as `differentiableAt_of_deriv_ne_zero` does for
functions of one variable.

## Main results

* `TauCeti.differentiableAt_of_fderiv_ne_zero`: a function is differentiable wherever its
  derivative does not vanish.
-/

public section

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f : E → F} {x : E}

/-- A function is differentiable wherever its totalized derivative does not vanish. -/
theorem differentiableAt_of_fderiv_ne_zero (h : fderiv 𝕜 f x ≠ 0) : DifferentiableAt 𝕜 f x := by
  by_contra hnd
  exact h (fderiv_zero_of_not_differentiableAt hnd)

end TauCeti
