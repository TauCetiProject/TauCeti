/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic

import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Touching functions have equal derivatives

If two real-valued functions satisfy `g ≤ φ` near a point `x`, with equality at `x`, then
`g - φ` has a local maximum at `x`. By Fermat's theorem, if both are differentiable at `x`,
then their derivatives at `x` agree.

## Main results

* `HasFDerivAt.eq_of_eventuallyLE`: touching functions have equal Fréchet derivatives.
-/

public section

open Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {g φ : E → ℝ} {g' φ' : E →L[ℝ] ℝ} {x : E}

/-- If `g ≤ φ` near `x` with equality at `x`, and both are differentiable at `x`, then their
derivatives at `x` agree: `g - φ` has a local maximum at `x`. -/
theorem HasFDerivAt.eq_of_eventuallyLE (hg : HasFDerivAt g g' x) (hφ : HasFDerivAt φ φ' x)
    (hle : g ≤ᶠ[𝓝 x] φ) (heq : g x = φ x) : g' = φ' := by
  have hmax : IsLocalMax (fun y ↦ g y - φ y) x :=
    hle.mono fun y hy ↦ by simpa [heq] using hy
  exact sub_eq_zero.mp (hmax.hasFDerivAt_eq_zero (hg.sub hφ))
