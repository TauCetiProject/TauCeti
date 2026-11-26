/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# The derivative of the exponential of a function on a manifold

For a real function `g` on a manifold, differentiable at `x`, the chain rule gives
`d(e^g)_x = e^{g x} dg_x` (`TauCeti.mvfderiv_exp`). This is the manifold analogue of
Mathlib's `fderiv_exp`; it computes `X(e^φ) = e^φ X(φ)` for weighted densities `e^φ dV`.
-/

public section

open scoped Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- **The chain rule for the exponential.** For a real function `g` differentiable at `x`, the
derivative of `e^g` at `x` is `e^{g x} dg_x`. -/
theorem mvfderiv_exp {g : M → ℝ} {x : M} (hg : MDifferentiableAt I 𝓘(ℝ) g x) :
    mvfderiv I (fun y ↦ Real.exp (g y)) x = Real.exp (g x) • mvfderiv I g x := by
  rw [← Function.comp_def, mvfderiv_scalar_comp hg Real.differentiable_exp.differentiableAt,
    Real.deriv_exp]

end TauCeti
