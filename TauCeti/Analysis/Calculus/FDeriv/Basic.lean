/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Topology.Algebra.Module.Determinant

import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Equiv

/-!
# Basic facts about Fréchet derivatives

The derivative `fderiv 𝕜 f` is totalized: it is `0` where `f` is not differentiable. So a
nonzero derivative certifies differentiability, as `differentiableAt_of_deriv_ne_zero` does for
functions of one variable.

An affine map `x ↦ A x + b` given by a continuous linear equivalence `A` has derivative `A` at
every point, and for an endomorphism this derivative has nonzero determinant.

## Main results

* `TauCeti.differentiableAt_of_fderiv_ne_zero`: a function is differentiable wherever its
  derivative does not vanish.
* `ContinuousLinearEquiv.fderiv_add_const`: the derivative of `x ↦ A x + b` is `A`.
* `ContinuousLinearEquiv.det_fderiv_add_const_ne_zero`: its determinant does not vanish.
-/

public section

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f : E → F} {x : E}

/-- A function is differentiable wherever its totalized derivative does not vanish. -/
theorem differentiableAt_of_fderiv_ne_zero (h : fderiv 𝕜 f x ≠ 0) : DifferentiableAt 𝕜 f x := by
  by_contra hnd
  exact h (fderiv_zero_of_not_differentiableAt hnd)

/-- The affine map `x ↦ A x + b` has derivative `A` at every point. -/
theorem _root_.ContinuousLinearEquiv.fderiv_add_const (A : E ≃L[𝕜] F) (b : F) (x : E) :
    fderiv 𝕜 (fun x => A x + b) x = (A : E →L[𝕜] F) :=
  (A.hasFDerivAt.add_const b).fderiv

/-- The derivative of the affine map `x ↦ A x + b` has nonzero determinant at every point. -/
theorem _root_.ContinuousLinearEquiv.det_fderiv_add_const_ne_zero (A : E ≃L[𝕜] E) (b x : E) :
    (fderiv 𝕜 (fun x => A x + b) x).det ≠ 0 := by
  rw [A.fderiv_add_const]
  exact A.toLinearEquiv.isUnit_det'.ne_zero

end TauCeti
