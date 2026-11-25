/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.IteratedGradient.Basic
public import Mathlib.LinearAlgebra.Trace

/-!
# The trace of a second-order iterated gradient along a linear isometry

A second-order iterated gradient `A : E →L[ℝ] E` is an endomorphism, and its trace is the
Laplacian when `A` is a Hessian. Pulling `A` back along a linear isometry `e : E ≃ₗᵢ[ℝ] E'`
(`LinearIsometryEquiv.iteratedGradientCongr`) conjugates it by `e`, so the trace does not change
(`LinearIsometryEquiv.trace_iteratedGradientCongr_symm_one`). This is the invariance of the
Laplacian under isometries, at the level of the Hessian fields that weak second derivatives
take values in.
-/

public section

namespace LinearIsometryEquiv

variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E']
  [NormedSpace ℝ E'] (e : E ≃ₗᵢ[ℝ] E')

/-- The pullback of a second-order iterated gradient along a linear isometry is a conjugate of it,
so it has the same trace. -/
theorem trace_iteratedGradientCongr_symm_one (A : TauCeti.IteratedGradient E' 1) :
    LinearMap.trace ℝ E ((e.iteratedGradientCongr 1).symm A : E →ₗ[ℝ] E) =
      LinearMap.trace ℝ E' (A : E' →ₗ[ℝ] E') := by
  rw [iteratedGradientCongr_symm_succ_apply, iteratedGradientCongr_zero]
  exact LinearMap.trace_conj' (A : E' →ₗ[ℝ] E') e.symm.toLinearEquiv

end LinearIsometryEquiv
