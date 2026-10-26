/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.Trace

/-!
# Real trace of complex-plane endomorphisms

The real trace of an arbitrary real-linear endomorphism of the complex plane is the sum
of its diagonal entries in the basis `(1,I)`. The formula turns the trace of a planar map's real
derivative into coordinate divergence.
-/

public section

open Complex

/-- The actual real trace on the complex plane is the sum of its two coordinate diagonal entries. -/
theorem LinearMap.trace_complex_apply (L : ℂ →ₗ[ℝ] ℂ) :
    LinearMap.trace ℝ ℂ L = (L 1).re + (L I).im := by
  rw [LinearMap.trace_eq_matrix_trace ℝ Complex.basisOneI, Matrix.trace_fin_two]
  simp [LinearMap.toMatrix_apply, Complex.coe_basisOneI, Complex.coe_basisOneI_repr]
