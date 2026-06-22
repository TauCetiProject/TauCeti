/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Real finrank of a compatible complex module

This file records the tower-law dimension formula for a complex module whose real scalar
structure is the ambient one. It is the linear-algebra input for almost-complex even-dimensionality
results, but has no symplectic hypotheses.
-/

namespace TauCeti

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- A compatible complex module structure forces the real dimension to be twice the complex
dimension. This is the tower law `finrank ℝ V = finrank ℝ ℂ * finrank ℂ V` together with
`finrank ℝ ℂ = 2`. -/
theorem finrank_real_eq_two_mul_finrank_complex [Module ℂ V] [IsScalarTower ℝ ℂ V] :
    Module.finrank ℝ V = 2 * Module.finrank ℂ V := by
  rw [← Module.finrank_mul_finrank ℝ ℂ V, Complex.finrank_real_complex]

end TauCeti
