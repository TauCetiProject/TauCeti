/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import TauCeti.Analysis.CStarAlgebra.Trace.Basic

/-!
# Checks for traces on C⋆-algebras

On `M₂(ℂ)` the positive functional `x ↦ x₁₁` is not a trace. With `x = e₁₂`, `x⋆x = e₂₂` has
`(1, 1)` entry `0` while `xx⋆ = e₁₁` has `(1, 1)` entry `1`, so the trace identity
`τ(x⋆x) = τ(xx⋆)` fails.
-/

public section

open scoped ENNReal ComplexOrder

namespace TauCeti.TraceExamples

/-- The corner functional `x ↦ Re x₁₁` on `M₂(ℂ)`, as a map to `ℝ≥0∞`. -/
noncomputable def corner : CStarMatrix (Fin 2) (Fin 2) ℂ → ℝ≥0∞ :=
  fun x ↦ ENNReal.ofReal (x 0 0).re

/-- The corner functional `x ↦ x₁₁` on `M₂(ℂ)` is not a trace. -/
theorem not_isTrace_corner : ¬ IsTrace corner := fun h ↦ by
  have := h.map_star_mul_self (CStarMatrix.ofMatrix (Matrix.single 0 1 1))
  simp [corner, CStarMatrix.mul_apply, CStarMatrix.star_apply,
    CStarMatrix.ofMatrix_apply, Matrix.single_apply] at this

end TauCeti.TraceExamples
