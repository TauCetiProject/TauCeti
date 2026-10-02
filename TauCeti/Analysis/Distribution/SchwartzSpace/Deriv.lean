/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

/-!
# Directional differentiation and linear maps on Schwartz space

Applying a continuous real-linear map to the values of a Schwartz function commutes with
directional differentiation. In particular, real and imaginary parts, and the embedding of
real-valued functions into complex Schwartz space, commute with differentiation.
-/

public section

namespace TauCeti

open scoped SchwartzMap LineDeriv

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Directional differentiation commutes with a continuous real-linear map on the values
of a Schwartz function. -/
theorem lineDerivOp_postcompCLM (v : E) (L : F →L[ℝ] G) (φ : 𝓢(E, F)) :
    ∂_{v} (φ.postcompCLM L) = (∂_{v} φ).postcompCLM L := by
  have hfun : ⇑(φ.postcompCLM L) = L ∘ φ :=
    funext (SchwartzMap.postcompCLM_apply L φ)
  ext x
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv, hfun,
    (L.hasFDerivAt.comp x φ.differentiableAt.hasFDerivAt).fderiv]
  simp only [ContinuousLinearMap.comp_apply, SchwartzMap.postcompCLM_apply,
    SchwartzMap.lineDerivOp_apply_eq_fderiv]

end TauCeti
