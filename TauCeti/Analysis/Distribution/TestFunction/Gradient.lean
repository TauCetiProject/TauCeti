/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TestFunction
public import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
# Gradients of test functions

The gradient is a continuous linear map from scalar test functions to vector test fields on
the same open set. This lets a test gradient serve as the input to pairings on vector test fields.
-/

public section

open InnerProductSpace TopologicalSpace
open scoped Distributions Gradient

namespace TestFunction

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {Ω : Opens E}

/-- The gradient on test functions, obtained by applying the inverse Riesz map to the
Fréchet derivative. -/
noncomputable def gradientCLM : 𝓓(Ω, ℝ) →L[ℝ] 𝓓(Ω, E) :=
  postcompCLM (toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L fderivCLM ℝ ⊤ ⊤

/-- The underlying field of a bundled test gradient is the pointwise gradient. -/
@[simp]
theorem gradientCLM_apply (φ : 𝓓(Ω, ℝ)) :
    (gradientCLM φ : E → E) = ∇ (φ : E → ℝ) := by
  funext x
  simp [gradientCLM, gradient]

end TestFunction
