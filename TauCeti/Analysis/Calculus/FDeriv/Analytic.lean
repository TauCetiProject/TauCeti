/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Analytic.Constructions

/-!
# Derivatives of analytic functions along analytic vector fields

Mathlib's `AnalyticAt.fderiv` says that the derivative `fderiv 𝕜 f` of a function analytic at `x`
is analytic at `x`. Evaluating it on a vector field `ξ` analytic at `x` gives the derivative of
`f` along `ξ`, `z ↦ f'(z) (ξ z)`, which is again analytic at `x` (`AnalyticAt.fderiv_apply`).
-/

public section

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F] {f : E → F} {ξ : E → E} {x : E}

/-- The derivative of a function analytic at `x` along a vector field analytic at `x` is analytic
at `x`. -/
theorem AnalyticAt.fderiv_apply (hf : AnalyticAt 𝕜 f x) (hξ : AnalyticAt 𝕜 ξ x) :
    AnalyticAt 𝕜 (fun z ↦ fderiv 𝕜 f z (ξ z)) x :=
  ((ContinuousLinearMap.apply 𝕜 F : E →L[𝕜] (E →L[𝕜] F) →L[𝕜] F).analyticAt_bilinear _).comp
    (hξ.prod hf.fderiv)
