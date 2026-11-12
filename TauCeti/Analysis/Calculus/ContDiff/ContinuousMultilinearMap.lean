/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Smooth diagonal pullback of continuous multilinear maps

Mathlib bundles multilinear pullback as the continuous multilinear operator
`ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear`.
Applying the same continuous linear map in every input slot gives an operator-valued
function that is smooth at every order, including the analytic order `ω`.
-/

public section

open scoped ContDiff

variable {𝕜 E F G ι : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] [Fintype ι]

namespace ContinuousMultilinearMap

/-- Pulling back continuous multilinear maps along the same continuous linear map in every
input slot is smooth as an operator-valued function, at every order including `ω`. -/
theorem contDiff_compContinuousLinearMapContinuousMultilinear_diagonal (n : WithTop ℕ∞) :
    ContDiff 𝕜 n (fun f : E →L[𝕜] F ↦
      compContinuousLinearMapContinuousMultilinear
        𝕜 (fun _ : ι ↦ E) (fun _ : ι ↦ F) G (fun _ ↦ f)) :=
  (compContinuousLinearMapContinuousMultilinear
    𝕜 (fun _ : ι ↦ E) (fun _ : ι ↦ F) G).contDiff.comp
      (contDiff_pi.mpr fun _ ↦ contDiff_id)

end ContinuousMultilinearMap
