/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Smooth operations on continuous multilinear maps

Mathlib bundles multilinear pullback as the continuous multilinear operator
`ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear`.
Applying the same continuous linear map in every input slot gives an operator-valued
function that is smooth at every order, including the analytic order `ω`.

Flipping the arguments of a multilinear map with values in operators,
`ContinuousMultilinearMap.flipLinear`, is the inverse of the continuous linear equivalence
`ContinuousLinearMap.flipMultilinearEquiv`, so it preserves the regularity of a family of such
maps (`ContDiffAt.continuousMultilinearMap_flipLinear`).
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

/-- Flipping the arguments of a `C^n` family of multilinear maps with values in operators gives a
`C^n` family of operators with values in multilinear maps. -/
theorem ContDiffAt.continuousMultilinearMap_flipLinear {X : Type*} [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] {M : ι → Type*} [∀ i, NormedAddCommGroup (M i)] [∀ i, NormedSpace 𝕜 (M i)]
    {Φ : X → ContinuousMultilinearMap 𝕜 M (F →L[𝕜] G)} {x : X} {n : ℕ∞ω}
    (hΦ : ContDiffAt 𝕜 n Φ x) : ContDiffAt 𝕜 n (fun y ↦ (Φ y).flipLinear) x := by
  -- Flipping is the inverse of the continuous linear equivalence `flipMultilinearEquiv`.
  simpa [Function.comp_def] using
    (ContinuousLinearMap.flipMultilinearEquiv 𝕜 M F G).symm.contDiff.contDiffAt.comp x hΦ
