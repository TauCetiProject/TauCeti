/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# The continuous dual of a finite-dimensional normed space

Over a complete nontrivially normed field every linear functional on a finite-dimensional normed
space is continuous, so the continuous dual `E →L[𝕜] 𝕜` coincides with the algebraic dual
`Module.Dual 𝕜 E`. Mathlib records that coincidence as the linear equivalence
`LinearMap.toContinuousLinearMap`; this file reads off the one consequence of it that dimension
counts need, namely that the continuous dual has the same dimension as the space.

## Main results

* `ContinuousLinearMap.dual_finrank_eq`: in finite dimensions the continuous dual has the same
  dimension as the space.
-/

public section

namespace TauCeti

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]

/-- In finite dimensions the continuous dual `E →L[𝕜] 𝕜` has the same dimension as `E`: every
linear functional on a finite-dimensional space is continuous, so the continuous dual coincides
with the algebraic one. -/
theorem _root_.ContinuousLinearMap.dual_finrank_eq :
    Module.finrank 𝕜 (E →L[𝕜] 𝕜) = Module.finrank 𝕜 E := by
  rw [← LinearEquiv.finrank_eq
    (LinearMap.toContinuousLinearMap : (E →ₗ[𝕜] 𝕜) ≃ₗ[𝕜] E →L[𝕜] 𝕜)]
  exact Subspace.dual_finrank_eq

end TauCeti

end
