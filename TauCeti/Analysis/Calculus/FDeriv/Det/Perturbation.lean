/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Trace
public import TauCeti.Analysis.Calculus.FDeriv.Det.Basic

/-!
# Differentiating the determinant at the identity endomorphism

The first-order change of the determinant along `id + t • A` is the trace of `A`.
This is the basis-free form of `Matrix.hasDerivAt_det_one_add_smul`.
-/

public section

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- The derivative at zero of `t ↦ det (id + t • A)` is the trace of `A`. -/
theorem ContinuousLinearMap.hasDerivAt_det_id_add_smul (A : E →L[𝕜] E) :
    HasDerivAt (fun t : 𝕜 ↦ (ContinuousLinearMap.id 𝕜 E + t • A).det)
      (LinearMap.trace 𝕜 E A.toLinearMap) 0 := by
  classical
  let b := Module.finBasis 𝕜 E
  have hdet (t : 𝕜) : (ContinuousLinearMap.id 𝕜 E + t • A).det =
      (1 + t • LinearMap.toMatrix b b A.toLinearMap).det := by
    rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix b]
    simp [ContinuousLinearMap.toLinearMap_add, ContinuousLinearMap.toLinearMap_smul]
  simp only [hdet, LinearMap.trace_eq_matrix_trace 𝕜 b]
  exact Matrix.hasDerivAt_det_one_add_smul _
