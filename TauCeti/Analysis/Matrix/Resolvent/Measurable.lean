/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.Resolvent.SelfConsistency
public import TauCeti.Analysis.Matrix.MeasurableSpace

/-!
# Measurability of matrix minor resolvents

At a fixed deletion index and spectral parameter, the minor resolvent and the corresponding
centered quadratic-form error are measurable functions of the matrix.
-/

public section

open MeasureTheory
open scoped NNReal

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The minor resolvent at a fixed parameter is measurable, including at singular shifts. -/
@[fun_prop]
theorem measurable_minorResolvent {𝕜 : Type*} [Field 𝕜] [TopologicalSpace 𝕜] [IsTopologicalRing 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] [SecondCountableTopology 𝕜] [MeasurableInv 𝕜]
    (i : n) (z : 𝕜) : Measurable (fun A : Matrix n n 𝕜 ↦ A.minorResolvent i z) := by
  simp only [minorResolvent_def]
  exact Measurable.inv ((continuous_id.matrix_submatrix _ _).measurable.sub_const _)

/-- At fixed index, spectral parameter and trace coefficient, the minor quadratic error
is measurable in the matrix. -/
@[fun_prop] theorem measurable_minorQuadraticError (i : n) (z : ℂ) (v : ℝ≥0) :
    Measurable (fun A : Matrix n n ℂ ↦ A.minorQuadraticError i z v) := by
  simp only [minorQuadraticError_def, dotProduct, mulVec, Pi.star_apply, trace, diag]
  fun_prop

end Matrix
