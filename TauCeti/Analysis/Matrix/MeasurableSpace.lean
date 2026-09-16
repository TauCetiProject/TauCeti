/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Measurability in the space of square matrices

Matrix inversion is not continuous: it jumps at the singular matrices, where Mathlib's totalized
inverse takes the value `0`. It is still measurable, because Cramer's rule writes it as the
adjugate — a polynomial in the entries — scaled by the inverse of the determinant, and inversion
of scalars is measurable even at zero.

## Main results

* `TauCeti.measurable_matrix_inv` — matrix inversion is measurable, and the `MeasurableInv`
  instance it supplies.
-/

public section

namespace TauCeti

variable {m : Type*} [Fintype m] [DecidableEq m] {𝕜 : Type*} [Field 𝕜] [TopologicalSpace 𝕜]
  [IsTopologicalRing 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜] [SecondCountableTopology 𝕜]
  [MeasurableInv 𝕜]

/-- Matrix inversion is measurable. -/
@[fun_prop]
theorem measurable_matrix_inv : Measurable fun A : Matrix m m 𝕜 => A⁻¹ := by
  rw [Matrix.measurable_iff]
  intro i j
  simp only [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv]
  exact ((Continuous.matrix_det continuous_id).measurable.inv).mul
    ((Continuous.matrix_adjugate continuous_id).matrix_elem i j).measurable

/-- Square matrices inherit `MeasurableInv` from the measurability of Cramer's rule, which makes
the generic `measurable_inv` API and `Measurable.inv` dot notation available for matrices. -/
instance : MeasurableInv (Matrix m m 𝕜) := ⟨measurable_matrix_inv⟩

end TauCeti
