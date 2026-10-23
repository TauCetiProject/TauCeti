/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Vec

/-!
# Measurability of matrix operations

The column-stacking vectorization `Matrix.vec` is a measurable equivalence between `m × n`
matrices and functions on `n × m`. It is packaged with target `WithLp p (n × m → α)`, so that for
real entries and `p = 2` it identifies matrices with `EuclideanSpace ℝ (n × m)`.

Matrix inversion is not continuous: it jumps at the singular matrices, where Mathlib's totalized
inverse takes the value `0`. It is still measurable, because Cramer's rule writes it as the
adjugate — a polynomial in the entries — scaled by the inverse of the determinant, and inversion
of scalars is measurable even at zero.

## Main results

* `TauCeti.measurable_matrix_vec` — vectorization is measurable.
* `TauCeti.matrixVecMeasurableEquiv` — vectorization as a measurable equivalence.
* `TauCeti.measurable_matrix_inv` — matrix inversion is measurable, and the `MeasurableInv`
  instance it supplies.
-/

public section

namespace TauCeti

/-- The column-stacking vectorization of matrices is measurable. -/
@[fun_prop]
theorem measurable_matrix_vec {m n α : Type*} [MeasurableSpace α] :
    Measurable fun A : Matrix m n α => A.vec :=
  .of_eval fun _ => Matrix.measurable_apply

/-- The column-stacking vectorization `Matrix.vec` as a measurable equivalence onto the `L^p` copy
of functions on the transposed index type. Its inverse reads entry `(i, j)` from coordinate
`(j, i)`. -/
def matrixVecMeasurableEquiv {m n α : Type*} [MeasurableSpace α] (p : ENNReal) :
    Matrix m n α ≃ᵐ WithLp p (n × m → α) where
  toFun A := WithLp.toLp p A.vec
  invFun x := Matrix.of fun i j => x.ofLp (j, i)
  left_inv _ := rfl
  right_inv _ := rfl
  measurable_toFun := (WithLp.measurable_toLp p _).comp measurable_matrix_vec
  measurable_invFun := by
    -- The goal is stated for the coercion of the bundled `Equiv.symm`, which `fun_prop` cannot
    -- see through, so restate it for the underlying function.
    change Measurable fun x : WithLp p (n × m → α) => Matrix.of fun i j => x.ofLp (j, i)
    fun_prop

@[simp]
theorem matrixVecMeasurableEquiv_apply {m n α : Type*} [MeasurableSpace α] (p : ENNReal)
    (A : Matrix m n α) : matrixVecMeasurableEquiv p A = WithLp.toLp p A.vec :=
  (rfl)

@[simp]
theorem matrixVecMeasurableEquiv_symm_apply {m n α : Type*} [MeasurableSpace α] (p : ENNReal)
    (x : WithLp p (n × m → α)) :
    (matrixVecMeasurableEquiv p).symm x = Matrix.of fun i j => x.ofLp (j, i) :=
  (rfl)

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
