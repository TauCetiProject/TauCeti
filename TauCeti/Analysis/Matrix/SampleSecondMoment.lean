/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.Star
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import TauCeti.Analysis.Convex.FiniteMean

/-!
# The empirical second-moment matrix

The empirical second-moment matrix `r⁻¹ ∑ᵢ Vᵢ Vᵢᵀ` of a finite sample `V₁, …, V_r` of real
vectors is the mean, in the sense of `TauCeti.finiteMean`, of the outer products of the samples.
Each of its entries is the sample mean of the corresponding products of coordinates, and it is
symmetric.

## Main declarations

* `TauCeti.sampleSecondMoment`: the empirical second-moment matrix.
* `TauCeti.sampleSecondMoment_eq_finiteMean`: it is the mean of the outer products.
* `TauCeti.sampleSecondMoment_apply`: its entries are sample means of products of coordinates.
* `TauCeti.isHermitian_sampleSecondMoment`: it is symmetric.
-/

public section

namespace TauCeti

variable {ι κ : Type*} [Fintype ι]

/-- The empirical second-moment matrix `r⁻¹ ∑ᵢ Vᵢ Vᵢᵀ` of a finite sample `V` of real vectors,
the mean of the outer products of the samples. Its entries are the sample means
`r⁻¹ ∑ᵢ Vᵢₖ Vᵢₗ`, see `TauCeti.sampleSecondMoment_apply`. -/
noncomputable def sampleSecondMoment (V : ι → κ → ℝ) : Matrix κ κ ℝ :=
  finiteMean ℝ fun i ↦ Matrix.vecMulVec (V i) (V i)

/-- The empirical second-moment matrix is the mean of the outer products of the samples. -/
theorem sampleSecondMoment_eq_finiteMean (V : ι → κ → ℝ) :
    sampleSecondMoment V = finiteMean ℝ fun i ↦ Matrix.vecMulVec (V i) (V i) :=
  (rfl)

/-- Each entry of the empirical second-moment matrix is the sample mean of the corresponding
products of coordinates. -/
@[simp]
theorem sampleSecondMoment_apply (V : ι → κ → ℝ) (k l : κ) :
    sampleSecondMoment V k l = finiteMean ℝ fun i ↦ V i k * V i l := by
  simp [sampleSecondMoment, finiteMean_eq_inv_smul_sum, Matrix.sum_apply, Matrix.vecMulVec_apply]

/-- The empirical second-moment matrix is symmetric. -/
theorem isHermitian_sampleSecondMoment (V : ι → κ → ℝ) : (sampleSecondMoment V).IsHermitian := by
  ext k l
  simp only [Matrix.conjTranspose_apply, star_trivial, sampleSecondMoment_apply, mul_comm]

end TauCeti
