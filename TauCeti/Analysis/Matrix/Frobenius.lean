/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Analysis.Matrix.Normed

public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.Frobenius

/-!
# The Frobenius inner product on real matrices

Mathlib's `Matrix.frobeniusNormedAddCommGroup` equips `Matrix m n ℝ` with the Frobenius norm
while keeping the topology and uniformity definitionally equal to the product ones. This file
adds the compatible real inner product `⟪A, B⟫_ℝ = ∑ i, ∑ j, A i j * B i j`, together with its
description through the trace.

Like the Frobenius norm itself, the inner product is not a global instance, because there are
several natural norms on matrices. It is registered as a scoped instance in the existing
`Matrix.Norms.Frobenius` namespace, so `open scoped Matrix.Norms.Frobenius` activates the norm
and the inner product together.

## Main declarations

* `Matrix.frobeniusInnerProductSpace` — the Frobenius inner product, compatible with
  `Matrix.frobeniusNormedAddCommGroup`.
* `Matrix.frobenius_inner_def` — the inner product is the sum of entrywise products.
* `Matrix.frobenius_inner_eq_trace_transpose_mul` — the inner product is `(Aᵀ * B).trace`.
-/

public section

noncomputable section

open scoped RealInnerProductSpace

namespace Matrix

variable {m n : Type*} [Fintype m] [Fintype n]

/-- The Frobenius inner product `⟪A, B⟫_ℝ = ∑ i, ∑ j, A i j * B i j` on real matrices,
compatible with the Frobenius norm of `Matrix.frobeniusNormedAddCommGroup`. Not declared as a
global instance because there are several natural choices of norm on matrices; it is available
through `open scoped Matrix.Norms.Frobenius`. -/
@[instance_reducible]
def frobeniusInnerProductSpace :
    letI : NormedAddCommGroup (Matrix m n ℝ) := Matrix.frobeniusNormedAddCommGroup
    InnerProductSpace ℝ (Matrix m n ℝ) :=
  letI : NormedAddCommGroup (Matrix m n ℝ) := Matrix.frobeniusNormedAddCommGroup
  { __ := (Matrix.frobeniusNormedSpace : NormedSpace ℝ (Matrix m n ℝ))
    inner A B := ∑ i, ∑ j, A i j * B i j
    norm_sq_eq_re_inner A := by
      have h : (0 : ℝ) ≤ ∑ i, ∑ j, ‖A i j‖ ^ (2 : ℝ) :=
        Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ Real.rpow_nonneg (norm_nonneg _) _
      rw [Matrix.frobenius_norm_def, ← Real.rpow_natCast _ 2, ← Real.rpow_mul h]
      norm_num [Real.rpow_two, pow_two]
    conj_inner_symm A B := by
      simp [mul_comm]
    add_left A B C := by
      simp [add_mul, Finset.sum_add_distrib]
    smul_left A B r := by
      simp [mul_assoc, Finset.mul_sum] }

namespace Norms.Frobenius

attribute [scoped instance] Matrix.frobeniusInnerProductSpace

end Norms.Frobenius

section lemmas

open scoped Matrix.Norms.Frobenius

/-- The Frobenius inner product is the sum of the entrywise products. -/
@[simp]
theorem frobenius_inner_def (A B : Matrix m n ℝ) : ⟪A, B⟫ = ∑ i, ∑ j, A i j * B i j :=
  (rfl)

/-- The Frobenius inner product is the trace of `Aᵀ * B`. -/
theorem frobenius_inner_eq_trace_transpose_mul (A B : Matrix m n ℝ) :
    ⟪A, B⟫ = (Aᵀ * B).trace := by
  rw [frobenius_inner_def, Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply]
  exact Finset.sum_comm

end lemmas

section Operators

open scoped InnerProductSpace Matrix.Norms.Frobenius

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- The Frobenius norm of the matrix of a rectangular operator in any orthonormal domain and
codomain bases equals its unitarily invariant Frobenius seminorm. -/
theorem frobenius_norm_toMatrix [DecidableEq n] (A : E →ₗ[𝕜] F) (b : OrthonormalBasis n 𝕜 E)
    (c : OrthonormalBasis m 𝕜 F) :
    ‖A.toMatrix b.toBasis c.toBasis‖ = TauCeti.UnitarilyInvariantSeminorm.frobenius 𝕜 E F A := by
  symm
  rw [TauCeti.UnitarilyInvariantSeminorm.frobenius_apply b A,
    Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simpa [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.repr_apply_apply, Real.rpow_two] using
    (c.sum_sq_norm_inner_right (A (b i))).symm

end Operators

end Matrix
