/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Analysis.InnerProductSpace.Gram.Distance
public import TauCeti.Analysis.InnerProductSpace.SingularValues
public import TauCeti.Analysis.Matrix.Resolvent.Basic

/-!
# The negative second-moment identity

For a real or complex rectangular matrix with linearly independent rows, the sum of the
reciprocal squared singular values is the sum of the reciprocal squared distances of the rows
from the spans of the other rows. The singular-value sum runs over the row dimension, so the
artificial zero tail of `LinearMap.singularValues` is excluded.

The intermediate trace formula identifies this sum with the real trace of `(A * Aᴴ)⁻¹`.
The identity converts control of row distances into control of small singular values.
Empty row types are allowed; both sums are then empty.

## References

* T. Tao, *Topics in Random Matrix Theory*, Section 2.7, negative second-moment identity.
-/

public section

noncomputable section

open Submodule

namespace Matrix

variable {𝕜 m n : Type*} [RCLike 𝕜] [Fintype m] [Fintype n]
  [DecidableEq m] [DecidableEq n]

/-- The real trace of the inverse row Gram matrix is the negative second moment of the
singular values, summed over the row dimension. -/
theorem re_trace_inv_mul_conjTranspose_eq_sum_inv_sq_singularValues
    (A : Matrix m n 𝕜) (hA : IsUnit (A * Aᴴ)) :
    RCLike.re (A * Aᴴ)⁻¹.trace =
      ∑ i : Fin (Fintype.card m), ((toEuclideanLin A).singularValues i ^ 2)⁻¹ := by
  let hH := isHermitian_mul_conjTranspose_self A
  have htrace := hH.trace_inv_sub_smul_one (spectrum.zero_notMem 𝕜 hA)
  simp only [zero_smul, sub_zero] at htrace
  have heig (i : Fin (Fintype.card m)) :
      (toEuclideanLin A).singularValues i ^ 2 = hH.eigenvalues₀ i := by
    rw [LinearMap.sq_singularValues_eq_eigenvalues_self_comp_adjoint _
      finrank_euclideanSpace i.isLt]
    have hop : toEuclideanLin A ∘ₗ (toEuclideanLin A).adjoint =
        toEuclideanLin (A * Aᴴ) := by
      rw [← toEuclideanLin_conjTranspose_eq_adjoint]
      exact (toLpLin_mul_same 2 A Aᴴ).symm
    exact congrFun (LinearMap.IsSymmetric.eigenvalues_congr hop _ _ _) i
  rw [htrace, map_sum]
  simp only [← RCLike.ofReal_inv, RCLike.ofReal_re]
  simp_rw [heig]
  exact Equiv.sum_comp (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card m))).symm
    (fun i ↦ (hH.eigenvalues₀ i)⁻¹)

omit [DecidableEq m] in
/-- **The negative second-moment identity.** For a matrix with linearly independent rows,
the sum of reciprocal squared singular values equals the sum of reciprocal squared distances
of each row from the span of all the other rows. This includes rectangular matrices and the
empty matrix. -/
theorem sum_inv_sq_singularValues_eq_sum_inv_infDist_sq (A : Matrix m n 𝕜)
    (hA : LinearIndependent 𝕜 (fun i ↦ WithLp.toLp 2 (A i))) :
    (∑ i : Fin (Fintype.card m), ((toEuclideanLin A).singularValues i ^ 2)⁻¹) =
      ∑ i, ((Metric.infDist (WithLp.toLp 2 (A i))
        (span 𝕜 ((fun j ↦ WithLp.toLp 2 (A j)) '' {i}ᶜ) : Set (EuclideanSpace 𝕜 n))) ^ 2)⁻¹ := by
  classical
  have hgram : (gram 𝕜 (fun i ↦ WithLp.toLp 2 (A i)))ᵀ = A * Aᴴ := by
    ext i j
    simp [gram_apply, EuclideanSpace.inner_toLp_toLp, Matrix.mul_apply, dotProduct]
  have hunit : IsUnit (A * Aᴴ) := by
    rw [isUnit_iff_isUnit_det, ← hgram, det_transpose, isUnit_iff_ne_zero]
    exact det_gram_ne_zero_iff_linearIndependent.2 hA
  rw [← re_trace_inv_mul_conjTranspose_eq_sum_inv_sq_singularValues A hunit,
    ← hgram, ← transpose_nonsing_inv, trace_transpose]
  exact hA.re_trace_gram_inv_eq_sum_inv_infDist_sq

end Matrix
