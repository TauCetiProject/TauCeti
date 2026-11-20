/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Otis Chodosh, The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Symmetric
public import TauCeti.LinearAlgebra.Matrix.Trace.Hermitian

/-!
# Contraction of skew and symmetric operators

The contraction of a skew-adjoint operator with a symmetric operator vanishes. The
skew-adjoint operator may act on a different inner product space, with an arbitrary linear map
carrying the symmetric operator's domain into that space. In particular, this applies to the
covariant derivative of an ambient Killing field and the shape operator of an immersion.
-/

public section

namespace OrthonormalBasis

variable {ι V W : Type*} [Fintype ι]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [SeminormedAddCommGroup W] [InnerProductSpace ℝ W]

/-- The contraction of a skew-adjoint operator with a symmetric operator is zero, including
after pulling the skew-adjoint operator back by an arbitrary linear map. -/
theorem sum_inner_map_map_symmetric_eq_zero (b : OrthonormalBasis ι ℝ V)
    (d : V →ₗ[ℝ] W) (K : W →ₗ[ℝ] W) (A : V →ₗ[ℝ] V)
    (hK : ∀ u v, inner ℝ (K u) v = -inner ℝ u (K v)) (hA : A.IsSymmetric) :
    ∑ i, inner ℝ (K (d (b i))) (d (A (b i))) = 0 := by
  classical
  have hexpand (i : ι) : inner ℝ (K (d (b i))) (d (A (b i))) =
      ∑ j, inner ℝ (b j) (A (b i)) * inner ℝ (K (d (b i))) (d (b j)) := by
    nth_rw 1 [← b.sum_repr' (A (b i))]
    simp only [map_sum, map_smul, inner_sum, real_inner_smul_right]
  have hcoeff (i j : ι) : inner ℝ (b j) (A (b i)) = inner ℝ (b i) (A (b j)) := by
    rw [← hA, real_inner_comm]
  have hskew (i j : ι) : inner ℝ (K (d (b i))) (d (b j)) =
      -inner ℝ (K (d (b j))) (d (b i)) := by
    rw [hK, real_inner_comm]
  let H : Matrix ι ι ℝ := Matrix.of fun i j ↦ inner ℝ (b i) (A (b j))
  let X : Matrix ι ι ℝ := Matrix.of fun i j ↦ inner ℝ (K (d (b i))) (d (b j))
  have hH : H.IsHermitian := Matrix.IsHermitian.ext fun i j ↦ by
    simpa only [H, Matrix.of_apply, star_trivial] using hcoeff i j
  have hX : X.conjTranspose = -X := by
    ext i j
    simpa only [Matrix.conjTranspose_apply, Matrix.neg_apply, X, Matrix.of_apply, star_trivial]
      using hskew j i
  have htrace := hH.re_trace_mul_eq_zero_of_conjTranspose_eq_neg hX
  simp only [RCLike.re_to_real, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, H, X,
    Matrix.of_apply] at htrace
  rw [Finset.sum_comm] at htrace
  simpa only [← hexpand] using htrace

end OrthonormalBasis
