/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Linarith

/-!
# Trace bounds for symmetric Riccati equations

Trace Cauchy–Schwarz bounds the trace of a symmetric square from below. Applied to the matrix
Riccati equation, this gives its scalar trace inequality in positive dimension.
-/

public section

open scoped BigOperators

namespace Matrix

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- The trace of the square of a symmetric matrix controls its diagonal
square sum. -/
theorem sum_sq_diagonal_le_trace_mul_self {ι : Type*} [Fintype ι]
    {S : Matrix ι ι 𝕜} (hS : S.IsSymm) :
    (∑ i, S i i ^ 2) ≤ (S * S).trace := by
  classical
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  apply Finset.sum_le_sum
  intro i hi
  have hs : ∀ j, S i j * S j i = S i j ^ 2 := by
    intro j
    rw [hS.apply i j, pow_two]
  simp only [hs]
  exact Finset.single_le_sum (fun j hj ↦ sq_nonneg (S i j)) (Finset.mem_univ i)

/-- Cauchy--Schwarz for the trace of a symmetric matrix, including the
zero-dimensional case. -/
theorem sq_trace_le_card_mul_trace_mul_self {ι : Type*} [Fintype ι]
    {S : Matrix ι ι 𝕜} (hS : S.IsSymm) :
    S.trace ^ 2 ≤ (Fintype.card ι : 𝕜) * (S * S).trace := by
  have hdiag : S.trace ^ 2 ≤ (Fintype.card ι : 𝕜) * ∑ i, S i i ^ 2 := by
    simpa only [Matrix.trace, Matrix.diag, one_mul, one_pow, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, mul_one] using
      (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : ι ↦ (1 : 𝕜))
        (fun i ↦ S i i))
  exact hdiag.trans (mul_le_mul_of_nonneg_left
    (sum_sq_diagonal_le_trace_mul_self hS) (Nat.cast_nonneg _))

/-- A Ricci lower bound and the traced Riccati equation give the scalar
Riccati inequality in positive transverse dimension. -/
theorem trace_riccati_inequality {ι : Type*} [Fintype ι]
    (hm : 0 < Fintype.card ι) {S : Matrix ι ι 𝕜} (hS : S.IsSymm)
    {h' ric κ : 𝕜}
    (hode : h' = -(S * S).trace - ric)
    (hric : -(Fintype.card ι : 𝕜) * κ ≤ ric) :
    h' + S.trace ^ 2 / (Fintype.card ι : 𝕜) ≤ (Fintype.card ι : 𝕜) * κ := by
  have hm' : (0 : 𝕜) < Fintype.card ι := Nat.cast_pos.mpr hm
  have htrace : S.trace ^ 2 / (Fintype.card ι : 𝕜) ≤ (S * S).trace := by
    apply (div_le_iff₀ hm').mpr
    simpa only [mul_comm] using sq_trace_le_card_mul_trace_mul_self hS
  linarith

/-- The scalar Riccati inequality obtained directly from its matrix equation. -/
theorem trace_riccati_inequality_of_matrix_equation {ι : Type*} [Fintype ι]
    (hm : 0 < Fintype.card ι) {S S' K : Matrix ι ι 𝕜} (hS : S.IsSymm)
    {κ : 𝕜} (hode : S' = -(S * S) - K)
    (hric : -(Fintype.card ι : 𝕜) * κ ≤ K.trace) :
    S'.trace + S.trace ^ 2 / (Fintype.card ι : 𝕜) ≤ (Fintype.card ι : 𝕜) * κ := by
  apply trace_riccati_inequality hm hS (ric := K.trace) _ hric
  simp only [hode, Matrix.trace_sub, Matrix.trace_neg]

end Matrix
