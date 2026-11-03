/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.LinearAlgebra.Matrix.Trace
public import TauCeti.Analysis.Matrix.Frobenius

/-!
# Frobenius trace inequalities

This file records trace inequalities obtained from the Frobenius inner product. They are useful
for proving inequalities involving traces of products of matrices.

The main results are `norm_trace_conjTranspose_mul_le`, the Frobenius Cauchy–Schwarz inequality
for the trace pairing, and `trace_mul_mul_sq_le`, the first nontrivial dyadic trace-power
inequality for positive semidefinite matrices.
-/

public section

open scoped ComplexOrder Matrix Matrix.Norms.Frobenius MatrixOrder

namespace Matrix

variable {m n : Type*} [Fintype m] [Fintype n] {𝕜 : Type*} [RCLike 𝕜]

/-- Cauchy–Schwarz for the trace pairing with the Frobenius norm. -/
theorem norm_trace_conjTranspose_mul_le (A B : Matrix m n 𝕜) :
    ‖(Aᴴ * B).trace‖ ≤ ‖A‖ * ‖B‖ := by
  let A' : PiLp 2 (fun i : m => PiLp 2 fun j : n => 𝕜) :=
    WithLp.toLp 2 fun i => WithLp.toLp 2 fun j => A i j
  let B' : PiLp 2 (fun i : m => PiLp 2 fun j : n => 𝕜) :=
    WithLp.toLp 2 fun i => WithLp.toLp 2 fun j => B i j
  have htrace : (Aᴴ * B).trace = inner 𝕜 A' B' := by
    calc
      (Aᴴ * B).trace = ∑ i : m, ∑ j : n, star (A i j) * B i j := by
        simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
          Matrix.conjTranspose_apply]
        rw [Finset.sum_comm]
      _ = inner 𝕜 A' B' := by
          simp [A', B', PiLp.inner_apply, mul_comm]
  have hnormA : ‖A‖ = ‖A'‖ := rfl
  have hnormB : ‖B‖ = ‖B'‖ := rfl
  calc
    ‖(Aᴴ * B).trace‖ = ‖inner 𝕜 A' B'‖ := by rw [htrace]
    _ ≤ ‖A'‖ * ‖B'‖ := norm_inner_le_norm _ _
    _ = ‖A‖ * ‖B‖ := by rw [← hnormA, ← hnormB]

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- The trace is bounded in Frobenius norm by the square root of the matrix dimension. -/
theorem norm_trace_le_sqrt_card_mul_norm (A : Matrix m m 𝕜) :
    ‖A.trace‖ ≤ Real.sqrt (Fintype.card m) * ‖A‖ := by
  have h := norm_trace_conjTranspose_mul_le (1 : Matrix m m 𝕜) A
  have hnorm : ‖(1 : Matrix m m 𝕜)‖ = Real.sqrt (Fintype.card m) := by
    have hterm (i j : m) :
        ‖(1 : Matrix m m 𝕜) i j‖ ^ (2 : ℝ) = if i = j then 1 else 0 := by
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
    have hsum : ∑ i : m, ∑ j : m,
        ‖(1 : Matrix m m 𝕜) i j‖ ^ (2 : ℝ) = Fintype.card m := by
      simp_rw [hterm]
      simp
    rw [frobenius_norm_def]
    rw [hsum, Real.sqrt_eq_rpow]
  simpa [hnorm] using h

/-- The trace of a matrix square is bounded by the squared Frobenius norm. -/
theorem norm_trace_mul_self_le (A : Matrix m m 𝕜) :
    ‖(A * A).trace‖ ≤ ‖A‖ ^ 2 := by
  simpa only [Matrix.conjTranspose_conjTranspose, Matrix.frobenius_norm_conjTranspose,
    pow_two] using
    (norm_trace_conjTranspose_mul_le (A := Aᴴ) (B := A))

/-- Rewrite the trace of `A² B²` as the squared Frobenius norm of `A * B`. -/
theorem trace_pow_two_mul_eq_trace_conjTranspose_mul (A B : Matrix m m 𝕜)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (A ^ 2 * B ^ 2).trace = ((A * B)ᴴ * (A * B)).trace := by
  rw [Matrix.conjTranspose_mul, hA.eq, hB.eq]
  simp only [pow_two]
  change ((A * A) * (B * B)).trace = ((B * A) * (A * B)).trace
  calc
    (A * A * (B * B)).trace = ((B * B) * (A * A)).trace :=
      Matrix.trace_mul_comm _ _
    _ = (B * (B * (A * A))).trace := by rw [Matrix.mul_assoc]
    _ = ((B * (A * A)) * B).trace := Matrix.trace_mul_comm _ _
    _ = ((B * A) * (A * B)).trace := by congr 1; noncomm_ring

/-- The first nontrivial dyadic trace-power inequality for Hermitian matrices. -/
theorem norm_trace_mul_mul_sq_le (A B : Matrix m m 𝕜)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    ‖((A * B) ^ 2).trace‖ ≤ ‖(A ^ 2 * B ^ 2).trace‖ := by
  have htrace := trace_pow_two_mul_eq_trace_conjTranspose_mul A B hA hB
  have hnorm : ‖(A * B)‖ ^ 2 = ‖(A ^ 2 * B ^ 2).trace‖ := by
    rw [htrace, ← Matrix.frobenius_inner_eq_trace_conjTranspose_mul]
    rw [inner_self_eq_norm_sq_to_K]
    simp
  calc
    ‖((A * B) ^ 2).trace‖ ≤ ‖A * B‖ ^ 2 := by
      simpa only [pow_two] using norm_trace_mul_self_le (A * B)
    _ = ‖(A ^ 2 * B ^ 2).trace‖ := hnorm

/-- The trace of `(A * B) ^ 2` is nonnegative when both factors are positive semidefinite. -/
theorem trace_mul_mul_sq_nonneg (A B : Matrix m m 𝕜)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ ((A * B) ^ 2).trace := by
  obtain ⟨C, -, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  let T := C * B * Cᴴ
  have hT : T.IsHermitian := by
    change (C * B * Cᴴ)ᴴ = C * B * Cᴴ
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      hB.isHermitian.eq]
    noncomm_ring
  have hT2 : (T * T).PosSemidef := by
    simpa [hT.eq] using (posSemidef_conjTranspose_mul_self T)
  have htrace : ((star C * C * B) ^ 2).trace = (T * T).trace := by
    simp only [pow_two]
    calc
      ((Cᴴ * C * B) * (Cᴴ * C * B)).trace =
          (Cᴴ * (C * B * Cᴴ * C * B)).trace := by congr 1; noncomm_ring
      _ = ((C * B * Cᴴ * C * B) * Cᴴ).trace := Matrix.trace_mul_comm _ _
      _ = (T * T).trace := by
        change (C * B * Cᴴ * C * B * Cᴴ).trace =
          ((C * B * Cᴴ) * (C * B * Cᴴ)).trace
        congr 1
        noncomm_ring
  have htrace' : ((Cᴴ * C * B) ^ 2).trace = (T * T).trace := by
    simpa only [Matrix.star_eq_conjTranspose] using htrace
  change 0 ≤ ((Cᴴ * C * B) ^ 2).trace
  rw [htrace']
  exact hT2.trace_nonneg

/-- The first dyadic trace-power inequality for positive semidefinite matrices. -/
theorem trace_mul_mul_sq_le (A B : Matrix m m 𝕜)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    ((A * B) ^ 2).trace ≤ (A ^ 2 * B ^ 2).trace := by
  have hleft := trace_mul_mul_sq_nonneg A B hA hB
  have hright : 0 ≤ (A ^ 2 * B ^ 2).trace := by
    rw [trace_pow_two_mul_eq_trace_conjTranspose_mul A B hA.isHermitian hB.isHermitian]
    exact (posSemidef_conjTranspose_mul_self (A * B)).trace_nonneg
  have hnorm := norm_trace_mul_mul_sq_le A B hA.isHermitian hB.isHermitian
  obtain ⟨x, hx, hx_eq⟩ := RCLike.nonneg_iff_exists_ofReal.mp hleft
  obtain ⟨y, hy, hy_eq⟩ := RCLike.nonneg_iff_exists_ofReal.mp hright
  rw [← hx_eq, ← hy_eq] at hnorm
  have hnormReal : x ≤ y := by
    simpa only [RCLike.norm_of_nonneg hx, RCLike.norm_of_nonneg hy] using hnorm
  rw [← hx_eq, ← hy_eq]
  exact_mod_cast hnormReal

end Matrix
