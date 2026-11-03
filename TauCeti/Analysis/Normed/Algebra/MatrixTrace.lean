/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Frobenius trace inequalities

This file records trace inequalities obtained from the Frobenius inner product. They are useful
for proving inequalities involving traces of products of matrices.
-/

public section

open scoped Matrix Matrix.Norms.Frobenius

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

/-- The trace of a matrix square is bounded by the squared Frobenius norm. -/
theorem norm_trace_mul_self_le (A : Matrix m m 𝕜) :
    ‖(A * A).trace‖ ≤ ‖A‖ ^ 2 := by
  simpa only [Matrix.conjTranspose_conjTranspose, Matrix.frobenius_norm_conjTranspose,
    pow_two] using
    (norm_trace_conjTranspose_mul_le (A := Aᴴ) (B := A))

end Matrix
