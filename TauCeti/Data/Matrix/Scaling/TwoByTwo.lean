/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.Matrix.Scaling.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Analysis.Real.Sqrt

/-!
# Exact two-point diagonal scaling

For a strictly positive two-by-two kernel, its scaling to uniform probability marginals has
an algebraic formula: its diagonal and off-diagonal entries are proportional to the square
roots of the diagonal and off-diagonal products of the kernel. This formula makes the limit
of the Sinkhorn iteration explicit.

The scaling conventions are those of Peyré and Cuturi, *Computational Optimal
Transport*, Chapter 4. The matrices here have row and column sums `1/2`, hence total mass one.
-/

public section

open Real

namespace Matrix

/-- A positive diagonal scaling of a positive two-by-two kernel to uniform probability
marginals has diagonal entries proportional to `√(K₀₀ K₁₁)` and off-diagonal entries
proportional to `√(K₀₁ K₁₀)`. -/
theorem IsDiagonalScaling.fin_two_eq {P K : Matrix (Fin 2) (Fin 2) ℝ}
    {u v : Fin 2 → ℝ} (hP : IsDiagonalScaling P K u v)
    (hK : ∀ i j, 0 < K i j) (hu : ∀ i, 0 < u i) (hv : ∀ j, 0 < v j)
    (hm : HasMarginals P (fun _ ↦ 1 / 2) (fun _ ↦ 1 / 2)) :
    P = (2 * (√(K 0 0 * K 1 1) + √(K 0 1 * K 1 0)))⁻¹ •
      !![√(K 0 0 * K 1 1), √(K 0 1 * K 1 0);
         √(K 0 1 * K 1 0), √(K 0 0 * K 1 1)] := by
  have hpos := hP.pos hK hu hv
  obtain ⟨hr, hc⟩ := (hasMarginals_def _ _ _).1 hm
  simp only [Fin.sum_univ_two] at hr hc
  have h01 : P 0 1 = P 1 0 := by linarith [hr 0, hc 0]
  have h11 : P 1 1 = P 0 0 := by linarith [hr 1, hc 0]
  have hcross : P 0 0 * P 1 1 * (K 0 1 * K 1 0) =
      P 0 1 * P 1 0 * (K 0 0 * K 1 1) := by
    simp only [isDiagonalScaling_def] at hP
    rw [hP 0 0, hP 1 1, hP 0 1, hP 1 0]
    ring
  let A := √(K 0 0 * K 1 1)
  let B := √(K 0 1 * K 1 0)
  have hA : 0 < A := sqrt_pos.2 (mul_pos (hK 0 0) (hK 1 1))
  have hB : 0 < B := sqrt_pos.2 (mul_pos (hK 0 1) (hK 1 0))
  have hAsq : A ^ 2 = K 0 0 * K 1 1 := sq_sqrt (mul_pos (hK 0 0) (hK 1 1)).le
  have hBsq : B ^ 2 = K 0 1 * K 1 0 := sq_sqrt (mul_pos (hK 0 1) (hK 1 0)).le
  have hbalance : P 0 0 * B = P 0 1 * A := by
    rw [← h01, h11, ← hAsq, ← hBsq] at hcross
    apply (sq_eq_sq₀ (mul_pos (hpos 0 0) hB).le (mul_pos (hpos 0 1) hA).le).1
    nlinarith only [hcross]
  have hden : 2 * (A + B) ≠ 0 := by positivity
  have hd : P 0 0 = (2 * (A + B))⁻¹ * A := by
    symm
    apply (inv_mul_eq_iff_eq_mul₀ hden).2
    nlinarith [hr 0]
  have ho : P 0 1 = (2 * (A + B))⁻¹ * B := by
    symm
    apply (inv_mul_eq_iff_eq_mul₀ hden).2
    nlinarith [hr 0]
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [Matrix.smul_apply, A, B] using hd
  · simpa [Matrix.smul_apply, A, B] using ho
  · simpa [Matrix.smul_apply, A, B, h01] using ho
  · simpa [Matrix.smul_apply, A, B, h11] using hd

end Matrix
