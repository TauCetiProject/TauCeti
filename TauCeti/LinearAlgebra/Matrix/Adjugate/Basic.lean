/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Matrix adjugation

This file records dimension-independent consequences of the standard matrix adjugate identities.

The adjugate identity `adj A * A = det A • 1` also acts on vectors with entries in a module: if a
family `v` of elements of an `R`-module satisfies the linear relations `∑ⱼ A i j • v j = 0`, then
`det A` kills every `v k` (`Matrix.det_smul_eq_zero_of_sum_smul_eq_zero`). This is the
determinant trick behind the Cayley–Hamilton and Nakayama arguments for finitely generated modules.

It also identifies the adjugate of a matrix `A` with a right inverse `B` as `det A • B`
(`Matrix.adjugate_eq_det_smul_of_mul_eq_one`); for a unitary matrix, `B` is the conjugate
transpose.

The same identity cancels a square matrix `A` with `A * B = c • 1` for a non-zero-divisor `c`, so
that `B * A = c • 1` as well (`Matrix.mul_eq_smul_one_comm`). For `c = 1` this is
`mul_eq_one_comm`; for general `c` it compares a form with its `c`-scaled dual, whose Gram matrix
is `c` times the inverse Gram matrix. Such inverses up to `c` are transported by congruence: if
`B₁ = Pᵀ * B₂ * P` where `P` has a right inverse `P'`, and `B₁ * D₁ = B₂ * D₂ = c • 1`, then
`D₁ = P' * D₂ * P'ᵀ` (`Matrix.mul_mul_transpose_eq_of_mul_eq_smul`).

Cramer's rule expresses the determinant of `A` with one row or one column replaced through the
adjugate. Summing over the replaced row, or over the replaced column, gives in both cases
`trace (adj A * B)` (`Matrix.sum_det_updateRow_eq_trace_adjugate_mul` and
`Matrix.sum_det_updateCol_eq_trace_adjugate_mul`): Jacobi's formula for the derivative of `det` at
`A` in the direction `B`, read row by row or column by column.
-/

public section

namespace Matrix

variable {R : Type*} [CommRing R]

/-- The adjugate of a square matrix `A` is a left inverse of `A` exactly when `det A = 1`. -/
@[simp]
theorem adjugate_mul_self_eq_one_iff_det_eq_one {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n R) :
    Matrix.adjugate A * A = 1 ↔ A.det = 1 := by
  rw [adjugate_mul]
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h, one_smul]⟩
  cases isEmpty_or_nonempty n
  · simp
  · inhabit n
    simpa using congr($h default default)

/-- The adjugate of a square matrix with a right inverse `B` is its determinant times `B`. -/
theorem adjugate_eq_det_smul_of_mul_eq_one {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n R} (h : A * B = 1) : A.adjugate = A.det • B := by
  rw [← Matrix.mul_one A.adjugate, ← h, ← Matrix.mul_assoc, adjugate_mul, Matrix.smul_mul,
    Matrix.one_mul]

/-- **The determinant trick.** If a family `v` of elements of a module satisfies the linear
relations `∑ⱼ A i j • v j = 0` for every `i`, then `det A` kills every member of the family. -/
theorem det_smul_eq_zero_of_sum_smul_eq_zero {ι M : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommMonoid M] [Module R M] (A : Matrix ι ι R) {v : ι → M}
    (hv : ∀ i, ∑ j, A i j • v j = 0) (k : ι) : A.det • v k = 0 := by
  calc A.det • v k = ∑ j, (A.adjugate * A) k j • v j := by
        simp [adjugate_mul, Matrix.smul_apply, Matrix.one_apply, ite_smul]
    _ = ∑ i, A.adjugate k i • ∑ j, A i j • v j := by
        simp only [Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, mul_smul]
        exact Finset.sum_comm
    _ = 0 := by simp [hv]

/-- **Inverses up to a scalar commute.** If `A * B = c • 1` for square matrices over a commutative
ring and a non-zero-divisor `c`, then `B * A = c • 1`. -/
theorem mul_eq_smul_one_comm {n : Type*} [Fintype n] [DecidableEq n] {A B : Matrix n n R} {c : R}
    (hc : c ∈ nonZeroDivisors R) : A * B = c • 1 ↔ B * A = c • 1 := by
  suffices key : ∀ A B : Matrix n n R, A * B = c • 1 → B * A = c • 1 from ⟨key A B, key B A⟩
  intro A B h
  -- `det A` divides a power of `c`, so it is a non-zero-divisor and cancels `A` on the left.
  have hdet : IsLeftRegular A.det := by
    have hBA : B.det * A.det = c ^ Fintype.card n := by
      rw [mul_comm, ← det_mul, h, det_smul, det_one, mul_one]
    exact .of_mul (hBA ▸ (isRegular_iff_mem_nonZeroDivisors.mpr hc).left.pow _)
  apply (isRegular_of_isLeftRegular_det hdet).left
  simp only [← Matrix.mul_assoc, h, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one]

/-- **Congruence transports inverses up to a scalar.** If `P` has a right inverse `P'` and
`B₁ = Pᵀ * B₂ * P`, and both `B₁ * D₁` and `B₂ * D₂` are the scalar matrix `c • 1` for a
non-zero-divisor `c`, then `P' * D₂ * P'ᵀ = D₁`. The right inverse `P'` is then also a left
inverse of `P`, since `D₁ * Pᵀ * B₂` is a left inverse of `P` up to `c`. -/
theorem mul_mul_transpose_eq_of_mul_eq_smul {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] {c : R} (hc : c ∈ nonZeroDivisors R) {P : Matrix κ ι R}
    {P' : Matrix ι κ R} {B₁ D₁ : Matrix ι ι R} {B₂ D₂ : Matrix κ κ R} (hPP' : P * P' = 1)
    (hG : B₁ = Pᵀ * B₂ * P) (h₁ : B₁ * D₁ = c • 1) (h₂ : B₂ * D₂ = c • 1) :
    P' * D₂ * P'ᵀ = D₁ := by
  have hHG := (mul_eq_smul_one_comm hc).mp h₁
  have hcancel {X Y : Matrix ι ι R} (h : c • X = c • Y) : X = Y := by
    ext i j
    have := congrFun (congrFun h i) j
    rwa [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul,
      mul_cancel_left_mem_nonZeroDivisors hc] at this
  -- `D₁ * Pᵀ * B₂` is `c • P'`, and it is a left inverse of `P` up to `c`, so `P' * P = 1`.
  have hQ : D₁ * Pᵀ * B₂ = c • P' := by
    calc D₁ * Pᵀ * B₂ = D₁ * Pᵀ * B₂ * (P * P') := by rw [hPP', Matrix.mul_one]
      _ = D₁ * B₁ * P' := by rw [hG]; simp only [Matrix.mul_assoc]
      _ = c • P' := by rw [hHG, Matrix.smul_mul, Matrix.one_mul]
  have hP'P : P' * P = 1 := hcancel <| by
    rw [← Matrix.smul_mul, ← hQ, ← hHG, hG]
    simp only [Matrix.mul_assoc]
  refine hcancel ?_
  calc c • (P' * D₂ * P'ᵀ)
      = D₁ * Pᵀ * (B₂ * D₂) * P'ᵀ := by
        rw [← Matrix.smul_mul, ← Matrix.smul_mul, ← hQ]
        simp only [Matrix.mul_assoc]
    _ = c • D₁ := by
        rw [h₂, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_assoc,
          ← Matrix.transpose_mul, hP'P, Matrix.transpose_one, Matrix.mul_one]

/-- **Jacobi's formula, by rows.** Replacing the `i`-th row of `A` by the `i`-th row of `B` and
summing the determinants over `i` gives `trace (adj A * B)`, the derivative of `det` at `A` in the
direction `B`. -/
theorem sum_det_updateRow_eq_trace_adjugate_mul {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n R) : ∑ i, (A.updateRow i (B i)).det = (adjugate A * B).trace := by
  simp only [← cramer_transpose_apply, cramer_eq_adjugate_mulVec, ← adjugate_transpose, trace,
    diag_apply, Matrix.mul_apply, mulVec, dotProduct, transpose_apply]
  exact Finset.sum_comm

/-- **Jacobi's formula, by columns.** Replacing the `j`-th column of `A` by the `j`-th column of `B`
and summing the determinants over `j` gives `trace (adj A * B)`, the derivative of `det` at `A` in
the direction `B`. -/
theorem sum_det_updateCol_eq_trace_adjugate_mul {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n R) : ∑ j, (A.updateCol j fun i ↦ B i j).det = (adjugate A * B).trace := by
  simp only [← cramer_apply, cramer_eq_adjugate_mulVec, trace, diag_apply, Matrix.mul_apply, mulVec,
    dotProduct]

end Matrix
