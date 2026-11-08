/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import TauCeti.Analysis.Matrix.Frobenius
public import TauCeti.Algebra.BigOperators.Finset.SquaredDeviation
public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# Finite-dimensional spectral oracle

The real parts of the diagonal entries minimize squared Frobenius loss among real diagonal
estimators. If an estimator must be constant on a block of coordinates, its optimal value is the
average of those real diagonal entries. For an eigenbasis, one may take blocks of indices with
the same eigenvalue; no spectral decomposition is formalized here.
-/

public section

noncomputable section

open scoped Matrix.Norms.Frobenius

namespace Matrix

/-- Squared Frobenius loss to a diagonal estimator in the target's coordinate basis. -/
def diagonalOracleLoss {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : Matrix ι ι ℂ) (d : ι → ℝ) : ℝ :=
  ‖T - Matrix.diagonal (fun i => (d i : ℂ))‖ ^ 2

/-- Diagonal loss is the sum of the squared entrywise differences. -/
theorem diagonalOracleLoss_eq_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : Matrix ι ι ℂ) (d : ι → ℝ) :
    diagonalOracleLoss T d =
      ∑ i, ∑ j, Complex.normSq (T i j - Matrix.diagonal (fun k => (d k : ℂ)) i j) := by
  rw [diagonalOracleLoss, frobenius_norm_sq_eq_sum_normSq]
  simp only [Matrix.sub_apply]

/-- The real parts of the target's diagonal entries in its current coordinates. -/
def diagonalOracle {ι : Type*} (T : Matrix ι ι ℂ) : ι → ℝ :=
  fun i => (T i i).re

/-- The oracle at an index is the real part of the corresponding diagonal entry. -/
@[simp] theorem diagonalOracle_apply {ι : Type*} (T : Matrix ι ι ℂ) (i : ι) :
    diagonalOracle T i = (T i i).re := by rfl

/-- Diagonal loss splits into off-diagonal energy and the real and imaginary diagonal errors. -/
theorem diagonalOracleLoss_eq_offDiagonal_add {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : Matrix ι ι ℂ) (d : ι → ℝ) :
    diagonalOracleLoss T d =
      (∑ i, ∑ j ∈ Finset.univ.erase i, Complex.normSq (T i j)) +
        ∑ i, (((T i i).re - d i) ^ 2 + (T i i).im ^ 2) := by
  rw [diagonalOracleLoss_eq_sum]
  have hsplit :
      (∑ i, ∑ j, Complex.normSq (T i j - Matrix.diagonal (fun k => (d k : ℂ)) i j)) =
        (∑ i, ∑ j ∈ Finset.univ.erase i,
          Complex.normSq (T i j - Matrix.diagonal (fun k => (d k : ℂ)) i j)) +
          ∑ i, Complex.normSq (T i i - Matrix.diagonal (fun k => (d k : ℂ)) i i) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    exact (Finset.sum_erase_add _ _ (Finset.mem_univ i)).symm
  rw [hsplit]
  have hoff :
      (∑ i, ∑ j ∈ Finset.univ.erase i,
          Complex.normSq (T i j - Matrix.diagonal (fun k => (d k : ℂ)) i j)) =
        ∑ i, ∑ j ∈ Finset.univ.erase i, Complex.normSq (T i j) := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    have hentry : Matrix.diagonal (fun k => (d k : ℂ)) i j = 0 := by
      simp [Ne.symm hji]
    rw [hentry]
    simp
  rw [hoff]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have hest : Matrix.diagonal (fun k => (d k : ℂ)) i i = (d i : ℂ) := by simp
  rw [hest]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
    Complex.ofReal_im, sub_zero]
  ring

/-- The loss equals the loss at the diagonal oracle plus the exact excess squared error. -/
theorem diagonalOracleLoss_eq_oracle_add {ι : Type*} [Fintype ι] [DecidableEq ι]
    {T : Matrix ι ι ℂ} (d : ι → ℝ) :
    diagonalOracleLoss T d =
      diagonalOracleLoss T (diagonalOracle T) +
        ∑ i, (d i - diagonalOracle T i) ^ 2 := by
  rw [diagonalOracleLoss_eq_offDiagonal_add T d,
    diagonalOracleLoss_eq_offDiagonal_add T (diagonalOracle T)]
  have hsq : (∑ i, ((T i i).re - d i) ^ 2) =
      ∑ i, (d i - (T i i).re) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp [diagonalOracle, Finset.sum_add_distrib, hsq, add_assoc, add_comm]

/-- The basis-diagonal oracle is the unique minimizer of squared Frobenius loss. -/
theorem diagonalOracleLoss_unique_minimizer {ι : Type*} [Fintype ι] [DecidableEq ι]
    {T : Matrix ι ι ℂ} :
    ∀ d : ι → ℝ, diagonalOracleLoss T (diagonalOracle T) ≤ diagonalOracleLoss T d ∧
      (diagonalOracleLoss T d = diagonalOracleLoss T (diagonalOracle T) ↔
        d = diagonalOracle T) := by
  intro d
  rw [diagonalOracleLoss_eq_oracle_add d]
  constructor
  · exact le_add_of_nonneg_right (Finset.sum_nonneg fun i hi => sq_nonneg _)
  · rw [add_eq_left]
    simp only [Finset.sum_sq_eq_zero_iff, Finset.mem_univ, true_implies]
    constructor
    · intro h
      funext i
      exact sub_eq_zero.mp (h i)
    · intro h i
      simp [h]

/-- The diagonal oracle attains no greater loss than any real diagonal estimator. -/
theorem diagonalOracleLoss_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : Matrix ι ι ℂ) (d : ι → ℝ) :
    diagonalOracleLoss T (diagonalOracle T) ≤ diagonalOracleLoss T d :=
  (diagonalOracleLoss_unique_minimizer (T := T) d).1

/-- Equality with the oracle loss characterizes the oracle. -/
theorem diagonalOracleLoss_eq_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : Matrix ι ι ℂ) (d : ι → ℝ) :
    diagonalOracleLoss T d = diagonalOracleLoss T (diagonalOracle T) ↔
      d = diagonalOracle T :=
  (diagonalOracleLoss_unique_minimizer (T := T) d).2

/-- Loss to an estimator diagonal in a unitary basis is its diagonal loss in that basis. -/
theorem norm_sub_unitary_diagonal_sq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U T : Matrix ι ι ℂ) (hU : U ∈ Matrix.unitaryGroup ι ℂ) (d : ι → ℝ) :
    ‖T - U * Matrix.diagonal (fun i => (d i : ℂ)) * Uᴴ‖ ^ 2 =
      diagonalOracleLoss (Uᴴ * T * U) d := by
  have hleft : Uᴴ * U = 1 := by
    simpa only [star_eq_conjTranspose] using (mem_unitaryGroup_iff'.mp hU)
  have htrans :
      Uᴴ * (T - U * Matrix.diagonal (fun i => (d i : ℂ)) * Uᴴ) * U =
        Uᴴ * T * U - Matrix.diagonal (fun i => (d i : ℂ)) := by
    simp only [mul_sub, sub_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ U, hleft,
      one_mul, mul_one]
  have h := frobenius_norm_sq_conj_unitary U
    (T - U * Matrix.diagonal (fun i => (d i : ℂ)) * Uᴴ) hU
  rw [htrans] at h
  simpa only [diagonalOracleLoss] using h.symm

/-- In a unitary basis, the real diagonal of `Uᴴ * T * U` minimizes Frobenius loss. -/
theorem norm_sub_unitary_diagonal_sq_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U T : Matrix ι ι ℂ) (hU : U ∈ Matrix.unitaryGroup ι ℂ) (d : ι → ℝ) :
    ‖T - U * Matrix.diagonal (fun i => (diagonalOracle (Uᴴ * T * U) i : ℂ)) * Uᴴ‖ ^ 2 ≤
      ‖T - U * Matrix.diagonal (fun i => (d i : ℂ)) * Uᴴ‖ ^ 2 := by
  rw [norm_sub_unitary_diagonal_sq U T hU, norm_sub_unitary_diagonal_sq U T hU]
  exact diagonalOracleLoss_le _ d

/-- Equality with the minimum in a unitary basis holds exactly at the diagonal oracle. -/
theorem norm_sub_unitary_diagonal_sq_eq_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U T : Matrix ι ι ℂ) (hU : U ∈ Matrix.unitaryGroup ι ℂ) (d : ι → ℝ) :
    ‖T - U * Matrix.diagonal (fun i => (d i : ℂ)) * Uᴴ‖ ^ 2 =
        ‖T - U * Matrix.diagonal (fun i => (diagonalOracle (Uᴴ * T * U) i : ℂ)) * Uᴴ‖ ^ 2 ↔
      d = diagonalOracle (Uᴴ * T * U) := by
  rw [norm_sub_unitary_diagonal_sq U T hU, norm_sub_unitary_diagonal_sq U T hU]
  exact diagonalOracleLoss_eq_iff _ d

/-- The average of the real target diagonal over a block, or zero for an empty block. -/
def diagonalBlockAverage {ι : Type*} (T : Matrix ι ι ℂ) (s : Finset ι) :
    ℝ :=
  (∑ i ∈ s, (T i i).re) / s.card

/-- The block average is the real part of the trace of the coordinate compression,
divided by the block's cardinality. -/
theorem diagonalBlockAverage_eq_trace_compression {ι : Type*}
    (T : Matrix ι ι ℂ) (s : Finset ι) :
    diagonalBlockAverage T s =
      (Matrix.trace (T.submatrix (fun i : {i // i ∈ s} => i.1)
        (fun i : {i // i ∈ s} => i.1))).re / s.card := by
  classical
  simp only [diagonalBlockAverage, Matrix.trace, Matrix.diag_apply, Matrix.submatrix_apply,
    Complex.re_sum]
  congr 1
  exact Finset.sum_subtype s (by simp) (fun i => (T i i).re)

/-- The diagonal squared-error contribution of assigning the common value `c` to a block. -/
def diagonalBlockLoss {ι : Type*} (T : Matrix ι ι ℂ) (s : Finset ι)
    (c : ℝ) : ℝ :=
  ∑ i ∈ s, ((T i i).re - c) ^ 2

/-- On any block, the squared-error loss is the loss at the average plus its excess. -/
theorem diagonalBlockLoss_eq_diagonalBlockAverage_add {ι : Type*} (T : Matrix ι ι ℂ)
    (s : Finset ι) (c : ℝ) :
    diagonalBlockLoss T s c =
      diagonalBlockLoss T s (diagonalBlockAverage T s) +
        s.card * (c - diagonalBlockAverage T s) ^ 2 := by
  simpa only [diagonalBlockLoss, diagonalBlockAverage] using
    Finset.sum_sq_sub_mean s (fun i => (T i i).re) c

/-- The average diagonal value is the unique minimizer when a diagonal estimator is required to
be constant on a nonempty block. -/
theorem diagonalBlockLoss_unique_minimizer {ι : Type*} (T : Matrix ι ι ℂ)
    (s : Finset ι) (hs : s.Nonempty) :
    ∀ c : ℝ, diagonalBlockLoss T s (diagonalBlockAverage T s) ≤ diagonalBlockLoss T s c ∧
      (diagonalBlockLoss T s c = diagonalBlockLoss T s (diagonalBlockAverage T s) ↔
        c = diagonalBlockAverage T s) := by
  intro c
  constructor
  · simpa only [diagonalBlockLoss, diagonalBlockAverage] using
      Finset.sum_sq_sub_mean_le s (fun i => (T i i).re) c
  · simpa only [diagonalBlockLoss, diagonalBlockAverage] using
      Finset.sum_sq_sub_mean_eq_iff s (fun i => (T i i).re) hs c

/-- On a nonempty block, the average has the least squared-error loss. -/
theorem diagonalBlockLoss_le {ι : Type*} (T : Matrix ι ι ℂ) (s : Finset ι)
    (hs : s.Nonempty) (c : ℝ) :
    diagonalBlockLoss T s (diagonalBlockAverage T s) ≤ diagonalBlockLoss T s c :=
  (diagonalBlockLoss_unique_minimizer T s hs c).1

/-- Equality with the block minimum characterizes the average. -/
theorem diagonalBlockLoss_eq_iff {ι : Type*} (T : Matrix ι ι ℂ) (s : Finset ι)
    (hs : s.Nonempty) (c : ℝ) :
    diagonalBlockLoss T s c = diagonalBlockLoss T s (diagonalBlockAverage T s) ↔
      c = diagonalBlockAverage T s :=
  (diagonalBlockLoss_unique_minimizer T s hs c).2

end Matrix

end
