/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# Finite-dimensional spectral oracle

In coordinates of a fixed orthonormal basis, the diagonal estimator with entries `T i i` is the
unique minimizer of squared Frobenius loss among diagonal estimators. If an estimator must be
constant on a block of basis vectors, its optimal value is the average of the corresponding
diagonal entries. For an eigenbasis, these blocks are the repeated-eigenvalue eigenspaces.
-/

public section

noncomputable section

open Matrix

namespace TauCeti

namespace Probability

/-- The squared Frobenius loss between two complex matrices, with diagonal and off-diagonal
entries separated. -/
def squaredFrobeniusLoss {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  (∑ i, ∑ j ∈ Finset.univ.erase i, Complex.normSq (A i j - B i j)) +
    ∑ i, Complex.normSq (A i i - B i i)

/-- The diagonal matrix with real entries `d`. -/
def realDiagonalEstimator {n : ℕ} (d : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal fun i => (d i : ℂ)

/-- Squared Frobenius loss to a diagonal estimator in the target's coordinate basis. -/
def diagonalOracleLoss {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℝ) : ℝ :=
  squaredFrobeniusLoss T (realDiagonalEstimator d)

/-- The diagonal entries of a Hermitian target, which are real-valued quadratic forms in the
chosen orthonormal basis. -/
def diagonalOracle {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ) : Fin n → ℝ :=
  fun i => (T i i).re

/-- The matrix of a target in the coordinates given by the columns of `U`. For an orthonormal
basis, `U` is its unitary basis matrix. -/
def matrixInBasis {n : ℕ} (U T : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Uᴴ * T * U

/-- The oracle entries in the basis given by the columns of `U`; the `i`th entry is
`uᵢ* T uᵢ`. -/
def diagonalOracleInBasis {n : ℕ} (U T : Matrix (Fin n) (Fin n) ℂ) : Fin n → ℝ :=
  diagonalOracle (matrixInBasis U T)

/-- The `i`th basis oracle entry is the real part of `uᵢ* T uᵢ`. -/
@[simp]
theorem diagonalOracleInBasis_apply {n : ℕ} (U T : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) :
    diagonalOracleInBasis U T i = ((Uᴴ * T * U) i i).re := by
  simp [diagonalOracleInBasis, diagonalOracle, matrixInBasis]

private theorem diagonalOracleLoss_eq_offDiagonal_add {n : ℕ}
    (T : Matrix (Fin n) (Fin n) ℂ) (hT : T.IsHermitian) (d : Fin n → ℝ) :
    diagonalOracleLoss T d =
      (∑ i, ∑ j ∈ Finset.univ.erase i, Complex.normSq (T i j)) +
        ∑ i, ((T i i).re - d i) ^ 2 := by
  unfold diagonalOracleLoss squaredFrobeniusLoss
  have hoff :
      (∑ i, ∑ j ∈ Finset.univ.erase i,
          Complex.normSq (T i j - realDiagonalEstimator d i j)) =
        ∑ i, ∑ j ∈ Finset.univ.erase i, Complex.normSq (T i j) := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    have hentry : realDiagonalEstimator d i j = 0 := by
      change Matrix.diagonal (fun i => (d i : ℂ)) i j = 0
      simp [Ne.symm hji]
    rw [hentry]
    simp
  rw [hoff]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have hest : realDiagonalEstimator d i i = (d i : ℂ) := by
    simp [realDiagonalEstimator]
  rw [hest]
  conv_lhs => rw [(Complex.conj_eq_iff_re.mp (hT.apply i i)).symm]
  rw [← Complex.ofReal_sub, Complex.normSq_ofReal]
  ring

/-- In a fixed orthonormal basis, the diagonal entries `uᵢ* T uᵢ` uniquely minimize squared
Frobenius loss among real diagonal estimators. The identity also gives the exact excess loss. -/
theorem diagonalOracleLoss_eq_oracle_add {n : ℕ} {T : Matrix (Fin n) (Fin n) ℂ}
    (hT : T.IsHermitian) (d : Fin n → ℝ) :
    diagonalOracleLoss T d =
      diagonalOracleLoss T (diagonalOracle T) +
        ∑ i, (d i - diagonalOracle T i) ^ 2 := by
  rw [diagonalOracleLoss_eq_offDiagonal_add T hT d,
    diagonalOracleLoss_eq_offDiagonal_add T hT (diagonalOracle T)]
  simp only [diagonalOracle]
  have hzero : (∑ i, ((T i i).re - (T i i).re) ^ 2) = 0 := by simp
  rw [hzero, add_zero]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- The basis-diagonal oracle is the unique minimizer of squared Frobenius loss. -/
theorem diagonalOracleLoss_unique_minimizer {n : ℕ} {T : Matrix (Fin n) (Fin n) ℂ}
    (hT : T.IsHermitian) :
    ∀ d : Fin n → ℝ, diagonalOracleLoss T (diagonalOracle T) ≤ diagonalOracleLoss T d ∧
      (diagonalOracleLoss T d = diagonalOracleLoss T (diagonalOracle T) ↔
        d = diagonalOracle T) := by
  intro d
  rw [diagonalOracleLoss_eq_oracle_add hT d]
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

/-- In the coordinates of any chosen orthonormal basis, the unique diagonal minimizer has entries
`uᵢ* T uᵢ`. -/
theorem diagonalOracleLoss_unique_minimizer_inBasis {n : ℕ}
    {U T : Matrix (Fin n) (Fin n) ℂ} (hT : T.IsHermitian) :
    ∀ d : Fin n → ℝ,
      diagonalOracleLoss (matrixInBasis U T) (diagonalOracleInBasis U T) ≤
          diagonalOracleLoss (matrixInBasis U T) d ∧
        (diagonalOracleLoss (matrixInBasis U T) d =
            diagonalOracleLoss (matrixInBasis U T) (diagonalOracleInBasis U T) ↔
          d = diagonalOracleInBasis U T) := by
  simpa [diagonalOracleInBasis] using
    (diagonalOracleLoss_unique_minimizer
      (show (matrixInBasis U T).IsHermitian from Matrix.isHermitian_conjTranspose_mul_mul U hT))

/-- The average target diagonal on a nonempty spectral block. For a Hermitian target and an
eigenspace, this is the trace of the compression divided by its dimension. -/
def spectralBlockOracle {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ) (s : Finset (Fin n)) :
    ℝ :=
  (∑ i ∈ s, (T i i).re) / s.card

/-- The diagonal squared-error contribution of assigning the common value `c` to a block. -/
def spectralBlockLoss {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ) (s : Finset (Fin n))
    (c : ℝ) : ℝ :=
  ∑ i ∈ s, ((T i i).re - c) ^ 2

/-- On any nonempty block, the squared-error loss is minimized by the average diagonal value;
the identity gives uniqueness and the exact excess loss. Applying this independently to each
repeated-eigenvalue block yields the spectral-estimator oracle. -/
theorem spectralBlockLoss_eq_average_add {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (s : Finset (Fin n)) (hs : s.Nonempty) (c : ℝ) :
    spectralBlockLoss T s c =
      spectralBlockLoss T s (spectralBlockOracle T s) +
        s.card * (c - spectralBlockOracle T s) ^ 2 := by
  let t : Fin n → ℝ := fun i => (T i i).re
  let a : ℝ := (∑ i ∈ s, t i) / s.card
  have hcard : (s.card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr hs)
  have hsum : ∑ i ∈ s, t i = (s.card : ℝ) * a := by
    dsimp [a]
    field_simp [hcard]
  have hsum_centered : ∑ i ∈ s, (t i - a) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hsum]
    ring
  change (∑ i ∈ s, (t i - c) ^ 2) =
    (∑ i ∈ s, (t i - a) ^ 2) + s.card * (c - a) ^ 2
  calc
    (∑ i ∈ s, (t i - c) ^ 2) =
        ∑ i ∈ s, ((t i - a) ^ 2 + (c - a) ^ 2 - 2 * (t i - a) * (c - a)) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = (∑ i ∈ s, (t i - a) ^ 2) + s.card * (c - a) ^ 2 -
          2 * (∑ i ∈ s, (t i - a)) * (c - a) := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
        nsmul_eq_mul]
      have hcross :
          (∑ i ∈ s, 2 * (t i - a) * (c - a)) =
            2 * (∑ i ∈ s, (t i - a)) * (c - a) := by
        calc
          (∑ i ∈ s, 2 * (t i - a) * (c - a)) =
              ∑ i ∈ s, 2 * ((t i - a) * (c - a)) := by
            apply Finset.sum_congr rfl
            intro i hi
            ring
          _ = 2 * (∑ i ∈ s, (t i - a) * (c - a)) := by rw [← Finset.mul_sum]
          _ = 2 * (∑ i ∈ s, (t i - a)) * (c - a) := by
            rw [← Finset.sum_mul]
            ring
      rw [hcross]
    _ = (∑ i ∈ s, (t i - a) ^ 2) + s.card * (c - a) ^ 2 := by
      rw [hsum_centered]
      ring

/-- The average diagonal value is the unique minimizer when a diagonal estimator is required to
be constant on a nonempty block. -/
theorem spectralBlockLoss_unique_minimizer {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (s : Finset (Fin n)) (hs : s.Nonempty) :
    ∀ c : ℝ, spectralBlockLoss T s (spectralBlockOracle T s) ≤ spectralBlockLoss T s c ∧
      (spectralBlockLoss T s c = spectralBlockLoss T s (spectralBlockOracle T s) ↔
        c = spectralBlockOracle T s) := by
  intro c
  rw [spectralBlockLoss_eq_average_add T s hs c]
  constructor
  · exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _)
      (sq_nonneg (c - spectralBlockOracle T s)))
  · rw [add_eq_left]
    constructor
    · intro h
      have hcard : 0 < (s.card : ℝ) := by exact_mod_cast hs.card_pos
      have hsq :
          (c - spectralBlockOracle T s) ^ 2 = 0 :=
        (mul_eq_zero.mp h).resolve_left (ne_of_gt hcard)
      nlinarith
    · intro h
      simp [h]

end Probability

end TauCeti

end
