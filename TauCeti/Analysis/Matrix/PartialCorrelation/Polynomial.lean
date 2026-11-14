/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.PartialCorrelation.Basic
public import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Polynomial expansion of the partial-correlation Gram construction

Regard partial correlations and residual square roots as separate formal variables. The
Cholesky and Gram constructions then become polynomial matrices. Evaluating the left
variables at `z` and the right variables at `√(1 - z²)` recovers the actual matrices, even
outside the partial-correlation cube. Polynomial coefficients therefore give finite
expansions suitable for computing mixed correlation-entry moments.

The underlying construction is that of Lewandowski, Kurowicka and Joe,
*Generating random correlation matrices based on vines and extended onion method* (2009).
-/

public section

noncomputable section

open scoped BigOperators Matrix

namespace TauCeti

variable {p : ℕ}

/-- The formal partial-correlation Cholesky factor. Left variables represent the partial
correlations; right variables represent their residual square roots. -/
def partialCorrelationCholeskyPolynomial (p : ℕ) :
    Matrix (Fin p) (Fin p) (MvPolynomial (strictLowerTriangle p ⊕ strictLowerTriangle p) ℝ) :=
  fun i j ↦ if h : j < i then
    MvPolynomial.X (Sum.inl ⟨(i, j), h⟩) *
      ∏ ij : strictLowerTriangle p with ij.1.1 = i ∧ ij.1.2 < j, MvPolynomial.X (Sum.inr ij)
    else if i = j then
      ∏ ij : strictLowerTriangle p with ij.1.1 = i, MvPolynomial.X (Sum.inr ij)
    else 0

/-- The formal Cholesky entry is a coordinate times preceding residual variables below the
diagonal, a product of residual variables on the diagonal, and zero above it. -/
theorem partialCorrelationCholeskyPolynomial_apply (p : ℕ) (i j : Fin p) :
    partialCorrelationCholeskyPolynomial p i j =
      if h : j < i then
        MvPolynomial.X (Sum.inl ⟨(i, j), h⟩) *
          ∏ ij : strictLowerTriangle p with ij.1.1 = i ∧ ij.1.2 < j,
            MvPolynomial.X (Sum.inr ij)
      else if i = j then
        ∏ ij : strictLowerTriangle p with ij.1.1 = i, MvPolynomial.X (Sum.inr ij)
      else 0 := (rfl)

/-- A formal Cholesky entry below the diagonal is a coordinate times preceding residuals. -/
@[simp]
theorem partialCorrelationCholeskyPolynomial_apply_of_gt {i j : Fin p} (h : j < i) :
    partialCorrelationCholeskyPolynomial p i j =
      MvPolynomial.X (Sum.inl ⟨(i, j), h⟩) *
        ∏ ij : strictLowerTriangle p with ij.1.1 = i ∧ ij.1.2 < j,
          MvPolynomial.X (Sum.inr ij) := by
  simp [partialCorrelationCholeskyPolynomial_apply, h]

/-- A formal Cholesky diagonal entry is the product of the residual variables in its row. -/
@[simp]
theorem partialCorrelationCholeskyPolynomial_apply_self (i : Fin p) :
    partialCorrelationCholeskyPolynomial p i i =
      ∏ ij : strictLowerTriangle p with ij.1.1 = i, MvPolynomial.X (Sum.inr ij) := by
  simp [partialCorrelationCholeskyPolynomial_apply]

/-- A formal Cholesky entry above the diagonal is zero. -/
@[simp]
theorem partialCorrelationCholeskyPolynomial_apply_of_lt {i j : Fin p} (h : i < j) :
    partialCorrelationCholeskyPolynomial p i j = 0 := by
  simp [partialCorrelationCholeskyPolynomial_apply, h.not_gt, h.ne]

/-- The formal partial-correlation Cholesky factor is lower triangular. -/
theorem isLowerTriangular_partialCorrelationCholeskyPolynomial (p : ℕ) :
    (partialCorrelationCholeskyPolynomial p).IsLowerTriangular :=
  fun _ _ h ↦ partialCorrelationCholeskyPolynomial_apply_of_lt h

/-- Evaluating the formal Cholesky entries at coordinates and residual square roots recovers
the partial-correlation factor, with the usual totalization of square root. -/
@[simp]
theorem eval_partialCorrelationCholeskyPolynomial (z : strictLowerTriangle p → ℝ)
    (i j : Fin p) :
    MvPolynomial.eval (Sum.elim z (fun ij ↦ Real.sqrt (1 - z ij ^ 2)))
      (partialCorrelationCholeskyPolynomial p i j) = partialCorrelationCholesky z i j := by
  rcases lt_trichotomy j i with h | rfl | h
  · simp [h]
  · simp
  · simp [h]

/-- The formal Gram matrix of the polynomial partial-correlation Cholesky factor. -/
def partialCorrelationGramPolynomial (p : ℕ) :
    Matrix (Fin p) (Fin p) (MvPolynomial (strictLowerTriangle p ⊕ strictLowerTriangle p) ℝ) :=
  partialCorrelationCholeskyPolynomial p * (partialCorrelationCholeskyPolynomial p)ᵀ

/-- The formal Gram matrix is the formal triangular factor times its transpose. -/
theorem partialCorrelationGramPolynomial_def (p : ℕ) :
    partialCorrelationGramPolynomial p =
      partialCorrelationCholeskyPolynomial p * (partialCorrelationCholeskyPolynomial p)ᵀ := (rfl)

/-- A formal Gram entry sums triangular column contributions up to its second index. -/
theorem partialCorrelationGramPolynomial_apply_eq_sum_Iic (p : ℕ) (i j : Fin p) :
    partialCorrelationGramPolynomial p i j =
      ∑ k ∈ Finset.Iic j,
        partialCorrelationCholeskyPolynomial p i k *
          partialCorrelationCholeskyPolynomial p j k := by
  rw [partialCorrelationGramPolynomial_def, Matrix.mul_apply]
  simp only [Matrix.transpose_apply]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro k _ hk
  simp only [Finset.mem_Iic, not_le] at hk
  rw [partialCorrelationCholeskyPolynomial_apply_of_lt hk, mul_zero]

/-- The formal partial-correlation Gram matrix is symmetric. -/
@[simp]
theorem partialCorrelationGramPolynomial_transpose (p : ℕ) :
    (partialCorrelationGramPolynomial p)ᵀ = partialCorrelationGramPolynomial p := by
  simp [partialCorrelationGramPolynomial_def, Matrix.transpose_mul]

/-- Evaluation of the polynomial Gram matrix recovers the correlation construction. -/
@[simp]
theorem eval_partialCorrelationGramPolynomial (z : strictLowerTriangle p → ℝ) (i j : Fin p) :
    MvPolynomial.eval (Sum.elim z (fun ij ↦ Real.sqrt (1 - z ij ^ 2)))
      (partialCorrelationGramPolynomial p i j) = partialCorrelationGram z i j := by
  simp [partialCorrelationGramPolynomial_def, partialCorrelationGram_def, Matrix.mul_apply]

/-- Expand the entry monomial with ordered-pair exponents `n` through the formal partial-correlation
Gram matrix. Its left variables are partial correlations and its right variables are residual
square roots. Its coefficients are obtained by ordinary finite polynomial arithmetic. -/
def partialCorrelationGramMonomialPolynomial (p : ℕ) (n : Fin p × Fin p → ℕ) :
    MvPolynomial (strictLowerTriangle p ⊕ strictLowerTriangle p) ℝ :=
  ∏ ij, partialCorrelationGramPolynomial p ij.1 ij.2 ^ n ij

/-- The entry-monomial polynomial is the product of formal Gram entries raised to their
specified natural exponents. -/
theorem partialCorrelationGramMonomialPolynomial_def (p : ℕ) (n : Fin p × Fin p → ℕ) :
    partialCorrelationGramMonomialPolynomial p n =
      ∏ ij, partialCorrelationGramPolynomial p ij.1 ij.2 ^ n ij := (rfl)

/-- Evaluation of the expanded polynomial is the original correlation-entry monomial. -/
@[simp]
theorem eval_partialCorrelationGramMonomialPolynomial (n : Fin p × Fin p → ℕ)
    (z : strictLowerTriangle p → ℝ) :
    MvPolynomial.eval (Sum.elim z (fun ij ↦ Real.sqrt (1 - z ij ^ 2)))
        (partialCorrelationGramMonomialPolynomial p n) =
      ∏ ij, partialCorrelationGram z ij.1 ij.2 ^ n ij := by
  simp [partialCorrelationGramMonomialPolynomial_def]

/-- The zeroth entry monomial expands to the constant polynomial one, in every dimension. -/
@[simp]
theorem partialCorrelationGramMonomialPolynomial_zero (p : ℕ) :
    partialCorrelationGramMonomialPolynomial p 0 = 1 := by
  simp [partialCorrelationGramMonomialPolynomial_def]

/-- A pointwise zero exponent function also simplifies to the constant polynomial one. -/
@[simp]
theorem partialCorrelationGramMonomialPolynomial_fun_zero (p : ℕ) :
    partialCorrelationGramMonomialPolynomial p (fun _ ↦ 0) = 1 := by
  simpa only [Pi.zero_def] using partialCorrelationGramMonomialPolynomial_zero p

/-- Adding entry exponents multiplies their formal Gram monomial polynomials. -/
theorem partialCorrelationGramMonomialPolynomial_add (m n : Fin p × Fin p → ℕ) :
    partialCorrelationGramMonomialPolynomial p (m + n) =
      partialCorrelationGramMonomialPolynomial p m *
        partialCorrelationGramMonomialPolynomial p n := by
  simp [partialCorrelationGramMonomialPolynomial_def, pow_add, Finset.prod_mul_distrib]

/-- A single-entry exponent expands to the corresponding formal Gram entry power. -/
@[simp]
theorem partialCorrelationGramMonomialPolynomial_single (ij : Fin p × Fin p) (k : ℕ) :
    partialCorrelationGramMonomialPolynomial p (Pi.single ij k) =
      partialCorrelationGramPolynomial p ij.1 ij.2 ^ k := by
  rw [partialCorrelationGramMonomialPolynomial_def, Finset.prod_eq_single ij]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · simp

end TauCeti
