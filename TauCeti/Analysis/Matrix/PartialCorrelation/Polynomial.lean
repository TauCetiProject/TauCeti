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

/-- Evaluating the formal Cholesky entries at coordinates and residual square roots recovers
the partial-correlation factor, with the usual totalization of square root. -/
@[simp]
theorem eval_partialCorrelationCholeskyPolynomial (z : strictLowerTriangle p → ℝ)
    (i j : Fin p) :
    MvPolynomial.eval (Sum.elim z (fun ij ↦ Real.sqrt (1 - z ij ^ 2)))
      (partialCorrelationCholeskyPolynomial p i j) = partialCorrelationCholesky z i j := by
  rcases lt_trichotomy j i with h | rfl | h
  · simp [partialCorrelationCholeskyPolynomial_apply, h,
      partialCorrelationCholesky_apply_of_gt]
  · simp [partialCorrelationCholeskyPolynomial_apply, partialCorrelationCholesky_apply_self]
  · simp [partialCorrelationCholeskyPolynomial_apply, h.not_gt, h.ne,
      partialCorrelationCholesky_apply_of_lt _ h]

/-- The formal Gram matrix of the polynomial partial-correlation Cholesky factor. -/
def partialCorrelationGramPolynomial (p : ℕ) :
    Matrix (Fin p) (Fin p) (MvPolynomial (strictLowerTriangle p ⊕ strictLowerTriangle p) ℝ) :=
  partialCorrelationCholeskyPolynomial p * (partialCorrelationCholeskyPolynomial p)ᵀ

/-- The formal Gram matrix is the formal triangular factor times its transpose. -/
theorem partialCorrelationGramPolynomial_def (p : ℕ) :
    partialCorrelationGramPolynomial p =
      partialCorrelationCholeskyPolynomial p * (partialCorrelationCholeskyPolynomial p)ᵀ := (rfl)

/-- Evaluation of the polynomial Gram matrix recovers the correlation construction. -/
@[simp]
theorem eval_partialCorrelationGramPolynomial (z : strictLowerTriangle p → ℝ) (i j : Fin p) :
    MvPolynomial.eval (Sum.elim z (fun ij ↦ Real.sqrt (1 - z ij ^ 2)))
      (partialCorrelationGramPolynomial p i j) = partialCorrelationGram z i j := by
  simp [partialCorrelationGramPolynomial_def, partialCorrelationGram_def, Matrix.mul_apply]

end TauCeti
