/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Cluster.ExchangeMatrix.Mutation
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Tactic.FinCases

/-!
# Periodic matrix mutation for Somos–4

The mutable indices are cyclically ordered in `Fin 4`. Under successive mutations at
`0, 1, 2, 3, …`, each exchange matrix is obtained from the initial one by rotating both
indices. In the next exchange column, the entry at the mutated index is zero, the two
neighboring entries are one, and the opposite entry is minus two. The positive and negative
parts of this column give natural exponents one and two in the two monomials of the
Somos–4 exchange numerator.

See Fomin and Zelevinsky, *The Laurent phenomenon*, Example 3.3, for the recurrence.
-/

public section

open scoped Fin.NatCast

namespace TauCeti.SomosFour

/-- The skew-symmetric initial exchange matrix in the column convention. -/
def initialMatrix : Matrix (Fin 4) (Fin 4) ℤ :=
  !![0, -1, 2, -1; 1, 0, -3, 2; -2, 3, 0, -1; 1, -2, 1, 0]

/-- The entries of the initial exchange matrix in the column convention. -/
@[simp]
theorem initialMatrix_apply (i j : Fin 4) :
    initialMatrix i j =
      !![(0 : ℤ), -1, 2, -1; 1, 0, -3, 2; -2, 3, 0, -1; 1, -2, 1, 0] i j := by
  rfl

/-- The sequence obtained by mutating once in each direction in cyclic order. -/
def exchangeMatrix : ℕ → Matrix (Fin 4) (Fin 4) ℤ
  | 0 => initialMatrix
  | n + 1 => matrixMutation (Function.Embedding.refl _) (exchangeMatrix n) (n : Fin 4)

/-- The initial term of the cyclic exchange-matrix sequence. -/
@[simp]
theorem exchangeMatrix_zero : exchangeMatrix 0 = initialMatrix := by
  rfl

/-- The next exchange matrix mutates the preceding matrix in the next cyclic direction. -/
theorem exchangeMatrix_succ (n : ℕ) :
    exchangeMatrix (n + 1) =
      matrixMutation (Function.Embedding.refl _) (exchangeMatrix n) (n : Fin 4) := by
  rfl

private theorem mutation_initial (i j : Fin 4) :
    matrixMutation (Function.Embedding.refl _) initialMatrix 0 i j =
      initialMatrix (i - 1) (j - 1) := by
  rw [matrixMutation_apply]
  fin_cases i <;> fin_cases j <;> decide

/-- At time `n`, both indices of the initial matrix have advanced by `n` modulo four. -/
theorem exchangeMatrix_eq_submatrix (n : ℕ) :
    exchangeMatrix n = initialMatrix.submatrix (· - (n : Fin 4)) (· - (n : Fin 4)) := by
  induction n with
  | zero => ext i j; simp
  | succ n ih =>
    let k : Fin 4 := n
    let f : Fin 4 → Fin 4 := (· - k)
    have hf : Function.Injective f := fun _ _ h ↦ sub_left_inj.mp h
    have hcompat (a : Fin 4) :
        f ((Function.Embedding.refl (Fin 4)) a) =
          (Function.Embedding.refl (Fin 4)) (f a) := by
      simp only [Function.Embedding.refl_apply]
    have hm : matrixMutation (Function.Embedding.refl (Fin 4))
        (initialMatrix.submatrix f f) k =
        (matrixMutation (Function.Embedding.refl (Fin 4)) initialMatrix (f k)).submatrix f f := by
      apply_rules [matrixMutation_submatrix, hf, hcompat]
    ext i j
    rw [exchangeMatrix_succ, ih, hm]
    simp [Matrix.submatrix_apply, f, k, mutation_initial, sub_sub]

/-- The entire exchange-matrix sequence has period four. -/
@[simp]
theorem exchangeMatrix_add_four (n : ℕ) : exchangeMatrix (n + 4) = exchangeMatrix n := by
  rw [exchangeMatrix_eq_submatrix, exchangeMatrix_eq_submatrix]
  simp

/-- The column in the next mutation direction, at an arbitrary row index. -/
@[simp]
theorem exchangeMatrix_apply_col (n : ℕ) (i : Fin 4) :
    exchangeMatrix n i n = ![(0 : ℤ), 1, -2, 1] (i - (n : Fin 4)) := by
  rw [exchangeMatrix_eq_submatrix]
  simp only [Matrix.submatrix_apply, sub_self]
  generalize i - (n : Fin 4) = r
  fin_cases r <;> decide

/-- All the exchange matrices admit the constant symmetrizer one. -/
theorem isSkewSymmetrizer_exchangeMatrix (n : ℕ) :
    (exchangeMatrix n).IsSkewSymmetrizer (fun _ ↦ 1) := by
  have h : initialMatrix.IsSkewSymmetrizer (fun _ ↦ 1) := by
    constructor
    · intro _; decide
    · intro i j; fin_cases i <;> fin_cases j <;> decide
  rw [exchangeMatrix_eq_submatrix]
  exact h.submatrix _

/-- Every diagonal entry of a cyclic exchange matrix is zero. -/
@[simp]
theorem exchangeMatrix_apply_self (n : ℕ) (i : Fin 4) : exchangeMatrix n i i = 0 := by
  exact (isSkewSymmetrizer_exchangeMatrix n).apply_self i

/-- The positive column monomial, in the original row order, is the product of the two
neighboring variables. -/
theorem prod_pow_toNat_exchangeMatrix {R : Type*} [CommMonoid R]
    (n : ℕ) (x : Fin 4 → R) :
    ∏ i : Fin 4, x i ^ (exchangeMatrix n i n).toNat =
      x ((n : Fin 4) + 1) * x ((n : Fin 4) + 3) := by
  rw [← Equiv.prod_comp (Equiv.addLeft (n : Fin 4))
    (fun i ↦ x i ^ (exchangeMatrix n i n).toNat)]
  simp [Fin.prod_univ_succ]

/-- The negative column monomial, in the original row order, is the square of the opposite
variable. -/
theorem prod_pow_toNat_neg_exchangeMatrix {R : Type*} [CommMonoid R]
    (n : ℕ) (x : Fin 4 → R) :
    ∏ i : Fin 4, x i ^ (-(exchangeMatrix n i n)).toNat = x ((n : Fin 4) + 2) ^ 2 := by
  rw [← Equiv.prod_comp (Equiv.addLeft (n : Fin 4))
    (fun i ↦ x i ^ (-(exchangeMatrix n i n)).toNat)]
  simp [Fin.prod_univ_succ]

/-- The positive and negative column monomials, in the original row order, give exactly
the two terms in the Somos–4 exchange numerator. -/
theorem prod_pow_toNat_exchangeMatrix_add_prod_pow_toNat_neg
    {R : Type*} [CommMonoid R] [Add R] (n : ℕ) (x : Fin 4 → R) :
    (∏ i : Fin 4, x i ^ (exchangeMatrix n i n).toNat) +
      (∏ i : Fin 4, x i ^ (-(exchangeMatrix n i n)).toNat) =
      x ((n : Fin 4) + 1) * x ((n : Fin 4) + 3) + x ((n : Fin 4) + 2) ^ 2 := by
  rw [prod_pow_toNat_exchangeMatrix, prod_pow_toNat_neg_exchangeMatrix]

end TauCeti.SomosFour
