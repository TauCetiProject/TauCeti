/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Cluster.ExchangeMatrix.Mutation
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Algebra.Group.Fin.Basic
public import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases

/-!
# Periodic matrix mutation for Somos–4

The mutable indices are cyclically ordered in `Fin 4`. Under successive mutations at
`0, 1, 2, 3, …`, each exchange matrix is obtained from the initial one by rotating both
indices. In its next exchange column, the two neighboring variables have exponent one
and the opposite variable has exponent minus two. These are the exponents in the
Somos–4 exchange numerator.

See Fomin and Zelevinsky, *The Laurent phenomenon*, Example 3.3, for the recurrence.
-/

public section

open scoped Fin.NatCast

namespace TauCeti.SomosFour

/-- The skew-symmetric initial exchange matrix in the column convention. -/
def initialMatrix : Matrix (Fin 4) (Fin 4) ℤ :=
  !![0, -1, 2, -1; 1, 0, -3, 2; -2, 3, 0, -1; 1, -2, 1, 0]

/-- The sequence obtained by mutating once in each direction in cyclic order. -/
def exchangeMatrix : ℕ → Matrix (Fin 4) (Fin 4) ℤ
  | 0 => initialMatrix
  | n + 1 => matrixMutation (Function.Embedding.refl _) (exchangeMatrix n) (n : Fin 4)

private theorem mutation_initial (i j : Fin 4) :
    matrixMutation (Function.Embedding.refl _) initialMatrix 0 i j =
      initialMatrix (i - 1) (j - 1) := by
  rw [matrixMutation_apply]
  fin_cases i <;> fin_cases j <;> decide

/-- At time `n`, both indices of the initial matrix have advanced by `n` modulo four. -/
theorem exchangeMatrix_eq_submatrix (n : ℕ) :
    exchangeMatrix n = initialMatrix.submatrix (· - (n : Fin 4)) (· - (n : Fin 4)) := by
  induction n with
  | zero => ext i j; simp [exchangeMatrix]
  | succ n ih =>
    let k : Fin 4 := n
    let f : Fin 4 → Fin 4 := (· - k)
    have hf : Function.Injective f := fun _ _ h ↦ sub_left_inj.mp h
    have hm := matrixMutation_submatrix (row := Function.Embedding.refl (Fin 4))
      (row' := Function.Embedding.refl (Fin 4)) (f := f) (g := f)
      hf hf (fun _ ↦ rfl) initialMatrix k
    ext i j
    rw [exchangeMatrix, ih]
    change matrixMutation _ (initialMatrix.submatrix f f) k i j = _
    rw [hm]
    simp [Matrix.submatrix_apply, f, k, mutation_initial, sub_sub]

/-- The entire exchange-matrix sequence has period four. -/
theorem exchangeMatrix_add_four (n : ℕ) : exchangeMatrix (n + 4) = exchangeMatrix n := by
  rw [exchangeMatrix_eq_submatrix, exchangeMatrix_eq_submatrix]
  simp

/-- The column in the next mutation direction, read starting at that direction. -/
theorem exchangeMatrix_column (n : ℕ) (r : Fin 4) :
    exchangeMatrix n ((n : Fin 4) + r) n = ![(0 : ℤ), 1, -2, 1] r := by
  rw [exchangeMatrix_eq_submatrix]
  simp only [Matrix.submatrix_apply, add_sub_cancel_left, sub_self]
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

/-- In cyclic order, the positive and negative column monomials give exactly the two
terms in the Somos–4 exchange numerator. -/
theorem exchangeNumerator {R : Type*} [CommSemiring R] (n : ℕ) (x : Fin 4 → R) :
    (∏ r : Fin 4, x ((n : Fin 4) + r) ^ (exchangeMatrix n ((n : Fin 4) + r) n).toNat) +
      (∏ r : Fin 4, x ((n : Fin 4) + r) ^ (-(exchangeMatrix n ((n : Fin 4) + r) n)).toNat) =
      x ((n : Fin 4) + 1) * x ((n : Fin 4) + 3) + x ((n : Fin 4) + 2) ^ 2 := by
  simp [exchangeMatrix_column, Fin.prod_univ_succ]

end TauCeti.SomosFour
