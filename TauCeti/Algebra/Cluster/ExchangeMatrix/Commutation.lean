/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Cluster.ExchangeMatrix.Mutation

import Mathlib.Tactic.Ring

/-!
# Mutation in nonadjacent directions

Two matrix mutations commute when both entries connecting their directions vanish.
The raw rectangular statement needs neither a zero diagonal nor a symmetrizer. For an
exchange matrix, one vanishing entry implies the other by skew-symmetrizability.

This is the independent-direction relation for amalgamated exchange matrices.
-/

public section

namespace TauCeti

variable {I K : Type*} [DecidableEq I] [DecidableEq K]

/-- Mutations in two directions with zero entries between them commute, for any rectangular
integer matrix, including matrices with nonzero diagonal. -/
theorem matrixMutation_matrixMutation_comm (row : K ↪ I) (B : Matrix I K ℤ) (k l : K)
    (hkl : B (row k) l = 0) (hlk : B (row l) k = 0) :
    matrixMutation row (matrixMutation row B k) l =
      matrixMutation row (matrixMutation row B l) k := by
  by_cases h : k = l
  · subst l
    rfl
  have hrow : row k ≠ row l := row.injective.ne h
  have rk (j : K) : matrixMutation row B l (row k) j = B (row k) j :=
    matrixMutation_apply_of_apply_col_eq_zero hrow hkl j
  have ck (i : I) : matrixMutation row B l i k = B i k :=
    matrixMutation_apply_of_apply_row_eq_zero h hlk i
  have rl (j : K) : matrixMutation row B k (row l) j = B (row l) j :=
    matrixMutation_apply_of_apply_col_eq_zero (Ne.symm hrow) hlk j
  have cl (i : I) : matrixMutation row B k i l = B i l :=
    matrixMutation_apply_of_apply_row_eq_zero (Ne.symm h) hkl i
  ext i j
  conv_lhs => rw [matrixMutation_apply]
  conv_rhs => rw [matrixMutation_apply]
  simp only [rk, ck, rl, cl]
  by_cases hik : i = row k
  · subst i
    by_cases hj : j = l <;> simp [matrixMutation_apply, hrow, hkl, hj]
  by_cases hil : i = row l
  · subst i
    by_cases hj : j = k <;> simp [matrixMutation_apply, Ne.symm hrow, hlk, hj]
  by_cases hjk : j = k
  · subst j
    simp [matrixMutation_apply, h, hik, hil, hlk]
  by_cases hjl : j = l
  · subst j
    simp [matrixMutation_apply, Ne.symm h, hik, hil, hkl]
  simp only [hik, hil, hjk, hjl, false_or, ite_false]
  rw [matrixMutation_apply_of_ne hik hjk, matrixMutation_apply_of_ne hil hjl]
  ring

namespace ExchangeMatrix

/-- Mutations at nonadjacent mutable indices commute. A single zero entry suffices because
the principal block is skew-symmetrizable. -/
theorem mutation_mutation_comm {row : K ↪ I} (B : ExchangeMatrix row) (k l : K)
    (hkl : B.matrix (row k) l = 0) : (B.mutation k).mutation l = (B.mutation l).mutation k := by
  ext : 1
  · simp only [mutation_matrix]
    exact matrixMutation_matrixMutation_comm row B.matrix k l hkl
      ((B.isSkewSymmetrizer.apply_eq_zero_iff).mp hkl)
  · simp

end ExchangeMatrix

end TauCeti
