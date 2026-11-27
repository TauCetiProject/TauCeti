/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Cluster.ExchangeMatrix.Factorization
public import TauCeti.Algebra.Cluster.ExchangeMatrix.Divisibility
public import Mathlib.Data.Int.Cast.Field
public import Mathlib.LinearAlgebra.LinearIndependent.Basic

/-!
# Column rank and independence along mutation words

For finite ambient row types, mutation words preserve the rank and column independence of extended
exchange matrices, including rectangular matrices with singular principal blocks. The chosen
symmetrizer supplies the zero mutable diagonal needed by the one-step factorization.
We iterate `rank_matrixMutation` and `linearIndependent_col_matrixMutation_iff`; the literature
references for these one-step results are in `ExchangeMatrix.Factorization`.

For polynomial exchange columns, exact division by column degrees is nonzero scalar rescaling.
The theorem `dvd_matrixMutationWord_iff` propagates divisibility along the word, so the divided
columns retain independence over any field where the degrees remain nonzero.
-/

public noncomputable section

namespace TauCeti.ExchangeMatrix

variable {I K : Type*} [DecidableEq I] [DecidableEq K] [Finite I]
    {row : K ↪ I} (B : ExchangeMatrix row)

/-- A finite mutation word preserves column rank after scalar change to any commutative ring. -/
@[simp]
theorem rank_matrixMutationWord {R : Type*} [CommRing R] (w : List K) :
    ((matrixMutationWord row B.matrix w).map ((↑) : ℤ → R)).rank =
      (B.matrix.map ((↑) : ℤ → R)).rank := by
  induction w generalizing B with
  | nil => simp
  | cons k w ih =>
    rw [matrixMutationWord_cons, ← mutation_matrix, ih, mutation_matrix]
    exact rank_matrixMutation row B.matrix k (B.matrix_row_self k)

/-- Mutation words preserve column independence. No full-rank assumption is imposed on the
principal block, and the scalar ring is allowed to be trivial. -/
@[simp]
theorem linearIndependent_col_matrixMutationWord_iff {R : Type*} [CommRing R] (w : List K) :
    LinearIndependent R ((matrixMutationWord row B.matrix w).map ((↑) : ℤ → R)).col ↔
      LinearIndependent R (B.matrix.map ((↑) : ℤ → R)).col := by
  induction w generalizing B with
  | nil => simp
  | cons k w ih =>
    rw [matrixMutationWord_cons, ← mutation_matrix, ih, mutation_matrix]
    exact linearIndependent_col_matrixMutation_iff row B.matrix k (B.matrix_row_self k)

/-- Exact division of polynomial exchange columns preserves independence along every mutation
word, provided each degree remains nonzero in the scalar field. Each degree `r j` is assumed
to divide every entry of column `j` of the initial matrix. Negative degrees and positive
characteristic are allowed. -/
theorem linearIndependent_col_ediv_matrixMutationWord_iff {F : Type*} [Field F]
    (r : K → ℤ) (hr : ∀ j, (r j : F) ≠ 0) (hdiv : ∀ i j, r j ∣ B.matrix i j) (w : List K) :
    LinearIndependent F
        ((Matrix.of fun i j ↦ matrixMutationWord row B.matrix w i j / r j).map
          ((↑) : ℤ → F)).col ↔
      LinearIndependent F (B.matrix.map ((↑) : ℤ → F)).col := by
  have hd (i : I) (j : K) : r j ∣ matrixMutationWord row B.matrix w i j :=
    (dvd_matrixMutationWord_iff (row := row) (B := B.matrix) (d := r j) (j := j) w).mpr
      (fun a ↦ hdiv a j) i
  let u : K → Fˣ := fun j ↦ (Units.mk0 (r j : F) (hr j))⁻¹
  have hc :
      ((Matrix.of fun i j ↦ matrixMutationWord row B.matrix w i j / r j).map
        ((↑) : ℤ → F)).col =
        u • ((matrixMutationWord row B.matrix w).map ((↑) : ℤ → F)).col := by
    ext j i
    simp only [Matrix.col_apply, Matrix.map_apply, Matrix.of_apply, Pi.smul_apply', Pi.smul_apply,
      Units.smul_def, smul_eq_mul]
    rw [Int.cast_div (hd i j) (hr j)]
    simp [u, div_eq_mul_inv, mul_comm]
  rw [hc, LinearIndependent.units_smul_iff, linearIndependent_col_matrixMutationWord_iff]

end TauCeti.ExchangeMatrix
