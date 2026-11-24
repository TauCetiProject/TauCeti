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

Finite words preserve the rank and column independence of extended exchange matrices, including
rectangular matrices with singular principal blocks. The chosen symmetrizer supplies the zero
mutable diagonal needed by the one-step factorization; no full-rank premise is used.

For polynomial exchange columns, exact division by column degrees is nonzero scalar rescaling.
Column divisibility persists along the word, so the divided columns retain independence over
any field where the degrees remain nonzero. Positivity and characteristic zero are unnecessary.
-/

public noncomputable section

namespace TauCeti.ExchangeMatrix

variable {I K : Type*} [DecidableEq I] [DecidableEq K] [Finite I]
    {row : K ↪ I} (B : ExchangeMatrix row)

/-- A finite mutation word preserves column rank after scalar change to any commutative ring. -/
theorem rank_mutationWord {R : Type*} [CommRing R] (w : List K) :
    ((B.mutationWord w).matrix.map (Int.castRingHom R)).rank =
      (B.matrix.map (Int.castRingHom R)).rank := by
  induction w generalizing B with
  | nil => simp
  | cons k w ih =>
    rw [mutationWord_cons, ih, mutation_matrix]
    exact rank_matrixMutation row B.matrix k (B.matrix_row_self k)

/-- Mutation words preserve column independence. No full-rank assumption is imposed on the
principal block, and the scalar ring is allowed to be trivial. -/
theorem linearIndependent_col_mutationWord_iff {R : Type*} [CommRing R] (w : List K) :
    LinearIndependent R ((B.mutationWord w).matrix.map (Int.castRingHom R)).col ↔
      LinearIndependent R (B.matrix.map (Int.castRingHom R)).col := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · let := hR
    have h : ((B.mutationWord w).matrix.map (Int.castRingHom R)).col =
        (B.matrix.map (Int.castRingHom R)).col := by
      ext j i
      exact Subsingleton.elim _ _
    rw [h]
  · let := hR
    have : Finite K := Finite.of_injective row row.injective
    let := Fintype.ofFinite K
    rw [linearIndependent_iff_card_eq_finrank_span, linearIndependent_iff_card_eq_finrank_span]
    exact Iff.of_eq (congrArg (Fintype.card K = ·) (B.rank_mutationWord (R := R) w))

/-- Exact division of polynomial exchange columns preserves independence along every mutation
word, provided each degree remains nonzero in the scalar field. Negative degrees and positive
characteristic are allowed; divisibility is required only of the initial integral columns. -/
theorem linearIndependent_col_ediv_mutationWord_iff {F : Type*} [Field F]
    (r : K → ℤ) (hr : ∀ j, (r j : F) ≠ 0) (hdiv : ∀ i j, r j ∣ B.matrix i j) (w : List K) :
    LinearIndependent F
        ((Matrix.of fun i j ↦ (B.mutationWord w).matrix i j / r j).map (Int.castRingHom F)).col ↔
      LinearIndependent F (B.matrix.map (Int.castRingHom F)).col := by
  have hd (i : I) (j : K) : r j ∣ (B.mutationWord w).matrix i j := by
    rw [mutationWord_matrix]
    exact (dvd_matrixMutationWord_iff (row := row) (B := B.matrix) (d := r j) (j := j) w).mpr
      (fun a ↦ hdiv a j) i
  let u : K → Fˣ := fun j ↦ (Units.mk0 (r j : F) (hr j))⁻¹
  have hc :
      ((Matrix.of fun i j ↦ (B.mutationWord w).matrix i j / r j).map (Int.castRingHom F)).col =
        u • ((B.mutationWord w).matrix.map (Int.castRingHom F)).col := by
    ext j i
    simp only [Matrix.col_apply, Matrix.map_apply, Matrix.of_apply, Pi.smul_apply', Pi.smul_apply,
      Units.smul_def, smul_eq_mul, Int.coe_castRingHom]
    rw [Int.cast_div (hd i j) (hr j)]
    simp [u, div_eq_mul_inv, mul_comm]
  rw [hc, LinearIndependent.units_smul_iff, linearIndependent_col_mutationWord_iff]

end TauCeti.ExchangeMatrix
