/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Cluster.ExchangeMatrix.Word

import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

/-!
# Column divisibility under matrix mutation

Polynomial exchange relations attach a positive degree to each mutable column, dividing every
entry of that column. This file proves that these divisibility conditions persist under mutation
and gives the exact mutation formula for the divided columns. The degree in the correction term
is the degree of the mutation direction, rather than that of the output column.

More generally, mutation preserves the common divisors of each individual column of any integer
matrix. In particular, a column is zero after mutation exactly when it was zero before mutation.
These assertions also hold along arbitrary finite mutation words. They require neither finite
index sets nor skew-symmetrizability, and apply to frozen rows as well as mutable rows.

## References

* Bai, Chen, Ding and Xu, *Generalized quantum cluster algebras: the Laurent
  phenomenon and upper bounds*, §2, for exchange degrees dividing integral columns.
* T. Nakanishi and D. Rupel, *Companion cluster algebras to a generalized cluster algebra*, §3,
  for degree-weighted matrix mutation.
-/

public section

namespace TauCeti

open Matrix

variable {I K : Type*} [DecidableEq I] [DecidableEq K]
  {row : K ↪ I} {B : Matrix I K ℤ} {d : ℤ} {j : K}

/-- Every common divisor of a column divides every entry of the same column after mutation.
The divisor can be zero or negative. -/
theorem dvd_matrixMutation (h : ∀ i, d ∣ B i j) (k : K) (i : I) :
    d ∣ matrixMutation row B k i j := by
  have hp : d ∣ (B (row k) j)⁺ := by
    rcases le_total (B (row k) j) 0 with hb | hb
    · simp [posPart_def, max_eq_right hb]
    · simpa [posPart_def, max_eq_left hb] using h (row k)
  have hn : d ∣ (B (row k) j)⁻ := by
    rcases le_total (B (row k) j) 0 with hb | hb
    · simpa [negPart_def, max_eq_left (neg_nonneg.mpr hb)] using (h (row k)).neg_right
    · simp [negPart_def, max_eq_right (neg_nonpos.mpr hb)]
  rw [matrixMutation_apply]
  split
  · exact (h i).neg_right
  · exact ((h i).add (hp.mul_left _)).sub (hn.mul_left _)

/-- Mutation preserves exactly the common divisors of each column. -/
@[simp]
theorem dvd_matrixMutation_iff (k : K) :
    (∀ i, d ∣ matrixMutation row B k i j) ↔ ∀ i, d ∣ B i j := by
  constructor
  · intro h i
    simpa using dvd_matrixMutation (row := row) h k i
  · exact fun h i ↦ dvd_matrixMutation h k i

/-- A column vanishes after mutation if and only if it vanished before mutation, including
when it is itself the mutation direction. -/
@[simp]
theorem matrixMutation_column_eq_zero_iff (k : K) :
    (∀ i, matrixMutation row B k i j = 0) ↔ ∀ i, B i j = 0 := by
  simpa using (dvd_matrixMutation_iff (row := row) (B := B) (d := 0) (j := j) k)

/-- Common column divisors are invariant along a finite word, evaluated in reading order. -/
@[simp]
theorem dvd_matrixMutationWord_iff (w : List K) :
    (∀ i, d ∣ matrixMutationWord row B w i j) ↔ ∀ i, d ∣ B i j := by
  induction w generalizing B with
  | nil => simp only [matrixMutationWord_nil]
  | cons k w ih => simp only [matrixMutationWord_cons, ih, dvd_matrixMutation_iff]

/-- The set of zero columns is invariant along every finite mutation word. -/
@[simp]
theorem matrixMutationWord_column_eq_zero_iff (w : List K) :
    (∀ i, matrixMutationWord row B w i j = 0) ↔ ∀ i, B i j = 0 := by
  simpa using (dvd_matrixMutationWord_iff (row := row) (B := B) (d := 0) (j := j) w)

/-- Exact mutation of divided columns. If each column `j` is divisible by its positive degree
`r j`, then the divided matrix mutates with the factor `r k` in direction `k`.

Integer division here is exact, by the column divisibility hypotheses and their preservation
under mutation. -/
theorem matrixMutation_ediv_apply (r : K → ℤ) (hr : ∀ j, 0 < r j)
    (h : ∀ i j, r j ∣ B i j) (k : K) (i : I) (j : K) :
    matrixMutation row B k i j / r j =
      if i = row k ∨ j = k then -(B i j / r j)
      else B i j / r j + r k * (B i k / r k)⁺ * (B (row k) j / r j)⁺ -
        r k * (B i k / r k)⁻ * (B (row k) j / r j)⁻ := by
  have hp (a : I) (b : K) : (B a b)⁺ = r b * (B a b / r b)⁺ := by
    simp only [posPart_def, mul_max_of_nonneg _ _ (hr b).le, mul_zero,
      Int.mul_ediv_cancel' (h a b)]
  have hn (a : I) (b : K) : (B a b)⁻ = r b * (B a b / r b)⁻ := by
    simp only [negPart_def, mul_max_of_nonneg _ _ (hr b).le, mul_zero,
      mul_neg, Int.mul_ediv_cancel' (h a b)]
  rw [matrixMutation_apply]
  split
  · exact Int.neg_ediv_of_dvd (h i j)
  · apply Int.ediv_eq_of_eq_mul_left (hr j).ne'
    rw [hp i k, hp (row k) j, hn i k, hn (row k) j]
    have hij := Int.ediv_mul_cancel (h i j)
    linear_combination -hij

/-! Unequal degrees `(3, 2)` and a frozen row give a nonzero correction, distinguishing the
mutation degree from the degree of the output column. -/

example :
    matrixMutation (Fin.castSuccEmb (n := 2)) (!![0, 2; -3, 0; 3, 0]) 0 =
      !![0, -2; 3, 0; -3, 6] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matrixMutation_apply]

example : ∀ i j, (![3, 2] : Fin 2 → ℤ) j ∣
    matrixMutation (Fin.castSuccEmb (n := 2)) (!![0, 2; -3, 0; 3, 0]) 0 i j := by
  intro i j
  apply dvd_matrixMutation (fun a ↦ ?_) 0 i
  fin_cases a <;> fin_cases j <;> decide

example :
    matrixMutation (Fin.castSuccEmb (n := 2)) (!![0, 2; -3, 0; 3, 0]) 0 2 1 / 2 = 3 := by
  simpa using (matrixMutation_ediv_apply (row := Fin.castSuccEmb (n := 2))
    (B := !![0, 2; -3, 0; 3, 0]) ![3, 2] (by decide)
    (by intro a b; fin_cases a <;> fin_cases b <;> decide) 0 2 1)

end TauCeti
