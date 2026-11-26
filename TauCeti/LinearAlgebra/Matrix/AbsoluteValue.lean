/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.AbsoluteValue.Int
public import Mathlib.Algebra.Order.Ring.IsNonarchimedean
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Order

/-!
# Entrywise absolute-value bounds for matrices

This file bounds the determinant, the entries of a product and the entries of the adjugate of a
matrix through entrywise bounds, starting with the `ℓ¹` and ultrametric forms of Hadamard's
determinant bound.

For a square matrix `A` and an absolute value `abv`, the absolute value of the determinant is at
most the product over the rows of the `ℓ¹` norms of the rows:
`abv A.det ≤ ∏ i, ∑ j, abv (A i j)`, and the same holds with columns in place of rows. When `abv`
is nonarchimedean (`IsNonarchimedean abv`), the ultrametric inequality on the Leibniz sum replaces
the `ℓ¹` sum by an entrywise row or column bound: if `abv (A i j) ≤ b i` (or `b j`), then
`abv A.det ≤ ∏ i, b i` (or `∏ j, b j`). For an arbitrary absolute value, the same entrywise row
or column bounds give `abv A.det ≤ n! · ∏ i, b i`, one factor for each of the `n!` permutations.

The proof is the Leibniz expansion. Each permutation contributes one product
`∏ i, abv (A i (σ i))`, and expanding the product of the row sums gives the sum of
`∏ i, abv (A i (f i))` over *all* maps `f`, of which the permutations are a part. In the
nonarchimedean case, `IsNonarchimedean.finset_image_add_of_nonempty` bounds `abv A.det` by a single
permutation term instead of the sum. These bounds complement Mathlib's `Matrix.det_le`, which
bounds the determinant by `n! · x ^ n` from a uniform entrywise bound `x`; the factorial row form
keeps a separate bound for each row, and the `ℓ¹` form is sharper when the rows have very different
sizes, as for the logarithmic embeddings of a family of units in
the bound on the regulator.

Over a linearly ordered commutative ring, the same entrywise reasoning bounds `|·|` of the entries
of a matrix product by the inner dimension times the product of the entrywise bounds, and of the
entries of an adjugate, which are determinants, through the factorial bound. Every finite matrix
is bounded entrywise, so multiplying a family of matrices by fixed factors on both sides keeps it
bounded entrywise.

## Main results

* `Matrix.abv_det_le_prod_sum_abv`: `abv A.det ≤ ∏ i, ∑ j, abv (A i j)`, the row form.
* `Matrix.abv_det_le_prod_sum_abv'`: `abv A.det ≤ ∏ j, ∑ i, abv (A i j)`, the column form.
* `Matrix.abs_det_le_prod_sum_abs` and `Matrix.abs_det_le_prod_sum_abs'`: the same bounds for
  `|·|` over a linearly ordered commutative ring.
* `Matrix.abv_det_le_prod_of_le` and `Matrix.abv_det_le_prod_of_le'`: for nonarchimedean `abv`,
  entrywise row bounds `b i` or column bounds `b j` give `abv A.det ≤ ∏ i, b i` and
  `abv A.det ≤ ∏ j, b j`.
* `Matrix.abv_det_le_one_of_isNonarchimedean`, `Matrix.abv_det_eq_one_of_mul_eq_one`: unit-ball
  determinant specializations for a nonarchimedean absolute value.
* `Matrix.abv_det_le_factorial_mul_of_forall_perm`: a bound on each permutation product gives
  the same bound on the determinant, multiplied by the factorial of the matrix size.
* `Matrix.abv_det_le_factorial_prod` and `Matrix.abv_det_le_factorial_prod'`: for any absolute
  value, entrywise row bounds `b i` or column bounds `b j` give
  `abv A.det ≤ n! · ∏ i, b i` and `abv A.det ≤ n! · ∏ j, b j`.
* `Matrix.abs_mul_apply_le`, `Matrix.abs_pow_apply_le`, and `Matrix.abs_adjugate_apply_le`:
  entrywise bounds on `|·|` for a product of two matrices, powers of a square matrix, and the
  adjugate of a square matrix.
* `Matrix.exists_abs_apply_le` and `Matrix.exists_abs_mul_mul_apply_le`: a finite matrix is
  bounded entrywise, and fixed factors on both sides preserve the entrywise boundedness of a
  family of matrices.
-/

public section

open Equiv Finset

namespace Matrix

variable {R S : Type*} [CommRing R]
  [CommRing S] [LinearOrder S] [IsStrictOrderedRing S]
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Hadamard's bound, `ℓ¹` column form.** The absolute value of a determinant is at most the
product of the `ℓ¹` norms of the columns. -/
theorem abv_det_le_prod_sum_abv' (A : Matrix n n R) (abv : AbsoluteValue R S) :
    abv A.det ≤ ∏ j, ∑ i, abv (A i j) := by
  classical
  rcases subsingleton_or_nontrivial R with hR | hR
  · rw [Subsingleton.elim A.det 0, map_zero]
    exact prod_nonneg fun _ _ ↦ sum_nonneg fun _ _ ↦ abv.nonneg _
  calc
    abv A.det ≤ ∑ σ : Perm n, abv (Perm.sign σ • ∏ i, A (σ i) i) := by
      rw [det_apply]
      exact abv.sum_le _ _
    _ = ∑ σ : Perm n, ∏ i, abv (A (σ i) i) :=
      sum_congr rfl fun σ _ => by rw [abv.map_units_int_smul, abv.map_prod]
    _ ≤ ∑ f : n → n, ∏ i, abv (A (f i) i) :=
      sum_le_sum_of_injOn (⇑) (DFunLike.coe_injective.injOn) (subset_univ _)
        (fun _ _ => le_rfl) fun _ _ _ => prod_nonneg fun _ _ => abv.nonneg _
    _ = ∏ j, ∑ i, abv (A i j) := (Fintype.prod_sum fun j i => abv (A i j)).symm

/-- **Hadamard's bound, `ℓ¹` row form.** The absolute value of a determinant is at most the
product of the `ℓ¹` norms of the rows. -/
theorem abv_det_le_prod_sum_abv (A : Matrix n n R) (abv : AbsoluteValue R S) :
    abv A.det ≤ ∏ i, ∑ j, abv (A i j) := by
  simpa only [det_transpose, transpose_apply] using abv_det_le_prod_sum_abv' Aᵀ abv

/-- **Hadamard's bound, `ℓ¹` column form, for `|·|`.** Over a linearly ordered commutative ring,
`|det A|` is at most the product of the `ℓ¹` norms of the columns of `A`. -/
theorem abs_det_le_prod_sum_abs' (A : Matrix n n S) : |A.det| ≤ ∏ j, ∑ i, |A i j| :=
  abv_det_le_prod_sum_abv' A AbsoluteValue.abs

/-- **Hadamard's bound, `ℓ¹` row form, for `|·|`.** Over a linearly ordered commutative ring,
`|det A|` is at most the product of the `ℓ¹` norms of the rows of `A`. -/
theorem abs_det_le_prod_sum_abs (A : Matrix n n S) : |A.det| ≤ ∏ i, ∑ j, |A i j| :=
  abv_det_le_prod_sum_abv A AbsoluteValue.abs

/-- **Ultrametric Hadamard bound, column form.** For a nonarchimedean absolute value `abv`, if
column `j` of `A` is bounded entrywise in `abv` by `b j`, then `abv A.det ≤ ∏ j, b j`. -/
theorem abv_det_le_prod_of_le' (A : Matrix n n R) {abv : AbsoluteValue R S}
    (habv : IsNonarchimedean abv) {b : n → S} (hA : ∀ i j, abv (A i j) ≤ b j) :
    abv A.det ≤ ∏ j, b j := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · rw [Subsingleton.elim A.det 0, map_zero]
    rcases isEmpty_or_nonempty n with hn | ⟨⟨i₀⟩⟩
    · simp
    · exact prod_nonneg fun j _ ↦ (abv.nonneg (A i₀ j)).trans (hA i₀ j)
  rw [det_apply]
  obtain ⟨σ, -, hσ⟩ := habv.finset_image_add_of_nonempty _ (univ_nonempty (α := Perm n))
  refine hσ.trans ?_
  rw [abv.map_units_int_smul, abv.map_prod]
  gcongr with j
  exact hA (σ j) j

/-- **Ultrametric Hadamard bound, row form.** For a nonarchimedean absolute value `abv`, if row `i`
of `A` is bounded entrywise in `abv` by `b i`, then `abv A.det ≤ ∏ i, b i`. -/
theorem abv_det_le_prod_of_le (A : Matrix n n R) {abv : AbsoluteValue R S}
    (habv : IsNonarchimedean abv) {b : n → S} (hA : ∀ i j, abv (A i j) ≤ b i) :
    abv A.det ≤ ∏ i, b i := by
  simpa only [det_transpose, transpose_apply] using
    abv_det_le_prod_of_le' Aᵀ habv fun i j => hA j i

/-- A square matrix with entries in the nonarchimedean unit ball has determinant in the unit
ball. -/
theorem abv_det_le_one_of_isNonarchimedean {A : Matrix n n R} {abv : AbsoluteValue R S}
    (habv : IsNonarchimedean abv) (hA : ∀ i j, abv (A i j) ≤ 1) :
    abv A.det ≤ 1 :=
  (A.abv_det_le_prod_of_le' habv hA).trans_eq prod_const_one

/-- If `A * B = 1` and both `A` and `B` have entries in the nonarchimedean unit ball, then
`abv A.det = 1`. -/
theorem abv_det_eq_one_of_mul_eq_one [Nontrivial R] {A B : Matrix n n R} {abv : AbsoluteValue R S}
    (habv : IsNonarchimedean abv) (hAB : A * B = 1) (hA : ∀ i j, abv (A i j) ≤ 1)
    (hB : ∀ i j, abv (B i j) ≤ 1) :
    abv A.det = 1 := by
  refine le_antisymm (A.abv_det_le_one_of_isNonarchimedean habv hA) ?_
  have hmul : abv A.det * abv B.det = 1 := by
    rw [← map_mul, ← det_mul, hAB, det_one, map_one]
  calc (1 : S) = abv A.det * abv B.det := hmul.symm
    _ ≤ abv A.det * 1 :=
      mul_le_mul_of_nonneg_left (B.abv_det_le_one_of_isNonarchimedean habv hB) (abv.nonneg _)
    _ = abv A.det := mul_one _

/-- A uniform bound on the absolute values of all permutation products bounds the determinant
by the same bound times the factorial of the matrix size. Unlike an entrywise bound, this can
retain correlations between the factors in each permutation product. -/
theorem abv_det_le_factorial_mul_of_forall_perm (A : Matrix n n R) (abv : AbsoluteValue R S)
    {B : S} (hA : ∀ σ : Perm n, ∏ i, abv (A (σ i) i) ≤ B) :
    abv A.det ≤ (Fintype.card n).factorial * B := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · rw [Subsingleton.elim A.det 0, map_zero]
    exact mul_nonneg (Nat.cast_nonneg _)
      ((prod_nonneg fun _ _ ↦ abv.nonneg _).trans (hA 1))
  calc
    abv A.det ≤ ∑ σ : Perm n, abv (Perm.sign σ • ∏ i, A (σ i) i) := by
      rw [det_apply]
      exact abv.sum_le _ _
    _ = ∑ σ : Perm n, ∏ i, abv (A (σ i) i) :=
      sum_congr rfl fun σ _ ↦ by rw [abv.map_units_int_smul, abv.map_prod]
    _ ≤ ∑ _σ : Perm n, B := sum_le_sum fun σ _ ↦ hA σ
    _ = (Fintype.card n).factorial * B := by simp [Fintype.card_perm]

/-- **Factorial determinant bound, column form.** If column `j` of `A` is bounded entrywise in
`abv` by `b j`, then `abv A.det ≤ n! · ∏ j, b j`, where `n` is the size of the matrix. This
refines Mathlib's uniform `Matrix.det_le` to column-dependent bounds. -/
theorem abv_det_le_factorial_prod' (A : Matrix n n R) (abv : AbsoluteValue R S) {b : n → S}
    (hA : ∀ i j, abv (A i j) ≤ b j) :
    abv A.det ≤ (Fintype.card n).factorial * ∏ j, b j :=
  abv_det_le_factorial_mul_of_forall_perm A abv fun σ ↦ by gcongr with j; exact hA (σ j) j

/-- **Factorial determinant bound, row form.** If row `i` of `A` is bounded entrywise in `abv` by
`b i`, then `abv A.det ≤ n! · ∏ i, b i`, where `n` is the size of the matrix. This refines
Mathlib's uniform `Matrix.det_le` to row-dependent bounds. -/
theorem abv_det_le_factorial_prod (A : Matrix n n R) (abv : AbsoluteValue R S) {b : n → S}
    (hA : ∀ i j, abv (A i j) ≤ b i) :
    abv A.det ≤ (Fintype.card n).factorial * ∏ i, b i := by
  simpa only [det_transpose, transpose_apply] using
    abv_det_le_factorial_prod' Aᵀ abv fun i j ↦ hA j i

/-- Entrywise bounds `|A i k| ≤ C` and `|B k j| ≤ D` bound every entry of `A * B` by `m · C · D`,
where `m` is the number of columns of `A`. -/
theorem abs_mul_apply_le {l m o : Type*} [Fintype m] {A : Matrix l m S} {B : Matrix m o S}
    {C D : S} (hA : ∀ i k, |A i k| ≤ C) (hB : ∀ k j, |B k j| ≤ D) (i : l) (j : o) :
    |(A * B) i j| ≤ Fintype.card m * (C * D) := by
  rw [Matrix.mul_apply]
  calc |∑ k, A i k * B k j| ≤ ∑ k, |A i k * B k j| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : m, C * D := sum_le_sum fun k _ ↦ by
        rw [abs_mul]
        exact mul_le_mul (hA i k) (hB k j) (abs_nonneg _) ((abs_nonneg _).trans (hA i k))
    _ = Fintype.card m * (C * D) := by simp

/-- A matrix with finitely many rows and columns is bounded entrywise in absolute value. -/
theorem exists_abs_apply_le {l m : Type*} [Finite l] [Finite m] (A : Matrix l m S) :
    ∃ C, ∀ i j, |A i j| ≤ C := by
  obtain ⟨C, hC⟩ := Finite.exists_le fun p : l × m ↦ |A p.1 p.2|
  exact ⟨C, fun i j ↦ hC (i, j)⟩

/-- Multiplying by fixed matrices on both sides preserves the entrywise boundedness in absolute
value of a family of matrices. -/
theorem exists_abs_mul_mul_apply_le {ι l m o p : Type*} [Finite l] [Fintype m] [Fintype o]
    [Finite p] {F : ι → Matrix m o S} (P : Matrix l m S) (Q : Matrix o p S)
    (hF : ∃ C, ∀ x i j, |F x i j| ≤ C) : ∃ C, ∀ x i j, |(P * F x * Q) i j| ≤ C := by
  obtain ⟨C, hC⟩ := hF
  obtain ⟨c, hc⟩ := exists_abs_apply_le P
  obtain ⟨d, hd⟩ := exists_abs_apply_le Q
  exact ⟨_, fun x ↦ abs_mul_apply_le (abs_mul_apply_le hc (hC x)) hd⟩

/-- An entrywise bound `|A i j| ≤ C` bounds every entry of the adjugate of `A` by
`n! · (max C 1) ^ n`, where `n` is the size of the matrix: each entry of the adjugate is the
determinant of `A` with one row replaced by a standard basis vector. -/
theorem abs_adjugate_apply_le {A : Matrix n n S} {C : S} (hA : ∀ i j, |A i j| ≤ C) (i j : n) :
    |adjugate A i j| ≤ (Fintype.card n).factorial * max C 1 ^ Fintype.card n := by
  rw [adjugate_apply]
  calc _ ≤ (Fintype.card n).factorial * ∏ _k : n, max C 1 :=
        abv_det_le_factorial_prod _ AbsoluteValue.abs fun k l ↦ ?_
    _ = _ := by rw [prod_const, card_univ]
  rw [AbsoluteValue.abs_apply, updateRow_apply]
  split_ifs
  · rw [Pi.single_apply]
    split_ifs <;> simp
  · exact (hA k l).trans (le_max_left _ _)

/-- Entrywise bound on matrix powers over a linearly ordered ring: if `|X i j| ≤ B` for all
entries (`0 ≤ B`), then `|(X ^ k) i j| ≤ (Fintype.card m * B) ^ k`. -/
theorem abs_pow_apply_le {m T : Type*} [Fintype m] [DecidableEq m] [Ring T] [LinearOrder T]
    [IsStrictOrderedRing T] {X : Matrix m m T} {B : T} (hB : 0 ≤ B) (hX : ∀ i j, |X i j| ≤ B)
    (k : ℕ) (i j : m) :
    |(X ^ k) i j| ≤ ((Fintype.card m : T) * B) ^ k := by
  induction k generalizing i j with
  | zero =>
    rw [pow_zero, pow_zero, Matrix.one_apply]
    split_ifs <;> simp
  | succ k ih =>
    rw [pow_succ, Matrix.mul_apply]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ l : m, |(X ^ k) i l * X l j|
        ≤ ∑ _l : m, ((Fintype.card m : T) * B) ^ k * B := sum_le_sum fun l _ ↦ by
          rw [abs_mul]
          exact mul_le_mul (ih i l) (hX l j) (abs_nonneg _)
            (pow_nonneg (mul_nonneg (Nat.cast_nonneg _) hB) k)
      _ = ((Fintype.card m : T) * B) ^ (k + 1) := by
          simp only [sum_const, card_univ, nsmul_eq_mul, ← mul_assoc]
          rw [Nat.cast_comm (Fintype.card m), mul_assoc, ← pow_succ]

end Matrix
