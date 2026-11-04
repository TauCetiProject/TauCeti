/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.AbsoluteValue.Int
public import Mathlib.Algebra.Order.Ring.IsNonarchimedean
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# The `ℓ¹` and ultrametric forms of Hadamard's determinant bound

For a square matrix `A` and an absolute value `abv`, the absolute value of the determinant is at
most the product over the rows of the `ℓ¹` norms of the rows:
`abv A.det ≤ ∏ i, ∑ j, abv (A i j)`, and the same holds with columns in place of rows. When `v` is
nonarchimedean, the ultrametric inequality replaces the column sums by uniform column bounds: if
`v (M i j) ≤ B j`, then `v M.det ≤ ∏ j, B j`.

The proof is the Leibniz expansion. Each permutation contributes one product
`∏ i, abv (A i (σ i))`, and expanding the product of the row sums gives the sum of
`∏ i, abv (A i (f i))` over *all* maps `f`, of which the permutations are a part. This bound
complements Mathlib's `Matrix.det_le`, which bounds the determinant by `n! · x ^ n` from a
uniform entrywise bound `x`; the `ℓ¹` form is sharper when the rows have very different sizes, as
for the logarithmic embeddings of a family of units in the bound on the regulator.

## Main results

* `Matrix.abv_det_le_prod_sum_abv`: `abv A.det ≤ ∏ i, ∑ j, abv (A i j)`, the row form.
* `Matrix.abv_det_le_prod_sum_abv'`: `abv A.det ≤ ∏ j, ∑ i, abv (A i j)`, the column form.
* `Matrix.abs_det_le_prod_sum_abs` and `Matrix.abs_det_le_prod_sum_abs'`: the same bounds for
  `|·|` over a linearly ordered commutative ring.
* `AbsoluteValue.det_le_prod`, `AbsoluteValue.det_le_one`,
  `AbsoluteValue.det_eq_one_of_mul_eq_one`: ultrametric determinant bounds for a nonarchimedean
  absolute value.
-/

public section

open Equiv Finset
open scoped Matrix

namespace Matrix

variable {R S : Type*} [CommRing R] [Nontrivial R]
  [CommRing S] [LinearOrder S] [IsStrictOrderedRing S]
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Hadamard's bound, `ℓ¹` column form.** The absolute value of a determinant is at most the
product of the `ℓ¹` norms of the columns. -/
theorem abv_det_le_prod_sum_abv' (A : Matrix n n R) (abv : AbsoluteValue R S) :
    abv A.det ≤ ∏ j, ∑ i, abv (A i j) := by
  classical
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

end Matrix

namespace AbsoluteValue

variable {R S n : Type*} [CommRing R] [CommRing S] [LinearOrder S] [IsStrictOrderedRing S]
  [Fintype n] [DecidableEq n]

/-- **Ultrametric Hadamard bound, column form.** If column `j` of a square matrix `M` is bounded by
`B j` with respect to a nonarchimedean absolute value `v`, then `v M.det ≤ ∏ j, B j`. -/
theorem det_le_prod (v : AbsoluteValue R S) (hv : IsNonarchimedean v) {M : Matrix n n R}
    {B : n → S} (hM : ∀ i j, v (M i j) ≤ B j) :
    v M.det ≤ ∏ j, B j := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · rw [Subsingleton.elim M.det 0, map_zero]
    rcases isEmpty_or_nonempty n with hn | ⟨⟨i₀⟩⟩
    · simp
    · exact prod_nonneg fun j _ ↦ (v.nonneg (M i₀ j)).trans (hM i₀ j)
  rw [Matrix.det_apply]
  refine (hv.apply_sum_le_sup ⟨1, mem_univ 1⟩).trans (sup'_le _ _ fun σ _ ↦ ?_)
  rw [v.map_units_int_smul, v.map_prod]
  exact prod_le_prod₀ (fun _ _ ↦ v.nonneg _) fun j _ ↦ hM (σ j) j

/-- A square matrix with entries in the nonarchimedean unit ball has determinant in the unit
ball. -/
theorem det_le_one (v : AbsoluteValue R S) (hv : IsNonarchimedean v) {M : Matrix n n R}
    (hM : ∀ i j, v (M i j) ≤ 1) :
    v M.det ≤ 1 :=
  (v.det_le_prod hv hM).trans_eq prod_const_one

/-- If `M * N = 1` and both `M` and `N` have entries in the nonarchimedean unit ball, then
`v M.det = 1`. -/
theorem det_eq_one_of_mul_eq_one [Nontrivial R] (v : AbsoluteValue R S) (hv : IsNonarchimedean v)
    {M N : Matrix n n R} (hMN : M * N = 1) (hM : ∀ i j, v (M i j) ≤ 1)
    (hN : ∀ i j, v (N i j) ≤ 1) :
    v M.det = 1 := by
  refine le_antisymm (v.det_le_one hv hM) ?_
  have hmul : v M.det * v N.det = 1 := by
    rw [← map_mul, ← Matrix.det_mul, hMN, Matrix.det_one, map_one]
  calc (1 : S) = v M.det * v N.det := hmul.symm
    _ ≤ v M.det * 1 := mul_le_mul_of_nonneg_left (v.det_le_one hv hN) (v.nonneg _)
    _ = v M.det := mul_one _

end AbsoluteValue
