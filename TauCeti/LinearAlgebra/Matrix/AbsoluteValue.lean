/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.AbsoluteValue.Int
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# The `ℓ¹` form of Hadamard's determinant bound

For a square matrix `A` and an absolute value `abv`, the absolute value of the determinant is at
most the product over the rows of the `ℓ¹` norms of the rows:
`abv A.det ≤ ∏ i, ∑ j, abv (A i j)`, and the same holds with columns in place of rows.

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
-/

public section

open Equiv Finset

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
