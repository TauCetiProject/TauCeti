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
`abv A.det ≤ ∏ i, ∑ j, abv (A i j)`, and the same holds with columns in place of rows. When `abv`
is nonarchimedean (`IsNonarchimedean abv`), the ultrametric inequality on the Leibniz sum replaces
the `ℓ¹` sum by an entrywise row or column bound: if `abv (A i j) ≤ b i` (or `b j`), then
`abv A.det ≤ ∏ i, b i` (or `∏ j, b j`).

The proof is the Leibniz expansion. Each permutation contributes one product
`∏ i, abv (A i (σ i))`, and expanding the product of the row sums gives the sum of
`∏ i, abv (A i (f i))` over *all* maps `f`, of which the permutations are a part. In the
nonarchimedean case, `IsNonarchimedean.finset_image_add_of_nonempty` bounds `abv A.det` by a single
permutation term instead of the sum. These bounds complement Mathlib's `Matrix.det_le`, which
bounds the determinant by `n! · x ^ n` from a uniform entrywise bound `x`; the `ℓ¹` form is sharper
when the rows have very different sizes, as for the logarithmic embeddings of a family of units in
the bound on the regulator.

## Main results

* `Matrix.abv_det_le_prod_sum_abv`: `abv A.det ≤ ∏ i, ∑ j, abv (A i j)`, the row form.
* `Matrix.abv_det_le_prod_sum_abv'`: `abv A.det ≤ ∏ j, ∑ i, abv (A i j)`, the column form.
* `Matrix.abs_det_le_prod_sum_abs` and `Matrix.abs_det_le_prod_sum_abs'`: the same bounds for
  `|·|` over a linearly ordered commutative ring.
* `Matrix.abv_det_le_prod_of_le` and `Matrix.abv_det_le_prod_of_le'`: for nonarchimedean `abv`,
  entrywise row bounds `b i` or column bounds `b j` give `abv A.det ≤ ∏ i, b i` and
  `abv A.det ≤ ∏ j, b j`.
-/

public section

open Equiv Finset

namespace Matrix

variable {R S : Type*} [CommRing R] [CommRing S] [LinearOrder S] [IsStrictOrderedRing S]
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Hadamard's bound, `ℓ¹` column form.** The absolute value of a determinant is at most the
product of the `ℓ¹` norms of the columns. -/
theorem abv_det_le_prod_sum_abv' (A : Matrix n n R) (abv : AbsoluteValue R S) :
    abv A.det ≤ ∏ j, ∑ i, abv (A i j) := by
  classical
  rcases subsingleton_or_nontrivial R with hR | hR
  · rw [Subsingleton.elim A.det 0, map_zero]
    exact prod_nonneg fun _ _ => sum_nonneg fun _ _ => abv.nonneg _
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
    exact prod_nonneg fun j _ => (abv.nonneg _).trans (hA j j)
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

end Matrix
