/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Dot products

A family of `n` linear forms on `K ^ n`, written as coefficient vectors `l i` so that the `i`-th
form sends `x` to `l i ⬝ᵥ x`, is linearly independent exactly when the square matrix with rows
`l i` is invertible. Its kernel is then trivial, so the forms cannot all vanish at a nonzero point.

Relabelling the indices of a square matrix `M` along `e : I ≃ J` is an isometry of the pairing
`(u, v) ↦ u ⬝ᵥ M *ᵥ v`.

When `A` scales `x` to a multiple of `x'` and `Aᵀ` scales `y'` to a multiple of `y`, the scalars
transform the dot products `x' ⬝ᵥ y'` and `x ⬝ᵥ y` into each other. For the character-lattice
matrix of a special isogeny acting on roots and coroots, this is the rule by which the Cartan
integers transform (R. Steinberg, *Endomorphisms of Linear Algebraic Groups*, §11).

## Main results

* `LinearIndependent.exists_dotProduct_ne_zero`: `n` linearly independent forms on `K ^ n` do not
  all vanish at a nonzero point.
* `Matrix.comp_equiv_symm_dotProduct_reindex_mulVec`: relabelling the indices is an isometry.
* `TauCeti.mul_dotProduct_eq_of_mulVec_eq_smul`: if `A *ᵥ x = a • x'` and `Aᵀ *ᵥ y' = b • y`,
  then `a * (x' ⬝ᵥ y') = b * (x ⬝ᵥ y)`.
-/

public section

open Matrix

/-- `n` linearly independent linear forms on `K ^ n` do not all vanish at a nonzero point. -/
theorem LinearIndependent.exists_dotProduct_ne_zero {K ι : Type*} [Field K] [Fintype ι]
    {l : ι → ι → K} (hl : LinearIndependent K l) {x : ι → K} (hx : x ≠ 0) :
    ∃ i, l i ⬝ᵥ x ≠ 0 := by
  classical
  have hinj : Function.Injective (Matrix.of l).mulVec := mulVec_injective_iff_isUnit.mpr <|
    (linearIndependent_row_iff_isUnit (A := Matrix.of l)).mp hl
  by_contra! h
  exact hx <| hinj <| by ext i; simpa [mulVec] using h i

/-- **Relabelling the vertices is an isometry**: for a relabelling `e : I ≃ J` of the indices of a
square matrix `M`, the vectors `u ∘ e.symm` and `v ∘ e.symm` pair under `M.reindex e e` as `u`
and `v` do under `M`. -/
theorem Matrix.comp_equiv_symm_dotProduct_reindex_mulVec {I J α : Type*} [Fintype I] [Fintype J]
    [NonUnitalNonAssocSemiring α] (e : I ≃ J) (M : Matrix I I α) (u v : I → α) :
    u ∘ e.symm ⬝ᵥ M.reindex e e *ᵥ (v ∘ e.symm) = u ⬝ᵥ M *ᵥ v := by
  simp [submatrix_mulVec_equiv, Function.comp_assoc]

/-- **Scaling by a matrix and by its transpose transforms the dot product.** If `A` sends `x` to
`a • x'` and `Aᵀ` sends `y'` to `b • y`, then `a * (x' ⬝ᵥ y') = b * (x ⬝ᵥ y)`. For the
character-lattice matrix of a special isogeny, with `x = α_i`, `x' = α_{σ i}`, `y' = α_{σ j}^∨`,
`y = α_j^∨`, `a = ℓ i` and `b = ℓ j`, this is the rule
`ℓ i ⟨α_{σ i}, α_{σ j}^∨⟩ = ℓ j ⟨α_i, α_j^∨⟩` by which the Cartan integers transform. -/
theorem TauCeti.mul_dotProduct_eq_of_mulVec_eq_smul {m n R : Type*} [Fintype m] [Fintype n]
    [NonUnitalCommSemiring R] {A : Matrix m n R} {x y : n → R} {x' y' : m → R} {a b : R}
    (hx : A *ᵥ x = a • x') (hy : Aᵀ *ᵥ y' = b • y) :
    a * (x' ⬝ᵥ y') = b * (x ⬝ᵥ y) := by
  have key := dotProduct_transpose_mulVec A x y'
  rwa [hx, hy, dotProduct_comm x, dotProduct_comm y', smul_dotProduct, smul_dotProduct,
    dotProduct_comm y, eq_comm] at key
