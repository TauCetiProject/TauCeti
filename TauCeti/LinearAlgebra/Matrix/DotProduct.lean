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

## Main results

* `LinearIndependent.exists_dotProduct_ne_zero`: `n` linearly independent forms on `K ^ n` do not
  all vanish at a nonzero point.
* `Matrix.comp_equiv_symm_dotProduct_reindex_mulVec`: relabelling the indices is an isometry.
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
