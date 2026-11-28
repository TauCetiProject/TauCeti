/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Elementary
public import TauCeti.LinearAlgebra.Matrix.UnitaryGroup.Form

/-!
# Unitary groups of an orthogonal sum of forms

The orthogonal sum of sesquilinear forms with Gram matrices `A` (on `m`) and `D` (on `n`) is the
form on `m ⊕ n` with the block-diagonal Gram matrix `fromBlocks A 0 0 D`; for diagonal forms it is
the diagonal form of the concatenated entries (`Matrix.diagonal_comp_sumElim`). Congruence by a
block-diagonal matrix acts blockwise:
`diag(x, y)ᴴ * diag(A, D) * diag(x, y) = diag(xᴴ * A * x, yᴴ * D * y)`
(`Matrix.conjTranspose_fromBlocks_mul_fromBlocks_mul_fromBlocks`). Hence a block-diagonal invertible
matrix `diag(g, h)` preserves the sum of the forms exactly when `g` preserves the form of `A` and
`h` that of `D` (`Matrix.fromBlocksGL_mem_unitaryGroupOf_iff`).

For `A = 1` and `D = 1` this underlies the block-diagonal sum of unitary matrices
`Matrix.UnitaryGroup.sum`, and for `A = 1`, `D = -1` the embedding of `U(p) × U(q)` in `U(p, q)`
(`TauCeti.Matrix.indefiniteUnitaryGroup.fromBlocksHom`). Over a CM field it gives the
block-diagonal elements of the adelic unitary group of an orthogonal sum of hermitian spaces.

## Main results

* `Matrix.diagonal_comp_sumElim`: the diagonal matrix of concatenated entries is block diagonal.
* `Matrix.conjTranspose_fromBlocks_mul_fromBlocks_mul_fromBlocks`: congruence by a
  block-diagonal matrix is blockwise congruence.
* `Matrix.fromBlocksGL_mem_unitaryGroupOf_iff`: `diag(g, h)` preserves `diag(A, D)` exactly when
  `g` preserves `A` and `h` preserves `D`.
-/

public section

namespace Matrix

open TauCeti

variable {m n p q R : Type*}

/-- **Congruence by a block-diagonal matrix is blockwise congruence**:
`diag(x, y)ᴴ * diag(A, D) * diag(x, y) = diag(xᴴ * A * x, yᴴ * D * y)`, for rectangular blocks `x`
and `y`. -/
theorem conjTranspose_fromBlocks_mul_fromBlocks_mul_fromBlocks [Fintype m] [Fintype n]
    [NonUnitalNonAssocSemiring R] [StarAddMonoid R] (x : Matrix m p R) (y : Matrix n q R)
    (A : Matrix m m R) (D : Matrix n n R) :
    (fromBlocks x 0 0 y)ᴴ * fromBlocks A 0 0 D * fromBlocks x 0 0 y =
      fromBlocks (xᴴ * A * x) 0 0 (yᴴ * D * y) := by
  simp [fromBlocks_conjTranspose, fromBlocks_multiply]

/-- **The Gram matrix of an orthogonal sum of diagonal forms**: the diagonal matrix of a function of
concatenated entries is the block-diagonal matrix of the diagonal matrices of the two parts. -/
theorem diagonal_comp_sumElim [DecidableEq m] [DecidableEq n] [Zero R] {α : Type*} (f : α → R)
    (d₁ : m → α) (d₂ : n → α) :
    (diagonal fun i ↦ f (Sum.elim d₁ d₂ i)) =
      fromBlocks (diagonal fun i ↦ f (d₁ i)) 0 0 (diagonal fun i ↦ f (d₂ i)) := by
  rw [fromBlocks_diagonal]
  congr 1
  ext (i | i) <;> simp

variable [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] [Ring R] [StarRing R]
  {A : Matrix m m R} {D : Matrix n n R}

/-- **A block-diagonal matrix preserves an orthogonal sum of forms** exactly when its blocks
preserve the summands: `diag(g, h) ∈ U(diag(A, D))` if and only if `g ∈ U(A)` and `h ∈ U(D)`. -/
theorem fromBlocksGL_mem_unitaryGroupOf_iff {g : GL m R} {h : GL n R} :
    fromBlocksGL (g, h) ∈ unitaryGroupOf (fromBlocks A 0 0 D) ↔
      g ∈ unitaryGroupOf A ∧ h ∈ unitaryGroupOf D := by
  simp only [mem_unitaryGroupOf_iff, coe_fromBlocksGL, star_eq_conjTranspose,
    conjTranspose_fromBlocks_mul_fromBlocks_mul_fromBlocks, fromBlocks_inj, true_and]

end Matrix
