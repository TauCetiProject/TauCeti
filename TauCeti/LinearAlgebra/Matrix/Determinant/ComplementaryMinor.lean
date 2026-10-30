/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Jacobi's complementary-minor identity in block form

Let `M` and `N` be square matrices over a commutative ring, indexed by `m ⊕ n`, with `M * N = 1`.
Then the top-left block of `M` and the bottom-right block of `N` have related determinants:

`det M * det N₂₂ = det M₁₁`.

Indeed `M * [1, N₁₂; 0, N₂₂] = [M₁₁, 0; M₂₁, 1]`, because the second block column of `M * N = 1`
is `[0; 1]`, and the two sides are block triangular.  Up to reordering rows and columns, which
introduces a sign, this is Jacobi's theorem that every minor of an invertible matrix is `det M`
times the complementary minor of `M⁻¹`.  It turns a determinant of one block of a matrix into a
determinant of the complementary block of its inverse; for example, the Jacobi--Trudi determinant
in complete homogeneous symmetric polynomials becomes its dual in elementary symmetric
polynomials.

## Main results

* `Matrix.det_mul_det_toBlocks₂₂_of_mul_eq_one`: if `M * N = 1`, then
  `det M * det N₂₂ = det M₁₁`.

## References

* [I. G. Macdonald, *Symmetric Functions and Hall Polynomials*][macdonald1995], Chapter I,
  Section 2, the proof of (2.9).
-/

public section

namespace Matrix

variable {m n R : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]

/-- **Jacobi's complementary-minor identity, block form.**  If `M * N = 1` for square matrices
indexed by `m ⊕ n`, then `det M` times the determinant of the bottom-right block of `N` is the
determinant of the top-left block of `M`. -/
theorem det_mul_det_toBlocks₂₂_of_mul_eq_one {M N : Matrix (m ⊕ n) (m ⊕ n) R} (h : M * N = 1) :
    M.det * N.toBlocks₂₂.det = M.toBlocks₁₁.det := by
  -- The second block column of `M * N = 1` reads `M₁₁ N₁₂ + M₁₂ N₂₂ = 0`, `M₂₁ N₁₂ + M₂₂ N₂₂ = 1`.
  have hblocks := h
  rw [← fromBlocks_toBlocks M, ← fromBlocks_toBlocks N, fromBlocks_multiply, ← fromBlocks_one,
    fromBlocks_inj] at hblocks
  obtain ⟨-, h₁₂, -, h₂₂⟩ := hblocks
  have key :
      M * fromBlocks 1 N.toBlocks₁₂ 0 N.toBlocks₂₂ = fromBlocks M.toBlocks₁₁ 0 M.toBlocks₂₁ 1 := by
    conv_lhs => rw [← fromBlocks_toBlocks M]
    rw [fromBlocks_multiply, h₁₂, h₂₂]
    simp
  simpa only [det_mul, det_fromBlocks_zero₂₁, det_fromBlocks_zero₁₂, det_one, one_mul, mul_one]
    using congrArg det key

end Matrix
