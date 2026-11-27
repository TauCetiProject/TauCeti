/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Basic
public import TauCeti.RingTheory.Nilpotent.Exp.CubeZero

/-!
# Matrix exponentials with vanishing cube preserving a bilinear form

Let `N` be a square matrix over a commutative ring `A` with `N³ = 0`, and `h : A` with `2h = 1`.
If `N` is antisymmetric for the bilinear form with Gram matrix `J`, in the sense that
`J Nᵀ = -(N J)`, then the truncated exponential `exp(a N) = 1 + a N + h a² N²` preserves `J`:
`exp(a N) J exp(a N)ᵀ = J` (`Matrix.one_add_smul_add_smul_mul_self_mul_mul_transpose`). Its
additivity is `TauCeti.one_add_smul_add_smul_mul_self_add`.
-/

public section

namespace Matrix

variable {n A : Type*} [Fintype n] [DecidableEq n] [CommRing A]

/-- **The exponential of an antisymmetric matrix with vanishing cube preserves the form**: if
`N³ = 0` and `J Nᵀ = -(N J)`, then `exp(a N) = 1 + a N + h a² N²` satisfies
`exp(a N) J exp(a N)ᵀ = J` when `2h = 1`. -/
theorem one_add_smul_add_smul_mul_self_mul_mul_transpose {N : Matrix n n A}
    (J : Matrix n n A) {h : A} (hh : 2 * h = 1) (h3 : N * N * N = 0) (hJ : J * Nᵀ = -(N * J))
    (a : A) :
    (1 + a • N + (h * a * a) • (N * N)) * J * (1 + a • N + (h * a * a) • (N * N))ᵀ = J := by
  have hJ2 : J * (Nᵀ * Nᵀ) = N * N * J := by
    rw [← Matrix.mul_assoc, hJ, Matrix.neg_mul, Matrix.mul_assoc, hJ,
      Matrix.mul_neg, neg_neg, Matrix.mul_assoc]
  have hJM : J * (1 + a • N + (h * a * a) • (N * N))ᵀ =
      (1 + (-a) • N + (h * (-a) * (-a)) • (N * N)) * J := by
    simp [Matrix.mul_add, add_mul, hJ, hJ2]
  rw [Matrix.mul_assoc, hJM, ← Matrix.mul_assoc,
    ← TauCeti.one_add_smul_add_smul_mul_self_add hh h3, add_neg_cancel]
  simp

end Matrix
