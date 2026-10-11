/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Classical
public import TauCeti.LinearAlgebra.SymplecticGroup
import Mathlib.Tactic.NoncommRing

/-!
# Membership in the symplectic Lie algebra

The symplectic Lie algebra `LieAlgebra.Symplectic.sp l R` is cut out by a condition relating a
matrix to its transpose through the canonical skew-symmetric matrix `Matrix.J l R`. This file
spells that condition out as `Aᵀ * J = -(J * A)`, the symplectic counterpart of Mathlib's
`LieAlgebra.Orthogonal.mem_so`, and rewrites it as a **conjugation by `J`**,
`Aᵀ = J * (-A) * J⁻¹`, which is the form the matrix exponential consumes.

Since `J * J = -1`, all of this is available over an arbitrary commutative ring with no
invertibility side conditions; `Matrix.eq_J_conj_iff_mul_J_eq` is the cancellation that moves a
matrix past `J`.

## Main results

* `LieAlgebra.Symplectic.mem_sp`: membership in the symplectic Lie algebra, spelled out as
  `Aᵀ * J = -(J * A)`.
* `LieAlgebra.Symplectic.mem_sp_iff_transpose_eq_J_conj_neg`: the same condition as a conjugation,
  `Aᵀ = J * (-A) * J⁻¹`.
* `LieAlgebra.Symplectic.mul_J_add_J_mul_transpose_eq_zero`: the additive form
  `A * J + J * Aᵀ = 0`.
* `Matrix.mem_symplecticLieAlgebra_iff`: the entrywise block criterion, with symmetric
  off-diagonal blocks and opposite transposed diagonal blocks.
-/

public section

open Matrix

namespace LieAlgebra.Symplectic

variable {l : Type*} [DecidableEq l] [Fintype l] {R : Type*} [CommRing R]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- **Membership in the symplectic Lie algebra**: `A` is skew-adjoint for the canonical
skew-symmetric form exactly when `Aᵀ * J = -(J * A)`. The symplectic counterpart of Mathlib's
`LieAlgebra.Orthogonal.mem_so`, whose `J = 1` makes the two multiplications disappear. -/
@[simp]
theorem mem_sp (A : Matrix (l ⊕ l) (l ⊕ l) R) :
    A ∈ sp l R ↔ Aᵀ * J l R = -(J l R * A) := by
  rw [sp, mem_skewAdjointMatricesLieSubalgebra, mem_skewAdjointMatricesSubmodule]
  simp only [Matrix.IsSkewAdjoint, Matrix.IsAdjointPair, mul_neg]

/-- **Membership in the symplectic Lie algebra, as a conjugation**: `Aᵀ = J * (-A) * J⁻¹`. This is
the shape `NormedSpace.exp` transports, by `Matrix.exp_conj`. -/
theorem mem_sp_iff_transpose_eq_J_conj_neg (A : Matrix (l ⊕ l) (l ⊕ l) R) :
    A ∈ sp l R ↔ Aᵀ = J l R * (-A) * (J l R)⁻¹ := by
  rw [mem_sp, Matrix.eq_J_conj_iff_mul_J_eq, mul_neg]

/-- **Membership in the symplectic Lie algebra, in additive form**: `A * J + J * Aᵀ = 0`. This is
the shape a congruence computation `X ↦ X * J * Xᵀ` differentiates to. -/
theorem mul_J_add_J_mul_transpose_eq_zero {A : Matrix (l ⊕ l) (l ⊕ l) R} (hA : A ∈ sp l R) :
    A * J l R + J l R * Aᵀ = 0 := by
  rw [(mem_sp_iff_transpose_eq_J_conj_neg A).mp hA, J_inv]
  calc A * J l R + J l R * (J l R * (-A) * (-J l R))
      = A * J l R + (J l R * J l R) * (-A) * (-J l R) := by noncomm_ring
    _ = 0 := by rw [J_squared]; noncomm_ring

/-- Membership in the symplectic Lie algebra is equivalent to the linearized
symplectic-group equation, also in characteristic two. -/
theorem mem_sp_iff_mul_J_add_J_mul_transpose_eq_zero (A : Matrix (l ⊕ l) (l ⊕ l) R) :
    A ∈ sp l R ↔ A * J l R + J l R * Aᵀ = 0 := by
  constructor
  · exact mul_J_add_J_mul_transpose_eq_zero
  · intro h
    rw [mem_sp_iff_transpose_eq_J_conj_neg, J_inv]
    have h' : J l R * A * J l R - Aᵀ = 0 := by
      simpa [mul_add, ← mul_assoc, J_squared, sub_eq_add_neg] using
        congrArg (fun X ↦ J l R * X) h
    rw [← sub_eq_zero.mp h']
    noncomm_ring

end LieAlgebra.Symplectic

namespace Matrix

variable {l : Type*} [DecidableEq l] [Fintype l] {R : Type*} [CommRing R]

/-- A symplectic Lie matrix has symmetric off-diagonal blocks and diagonal blocks
which are negatives of each other's transposes. This criterion includes characteristic two. -/
theorem mem_symplecticLieAlgebra_iff (A : Matrix (l ⊕ l) (l ⊕ l) R) :
    A ∈ LieAlgebra.Symplectic.sp l R ↔
      (∀ i j, A (.inl i) (.inr j) = A (.inl j) (.inr i)) ∧
      (∀ i j, A (.inr i) (.inl j) = A (.inr j) (.inl i)) ∧
      (∀ i j, A (.inr i) (.inr j) = -A (.inl j) (.inl i)) := by
  rw [← A.fromBlocks_toBlocks, LieAlgebra.Symplectic.mem_sp]
  simp only [J, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_neg,
    mul_zero, zero_mul, mul_one, one_mul, mul_neg, neg_mul, add_zero, zero_add,
    fromBlocks_inj, neg_inj, neg_neg]
  simp only [← Matrix.ext_iff, transpose_apply, toBlocks₁₁, toBlocks₁₂,
    toBlocks₂₁, toBlocks₂₂, neg_apply, Matrix.of_apply, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
    fromBlocks_apply₂₁, fromBlocks_apply₂₂]
  grind

end Matrix
