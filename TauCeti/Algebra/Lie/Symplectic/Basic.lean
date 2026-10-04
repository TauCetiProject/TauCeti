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

end LieAlgebra.Symplectic
