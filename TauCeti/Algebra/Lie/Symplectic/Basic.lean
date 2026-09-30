/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Classical

/-!
# The symplectic group and the symplectic Lie algebra, in conjugated form

Both the symplectic group `Matrix.symplecticGroup l R` and the symplectic Lie algebra
`LieAlgebra.Symplectic.sp l R` are cut out by a condition relating a matrix to its transpose
through the canonical skew-symmetric matrix `Matrix.J l R`. This file rewrites each of those
conditions as a **conjugation by `J`**, which is the form the matrix exponential consumes: the
exponential does not interact with `Aᵀ * J = J * (-A)`, but it does turn
`Aᵀ = J * (-A) * J⁻¹` into `(exp A)ᵀ = J * (exp A)⁻¹ * J⁻¹`.

The matrix `J` satisfies `J * J = -1`, so it is invertible with `J⁻¹ = -J` (Mathlib's
`Matrix.J_squared` and `Matrix.J_inv`); everything below is that identity applied twice, so the
whole file is stated over an arbitrary commutative ring and no invertibility side conditions
appear.

## Main results

* `Matrix.J_mul_neg_J`, `Matrix.neg_J_mul_J` and `Matrix.isUnit_J`: the canonical skew-symmetric
  matrix is a unit, with inverse `-J`.
* `LieAlgebra.Symplectic.mem_sp`: membership in the symplectic Lie algebra, spelled out as
  `Aᵀ * J = -(J * A)`. This is the symplectic counterpart of Mathlib's
  `LieAlgebra.Orthogonal.mem_so`.
* `LieAlgebra.Symplectic.mem_sp_iff_transpose_eq_conj`: the same condition as a conjugation,
  `Aᵀ = J * (-A) * J⁻¹`.
* `SymplecticGroup.transpose_eq_J_conj_inv`: the transpose of a symplectic matrix is the
  `J`-conjugate of its inverse, `Aᵀ = J * A⁻¹ * J⁻¹`.

## References

* [Lie groups and the Lie algebra correspondence roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieGroups/README.md),
  Deliverable A, Layer 2, "Consequences": the matrix groups are Lie groups, with their Lie
  algebras named explicitly.
-/

public section

open Matrix

namespace Matrix

variable (l : Type*) [DecidableEq l] [Fintype l] (R : Type*) [CommRing R]

/-- `J * (-J) = 1`: the companion of `Matrix.J_squared` in the form the conjugation arguments
below use. -/
theorem J_mul_neg_J : J l R * (-J l R) = 1 := by
  rw [mul_neg, J_squared, neg_neg]

/-- `(-J) * J = 1`, the other one-sided inverse identity for `Matrix.J`. -/
theorem neg_J_mul_J : (-J l R) * J l R = 1 := by
  rw [neg_mul, J_squared, neg_neg]

/-- The canonical skew-symmetric matrix is a unit, with inverse `-J`, because `J * J = -1`. -/
theorem isUnit_J : IsUnit (J l R) :=
  ⟨⟨J l R, -J l R, J_mul_neg_J l R, neg_J_mul_J l R⟩, rfl⟩

end Matrix

variable {l : Type*} [DecidableEq l] [Fintype l] {R : Type*} [CommRing R]

namespace SymplecticGroup

/-- **The transpose of a symplectic matrix is the `J`-conjugate of its inverse.** Mathlib's
`SymplecticGroup.inv_eq_symplectic_inv` computes the inverse as `-J * Aᵀ * J`; conjugating that
identity by `J` solves it for `Aᵀ` instead. -/
theorem transpose_eq_J_conj_inv {A : Matrix (l ⊕ l) (l ⊕ l) R}
    (hA : A ∈ Matrix.symplecticGroup l R) : Aᵀ = J l R * A⁻¹ * (J l R)⁻¹ := by
  rw [inv_eq_symplectic_inv A hA, J_inv]
  calc Aᵀ = J l R * (-J l R) * (Aᵀ * (J l R * (-J l R))) := by
        rw [J_mul_neg_J, one_mul, mul_one]
    _ = J l R * (-J l R * Aᵀ * J l R) * (-J l R) := by noncomm_ring

end SymplecticGroup

namespace LieAlgebra.Symplectic

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
theorem mem_sp_iff_transpose_eq_conj (A : Matrix (l ⊕ l) (l ⊕ l) R) :
    A ∈ sp l R ↔ Aᵀ = J l R * (-A) * (J l R)⁻¹ := by
  rw [mem_sp, J_inv]
  constructor
  · intro h
    calc Aᵀ = Aᵀ * (J l R * (-J l R)) := by rw [J_mul_neg_J, mul_one]
      _ = -(J l R * A) * (-J l R) := by rw [← mul_assoc, h]
      _ = J l R * (-A) * (-J l R) := by noncomm_ring
  · intro h
    rw [h]
    calc J l R * (-A) * (-J l R) * J l R
        = J l R * (-A) * (-(J l R * J l R)) := by noncomm_ring
      _ = -(J l R * A) := by rw [J_squared]; noncomm_ring

end LieAlgebra.Symplectic
