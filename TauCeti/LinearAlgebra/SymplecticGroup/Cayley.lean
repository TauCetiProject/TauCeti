/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.Star
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.SymplecticGroup

/-!
# The symplectic Cayley transform

For a real `2n × 2n` matrix `A` with `1 + A` invertible, the **symplectic Cayley transform** is
`C(A) = J (1 - A) (1 + A)⁻¹` (`Matrix.symplecticCayley`). When `A` is symplectic, `C(A)` is
symmetric (`Matrix.isHermitian_symplecticCayley`).

## Main definitions

* `Matrix.symplecticCayley`: the symplectic Cayley transform `J (1 - A) (1 + A)⁻¹`.

## Main results

* `Matrix.isHermitian_symplecticCayley`: the symplectic Cayley transform of a symplectic matrix
  is symmetric.
-/

public section

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The **symplectic Cayley transform** `J (1 - A) (1 + A)⁻¹` of a real matrix `A`. -/
noncomputable def symplecticCayley (A : Matrix (n ⊕ n) (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ :=
  J n ℝ * (1 - A) * (1 + A)⁻¹

/-- The definition of the symplectic Cayley transform. -/
theorem symplecticCayley_def (A : Matrix (n ⊕ n) (n ⊕ n) ℝ) :
    symplecticCayley A = J n ℝ * (1 - A) * (1 + A)⁻¹ :=
  (rfl)

/-- The symplectic Cayley transform of the identity vanishes. -/
@[simp]
theorem symplecticCayley_one : symplecticCayley (1 : Matrix (n ⊕ n) (n ⊕ n) ℝ) = 0 := by
  simp [symplecticCayley]

/-- The characterization `C(A) (1 + A) = J (1 - A)` of the symplectic Cayley transform, when
`1 + A` is invertible. -/
theorem symplecticCayley_mul_one_add {A : Matrix (n ⊕ n) (n ⊕ n) ℝ} (h : IsUnit (1 + A).det) :
    symplecticCayley A * (1 + A) = J n ℝ * (1 - A) := by
  rw [symplecticCayley, Matrix.nonsing_inv_mul_cancel_right _ _ h]

/-- **The symplectic Cayley transform of a symplectic matrix is symmetric.** If `Aᵀ J A = J` and
`1 + A` is invertible, then `J (1 - A) (1 + A)⁻¹` is symmetric: both `-(1 - A)ᵀ J (1 + A)` and
`(1 + A)ᵀ J (1 - A)` equal `Aᵀ J - J A`. -/
theorem isHermitian_symplecticCayley {A : Matrix (n ⊕ n) (n ⊕ n) ℝ}
    (hA : A ∈ symplecticGroup n ℝ) (h : IsUnit (1 + A).det) :
    (symplecticCayley A).IsHermitian := by
  have hP : IsUnit (1 + A)ᵀ.det := by rwa [det_transpose]
  have hkey : -((1 - A)ᵀ * J n ℝ) * (1 + A) = (1 + A)ᵀ * (J n ℝ * (1 - A)) := by
    have hJ := SymplecticGroup.mem_iff'.1 hA
    simp only [transpose_sub, transpose_add, transpose_one, Matrix.sub_mul, Matrix.add_mul,
      Matrix.mul_sub, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.neg_mul,
      ← Matrix.mul_assoc, hJ]
    abel
  rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, symplecticCayley, transpose_mul,
    transpose_mul, J_transpose, transpose_nonsing_inv, Matrix.mul_neg]
  calc ((1 + A)ᵀ)⁻¹ * -((1 - A)ᵀ * J n ℝ)
      = ((1 + A)ᵀ)⁻¹ * (-((1 - A)ᵀ * J n ℝ) * (1 + A)) * (1 + A)⁻¹ := by
        rw [Matrix.mul_assoc _ _ (1 + A)⁻¹, Matrix.mul_nonsing_inv_cancel_right _ _ h]
    _ = J n ℝ * (1 - A) * (1 + A)⁻¹ := by
        rw [hkey, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hP, Matrix.one_mul]

end Matrix
