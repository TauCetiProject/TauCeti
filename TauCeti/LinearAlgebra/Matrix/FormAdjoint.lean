/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# The adjoint of a matrix between two sesquilinear forms

Let `R` be a commutative ring with an involution `star`. A square matrix `J` over `R` is the Gram
matrix of the sesquilinear form `⟨x, y⟩_J = star x ⬝ᵥ J *ᵥ y`, conjugate-linear in the first
slot, the convention of `Matrix.unitaryGroupOf`. For Gram matrices `J` on `n` and `J'` on `m`, the
**form adjoint** of a matrix `T : Matrix m n R`, read as a map `(n → R) → (m → R)`, is

  `Matrix.formAdjoint J J' T = J⁻¹ * Tᴴ * J'`.

When `J` is invertible it is the unique matrix `T†` with `⟨x, T† y⟩_J = ⟨T x, y⟩_J'` for all
vectors `x` and `y` (`Matrix.formAdjoint_eq_iff_forall_dotProduct`). For `J = J' = 1` it is the
conjugate transpose, and for invertible `J` the inverse of an element `g` of
`Matrix.unitaryGroupOf J` is `formAdjoint J J g` (`Matrix.val_inv_of_mem_unitaryGroupOf`).

## Main definitions

* `Matrix.formAdjoint J J' T`: the adjoint `J⁻¹ * Tᴴ * J'` of `T` for the forms of `J` and `J'`.

## Main results

* `Matrix.mul_formAdjoint`: `J * formAdjoint J J' T = Tᴴ * J'` for invertible `J`.
* `Matrix.formAdjoint_eq_iff`: the form adjoint is the unique solution `S` of `J * S = Tᴴ * J'`.
* `Matrix.dotProduct_mulVec_formAdjoint`: the adjunction `⟨x, T† y⟩_J = ⟨T x, y⟩_J'`.
* `Matrix.formAdjoint_eq_iff_forall_dotProduct`: the adjunction characterises the form adjoint.
* `Matrix.formAdjoint_mul`: `(S * T)† = T† * S†` when the middle Gram matrix is invertible.
-/

public section

namespace Matrix

variable {l m n R : Type*} [Fintype m] [Fintype n] [DecidableEq n] [CommRing R] [StarRing R]

/-- The **form adjoint** `J⁻¹ * Tᴴ * J'` of `T : Matrix m n R` for the sesquilinear forms
`⟨x, y⟩_J = star x ⬝ᵥ J *ᵥ y` on `n → R` and `⟨x, y⟩_J' = star x ⬝ᵥ J' *ᵥ y` on `m → R`. When `J`
is invertible it is the unique matrix `T†` with `⟨x, T† y⟩_J = ⟨T x, y⟩_J'`. -/
noncomputable def formAdjoint (J : Matrix n n R) (J' : Matrix m m R) (T : Matrix m n R) :
    Matrix n m R :=
  J⁻¹ * Tᴴ * J'

variable {J : Matrix n n R} {J' : Matrix m m R} {T : Matrix m n R}

theorem formAdjoint_def (J : Matrix n n R) (J' : Matrix m m R) (T : Matrix m n R) :
    formAdjoint J J' T = J⁻¹ * Tᴴ * J' :=
  (rfl)

/-- The defining equation of the form adjoint: `J * T† = Tᴴ * J'` when `J` is invertible. -/
theorem mul_formAdjoint (hJ : IsUnit J.det) : J * formAdjoint J J' T = Tᴴ * J' := by
  rw [formAdjoint_def, Matrix.mul_assoc, mul_nonsing_inv_cancel_left _ _ hJ]

/-- For invertible `J`, the form adjoint of `T` is the unique matrix `S` with
`J * S = Tᴴ * J'`. -/
theorem formAdjoint_eq_iff (hJ : IsUnit J.det) {S : Matrix n m R} :
    formAdjoint J J' T = S ↔ J * S = Tᴴ * J' := by
  refine ⟨fun h ↦ h ▸ mul_formAdjoint hJ, fun h ↦ ?_⟩
  rw [formAdjoint_def, Matrix.mul_assoc, ← h, nonsing_inv_mul_cancel_left _ _ hJ]

/-- **The adjunction**: `⟨x, T† y⟩_J = ⟨T x, y⟩_J'` when `J` is invertible. -/
theorem dotProduct_mulVec_formAdjoint (hJ : IsUnit J.det) (x : n → R) (y : m → R) :
    star x ⬝ᵥ J *ᵥ (formAdjoint J J' T *ᵥ y) = star (T *ᵥ x) ⬝ᵥ J' *ᵥ y := by
  rw [mulVec_mulVec, mul_formAdjoint hJ, ← mulVec_mulVec, dotProduct_mulVec, star_mulVec]

/-- For invertible `J`, the form adjoint of `T` is the unique matrix `S` with
`⟨x, S y⟩_J = ⟨T x, y⟩_J'` for all `x` and `y`. -/
theorem formAdjoint_eq_iff_forall_dotProduct (hJ : IsUnit J.det) {S : Matrix n m R} :
    formAdjoint J J' T = S ↔
      ∀ x y, star x ⬝ᵥ J *ᵥ (S *ᵥ y) = star (T *ᵥ x) ⬝ᵥ J' *ᵥ y := by
  refine ⟨fun h ↦ h ▸ dotProduct_mulVec_formAdjoint hJ, fun h ↦ (formAdjoint_eq_iff hJ).2 ?_⟩
  classical
  ext i j
  have hij := h (Pi.single i 1) (Pi.single j 1)
  rw [mulVec_mulVec, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec] at hij
  simpa [mulVec_single_one, Pi.star_single, single_one_dotProduct] using hij

/-- **The form adjoint of a product** is the product of the form adjoints in reverse order, when
the Gram matrix `J'` of the middle space is invertible. -/
theorem formAdjoint_mul [Fintype l] [DecidableEq m] {J'' : Matrix l l R} (hJ' : IsUnit J'.det)
    (S : Matrix l m R) (T : Matrix m n R) :
    formAdjoint J J'' (S * T) = formAdjoint J J' T * formAdjoint J' J'' S := by
  simp only [formAdjoint_def, conjTranspose_mul, Matrix.mul_assoc,
    mul_nonsing_inv_cancel_left _ _ hJ']

end Matrix
