/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.BilinearForm.ElementaryDivisors
import TauCeti.LinearAlgebra.Matrix.Determinant.FromBlocks

/-!
# Types of integral alternating forms: examples

The alternating form on `ℤ⁴ = ℤ^(Fin 2 ⊕ Fin 2)` with matrix `[[0, D], [-D, 0]]`,
`D = diag(1, 2)`, is nondegenerate of type `(1, 2)`, and its determinant is `4 = (1 · 2)²`.
-/

public section

open Matrix Module LinearMap

namespace TauCeti.PolarizationTypeExamples

/-- The matrix `[[0, D], [-D, 0]]` with `D = diag(1, 2)`. -/
abbrev typeOneTwo : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ :=
  fromBlocks 0 (diagonal ![1, 2]) (-diagonal ![1, 2]) 0

/-- The form of `typeOneTwo` is alternating. -/
theorem isAlt_typeOneTwo : (Matrix.toBilin' typeOneTwo).IsAlt := fun x ↦ by
  simp only [Matrix.toBilin'_apply', dotProduct, mulVec, Fintype.sum_sum_type, Fin.sum_univ_two,
    fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
    diagonal_apply]
  simp
  ring

/-- The determinant of `typeOneTwo` is `4`. -/
theorem det_typeOneTwo : typeOneTwo.det = 4 := by
  rw [det_fromBlocks_zero₁₁_zero₂₂, det_neg, det_diagonal]
  simp [Fin.prod_univ_two]

/-- The form of `typeOneTwo` is nondegenerate. -/
theorem nondegenerate_typeOneTwo : (Matrix.toBilin' typeOneTwo).Nondegenerate :=
  BilinForm.nondegenerate_toBilin'_of_det_ne_zero' _ (by rw [det_typeOneTwo]; decide)

/-- `ℤ⁴` has half-rank `2`. -/
theorem finrank_div_two : finrank ℤ (Fin 2 ⊕ Fin 2 → ℤ) / 2 = 2 := by
  simp

/-- The form of `typeOneTwo` has type `(1, 2)`. -/
example : isAlt_typeOneTwo.polarizationType nondegenerate_typeOneTwo =
    ![1, 2] ∘ Fin.cast finrank_div_two :=
  isAlt_typeOneTwo.polarizationType_eq nondegenerate_typeOneTwo finrank_div_two
    (b := Pi.basisFun ℤ _) (by decide) (by decide)
    (by rw [BilinForm.toMatrix_basisFun, BilinForm.toMatrix'_toBilin'])

/-- The square of the product of the type of the form of `typeOneTwo` is its determinant `4`. -/
example : (∏ i, isAlt_typeOneTwo.polarizationType nondegenerate_typeOneTwo i) ^ 2 = 4 := by
  rw [← isAlt_typeOneTwo.det_toMatrix_eq_prod_polarizationType_sq nondegenerate_typeOneTwo
    (Pi.basisFun ℤ _), BilinForm.toMatrix_basisFun, BilinForm.toMatrix'_toBilin', det_typeOneTwo]

end TauCeti.PolarizationTypeExamples
