/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.IsotropicFlag.Antidiagonal.Congr

/-!
# The long simple root group of `Sp₄` in the antidiagonal model: checks

Checks for the antidiagonal form `Q = TauCeti.JAntidiag 2 R` and its congruence
`TauCeti.antidiagCongr` to `JFin 2 R`. In one-based matrix units, with zero-based indices in the
Lean statements:

* the long simple root group `x_{2ε₂}(a) = I + a E₂₃` preserves `Q`;
* `I + a E₁₃` does not, for `a ≠ 0`;
* conjugated into the `JFin` model, `P (I + a E₂₃) P⁻¹ = I - a E₂₄`: the same root group is the
  group of matrix units `E₂₄` there.
-/

public section

open Matrix

namespace TauCeti.Examples.AntidiagonalSymplectic

variable {R : Type*} [CommRing R]

/-- The long simple root group `I + a E₂₃` preserves the antidiagonal form of `Sp₄`. -/
theorem root_mul_JAntidiag_mul_transpose (a : R) :
    (1 + single (1 : Fin (2 + 2)) 2 a) * JAntidiag 2 R * (1 + single (1 : Fin (2 + 2)) 2 a)ᵀ =
      JAntidiag 2 R := by
  rw [JAntidiag_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply, single_apply]

/-- The matrix `I + a E₁₃` does not preserve the antidiagonal form of `Sp₄` for `a ≠ 0`. -/
theorem not_mul_JAntidiag_mul_transpose {a : R} (ha : a ≠ 0) :
    (1 + single (0 : Fin (2 + 2)) 2 a) * JAntidiag 2 R * (1 + single (0 : Fin (2 + 2)) 2 a)ᵀ ≠
      JAntidiag 2 R := by
  rw [JAntidiag_two]
  intro h
  have h₀₁ := congrFun (congrFun h 0) 1
  refine ha ?_
  simpa [Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply, single_apply] using h₀₁

open GLSymplecticFin.IsotropicFlag in
/-- In the `JFin` model the root group `I + a E₂₃` of the antidiagonal model becomes `I - a E₂₄`. -/
theorem antidiagCongr_mul_root_mul_inv (a : R) :
    (antidiagCongr 2 R : Matrix (Fin (2 + 2)) (Fin (2 + 2)) R) *
        (1 + single (1 : Fin (2 + 2)) 2 a) *
        (((antidiagCongr 2 R)⁻¹ : GL (Fin (2 + 2)) R) : Matrix (Fin (2 + 2)) (Fin (2 + 2)) R) =
      1 - single (1 : Fin (2 + 2)) 3 a := by
  have h₀ : flagOrder 2 0 = 0 := by simpa using flagOrder_castAdd 2 0
  have h₁ : flagOrder 2 1 = 1 := by simpa using flagOrder_castAdd 2 1
  have h₂ : flagOrder 2 2 = 3 := by simpa using flagOrder_addNat 2 0
  have h₃ : flagOrder 2 3 = 2 := by simpa using flagOrder_addNat 2 1
  have s₀ : antidiagSign 2 R 0 = -1 := by simpa using antidiagSign_castAdd (R := R) (m := 2) 0
  have s₁ : antidiagSign 2 R 1 = -1 := by simpa using antidiagSign_castAdd (R := R) (m := 2) 1
  have s₂ : antidiagSign 2 R 2 = 1 := by simpa using antidiagSign_addNat (R := R) (m := 2) 0
  have s₃ : antidiagSign 2 R 3 = 1 := by simpa using antidiagSign_addNat (R := R) (m := 2) 1
  rw [coe_antidiagCongr, coe_antidiagCongr_inv, antidiagCongrMatrix_mul_mul_transpose]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [h₀, h₁, h₂, h₃, s₀, s₁, s₂, s₃]

end TauCeti.Examples.AntidiagonalSymplectic
