/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.SymmetricPower.Polynomial

/-!
# Binary monomials, substitution and the symmetric-power dictionary in small degree

Checks of `TauCeti.RepresentationTheory.ClassicalGroups.SymmetricPower.Polynomial` in two complex
variables `x = X 0` and `y = X 1`. Each value below excludes a plausible wrong convention.

* The monomial `e_0^0` is `1`, not an empty product read as `0`; `e_1^2` is `x y` with
  coefficient `1`, not `2 x y`; `e_2^1` is `0`, not `y²` from truncated subtraction.
* The identity matrix fixes `x` and `y`; `diag(2, 3)` sends `x y` to `6 x y`, where the
  contragredient substitution would give `x y / 6`; the upper unipotent matrix `!![1, 1; 0, 1]`
  fixes `x` and sends `y` to `x + y`, where inverse-transpose substitution would send `x` to
  `x - y`.
* In degree `0` the dictionary between symmetric tensors and forms matches the unit tensor with
  the constant `1`, which the zero map does not; in degree `2` it sends the pure symmetric tensor
  of the two standard vectors to `x y` with coefficient `1`.
-/

public section

open MvPolynomial Matrix
open scoped TensorProduct

namespace TauCeti.Examples

/-! ### Binary monomials -/

/-- The monomial `e_0^0` is the constant `1`. -/
example : polynomialMonomial ℂ 0 0 = 1 := by
  simp

/-- The monomial `e_1^2` is `x y`. -/
example : polynomialMonomial ℂ 2 1 = X 0 * X 1 := by
  simp [polynomialMonomial_of_le]

/-- The monomial `e_1^2` has coefficient `1` at the exponent `(1, 1)`. -/
example : (polynomialMonomial ℂ 2 1).coeff (Finsupp.single 0 1 + Finsupp.single 1 1) = 1 :=
  coeff_polynomialMonomial_self ℂ (by norm_num)

/-- The monomial `e_2^1` is zero. -/
example : polynomialMonomial ℂ 1 2 = 0 :=
  polynomialMonomial_of_lt ℂ (by norm_num)

/-! ### Substitution of standard vectors -/

/-- The identity matrix fixes `x`. -/
example : polynomialAction (1 : Matrix (Fin 2) (Fin 2) ℂ) (X 0) = X 0 := by
  simp

/-- The identity matrix fixes `y`. -/
example : polynomialAction (1 : Matrix (Fin 2) (Fin 2) ℂ) (X 1) = X 1 := by
  simp

/-- The diagonal matrix `diag(2, 3)` sends `x y` to `6 x y`. -/
example : polynomialAction (diagonal ![2, 3]) (X 0 * X 1 : MvPolynomial (Fin 2) ℂ) =
    C 6 * (X 0 * X 1) := by
  rw [polynomialAction_diagonal, map_mul, rescale_X, rescale_X,
    show (6 : ℂ) = 2 * 3 by norm_num, map_mul]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  ring

/-- The upper unipotent matrix `!![1, 1; 0, 1]` fixes `x`. -/
example : polynomialAction !![1, 1; 0, 1] (X 0 : MvPolynomial (Fin 2) ℂ) = X 0 := by
  simp [Fin.sum_univ_two]

/-- The upper unipotent matrix `!![1, 1; 0, 1]` sends `y` to `x + y`. -/
example : polynomialAction !![1, 1; 0, 1] (X 1 : MvPolynomial (Fin 2) ℂ) = X 0 + X 1 := by
  simp [Fin.sum_univ_two]

/-! ### The dictionary between symmetric tensors and forms -/

/-- In degree `0` the dictionary sends the constant polynomial `1` to the unit tensor. -/
example : (symPowerRepEquivPolynomialRep ℂ 2 0).symm
      ⟨1, isHomogeneous_one (Fin 2) ℂ⟩ = ⨂ₛ[ℂ] i : Fin 0, Fin.elim0 i := by
  apply EquivLike.injective (symPowerRepEquivPolynomialRep ℂ 2 0)
  rw [Representation.Equiv.apply_symm_apply]
  ext : 1
  simp [coe_symPowerRepEquivPolynomialRep_tprod]

/-- In degree `2` the dictionary sends the pure symmetric tensor of the two standard vectors to
the monomial `e_1^2 = x y`. -/
example : (symPowerRepEquivPolynomialRep ℂ 2 2
      (⨂ₛ[ℂ] i, ![Pi.single 0 1, Pi.single 1 1] i) : MvPolynomial (Fin 2) ℂ) =
    polynomialMonomial ℂ 2 1 := by
  simp [coe_symPowerRepEquivPolynomialRep_tprod, Fin.sum_univ_two, polynomialMonomial_of_le]

end TauCeti.Examples
