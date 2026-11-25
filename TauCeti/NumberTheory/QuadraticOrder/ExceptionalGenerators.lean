/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Algebra.QuadraticAlgebra.Int
import TauCeti.RingTheory.RootsOfUnity.FourthAndSixth

/-!
# Explicit generators in the exceptional quadratic orders

The coordinate generator `ω` is a unit in the Gaussian and Eisenstein integral models, with
inverse `-ω` and `1 - ω`, respectively. These generators are primitive fourth and sixth roots
of unity directly in their integral models.
-/

public section

open scoped QuadraticAlgebra

namespace TauCeti.QuadraticAlgebra

/-- The Gaussian generator `ω = √-1` as a unit, with inverse `-ω`. -/
def gaussianUnit : (QuadraticAlgebra ℤ (-1) 0)ˣ :=
  Units.mkOfMulEqOne ω (-ω) (by ext <;> simp)

/-- The underlying Gaussian integer of the generator is `ω`. -/
@[simp] theorem gaussianUnit_val :
    (gaussianUnit : QuadraticAlgebra ℤ (-1) 0) = ω := by simp [gaussianUnit]

/-- The inverse Gaussian generator has underlying value `-ω`. -/
@[simp] theorem gaussianUnit_inv_val :
    (↑(gaussianUnit⁻¹) : QuadraticAlgebra ℤ (-1) 0) = -ω := by
  apply Units.inv_eq_of_mul_eq_one_right
  ext <;> simp

/-- The Eisenstein generator `ω = (1 + √-3)/2` as a unit, with inverse `1 - ω`. -/
def eisensteinUnit : (QuadraticAlgebra ℤ (-1) 1)ˣ :=
  Units.mkOfMulEqOne ω (1 - ω) (by ext <;> simp)

/-- The underlying Eisenstein integer of the generator is `ω`. -/
@[simp] theorem eisensteinUnit_val :
    (eisensteinUnit : QuadraticAlgebra ℤ (-1) 1) = ω := by simp [eisensteinUnit]

/-- The inverse Eisenstein generator has underlying value `1 - ω`. -/
@[simp] theorem eisensteinUnit_inv_val :
    (↑(eisensteinUnit⁻¹) : QuadraticAlgebra ℤ (-1) 1) = 1 - ω := by
  apply Units.inv_eq_of_mul_eq_one_right
  ext <;> simp

/-- The Eisenstein generator is a root of the sixth cyclotomic polynomial `X² - X + 1`. -/
theorem eisensteinUnit_sq_sub_add_one_eq_zero :
    (eisensteinUnit : QuadraticAlgebra ℤ (-1) 1) ^ 2 - eisensteinUnit + 1 = 0 := by
  simp [QuadraticAlgebra.omega_pow_two_eq_add]

/-- The Gaussian generator is a primitive fourth root of unity. -/
theorem isPrimitiveRoot_gaussianUnit :
    IsPrimitiveRoot (gaussianUnit : QuadraticAlgebra ℤ (-1) 0) 4 := by
  apply TauCeti.isPrimitiveRoot_four_of_sq_eq_neg_one
  simp [QuadraticAlgebra.omega_pow_two_eq_add]

/-- The Eisenstein generator is a primitive sixth root of unity. -/
theorem isPrimitiveRoot_eisensteinUnit :
    IsPrimitiveRoot (eisensteinUnit : QuadraticAlgebra ℤ (-1) 1) 6 := by
  have : Fact (¬ IsSquare (QuadraticAlgebra.discr (-1 : ℤ) 1)) :=
    ⟨not_isSquare_of_neg (by norm_num [QuadraticAlgebra.discr_def])⟩
  exact (TauCeti.isPrimitiveRoot_six_iff (R := QuadraticAlgebra ℤ (-1) 1)).2
    eisensteinUnit_sq_sub_add_one_eq_zero

end TauCeti.QuadraticAlgebra
