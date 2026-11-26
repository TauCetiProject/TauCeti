/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.QuadraticAlgebra.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
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
  omegaUnit 0

/-- The underlying Gaussian integer of the generator is `ω`. -/
@[simp] theorem gaussianUnit_val :
    (gaussianUnit : QuadraticAlgebra ℤ (-1) 0) = ω := by
  simp [gaussianUnit]

/-- The inverse Gaussian generator has underlying value `-ω`. -/
@[simp] theorem gaussianUnit_inv_val :
    (↑(gaussianUnit⁻¹) : QuadraticAlgebra ℤ (-1) 0) = -ω := by
  simp [gaussianUnit]

/-- The Eisenstein generator `ω = (1 + √-3)/2` as a unit, with inverse `1 - ω`. -/
def eisensteinUnit : (QuadraticAlgebra ℤ (-1) 1)ˣ :=
  omegaUnit 1

/-- The underlying Eisenstein integer of the generator is `ω`. -/
@[simp] theorem eisensteinUnit_val :
    (eisensteinUnit : QuadraticAlgebra ℤ (-1) 1) = ω := by
  simp [eisensteinUnit]

/-- The inverse Eisenstein generator has underlying value `1 - ω`. -/
@[simp] theorem eisensteinUnit_inv_val :
    (↑(eisensteinUnit⁻¹) : QuadraticAlgebra ℤ (-1) 1) = 1 - ω := by
  simp [eisensteinUnit]

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
  have : NeZero (3 : QuadraticAlgebra ℤ (-1) 1) := ⟨by norm_num⟩
  exact TauCeti.isPrimitiveRoot_six_of_sq_sub_add_one_eq_zero
    eisensteinUnit_sq_sub_add_one_eq_zero

/-- The Gaussian generator has order four in the unit group. -/
@[simp] theorem orderOf_gaussianUnit : orderOf gaussianUnit = 4 :=
  (IsPrimitiveRoot.coe_units_iff.mp isPrimitiveRoot_gaussianUnit).eq_orderOf.symm

/-- The Eisenstein generator has order six in the unit group. -/
@[simp] theorem orderOf_eisensteinUnit : orderOf eisensteinUnit = 6 :=
  (IsPrimitiveRoot.coe_units_iff.mp isPrimitiveRoot_eisensteinUnit).eq_orderOf.symm

end TauCeti.QuadraticAlgebra
