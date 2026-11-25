/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Derivation.Basic

/-!
# Conjugating derivations by multiplication

Conjugating a derivation `D` by multiplication by a unit `u` subtracts multiplication by the
logarithmic derivative `u⁻¹ D(u)`. This identifies the rank-one operators `D + a` admitting `u`
as a horizontal generator with the conjugate of `D` by multiplication by `u`. Conjugation uses
`LinearEquiv.conjAlgEquiv` with `Units.mulLeftLinearEquiv`, so the identification also determines
the powers of the conjugated operator.
-/

public section

namespace Derivation

variable {R A : Type*} [CommSemiring R] [CommRing A] [Algebra R A]

/-- The conjugate `u ∘ D ∘ u⁻¹`, where `u` and `u⁻¹` act by multiplication, is `D` minus
multiplication by the logarithmic derivative `u⁻¹ D(u)`. -/
@[simp]
theorem conjAlgEquiv_mulLeftLinearEquiv_toLinearMap (D : Derivation R A A) (u : Aˣ) :
    (u.mulLeftLinearEquiv R A).conjAlgEquiv R D.toLinearMap =
      D.toLinearMap - LinearMap.mulLeft R ((↑u⁻¹ : A) * D u) := by
  ext b
  simp only [LinearEquiv.conjAlgEquiv_apply_apply, Units.mulLeftLinearEquiv_apply,
    Units.symm_mulLeftLinearEquiv_apply, Derivation.coeFn_coe, LinearMap.sub_apply,
    LinearMap.mulLeft_apply]
  apply eq_sub_iff_add_eq.mpr
  simpa [smul_eq_mul, mul_right_comm] using (D.leibniz (↑u) ((↑u⁻¹ : A) * b)).symm

/-- A rank-one operator `D + a` annihilates a unit `u` exactly when it is `D` conjugated by
multiplication by `u`. -/
theorem add_mulLeft_apply_unit_eq_zero_iff (D : Derivation R A A) (a : A) (u : Aˣ) :
    (D.toLinearMap + LinearMap.mulLeft R a) (u : A) = 0 ↔
      D.toLinearMap + LinearMap.mulLeft R a =
        (u.mulLeftLinearEquiv R A).conjAlgEquiv R D.toLinearMap := by
  constructor
  · intro h
    have ha : a = -((↑u⁻¹ : A) * D u) := by
      rw [LinearMap.add_apply, LinearMap.mulLeft_apply, Derivation.coeFn_coe,
        add_eq_zero_iff_eq_neg'] at h
      simpa [mul_comm, mul_assoc] using congrArg ((↑u⁻¹ : A) * ·) h
    rw [conjAlgEquiv_mulLeftLinearEquiv_toLinearMap, ha]
    ext b
    simp [sub_eq_add_neg, mul_assoc]
  · intro h
    rw [h]
    simp only [LinearEquiv.conjAlgEquiv_apply_apply, Units.mulLeftLinearEquiv_apply,
      Units.symm_mulLeftLinearEquiv_apply, Units.inv_mul, Derivation.coeFn_coe,
      Derivation.map_one_eq_zero, mul_zero]

end Derivation
