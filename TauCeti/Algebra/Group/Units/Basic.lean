/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.Group.Units.Equiv

/-!
# Units in monoids

This file lifts units in the range of a local monoid homomorphism to units of its source.
It also rewrites a strictly negative integer power of a product `a * b` with `a` a unit as an
inverse monomial with consecutive natural exponents, which lets the negative half of a bilateral
sum over integer powers be expressed as a sum over natural numbers without requiring a zero in the
ambient monoid. The nonnegative half is `TauCeti.mul_pow_mul_eq_pow_succ_mul_pow` in
`TauCeti.Algebra.Group.Pow`.

## Main results

* `TauCeti.mem_range_iff_exists_units_map_eq`: a unit lies in the range of a local monoid
  homomorphism exactly when it is the image of a unit under `Units.map`.
* `Units.mul_mul_inv_eq_iff_eq_of_commute`: for `z` commuting with a unit `u`, the conjugate of
  `a` by `u` equals `z` exactly when `a` does.
* `Units.map_coeHom_bijective`: `Units.map (Units.coeHom M) : Mˣˣ →* Mˣ` is bijective: it is
  the inverse of Mathlib's `toUnits : Mˣ ≃* Mˣˣ`.
* `Units.val_inv_mul_mul_mul_eq_one`: if `(a : M) = z`, then `(l * a)⁻¹ * l * z = 1`.
* `Units.val_inv_mul_mul_inv_mul_eq_one`: if `(a : M) = z` and `l ^ 2 * z = b`, then
  `(l * a)⁻¹ * l⁻¹ * b = 1`.
* `IsUnit.mul_zpow_neg_natCast_succ_mul`: negative product powers give inverse monomials.
-/

public section

namespace TauCeti

/-- A unit in the range of a local monoid homomorphism comes from a unit of the source. -/
theorem mem_range_iff_exists_units_map_eq {M N F : Type*} [Monoid M] [Monoid N]
    [FunLike F M N] [MonoidHomClass F M N] (f : F) [IsLocalHom f] (u : Nˣ) :
    (u : N) ∈ Set.range f ↔ ∃ a : Mˣ, Units.map (f : M →* N) a = u :=
  ⟨fun ⟨a, ha⟩ ↦ ⟨(IsUnit.of_map f a (ha ▸ u.isUnit)).unit, Units.ext (by simp [ha])⟩,
    fun ⟨a, ha⟩ ↦ ⟨a, by simp [← ha]⟩⟩

end TauCeti

namespace Units

/-- `Units.map (Units.coeHom M) : Mˣˣ →* Mˣ` is bijective, being the inverse of Mathlib's
`toUnits : Mˣ ≃* Mˣˣ`: the units of the group `Mˣ` are the units of `M`. -/
theorem map_coeHom_bijective (M : Type*) [Monoid M] : Function.Bijective (map (coeHom M)) := by
  have h : ⇑(map (coeHom M)) = (toUnits (G := Mˣ)).symm := funext fun x => by
    ext; simp [toUnits_symm_apply]
  exact h ▸ (toUnits (G := Mˣ)).symm.bijective

/-- For an element `z` commuting with a unit `u`, the conjugate of `a` by `u` equals `z` exactly
when `a` does. -/
theorem mul_mul_inv_eq_iff_eq_of_commute {A : Type*} [Monoid A] {a z : A} (u : Aˣ)
    (hz : Commute z u) : (u : A) * a * ↑u⁻¹ = z ↔ a = z := by
  rw [Units.mul_inv_eq_iff_eq_mul, hz.eq, Units.mul_right_inj]

/-- If `(a : M) = z`, then `(l * a)⁻¹ * l * z = 1`. -/
theorem val_inv_mul_mul_mul_eq_one {M : Type*} [Monoid M] (a l : Mˣ) {z : M} (ha : (a : M) = z) :
    (↑(l * a)⁻¹ : M) * (l : M) * z = 1 := by
  rw [← ha, mul_assoc, ← Units.val_mul, Units.inv_mul]

/-- If `(a : M) = z` and `l ^ 2 * z = b`, then `(l * a)⁻¹ * l⁻¹ * b = 1`. -/
theorem val_inv_mul_mul_inv_mul_eq_one {M : Type*} [Monoid M] (a l : Mˣ) {z b : M}
    (ha : (a : M) = z) (hl : (l : M) ^ 2 * z = b) :
    (↑(l * a)⁻¹ : M) * (↑l⁻¹ : M) * b = 1 := by
  have h : (l * a)⁻¹ * l⁻¹ * (l ^ 2 * a) = 1 := by
    simp [sq, mul_assoc]
  simpa only [ha, hl, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_one] using
    congrArg Units.val h

end Units

namespace IsUnit

/-- In a commutative division monoid, a strictly negative power of a product `a * b` with `a` a
unit, multiplied by `a`, is the inverse of the monomial with the consecutive exponents exchanged.
The second factor `b` need not be a unit. -/
theorem mul_zpow_neg_natCast_succ_mul {M : Type*} [DivisionCommMonoid M] {a : M}
    (ha : IsUnit a) (b : M) (n : ℕ) :
    (a * b) ^ (-((n : ℤ) + 1)) * a = (b ^ (n + 1) * a ^ n)⁻¹ := by
  -- Split one factor `a` off the positive power, so that it cancels against the trailing `a`.
  have h : (a * b) ^ (n + 1) = b ^ (n + 1) * a ^ n * a := by
    rw [mul_pow, pow_succ a, mul_comm, mul_assoc]
  rw [← Int.negSucc_eq, zpow_negSucc, h, mul_inv, ha.inv_mul_cancel_right]

end IsUnit
