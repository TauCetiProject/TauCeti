/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Algebra.GroupWithZero.Associated

/-!
# Units after inverting a prime element

Every unit in a localization away from a prime element is the product of an original
unit and an integral power of that prime. No unique factorization hypothesis is needed.
-/

public section

/-- After inverting a prime `p`, every unit is the image of a unit times an integral
power of the image of `p`. -/
theorem Prime.exists_units_mul_zpow_of_away {R S : Type*} [CommSemiring R] [IsCancelMulZero R]
    [CommSemiring S] [Algebra R S] {p : R} [IsLocalization.Away p S] (hp : Prime p) (u : Sˣ) :
    ∃ v : Rˣ, ∃ n : ℤ, u = Units.map (algebraMap R S).toMonoidHom v *
      (IsLocalization.Away.algebraMap_isUnit (S := S) p).unit ^ n := by
  let P := (IsLocalization.Away.algebraMap_isUnit (S := S) p).unit
  obtain ⟨m, r, hm⟩ := IsLocalization.Away.surj p (u : S)
  have hr : IsUnit (algebraMap R S r) := by
    rw [← hm]
    exact u.isUnit.mul ((IsLocalization.Away.algebraMap_isUnit p).pow m)
  obtain ⟨k, hk⟩ := (IsLocalization.Away.algebraMap_isUnit_iff p).mp hr
  obtain ⟨j, _, hj⟩ := (dvd_prime_pow hp k).mp hk
  obtain ⟨v, hv⟩ := hj.symm
  have hmul : u * P ^ m = Units.map (algebraMap R S).toMonoidHom v * P ^ j := by
    apply Units.ext
    rw [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_mul, Units.val_pow_eq_pow_val,
      Units.coe_map]
    calc
      _ = algebraMap R S r := hm
      _ = _ := by rw [← hv, map_mul, map_pow, mul_comm]; rfl
  refine ⟨v, (j : ℤ) - m, ?_⟩
  rw [zpow_sub, zpow_natCast, zpow_natCast, ← mul_assoc, ← hmul, mul_inv_cancel_right]
