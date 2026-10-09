/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LaurentSeries
public import TauCeti.RingTheory.PowerSeries.Derivative

/-!
# Scalar towers and residues of `φⁿ dφ` for Laurent series

The `R`-algebra structure on `R⸨X⸩` is the one inherited from `R⟦X⟧` through
`HahnSeries.ofPowerSeries`, so its scalar action is multiplication by the image of a constant
power series. This is propositionally, but not definitionally, equal to the coefficientwise
action `HahnSeries.instSMul` found by default.

This file records that the algebra actions form a scalar tower `R → R⟦X⟧ → R⸨X⸩`. This is what
fraction-field constructions such as `IsFractionRing.algEquivOfAlgEquiv` require to extend an
`R`-algebra equivalence with `R⟦X⟧` to one with `R⸨X⸩`.

The second part computes the residue, the coefficient of `X⁻¹`, of `φ ^ n * φ'` for a power
series `φ` of order one over a field and every integer `n`: it is `1` for `n = -1` and `0`
otherwise. This is the formal statement that the residue is unchanged by the substitution
`X ↦ φ`. For `n ≠ -1` in characteristic zero, `φ ^ n * φ'` is the derivative of
`φ ^ (n + 1) / (n + 1)`; in characteristic `p` this fails when `p ∣ n + 1`, and the proof
uses `PowerSeries.coeff_succ_pow_succ_eq_coeff_pow_mul_derivative` instead.

## Main results

* `TauCeti.LaurentSeries.isScalarTower_powerSeries`: the algebra actions of `R` on `R⟦X⟧` and
  `R⸨X⸩` form a scalar tower.
* `PowerSeries.coe_derivative`: the derivative of Laurent series extends that of power series.
* `PowerSeries.coeff_neg_one_coe_zpow_mul_derivative`: the residue of `φ ^ n * φ'` for a power
  series `φ` of order one is `1` if `n = -1` and `0` otherwise.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section IV.2, Proposition 4.2.9.
-/

public section

open scoped LaurentSeries PowerSeries

namespace TauCeti.LaurentSeries

variable {R : Type*} [CommSemiring R]

/-- The constant scalars on `R⸨X⸩` factor through `R⟦X⟧`. The scalar actions are stated through
the algebra structures, since the `R`-algebra structure on `R⸨X⸩` is the one inherited from
`R⟦X⟧` rather than the coefficientwise action. -/
instance isScalarTower_powerSeries :
    @IsScalarTower R R⟦X⟧ R⸨X⸩ Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
  .of_algebraMap_eq' rfl

end TauCeti.LaurentSeries

namespace PowerSeries

open HahnSeries LaurentSeries

/-- The derivative of Laurent series extends the derivative of power series. -/
@[simp]
theorem coe_derivative {R : Type*} [CommRing R] (f : R⟦X⟧) :
    ((d⁄dX f : R⟦X⟧) : R⸨X⸩) = LaurentSeries.derivative R (f : R⸨X⸩) := by
  ext i
  rw [derivative_apply, hasseDeriv_coeff, coeff_coe, coeff_coe]
  rcases i with m | m
  · have hm : ((m : ℤ) + 1).natAbs = m + 1 := by omega
    simp [coeff_derivative, mul_comm, hm, show ¬((m : ℤ) + 1 < 0) by omega]
  · rcases m with _ | m
    · simp
    · simp [Int.negSucc_lt_zero, show Int.negSucc (m + 1) + 1 < 0 by omega]

/-- **The residue of `φ ^ n dφ`.** For a power series `φ` of order one over a field, the
coefficient of `X⁻¹` in the Laurent series `φ ^ n * φ'` is `1` if `n = -1` and `0` otherwise.
Equivalently, the residue of `X ^ n dX` is unchanged by the substitution `X ↦ φ`. -/
theorem coeff_neg_one_coe_zpow_mul_derivative {k : Type*} [Field k] {φ : k⟦X⟧} (hφ : φ.order = 1)
    (n : ℤ) :
    ((φ : k⸨X⸩) ^ n * LaurentSeries.derivative k (φ : k⸨X⸩)).coeff (-1) =
      if n = -1 then 1 else 0 := by
  rw [← coe_derivative]
  rcases n with m | m
  · -- For `n ≥ 0` the product is a power series.
    rw [Int.ofNat_eq_natCast, zpow_natCast, ← coe_pow, ← coe_mul, coeff_coe]
    simp [show (m : ℤ) ≠ -1 by omega]
  · -- Write `φ = X * u` with `u` a unit power series.
    obtain ⟨u, hu0, rfl⟩ : ∃ u : k⟦X⟧, constantCoeff u ≠ 0 ∧ φ = X * u := by
      refine ⟨φ.divXPowOrder, ?_, ?_⟩
      · rw [Ne, constantCoeff_divXPowOrder_eq_zero_iff]
        rintro rfl
        simp at hφ
      · conv_lhs => rw [← X_pow_order_mul_divXPowOrder (f := φ)]
        simp [hφ]
    have hvu : u⁻¹ * u = 1 := PowerSeries.inv_mul_cancel u hu0
    have hinv : (((X * u : k⟦X⟧) : k⸨X⸩) ^ (m + 1))⁻¹ =
        single (-((m + 1 : ℕ) : ℤ)) (1 : k) * ((u⁻¹ ^ (m + 1) : k⟦X⟧) : k⸨X⸩) := by
      refine inv_eq_of_mul_eq_one_right ?_
      rw [coe_mul, ofPowerSeries_X, mul_pow, single_pow, one_pow, ← coe_pow,
        mul_mul_mul_comm, single_mul_single, ← coe_mul, ← mul_pow, mul_comm u, hvu]
      simp
    rw [zpow_negSucc, hinv, mul_assoc, ← coe_mul, coeff_single_mul, one_mul, coeff_coe,
      ite_eq_right (show ¬(-1 - -((m + 1 : ℕ) : ℤ) < 0) by omega),
      show (-1 - -((m + 1 : ℕ) : ℤ)).natAbs = m by omega]
    -- Since `u⁻¹ * u = 1`, `u⁻¹ ^ (m + 1) * (X * u)'` is `u⁻¹ ^ m + X * u⁻¹ ^ (m + 1) * u'`.
    have hd : u⁻¹ ^ (m + 1) * d⁄dX (X * u) = u⁻¹ ^ m + X * (u⁻¹ ^ (m + 1) * d⁄dX u) := by
      rw [Derivation.leibniz, derivative_X, smul_eq_mul, smul_eq_mul, mul_one, pow_succ]
      linear_combination u⁻¹ ^ m * hvu
    rw [hd, map_add]
    rcases m with _ | m
    · simp
    · -- Since `(u⁻¹)' = -(u⁻¹) ^ 2 * u'`, the remaining coefficient is that of
      -- `u⁻¹ ^ (m + 1) - X * u⁻¹ ^ m * (u⁻¹)'`, which vanishes by
      -- `coeff_succ_pow_succ_eq_coeff_pow_mul_derivative`.
      have hv : u⁻¹ ^ (m + 2) * d⁄dX u = -(u⁻¹ ^ m * d⁄dX u⁻¹) := by
        rw [derivative_inv']
        ring
      rw [hv, coeff_succ_X_mul, map_neg, ← coeff_succ_pow_succ_eq_coeff_pow_mul_derivative]
      simp [show Int.negSucc (m + 1) ≠ -1 by omega]

end PowerSeries
