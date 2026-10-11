/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LaurentSeries
public import TauCeti.RingTheory.PowerSeries.Derivative

/-!
# Scalar towers, the product rule, and residues of `φⁿ dφ` for Laurent series

The `R`-algebra structure on `R⸨X⸩` is the one inherited from `R⟦X⟧` through
`HahnSeries.ofPowerSeries`, so its scalar action is multiplication by the image of a constant
power series. This is propositionally, but not definitionally, equal to the coefficientwise
action `HahnSeries.instSMul` found by default.

This file records that the algebra actions form a scalar tower `R → R⟦X⟧ → R⸨X⸩`. This is what
fraction-field constructions such as `IsFractionRing.algEquivOfAlgEquiv` require to extend an
`R`-algebra equivalence with `R⟦X⟧` to one with `R⸨X⸩`.

The second part proves the product rule for the derivative of Laurent series,
`(f * g)' = f' * g + f * g'`. Mathlib defines `LaurentSeries.derivative` only as a linear map,
the first Hasse derivative; the product rule is what makes it a derivation, so that composing it
with a ring homomorphism into `R⸨X⸩` gives a derivation, as for Laurent expansions of functions.
It is reduced to the product rule for power series by writing a Laurent series as a monomial
times a power series.

The third part computes the residue, the coefficient of `X⁻¹`, of `φ ^ n * φ'` for a power
series `φ` of order one over a field and every integer `n`: it is `1` for `n = -1` and `0`
otherwise. This is the formal statement that the residue is unchanged by the substitution
`X ↦ φ`. For `n ≠ -1` in characteristic zero, `φ ^ n * φ'` is the derivative of
`φ ^ (n + 1) / (n + 1)`; in characteristic `p` this fails when `p ∣ n + 1`, and the proof
uses `PowerSeries.coeff_succ_pow_succ_eq_coeff_pow_mul_derivative` instead.

## Main results

* `TauCeti.LaurentSeries.isScalarTower_powerSeries`: the algebra actions of `R` on `R⟦X⟧` and
  `R⸨X⸩` form a scalar tower.
* `TauCeti.LaurentSeries.coeff_algebraMap_mul`: multiplication by a constant of the algebra
  structure acts coefficientwise.
* `TauCeti.laurentSeries_algebraMap_mul_eq_smul`: the algebra action agrees with the
  coefficientwise scalar action.
* `LaurentSeries.derivative_mul`: the product rule for the derivative of Laurent series.
* `PowerSeries.coe_derivative`: the derivative of Laurent series extends that of power series.
* `LaurentSeries.valuation_derivative_sub_zsmul_single_mul_le`: if `f` vanishes to order at least
  `m`, so does `f' - m X⁻¹ f`.
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

/-- Multiplying a Laurent series by a constant of the `R`-algebra structure on `R⸨X⸩` multiplies
each coefficient by that constant. -/
@[simp]
theorem coeff_algebraMap_mul (c : R) (f : R⸨X⸩) (n : ℤ) :
    (algebraMap R R⸨X⸩ c * f).coeff n = c * f.coeff n := by
  rw [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_eq, HahnSeries.ofPowerSeries_C,
    HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul]

end TauCeti.LaurentSeries

namespace TauCeti

/-- Multiplication by a constant of the Laurent-series algebra structure agrees with the
coefficientwise scalar action. -/
theorem laurentSeries_algebraMap_mul_eq_smul {R : Type*} [CommSemiring R]
    (c : R) (f : LaurentSeries R) :
    algebraMap R (LaurentSeries R) c * f = c • f := by
  ext n
  rw [LaurentSeries.coeff_algebraMap_mul, HahnSeries.coeff_smul, smul_eq_mul]

end TauCeti

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

end PowerSeries

namespace LaurentSeries

open HahnSeries

variable {R : Type*} [CommRing R]

/-- The product rule for a monomial: `(c X ^ m * f)' = m c X ^ (m - 1) * f + c X ^ m * f'`. -/
theorem derivative_single_mul (m : ℤ) (c : R) (f : R⸨X⸩) :
    derivative R (single m c * f) = single (m - 1) (m * c) * f + single m c * derivative R f := by
  ext n
  simp only [derivative_apply, hasseDeriv_coeff, coeff_add, coeff_single_mul,
    Ring.choose_one_right, zsmul_eq_mul]
  rw [show n - (m - 1) = n + 1 - m by ring, show n - m + (1 : ℕ) = n + 1 - m by push_cast; ring]
  push_cast
  ring

/-- The product rule for a monomial times a power series:
`(c X ^ m * φ)' = m c X ^ (m - 1) * φ + c X ^ m * φ'`. -/
theorem derivative_single_mul_coe (m : ℤ) (c : R) (φ : R⟦X⟧) :
    derivative R (single m c * (φ : R⸨X⸩)) =
      single (m - 1) (m * c) * φ + single m c * ((d⁄dX φ : R⟦X⟧) : R⸨X⸩) := by
  rw [derivative_single_mul, ← PowerSeries.coe_derivative]

/-- **The product rule** for the derivative of Laurent series: `(f * g)' = f' * g + f * g'`. -/
theorem derivative_mul (f g : R⸨X⸩) :
    derivative R (f * g) = derivative R f * g + f * derivative R g := by
  -- Write `f = X ^ a * φ` and `g = X ^ b * ψ` with power series `φ` and `ψ`, so that
  -- `f * g = X ^ (a + b) * (φ * ψ)`, and use the product rule for power series.
  rw [← single_order_mul_powerSeriesPart f, ← single_order_mul_powerSeriesPart g]
  set a := f.order
  set b := g.order
  set φ := f.powerSeriesPart
  set ψ := g.powerSeriesPart
  have hab : (single (a + b) (1 : R) : R⸨X⸩) = single a 1 * single b 1 := by
    rw [single_mul_single, one_mul]
  have hfg : (single a (1 : R) * (φ : R⸨X⸩)) * (single b 1 * (ψ : R⸨X⸩)) =
      single (a + b) 1 * ((φ * ψ : R⟦X⟧) : R⸨X⸩) := by
    rw [PowerSeries.coe_mul, hab]
    ring
  -- The derivative of the monomial `X ^ (a + b)` splits as `(X ^ a)' X ^ b + X ^ a (X ^ b)'`.
  have hd : (single (a + b - 1) (((a + b : ℤ) : R) * 1) : R⸨X⸩) =
      single (a - 1) ((a : R) * 1) * single b 1 + single a 1 * single (b - 1) ((b : R) * 1) := by
    rw [single_mul_single, single_mul_single, show a - 1 + b = a + b - 1 by ring,
      show a + (b - 1) = a + b - 1 by ring, ← single_add]
    push_cast
    ring_nf
  simp only [hfg, derivative_single_mul_coe]
  simp only [Derivation.leibniz, smul_eq_mul, PowerSeries.coe_add, PowerSeries.coe_mul]
  rw [hd, hab]
  ring

/-- The derivative of `f` agrees with `m X⁻¹ f` up to a correction whose coefficient of `Xⁿ` is
`(n + 1 - m)` times the coefficient of `Xⁿ⁺¹` in `f`. -/
theorem coeff_derivative_sub_zsmul_single_mul (m n : ℤ) (f : R⸨X⸩) :
    (derivative R f - m • (single (-1) 1 * f)).coeff n =
      ((n + 1 - m : ℤ) : R) * f.coeff (n + 1) := by
  rw [coeff_sub, coeff_smul, coeff_single_mul, derivative_apply, hasseDeriv_coeff,
    Ring.choose_one_right, sub_neg_eq_add, one_mul, zsmul_eq_mul, zsmul_eq_mul]
  push_cast
  ring

/-- **Differentiation lowers the order by at most one, with leading term `m X⁻¹ f`.** If `f` has
valuation at most `exp (-m)`, that is, vanishes to order at least `m`, then `f' - m X⁻¹ f` again
vanishes to order at least `m`. -/
theorem valuation_derivative_sub_zsmul_single_mul_le {K : Type*} [Field K] {m : ℤ} {f : K⸨X⸩}
    (hf : Valued.v f ≤ WithZero.exp (-m)) :
    Valued.v (derivative K f - m • (single (-1) 1 * f)) ≤ WithZero.exp (-m) := by
  rw [valuation_le_iff_coeff_lt_eq_zero] at hf ⊢
  intro n hn
  rw [coeff_derivative_sub_zsmul_single_mul]
  -- Below `m - 1` the coefficient of `f` vanishes; at `m - 1` the integer factor does.
  rcases lt_or_eq_of_le (show n + 1 ≤ m by omega) with h | h
  · rw [hf _ h, mul_zero]
  · simp [h]

end LaurentSeries

namespace PowerSeries

open HahnSeries LaurentSeries

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
      -- Cancel `u` in `k⟦X⟧`, then cancel `X ^ (m + 1)` against `single (-(m + 1)) 1`.
      have hX : (X * u) ^ (m + 1) * u⁻¹ ^ (m + 1) = X ^ (m + 1) := by
        rw [mul_pow, mul_assoc, ← mul_pow, mul_comm u, hvu, one_pow, mul_one]
      rw [← coe_pow, mul_left_comm, ← coe_mul, hX, ofPowerSeries_X_pow]
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
