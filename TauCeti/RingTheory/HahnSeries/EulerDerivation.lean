/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.HahnSeries.Multiplication

/-!
# Euler derivations of Hahn series

Let `w : Γ →+ R` be an additive weight on the exponent monoid `Γ` with values in a commutative
semiring `R`. Multiplying the coefficient of `t ^ g` by `w g` is an `R`-derivation of
`HahnSeries Γ R`, the **Euler derivation** `θ_w`: it can only shrink supports, and it satisfies the
Leibniz rule because `w (g + h) = w g + w h` for every pair of exponents `(g, h)` contributing to a
coefficient of a product. It is the infinitesimal counterpart of the twist by a character
(`HahnSeries.twist`).

For Laurent series and `w = Int.cast`, `θ_w` is the Euler operator `X * d/dX`. For rational
exponents over a field of characteristic zero and `w = Rat.cast`, it is `t * d/dt`, so that the
derivative of Puiseux series, `t ^ q ↦ q t ^ (q - 1)`, is `t⁻¹ θ_w`.

## Main definitions

* `HahnSeries.eulerDerivation w`: the `R`-derivation of `HahnSeries Γ R` multiplying the
  coefficient of `t ^ g` by `w g`.

## Main results

* `HahnSeries.coeff_eulerDerivation`: the coefficients of `θ_w x`.
* `HahnSeries.support_eulerDerivation_subset`: `θ_w` does not enlarge supports.
* `HahnSeries.eulerDerivation_single`: `θ_w (r t ^ g) = w g r t ^ g`.
-/

public section

open Finset

namespace HahnSeries

variable {Γ R : Type*} [AddCommMonoid Γ] [PartialOrder Γ] [IsOrderedCancelAddMonoid Γ]
  [CommSemiring R]

/-- The coefficientwise Euler operator before bundling: its coefficient of `t ^ g` is `w g` times
that of `x`. -/
private def eulerFun (w : Γ →+ R) (x : HahnSeries Γ R) : HahnSeries Γ R where
  coeff g := w g * x.coeff g
  isPWO_support' := x.isPWO_support.mono (Function.support_mul_subset_right _ _)

omit [IsOrderedCancelAddMonoid Γ] in
private theorem coeff_eulerFun (w : Γ →+ R) (x : HahnSeries Γ R) (g : Γ) :
    (eulerFun w x).coeff g = w g * x.coeff g :=
  rfl

omit [IsOrderedCancelAddMonoid Γ] in
private theorem support_eulerFun_subset (w : Γ →+ R) (x : HahnSeries Γ R) :
    (eulerFun w x).support ⊆ x.support :=
  Function.support_mul_subset_right _ _

/-- The coefficient of `t ^ a` in `x * y`, summed over the antidiagonal of the supports of `x` and
`y`, with each term weighted by `w` of its first exponent. This is the coefficient of
`eulerFun w x * y`. -/
private theorem coeff_eulerFun_mul (w : Γ →+ R) (x y : HahnSeries Γ R) (a : Γ) :
    (eulerFun w x * y).coeff a = ∑ ij ∈ antidiagonal x.isPWO_support y.isPWO_support a,
      w ij.1 * (x.coeff ij.1 * y.coeff ij.2) := by
  rw [coeff_mul_left' x.isPWO_support (support_eulerFun_subset w x)]
  exact sum_congr rfl fun ij _ ↦ by rw [coeff_eulerFun, mul_assoc]

/-- The **Euler derivation** of Hahn series attached to an additive weight `w : Γ →+ R`: the
`R`-derivation multiplying the coefficient of `t ^ g` by `w g`. -/
noncomputable def eulerDerivation (w : Γ →+ R) : Derivation R (HahnSeries Γ R) (HahnSeries Γ R)
    where
  toFun := eulerFun w
  map_add' x y := by
    ext g
    rw [coeff_eulerFun, coeff_add, coeff_add, coeff_eulerFun, coeff_eulerFun, mul_add]
  map_smul' c x := by
    ext g
    rw [coeff_eulerFun, coeff_smul, coeff_smul, coeff_eulerFun, RingHom.id_apply, smul_eq_mul,
      smul_eq_mul, mul_left_comm]
  map_one_eq_zero' := by
    ext g
    rw [LinearMap.coe_mk, AddHom.coe_mk, coeff_eulerFun, coeff_one, coeff_zero]
    split_ifs with h
    · rw [h, map_zero, zero_mul]
    · rw [mul_zero]
  leibniz' x y := by
    ext a
    -- Both products are summed over the antidiagonal of the supports of `x` and `y`; on it,
    -- `w a = w i + w j`.
    simp only [LinearMap.coe_mk, AddHom.coe_mk, smul_eq_mul, coeff_add]
    rw [mul_comm y, coeff_eulerFun_mul, coeff_mul_right' y.isPWO_support
      (support_eulerFun_subset w y), coeff_eulerFun, coeff_mul, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun ij hij ↦ ?_
    rw [coeff_eulerFun, ← (mem_antidiagonal.1 hij).2.2, map_add]
    ring

/-- The Euler derivation multiplies the coefficient of `t ^ g` by `w g`. -/
@[simp]
theorem coeff_eulerDerivation (w : Γ →+ R) (x : HahnSeries Γ R) (g : Γ) :
    (eulerDerivation w x).coeff g = w g * x.coeff g :=
  (rfl)

/-- The Euler derivation does not enlarge supports. -/
theorem support_eulerDerivation_subset (w : Γ →+ R) (x : HahnSeries Γ R) :
    (eulerDerivation w x).support ⊆ x.support :=
  support_eulerFun_subset w x

/-- The Euler derivation of the monomial `r t ^ g` is `w g r t ^ g`. -/
@[simp]
theorem eulerDerivation_single (w : Γ →+ R) (g : Γ) (r : R) :
    eulerDerivation w (single g r) = single g (w g * r) := by
  ext h
  rw [coeff_eulerDerivation, coeff_single, coeff_single]
  split_ifs with hh
  · rw [hh]
  · rw [mul_zero]

end HahnSeries
