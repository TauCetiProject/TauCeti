/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Binomial
public import Mathlib.RingTheory.PowerSeries.Substitution

/-!
# Substitution of power series: orders, and the binomial series

Mathlib substitutes a power series `b` with nilpotent constant coefficient into a power series
`f` through `PowerSeries.subst b f`, and records the side condition on `b` as
`PowerSeries.HasSubst b`.

Over a ring without zero divisors, substituting a series `φ` of zero constant coefficient
multiplies orders: `ord (f (φ)) = ord φ * ord f`. Mathlib records only the inequality
`PowerSeries.le_order_subst`. The equality shows that substitution of a nonzero such `φ` is
injective, which is what extends it to Laurent series by passing to fraction fields.

This file also records that the substitution `X ↦ (1 + X) ^ u - 1`, for a binomial series
`(1 + X) ^ u`, is legitimate: it is the change of variable relating the power-series coordinates
of a completed group algebra attached to two topological generators.

## Main results

* `PowerSeries.order_subst`: `ord (f (φ)) = ord φ * ord f` when `φ` has zero constant
  coefficient.
* `PowerSeries.subst_eq_zero_iff`: substitution of a nonzero `φ` of zero constant coefficient
  has trivial kernel.
* `PowerSeries.toNat_order_ne_zero`: such a `φ` has positive integer order.
* `TauCeti.hasSubst_binomialSeries_sub_one`: `(1 + X) ^ u - 1` can be substituted.
-/

public section

namespace PowerSeries

/-- A nonzero power series of zero constant coefficient has positive integer order, so it
multiplies orders under substitution by a positive integer. -/
theorem toNat_order_ne_zero {R : Type*} [Semiring R] {φ : R⟦X⟧} (hφ : constantCoeff φ = 0)
    (hφ₀ : φ ≠ 0) : φ.order.toNat ≠ 0 := by
  rw [Ne, ENat.toNat_eq_zero, not_or, order_eq_top]
  exact ⟨order_ne_zero_iff_constCoeff_eq_zero.mpr hφ, hφ₀⟩

variable {R : Type*} [CommRing R] [NoZeroDivisors R] {φ : R⟦X⟧}

/-- Substituting a power series `φ` of zero constant coefficient multiplies orders:
`ord (f (φ)) = ord φ * ord f`. -/
theorem order_subst (hφ : constantCoeff φ = 0) (f : R⟦X⟧) :
    PowerSeries.order (f.subst φ) = φ.order * f.order := by
  have ha : HasSubst φ := .of_constantCoeff_zero' hφ
  rcases eq_or_ne f 0 with rfl | hf
  · rw [← coe_substAlgHom ha, map_zero, order_zero, ENat.mul_top]
    exact order_ne_zero_iff_constCoeff_eq_zero.mpr hφ
  have : Nontrivial R := have := nontrivial_of_ne f 0 hf; (C (R := R)).domain_nontrivial
  -- Write `f = X ^ m * g` with `m = ord f`; then `g (φ)` has the nonzero constant coefficient
  -- of `g`, so it has order zero.
  have hg : PowerSeries.order (f.divXPowOrder.subst φ) = 0 := by
    rw [← not_ne_iff, order_ne_zero_iff_constCoeff_eq_zero]
    have h := constantCoeff_subst_of_constantCoeff_zero hφ f.divXPowOrder
    rw [Algebra.algebraMap_self_apply] at h
    -- `h` is stated with the multivariate constant coefficient, which is the univariate one
    rw [show constantCoeff (f.divXPowOrder.subst φ) = f.divXPowOrder.constantCoeff from h]
    exact constantCoeff_divXPowOrder_eq_zero_iff.not.mpr hf
  nth_rw 1 [← X_pow_order_mul_divXPowOrder (f := f)]
  rw [subst_mul ha, subst_pow ha, subst_X ha, order_mul, order_pow, hg, add_zero, nsmul_eq_mul,
    coe_toNat_order hf, mul_comm]

/-- Substituting a nonzero power series `φ` of zero constant coefficient sends only `0` to `0`. -/
theorem subst_eq_zero_iff (hφ : constantCoeff φ = 0) (hφ₀ : φ ≠ 0) {f : R⟦X⟧} :
    (f.subst φ : R⟦X⟧) = 0 ↔ f = 0 := by
  have h₀ := order_ne_zero_iff_constCoeff_eq_zero.mpr hφ
  have h₁ : φ.order ≠ ⊤ := order_eq_top.not.mpr hφ₀
  rw [← order_eq_top, ← order_eq_top (φ := f), order_subst hφ]
  exact WithTop.mul_eq_top_iff.trans (by tauto)

end PowerSeries

namespace TauCeti

open PowerSeries

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- The binomial series `(1 + X) ^ u - 1` has constant coefficient zero, so power series can be
substituted into it. -/
theorem hasSubst_binomialSeries_sub_one [BinomialRing R] (u : R) :
    HasSubst (binomialSeries S u - 1) :=
  HasSubst.of_constantCoeff_zero' (by simp)

end TauCeti
