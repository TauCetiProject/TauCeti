/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Basic

import Mathlib.Algebra.MvPolynomial.Coeff

/-!
# Polynomial products as power series

`MvPolynomial.coe_finsuppProd_pow` moves a finitely supported product of polynomial powers
through the coercion to multivariate power series. It lets coefficient computations for such
products use the polynomial API, for example when substituting polynomials into power series.
The coefficient semiring need only be commutative; no norm or topology is required.

`MvPowerSeries.coeff_X_add_X_pow` is the binomial formula for the coefficients of `(X + Y) ^ n` in
`R⟦X, Y⟧`, the power-series counterpart of `MvPolynomial.coeff_add_pow`, over any semiring.
-/

public section

namespace MvPolynomial

variable {σ τ R : Type*} [CommSemiring R]

/-- The coercion of polynomials to power series commutes with products of powers. -/
@[simp, norm_cast]
theorem coe_finsuppProd_pow (a : σ → MvPolynomial τ R) (d : σ →₀ ℕ) :
    ((d.prod fun s n ↦ a s ^ n : MvPolynomial τ R) : MvPowerSeries τ R) =
      d.prod fun s n ↦ (a s : MvPowerSeries τ R) ^ n := by
  simpa only [map_pow, coeToMvPowerSeries.ringHom_apply] using
    map_finsuppProd (coeToMvPowerSeries.ringHom (σ := τ) (R := R)) d (fun s n ↦ a s ^ n)

end MvPolynomial

namespace MvPowerSeries

variable {R : Type*} [Semiring R]

/-- The coefficient of `X^(d 0) Y^(d 1)` in `(X + Y) ^ n` is `n.choose (d 0)` if
`d 0 + d 1 = n`, and `0` otherwise. -/
theorem coeff_X_add_X_pow (d : Fin 2 →₀ ℕ) (n : ℕ) :
    coeff d ((X 0 + X 1 : MvPowerSeries (Fin 2) R) ^ n) =
      if d 0 + d 1 = n then (n.choose (d 0) : R) else 0 := by
  -- Over `ℕ` this is `MvPolynomial.coeff_add_pow`; it maps to any semiring.
  have hnat : coeff d ((X 0 + X 1 : MvPowerSeries (Fin 2) ℕ) ^ n) =
      if d 0 + d 1 = n then n.choose (d 0) else 0 := by
    simpa [← MvPolynomial.coeff_coe] using MvPolynomial.coeff_add_pow (R := ℕ) d n
  simpa only [← coeff_map, map_pow, map_add, map_X, Nat.coe_castRingHom, apply_ite,
    Nat.cast_zero] using congrArg (Nat.castRingHom R) hnat

end MvPowerSeries
