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

`MvPowerSeries.mem_map_rangeS` says that a power series is the image under `map f` of a power
series exactly when each of its coefficients is in the range of `f`, as Mathlib's
`Polynomial.mem_map_rangeS` does for polynomials. For the inclusion of a subring, it lifts a power
series with coefficients in the subring to a power series over the subring.
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

section Map

variable {σ S : Type*} [Semiring S] (f : R →+* S)

/-- A power series over `S` is in the range of `map f` if and only if each of its coefficients is
in the range of `f`. This is the power-series form of Mathlib's `Polynomial.mem_map_rangeS`. -/
theorem mem_map_rangeS {p : MvPowerSeries σ S} :
    p ∈ (map (σ := σ) f).rangeS ↔ ∀ d, coeff d p ∈ f.rangeS := by
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨q, rfl⟩ d
    rw [coeff_map]
    exact f.mem_rangeS_self _
  · simp only [RingHom.mem_rangeS] at h
    choose c hc using h
    -- a power series is its coefficient function
    let q : MvPowerSeries σ R := c
    exact ⟨q, ext fun d ↦ by rw [coeff_map, coeff_apply]; exact hc d⟩

end Map

end MvPowerSeries
