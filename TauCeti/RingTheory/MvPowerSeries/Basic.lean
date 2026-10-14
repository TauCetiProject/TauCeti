/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Basic

/-!
# Polynomial products as power series

`MvPolynomial.coe_finsuppProd_pow` moves a finitely supported product of polynomial powers
through the coercion to multivariate power series. It lets coefficient computations for such
products use the polynomial API, for example when substituting polynomials into power series.
The coefficient semiring need only be commutative; no norm or topology is required.
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
