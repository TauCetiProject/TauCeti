/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.LFunction
import Mathlib.FieldTheory.Finite.Basic
public import TauCeti.NumberTheory.LSeries.Continuation

/-!
# Multiplicativity of the `L`-function of a Weierstrass curve

Mathlib's `WeierstrassCurve.LFunction` is the formal Euler product, over the primes of a number
field, of the local Euler factors `WeierstrassCurve.localEulerFactor`, each the Dirichlet series
`1 / f(q⁻ˢ)` of a local polynomial `f` with constant term `1`. This file shows that every local
factor, and hence the Euler product, is a multiplicative arithmetic function. In particular the
first coefficient of the `L`-function is `1`, so its `L`-series is not the zero series, and every
analytic continuation of it (`LSeries.IsContinuationOn`) vanishes to finite order at each point of
its domain. This makes the order of vanishing and the leading Taylor coefficient of the `L`-function
at `s = 1`, the analytic side of the Birch–Swinnerton-Dyer conjecture, honest finite data.

## Main results

* `WeierstrassCurve.isMultiplicative_localEulerFactor`: each local Euler factor is multiplicative.
* `WeierstrassCurve.isMultiplicative_LFunction`: the `L`-function is multiplicative.
* `WeierstrassCurve.LFunction_apply_one`: its first coefficient is `1`.
* `WeierstrassCurve.analyticOrderAt_ne_top_of_isContinuationOn`: a continuation of the `L`-series
  has finite order of vanishing at each point of its domain.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], Appendix C, §16.
-/

public section

namespace WeierstrassCurve

open ArithmeticFunction

section LocalField

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {K : Type*}
  [Field K] [Algebra R K] [IsFractionRing R K] (W : WeierstrassCurve K)

/-- The local power series `1 / f(T)` of a Weierstrass curve has constant term `1`. -/
@[simp]
theorem constantCoeff_localPowerSeries : (W.localPowerSeries R).constantCoeff = 1 := by
  simp [localPowerSeries, PowerSeries.constantCoeff_invOfUnit]

/-- **The local Euler factor of a Weierstrass curve is multiplicative.** When the residue field is
finite its order is a prime power; otherwise the factor is the junk value `1`. -/
theorem isMultiplicative_localEulerFactor : (W.localEulerFactor R).IsMultiplicative := by
  by_cases hq : IsPrimePow (Nat.card (IsLocalRing.ResidueField R))
  · exact isMultiplicative_ofPowerSeries_of_isPrimePow _ hq _ (W.constantCoeff_localPowerSeries R)
  · have : Nat.card (IsLocalRing.ResidueField R) = 0 := by
      by_contra h
      have := Nat.finite_of_card_ne_zero h
      let := Fintype.ofFinite (IsLocalRing.ResidueField R)
      exact hq (Nat.card_eq_fintype_card (α := IsLocalRing.ResidueField R) ▸
        FiniteField.isPrimePow_card _)
    -- `ofPowerSeries 0 f` is the junk value `f.constantCoeff`, here `1`.
    rw [localEulerFactor, this]
    simp [ofPowerSeries]

end LocalField

section NumberField

variable {K : Type*} [Field K] [NumberField K] (W : WeierstrassCurve K)

/-- **The `L`-function of a Weierstrass curve is multiplicative**, as an Euler product of
multiplicative local factors. -/
theorem isMultiplicative_LFunction : W.LFunction.IsMultiplicative :=
  isMultiplicative_eulerProduct _ fun _ ↦ isMultiplicative_localEulerFactor _ _

/-- **The first coefficient of the `L`-function is `1`.** -/
@[simp]
theorem LFunction_apply_one : W.LFunction 1 = 1 :=
  W.isMultiplicative_LFunction.map_one

/-- **A continuation of the `L`-series vanishes to finite order**: if `F` continues the
`L`-series of `W` to a connected open set `U`, then `F` has finite order of vanishing at every
point of `U`. -/
theorem analyticOrderAt_ne_top_of_isContinuationOn {F : ℂ → ℂ} {U : Set ℂ}
    (h : LSeries.IsContinuationOn ((↑) ∘ W.LFunction) F U) {s : ℂ} (hs : s ∈ U) :
    analyticOrderAt F s ≠ ⊤ :=
  h.analyticOrderAt_ne_top ⟨1, one_ne_zero, by simp⟩ hs

end NumberField

end WeierstrassCurve
