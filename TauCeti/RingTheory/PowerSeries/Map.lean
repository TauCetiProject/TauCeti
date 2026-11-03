/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.Restricted
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Map

/-!
# Coefficient maps on restricted power series

A bounded coefficient homomorphism acts on restricted power series through the multivariate
`TauCeti.MvPowerSeries.restrictedMap`. Here we express its underlying univariate series and
its compatibility with the polynomial inclusion. These formulas let polynomial factorizations
and division identities be transported in the restricted-series ring.
-/

public section

namespace TauCeti.PowerSeries

open TauCeti.MvPowerSeries

variable {R S : Type*} [NormedRing R] [IsUltrametricDist R]
  [NormedRing S] [IsUltrametricDist S] {c : ℝ}
  (φ : R →+* S) {C : ℝ} (hφ : ∀ a, ‖φ a‖ ≤ C * ‖a‖)

/-- The bounded restricted map acts as the coefficient map on underlying univariate series. -/
theorem coe_restrictedMap_powerSeries (f : PowerSeries.IsRestricted.subring (R := R) c) :
    (restrictedMap φ hφ f : PowerSeries S) = PowerSeries.map φ f :=
  -- PowerSeries.map is MvPowerSeries.map with variable type Unit.
  coe_restrictedMap φ hφ f

section CommRing

variable {R S : Type*} [NormedCommRing R] [IsUltrametricDist R]
  [NormedCommRing S] [IsUltrametricDist S]
  (φ : R →+* S) {C : ℝ} (hφ : ∀ a, ‖φ a‖ ≤ C * ‖a‖)

/-- Bounded coefficient maps commute with the inclusion of polynomials into restricted series. -/
@[simp]
theorem restrictedMap_polynomialToRestricted (p : Polynomial R) :
    restrictedMap φ hφ (polynomialToRestricted c p) = polynomialToRestricted c (p.map φ) := by
  apply Subtype.ext
  simp only [coe_restrictedMap_powerSeries, coe_polynomialToRestricted,
    Polynomial.polynomial_map_coe]

end CommRing

end TauCeti.PowerSeries
