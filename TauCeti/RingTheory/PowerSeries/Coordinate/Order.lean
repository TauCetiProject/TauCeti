/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.Coordinate.Basic

/-!
# Formal coordinates preserve order

Composition on either side with a formal coordinate preserves the order of a power series.
These statements hold over arbitrary commutative rings, including rings with zero divisors:
the inverse coordinate gives the reverse order inequality. They allow orders of formal-group
multiplication series to be compared in different coordinates.
-/

public section

namespace TauCeti.FormalCoordinate

variable {R : Type*} [CommRing R]

/-- Substituting a formal coordinate into a power series preserves its order. -/
@[simp]
theorem order_subst_toPowerSeries (φ : FormalCoordinate R) (f : PowerSeries R) :
    PowerSeries.order (PowerSeries.subst φ.toPowerSeries f) = f.order := by
  apply le_antisymm
  · have h := PowerSeries.le_order_subst_left' (φ⁻¹.constantCoeff_toPowerSeries)
      (φ := PowerSeries.subst φ.toPowerSeries f)
    rwa [φ.subst_subst φ⁻¹ f, mul_inv_cancel, toPowerSeries_one,
      PowerSeries.X_subst] at h
  · exact PowerSeries.le_order_subst_left' φ.constantCoeff_toPowerSeries

/-- Applying a formal coordinate to a series with zero constant coefficient preserves its order. -/
@[simp]
theorem order_subst (φ : FormalCoordinate R) {f : PowerSeries R}
    (hf : PowerSeries.constantCoeff f = 0) :
    PowerSeries.order (PowerSeries.subst f φ.toPowerSeries) = f.order := by
  apply le_antisymm
  · have h := PowerSeries.le_order_subst_right'
      (PowerSeries.constantCoeff_subst_eq_zero hf _ φ.constantCoeff_toPowerSeries)
      φ⁻¹.constantCoeff_toPowerSeries
    rwa [φ.subst_inv_subst (PowerSeries.HasSubst.of_constantCoeff_zero' hf)] at h
  · exact PowerSeries.le_order_subst_right' hf φ.constantCoeff_toPowerSeries

end TauCeti.FormalCoordinate
