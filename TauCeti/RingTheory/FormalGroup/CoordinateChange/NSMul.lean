/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.CoordinateChange.Basic
public import TauCeti.RingTheory.FormalGroup.NSMul.Basic
public import TauCeti.RingTheory.PowerSeries.Coordinate.Order

/-!
# Multiplication series under a change of coordinate

A coordinate change `φ` intertwines multiplication by every natural number on `F` and `φ • F`.
Consequently the multiplication series transform by conjugation, and their orders are independent
of the chosen coordinate, even over coefficient rings with zero divisors. In characteristic `p`
this is the coordinate comparison needed for the height of a formal group.

## References

* J. Silverman, *The Arithmetic of Elliptic Curves*, IV.7.
-/

public section

namespace TauCeti.FormalCoordinate

variable {R : Type*} [CommRing R]

/-- The multiplication series in the new coordinate is the conjugate
`[n]_{φ • F} = φ ∘ [n]_F ∘ φ⁻¹`. -/
theorem nsmulSeries_smul (φ : FormalCoordinate R) (F : FormalGroup R) (n : ℕ) :
    (φ • F).nsmulSeries n =
      PowerSeries.subst
        (PowerSeries.subst φ⁻¹.toPowerSeries (F.nsmulSeries n)) φ.toPowerSeries := by
  have hintertwine := (FormalGroup.smulIso φ F).toHom.subst_nsmulSeries n
  rw [FormalGroup.smulIso_toHom_toPowerSeries] at hintertwine
  have h := congrArg (PowerSeries.subst φ⁻¹.toPowerSeries) hintertwine.symm
  rw [φ.subst_subst φ⁻¹, mul_inv_cancel, toPowerSeries_one, PowerSeries.X_subst,
    PowerSeries.subst_comp_subst_apply
      (PowerSeries.HasSubst.of_constantCoeff_zero' (F.constantCoeff_nsmulSeries n))
      φ⁻¹.hasSubst] at h
  exact h

/-- The order of a multiplication series is independent of the coordinate. This also includes
identically zero multiplication series, whose order is infinite. -/
@[simp]
theorem order_nsmulSeries_smul (φ : FormalCoordinate R) (F : FormalGroup R) (n : ℕ) :
    ((φ • F).nsmulSeries n).order = (F.nsmulSeries n).order := by
  rw [φ.nsmulSeries_smul, φ.order_subst (PowerSeries.constantCoeff_subst_eq_zero
    φ⁻¹.constantCoeff_toPowerSeries _ (F.constantCoeff_nsmulSeries n)),
    φ⁻¹.order_subst_toPowerSeries]

/-- A multiplication series vanishes in the new coordinate exactly when it vanishes in the old
one. In particular, changing coordinates preserves exponent conditions on the formal group. -/
@[simp]
theorem nsmulSeries_smul_eq_zero_iff (φ : FormalCoordinate R) (F : FormalGroup R) (n : ℕ) :
    (φ • F).nsmulSeries n = 0 ↔ F.nsmulSeries n = 0 := by
  rw [← PowerSeries.order_eq_top, φ.order_nsmulSeries_smul, PowerSeries.order_eq_top]

end TauCeti.FormalCoordinate
