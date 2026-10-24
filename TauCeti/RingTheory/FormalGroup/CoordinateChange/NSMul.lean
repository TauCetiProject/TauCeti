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

open MvPowerSeries

namespace TauCeti.FormalCoordinate

variable {R : Type*} [CommRing R]

/-- A coordinate change intertwines multiplication by `n`:
`[n]_{φ • F}(φ(T)) = φ([n]_F(T))`. No commutativity assumption on `F` is needed. -/
theorem subst_nsmulSeries (φ : FormalCoordinate R) (F : FormalGroup R) (n : ℕ) :
    PowerSeries.subst φ.toPowerSeries ((φ • F).nsmulSeries n) =
      PowerSeries.subst (F.nsmulSeries n) φ.toPowerSeries := by
  induction n with
  | zero =>
      simp [← PowerSeries.coe_substAlgHom φ.hasSubst]
  | succ n ih =>
      rw [FormalGroup.nsmulSeries_succ, FormalGroup.nsmulSeries_succ,
        PowerSeries.subst_def _ (subst _ _),
        subst_comp_subst_apply ((φ • F).hasSubst_nsmulSeries_X n) φ.hasSubst.const]
      have hpair : (fun i ↦ subst (fun _ ↦ φ.toPowerSeries)
          ((![(φ • F).nsmulSeries n, PowerSeries.X] : Fin 2 → PowerSeries R) i)) =
          ![PowerSeries.subst (F.nsmulSeries n) φ.toPowerSeries, φ.toPowerSeries] := by
        funext i
        fin_cases i
        · exact ih
        · exact PowerSeries.subst_X φ.hasSubst
      rw [hpair]
      simpa only [PowerSeries.X_subst] using
        FormalGroup.subst_smul_toPowerSeries_subst φ F
          (PowerSeries.HasSubst.of_constantCoeff_zero' (F.constantCoeff_nsmulSeries n))
          PowerSeries.HasSubst.X'

/-- The multiplication series in the new coordinate is the conjugate
`[n]_{φ • F} = φ ∘ [n]_F ∘ φ⁻¹`. -/
theorem nsmulSeries_smul (φ : FormalCoordinate R) (F : FormalGroup R) (n : ℕ) :
    (φ • F).nsmulSeries n =
      PowerSeries.subst
        (PowerSeries.subst φ⁻¹.toPowerSeries (F.nsmulSeries n)) φ.toPowerSeries := by
  have h := congrArg (PowerSeries.subst φ⁻¹.toPowerSeries) (φ.subst_nsmulSeries F n)
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
  have h := congrArg PowerSeries.order (φ.subst_nsmulSeries F n)
  simpa only [φ.order_subst_toPowerSeries,
    φ.order_subst (F.constantCoeff_nsmulSeries n)] using h

/-- A multiplication series vanishes in the new coordinate exactly when it vanishes in the old
one. In particular, changing coordinates preserves exponent conditions on the formal group. -/
@[simp]
theorem nsmulSeries_smul_eq_zero_iff (φ : FormalCoordinate R) (F : FormalGroup R) (n : ℕ) :
    (φ • F).nsmulSeries n = 0 ↔ F.nsmulSeries n = 0 := by
  rw [← PowerSeries.order_eq_top, φ.order_nsmulSeries_smul, PowerSeries.order_eq_top]

end TauCeti.FormalCoordinate
