/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.Coordinate.Basic
import TauCeti.RingTheory.MvPowerSeries.Order
import TauCeti.RingTheory.MvPowerSeries.Substitution

/-!
# Order under a change of formal coordinate

`TauCeti.FormalCoordinate.order_subst` shows that applying the same invertible change of
coordinate to each variable of a multivariate power series preserves total order. It uses
`MvPowerSeries.order_le_order_subst` in both directions and Mathlib's substitution composition
identity.
-/

public section

open MvPowerSeries

namespace TauCeti.FormalCoordinate

/-- Substituting `X i ↦ φ(X i)` in every variable of `f` preserves total order. -/
theorem order_subst {R σ : Type*} [CommRing R] (φ : FormalCoordinate R)
    (f : MvPowerSeries σ R) :
    (f.subst (fun i ↦ PowerSeries.subst (X i : MvPowerSeries σ R) φ.toPowerSeries)).order =
      f.order := by
  let a (ψ : FormalCoordinate R) (i : σ) :=
    PowerSeries.subst (X i : MvPowerSeries σ R) ψ.toPowerSeries
  have hzero (ψ : FormalCoordinate R) (i : σ) : constantCoeff (a ψ i) = 0 := by
    exact PowerSeries.constantCoeff_subst_eq_zero (constantCoeff_X i)
      ψ.toPowerSeries ψ.constantCoeff_toPowerSeries
  have hsubst (ψ : FormalCoordinate R) : HasSubst (a ψ) := by
    obtain ⟨g, hg⟩ := PowerSeries.X_dvd_iff.mpr ψ.constantCoeff_toPowerSeries
    have ha : a ψ = X * (fun i ↦ PowerSeries.subst (X i : MvPowerSeries σ R) g) := by
      ext i : 1
      simp only [a, hg, Pi.mul_apply, PowerSeries.subst_mul (PowerSeries.HasSubst.X i),
        PowerSeries.subst_X (PowerSeries.HasSubst.X i)]
    rw [ha]
    exact HasSubst.X.mul_right _
  have hcancel : (f.subst (a φ)).subst (a φ⁻¹) = f := by
    rw [subst_comp_subst_apply (hsubst φ) (hsubst φ⁻¹)]
    have hX (i : σ) : (a φ i).subst (a φ⁻¹) = X i := by
      dsimp only [a]
      rw [subst_powerSeriesSubst (hsubst φ⁻¹) (PowerSeries.HasSubst.X i),
        subst_X (hsubst φ⁻¹), φ.subst_subst_inv (PowerSeries.HasSubst.X i)]
    simp only [hX, subst_self, id_eq]
  refine le_antisymm ?_ (order_le_order_subst (hsubst φ) (hzero φ) f)
  calc
    (f.subst (a φ)).order ≤ ((f.subst (a φ)).subst (a φ⁻¹)).order :=
      order_le_order_subst (hsubst φ⁻¹) (hzero φ⁻¹) _
    _ = f.order := congrArg MvPowerSeries.order hcancel

end TauCeti.FormalCoordinate
