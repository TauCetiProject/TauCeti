/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.NSMul.Basic

/-!
# Base change for multiplication series of formal groups

The multiplication series `[n]_F` of a formal group law is natural in its coefficient ring:
applying a ring homomorphism to its coefficients gives the multiplication series of the
base-changed formal group.

## Main results

* `FormalGroup.map_nsmulSeries`: `[n]_F` commutes with base change.
* `FormalGroup.coeff_nsmulSeries_map`: coefficientwise form of the base-change identity.
-/

public section

open MvPowerSeries

namespace FormalGroup

variable {R S : Type*} [CommRing R] [CommRing S]

/-- Multiplication by `n` commutes with base change of the coefficient ring. -/
@[simp]
theorem map_nsmulSeries (F : FormalGroup R) (f : R →+* S) (n : ℕ) :
    PowerSeries.map f (F.nsmulSeries n) = (F.map f).nsmulSeries n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [nsmulSeries_succ, nsmulSeries_succ]
      let a : Fin 2 → PowerSeries R := ![F.nsmulSeries n, PowerSeries.X]
      have ha : HasSubst a := F.hasSubst_nsmulSeries_X n
      rw [map_toPowerSeries]
      -- `PowerSeries.map` is by definition `MvPowerSeries.map` in the unique variable
      change MvPowerSeries.map f (subst a F.toPowerSeries) = _
      rw [MvPowerSeries.map_subst ha]
      congr 1
      funext i
      fin_cases i
      · exact ih
      · exact PowerSeries.map_X f

/-- The coefficients of multiplication series are preserved by base change. -/
@[simp]
theorem coeff_nsmulSeries_map (F : FormalGroup R) (f : R →+* S) (n k : ℕ) :
    PowerSeries.coeff k ((F.map f).nsmulSeries n) = f (PowerSeries.coeff k (F.nsmulSeries n)) := by
  rw [← F.map_nsmulSeries f n, PowerSeries.coeff_map]

end FormalGroup
