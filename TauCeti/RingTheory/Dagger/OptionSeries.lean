/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Dagger.WashnitzerAlgebra
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Iterate

/-!
# Separating a variable in overconvergent power series

Separating `Y = X none` in an overconvergent series in `Option σ` gives a formal univariate
series whose coefficients are overconvergent in `σ`. The map `washnitzerAlgebra.optionSeries`
is injective and agrees with `MvPowerSeries.optionEquivLeft` on underlying formal series.
It provides the coefficient ring for polynomial remainders in overconvergent Weierstrass
division. No claim is made that an arbitrary series of overconvergent coefficients is itself
overconvergent: the coefficients must satisfy a common radius bound.

## References

* E. Grosse-Klönne, *Rigid analytic spaces with overconvergent structure sheaf*,
  J. reine angew. Math. 519 (2000), §1.3.
-/

public section

namespace TauCeti.Dagger

open _root_.MvPowerSeries

variable {σ R : Type*} [NormedCommRing R] [IsUltrametricDist R]

/-- Every coefficient slice of an overconvergent series is overconvergent. -/
theorem coeff_optionEquivLeft_mem_washnitzerAlgebra {f : MvPowerSeries (Option σ) R}
    (hf : f ∈ washnitzerAlgebra (Option σ) R) (m : ℕ) :
    PowerSeries.coeff m (optionEquivLeft σ R f) ∈ washnitzerAlgebra σ R := by
  obtain ⟨ρ, hρ, hf⟩ := mem_washnitzerAlgebra.mp hf
  exact mem_washnitzerAlgebra.mpr
    ⟨ρ, hρ, Huber.isRestricted_coeff_optionEquivLeft (zero_lt_one.trans hρ) hf m⟩

namespace washnitzerAlgebra

/-- Forgetting overconvergence coefficientwise is injective on formal power series. -/
theorem map_val_injective : Function.Injective
    (PowerSeries.map ((washnitzerAlgebra σ R).val :
      washnitzerAlgebra σ R →+* MvPowerSeries σ R)) :=
  PowerSeries.map_injective _ Subtype.val_injective

/-- Separate `Y = X none`, retaining overconvergent coefficients in the other variables. -/
noncomputable def optionSeries :
    washnitzerAlgebra (Option σ) R →ₐ[R] PowerSeries (washnitzerAlgebra σ R) := by
  let F (f : washnitzerAlgebra (Option σ) R) : PowerSeries (washnitzerAlgebra σ R) :=
    PowerSeries.mk fun m ↦ ⟨_, coeff_optionEquivLeft_mem_washnitzerAlgebra f.2 m⟩
  have hF (f) : PowerSeries.map ((washnitzerAlgebra σ R).val :
    washnitzerAlgebra σ R →+* MvPowerSeries σ R) (F f) =
      optionEquivLeft σ R (f : MvPowerSeries (Option σ) R) := by
    ext m : 1
    simp [F, Subalgebra.val_apply]
  have hi := map_val_injective (σ := σ) (R := R)
  refine
    { toFun := F
      map_zero' := hi (by rw [hF]; simp)
      map_one' := hi (by rw [hF]; simp)
      map_add' := fun f g ↦ hi (by rw [map_add, hF, hF, hF]; simp)
      map_mul' := fun f g ↦ hi (by rw [map_mul, hF, hF, hF]; simp)
      commutes' := fun a ↦ hi ?_ }
  rw [hF]
  simp [PowerSeries.algebraMap_apply]

/-- The separated coefficients are the formal coefficient slices. -/
@[simp]
theorem coe_coeff_optionSeries (f : washnitzerAlgebra (Option σ) R) (m : ℕ) :
    (PowerSeries.coeff (R := washnitzerAlgebra σ R) m (optionSeries f) : MvPowerSeries σ R) =
      PowerSeries.coeff m (optionEquivLeft σ R (f : MvPowerSeries (Option σ) R)) := by
  simp [optionSeries]

/-- Forgetting overconvergence of the coefficients recovers the formal variable separation. -/
@[simp]
theorem map_val_optionSeries (f : washnitzerAlgebra (Option σ) R) :
    PowerSeries.map ((washnitzerAlgebra σ R).val :
      washnitzerAlgebra σ R →+* MvPowerSeries σ R) (optionSeries f) =
      optionEquivLeft σ R (f : MvPowerSeries (Option σ) R) := by
  ext m : 1
  simp [Subalgebra.val_apply]

/-- Variable separation is injective. -/
theorem optionSeries_injective : Function.Injective (optionSeries (σ := σ) (R := R)) := by
  intro f g h
  apply Subtype.ext
  apply (optionEquivLeft σ R).injective
  have hm := congrArg (PowerSeries.map ((washnitzerAlgebra σ R).val :
    washnitzerAlgebra σ R →+* MvPowerSeries σ R)) h
  rwa [map_val_optionSeries, map_val_optionSeries] at hm

/-- The separated variable becomes the univariate variable. -/
@[simp]
theorem optionSeries_X_none : optionSeries (X (Option σ) R none) = PowerSeries.X := by
  apply map_val_injective
  rw [map_val_optionSeries, coe_X, optionEquivLeft_X_none, PowerSeries.map_X]

/-- A remaining variable becomes a constant coefficient. -/
@[simp]
theorem optionSeries_X_some (i : σ) :
    optionSeries (X (Option σ) R (some i)) = PowerSeries.C (X σ R i) := by
  apply map_val_injective
  rw [map_val_optionSeries, coe_X, optionEquivLeft_X_some, PowerSeries.map_C]
  exact congrArg PowerSeries.C (coe_X i).symm

/-- Mapping the separated coefficients into the unit-radius Tate algebra agrees with
the restricted-series iteration. -/
@[simp]
theorem map_toTate_optionSeries (f : washnitzerAlgebra (Option σ) R) :
    PowerSeries.map (toTate σ R : washnitzerAlgebra σ R →+*
      IsRestricted.subring (R := R) (fun _ : σ ↦ (1 : ℝ))) (optionSeries f) =
      (Huber.restrictedOptionEquiv (toTate (Option σ) R f) :
        PowerSeries (IsRestricted.subring (R := R) (fun _ : σ ↦ (1 : ℝ)))) := by
  ext m : 1
  apply Subtype.ext
  rw [PowerSeries.coeff_map, Huber.coeff_restrictedOptionEquiv (c := fun _ ↦ 1),
    coe_toTate]
  exact (coe_toTate _).trans (coe_coeff_optionSeries f m)

end washnitzerAlgebra

end TauCeti.Dagger
