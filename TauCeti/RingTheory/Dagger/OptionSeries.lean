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
division. Conversely, `washnitzerAlgebra.optionC` views an overconvergent series in `σ` as one in
`Option σ` that is constant in `Y`; along it, `washnitzerAlgebra.polynomialToOption` evaluates
polynomials over the coefficient ring at `Y`. No claim is made that an arbitrary series of
overconvergent coefficients is itself overconvergent: the coefficients must satisfy a common
radius bound. The split polyradius `MvPowerSeries.splitRadius r ρ`, with radius `r` in `Y` and
`ρ` elsewhere, is the unequal-radius setting in which overconvergent preparation and division
are carried out. By `MvPowerSeries.isRestricted_of_map_subtype_eq_optionEquivLeft`, separating `Y`
in a series restricted at `r` gives a series in `Y` restricted at `r` over the series restricted
at `ρ ≤ r`.

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
    ⟨ρ, hρ, isRestricted_coeff_optionEquivLeft (zero_lt_one.trans hρ) hf m⟩

/-- An overconvergent series in `σ`, viewed as a series in `Option σ` constant in the separated
variable `Y = X none`, is overconvergent. -/
theorem optionEquivLeft_symm_C_mem_washnitzerAlgebra {f : MvPowerSeries σ R}
    (hf : f ∈ washnitzerAlgebra σ R) :
    (optionEquivLeft σ R).symm (PowerSeries.C f) ∈ washnitzerAlgebra (Option σ) R := by
  obtain ⟨ρ, hρ, hf⟩ := mem_washnitzerAlgebra.mp hf
  have : Fact (0 < ρ) := ⟨zero_lt_one.trans hρ⟩
  let g := (restrictedOptionEquiv (c := fun _ : Option σ ↦ ρ)).symm
    ⟨PowerSeries.C ⟨f, hf⟩, PowerSeries.isRestricted_C _ _⟩
  refine mem_washnitzerAlgebra.mpr ⟨ρ, hρ, ?_⟩
  have hg : (g : MvPowerSeries (Option σ) R) = (optionEquivLeft σ R).symm (PowerSeries.C f) := by
    simp [g]
  exact hg ▸ g.2

namespace washnitzerAlgebra

/-- Forgetting overconvergence coefficientwise is injective on formal power series. -/
theorem map_val_injective : Function.Injective
    (PowerSeries.map ((washnitzerAlgebra σ R).val :
      washnitzerAlgebra σ R →+* MvPowerSeries σ R)) :=
  PowerSeries.map_injective _ Subtype.val_injective

/-- The coefficientwise separation of `Y = X none` underlying `optionSeries`. -/
private noncomputable def optionSeriesFun (f : washnitzerAlgebra (Option σ) R) :
    PowerSeries (washnitzerAlgebra σ R) :=
  PowerSeries.mk fun m ↦ ⟨_, coeff_optionEquivLeft_mem_washnitzerAlgebra f.2 m⟩

private theorem coe_coeff_optionSeriesFun (f : washnitzerAlgebra (Option σ) R) (m : ℕ) :
    (PowerSeries.coeff (R := washnitzerAlgebra σ R) m (optionSeriesFun f) : MvPowerSeries σ R) =
      PowerSeries.coeff m (optionEquivLeft σ R (f : MvPowerSeries (Option σ) R)) := by
  simp only [optionSeriesFun, PowerSeries.coeff_mk]

private theorem map_val_optionSeriesFun (f : washnitzerAlgebra (Option σ) R) :
    PowerSeries.map ((washnitzerAlgebra σ R).val :
      washnitzerAlgebra σ R →+* MvPowerSeries σ R) (optionSeriesFun f) =
      optionEquivLeft σ R (f : MvPowerSeries (Option σ) R) := by
  ext m : 1
  rw [PowerSeries.coeff_map]
  exact coe_coeff_optionSeriesFun f m

/-- Separate `Y = X none`, retaining overconvergent coefficients in the other variables. -/
noncomputable def optionSeries :
    washnitzerAlgebra (Option σ) R →ₐ[R] PowerSeries (washnitzerAlgebra σ R) where
  toFun := optionSeriesFun
  map_zero' := map_val_injective (by rw [map_val_optionSeriesFun]; simp)
  map_one' := map_val_injective (by rw [map_val_optionSeriesFun]; simp)
  map_add' f g := map_val_injective (by
    rw [map_add, map_val_optionSeriesFun, map_val_optionSeriesFun, map_val_optionSeriesFun]
    simp)
  map_mul' f g := map_val_injective (by
    rw [map_mul, map_val_optionSeriesFun, map_val_optionSeriesFun, map_val_optionSeriesFun]
    simp)
  commutes' a := map_val_injective (by
    rw [map_val_optionSeriesFun]
    simp [PowerSeries.algebraMap_apply])

/-- The separated coefficients are the formal coefficient slices. -/
@[simp]
theorem coe_coeff_optionSeries (f : washnitzerAlgebra (Option σ) R) (m : ℕ) :
    (PowerSeries.coeff (R := washnitzerAlgebra σ R) m (optionSeries f) : MvPowerSeries σ R) =
      PowerSeries.coeff m (optionEquivLeft σ R (f : MvPowerSeries (Option σ) R)) :=
  coe_coeff_optionSeriesFun f m

/-- Forgetting overconvergence of the coefficients recovers the formal variable separation. -/
@[simp]
theorem map_val_optionSeries (f : washnitzerAlgebra (Option σ) R) :
    PowerSeries.map ((washnitzerAlgebra σ R).val :
      washnitzerAlgebra σ R →+* MvPowerSeries σ R) (optionSeries f) =
      optionEquivLeft σ R (f : MvPowerSeries (Option σ) R) :=
  map_val_optionSeriesFun f

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

/-- An overconvergent series in `σ` as an overconvergent series in `Option σ`, constant in the
separated variable `Y = X none`. -/
noncomputable def optionC : washnitzerAlgebra σ R →ₐ[R] washnitzerAlgebra (Option σ) R :=
  (((optionEquivLeft σ R).symm : PowerSeries (MvPowerSeries σ R) →ₐ[R]
      MvPowerSeries (Option σ) R).comp
    ((IsScalarTower.toAlgHom R (MvPowerSeries σ R) (PowerSeries (MvPowerSeries σ R))).comp
      (washnitzerAlgebra σ R).val)).codRestrict _ fun f ↦ by
    simpa [PowerSeries.algebraMap_apply] using
      optionEquivLeft_symm_C_mem_washnitzerAlgebra f.2

/-- The series underlying `optionC f` is `f`, constant in the separated variable. -/
@[simp]
theorem coe_optionC (f : washnitzerAlgebra σ R) :
    (optionC f : MvPowerSeries (Option σ) R) =
      (optionEquivLeft σ R).symm (PowerSeries.C (f : MvPowerSeries σ R)) := by
  simp [optionC]

/-- Separating `Y` from `optionC f` gives the constant univariate series `f`. -/
@[simp]
theorem optionSeries_optionC (f : washnitzerAlgebra σ R) :
    optionSeries (optionC f) = PowerSeries.C f := by
  apply map_val_injective
  simp

/-- `optionC` sends the variable `Xᵢ` to the variable `X (some i)`. -/
@[simp]
theorem optionC_X (i : σ) : optionC (X σ R i) = X (Option σ) R (some i) :=
  optionSeries_injective (by simp)

/-- `optionC` is injective. -/
theorem optionC_injective : Function.Injective (optionC (σ := σ) (R := R)) := fun f g h ↦
  PowerSeries.C_injective (by simpa using congrArg optionSeries h)

/-- Evaluation of polynomials over `R⟨X⟩†` at the separated variable `Y = X none`, as a ring map
`R⟨X⟩†[Y] → R⟨X, Y⟩†`. -/
noncomputable def polynomialToOption :
    Polynomial (washnitzerAlgebra σ R) →+* washnitzerAlgebra (Option σ) R :=
  Polynomial.eval₂RingHom (optionC (σ := σ) (R := R) : _ →+* _) (X (Option σ) R none)

/-- Constant polynomials evaluate to series constant in `Y`. -/
@[simp]
theorem polynomialToOption_C (a : washnitzerAlgebra σ R) :
    polynomialToOption (Polynomial.C a) = optionC a :=
  Polynomial.eval₂_C _ _

/-- The variable of the polynomial ring evaluates to `Y = X none`. -/
@[simp]
theorem polynomialToOption_X :
    polynomialToOption (Polynomial.X : Polynomial (washnitzerAlgebra σ R)) = X (Option σ) R none :=
  Polynomial.eval₂_X _ _

/-- Separating `Y` from the evaluation of a polynomial at `Y` recovers the polynomial. -/
@[simp]
theorem optionSeries_polynomialToOption (p : Polynomial (washnitzerAlgebra σ R)) :
    optionSeries (polynomialToOption p) = (p : PowerSeries (washnitzerAlgebra σ R)) := by
  have h : (optionSeries : washnitzerAlgebra (Option σ) R →ₐ[R] _).toRingHom.comp
      polynomialToOption = Polynomial.coeToPowerSeries.ringHom :=
    Polynomial.ringHom_ext (fun a ↦ by simp) (by simp)
  exact RingHom.congr_fun h p

/-- Evaluation at `Y` is injective: a polynomial is recovered by separating `Y` again. -/
theorem polynomialToOption_injective :
    Function.Injective (polynomialToOption (σ := σ) (R := R)) := fun p q h ↦
  Polynomial.coe_injective _ (by simpa using congrArg optionSeries h)

/-- Mapping the separated coefficients into the unit-radius Tate algebra agrees with
the restricted-series iteration. -/
@[simp]
theorem map_toTate_optionSeries (f : washnitzerAlgebra (Option σ) R) :
    PowerSeries.map (toTate σ R : washnitzerAlgebra σ R →+*
      IsRestricted.subring (R := R) (fun _ : σ ↦ (1 : ℝ))) (optionSeries f) =
      (restrictedOptionEquiv (toTate (Option σ) R f) :
        PowerSeries (IsRestricted.subring (R := R) (fun _ : σ ↦ (1 : ℝ)))) := by
  ext m : 1
  apply Subtype.ext
  rw [PowerSeries.coeff_map, coeff_restrictedOptionEquiv (c := fun _ ↦ 1),
    coe_toTate]
  exact (coe_toTate _).trans (coe_coeff_optionSeries f m)

/-- In the unit-radius Tate algebra, the evaluation of `p` at `Y` is `p` with coefficients mapped
along `toTate`. -/
@[simp]
theorem restrictedOptionEquiv_toTate_polynomialToOption
    (p : Polynomial (washnitzerAlgebra σ R)) :
    (restrictedOptionEquiv (toTate _ R (polynomialToOption p)) :
      PowerSeries (IsRestricted.subring (R := R) (fun _ : σ ↦ (1 : ℝ)))) =
      (p.map (toTate σ R).toRingHom :
        PowerSeries (IsRestricted.subring (R := R) (fun _ : σ ↦ (1 : ℝ)))) := by
  rw [← map_toTate_optionSeries, optionSeries_polynomialToOption]
  ext m : 1
  simp [Polynomial.coeff_coe]

end washnitzerAlgebra

end TauCeti.Dagger
