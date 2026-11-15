/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.HahnSeries.PowerSeries

/-!
# Derivations of Hahn series

For an additive map `w : Γ →+ R`, scaling the coefficient of `t ^ g` by `w g` is an `R`-derivation
`HahnSeries.weightDerivation w` of `HahnSeries Γ R`: exponents add under multiplication, so the
additivity `w (g + h) = w g + w h` is exactly the Leibniz rule. For `Γ = ℤ` and `w` the integer
cast it is the Euler operator `t d/dt` on Laurent series.

Over a `ℚ`-algebra `R`, the Euler operator with the rational cast as weight, followed by
multiplication by `t⁻¹`, is the derivative `d/dt` of rational-exponent Hahn series,
`TauCeti.ratHahnSeriesDerivation R`, given by the coefficient rule `d/dt (t ^ q) = q t ^ (q - 1)`.
It restricts to the derivative of Puiseux series.

`HahnSeries.weightDerivation` is an `R`-derivation for the coefficientwise `R`-algebra structure
`HahnSeries.instAlgebra`, the only one available for a general `Γ`. When `Γ` is an ordered
semiring, such as `ℤ` or `ℚ`, instance search instead finds the structure inherited from `R⟦X⟧`
through `HahnSeries.powerSeriesAlgebra`, which agrees with it only propositionally; the derivative
`TauCeti.ratHahnSeriesDerivation R` is stated for the latter, so that it restricts to `K`-algebras
of rational-exponent series such as the Puiseux field.

## Main definitions

* `HahnSeries.weightDerivation w`: the derivation scaling the coefficient of `t ^ g` by `w g`.
* `TauCeti.ratHahnSeriesDerivation R`: the derivative `d/dt` on `HahnSeries ℚ R`.

## Main results

* `HahnSeries.coeff_weightDerivation`, `TauCeti.coeff_ratHahnSeriesDerivation`: the coefficient
  formulas.
* `TauCeti.orderTop_le_orderTop_ratHahnSeriesDerivation_add_one`: `d/dt` lowers the order by at
  most one.
* `TauCeti.ratHahnSeriesDerivation_eq_zero_iff`: the series with derivative zero are the
  constants.
-/

public section

namespace HahnSeries

variable {Γ R : Type*} [AddCommMonoid Γ] [PartialOrder Γ] [CommSemiring R]

/-- The `R`-linear map scaling the coefficient of `t ^ g` by `w g`, underlying
`HahnSeries.weightDerivation w`. -/
private noncomputable def weightLinearMap (w : Γ →+ R) :
    HahnSeries Γ R →ₗ[R] HahnSeries Γ R where
  toFun x :=
    { coeff g := w g * x.coeff g
      isPWO_support' := x.isPWO_support.mono fun _ hg ↦ right_ne_zero_of_mul hg }
  map_add' x y := by
    ext g
    simp [mul_add]
  map_smul' r x := by
    ext g
    simp [mul_left_comm]

private theorem coeff_weightLinearMap (w : Γ →+ R) (x : HahnSeries Γ R) (g : Γ) :
    (weightLinearMap w x).coeff g = w g * x.coeff g :=
  (rfl)

private theorem support_weightLinearMap_subset (w : Γ →+ R) (x : HahnSeries Γ R) :
    (weightLinearMap w x).support ⊆ x.support := fun _ hg ↦ right_ne_zero_of_mul hg

variable [IsOrderedCancelAddMonoid Γ]

/-- The **weight derivation** of Hahn series attached to an additive map `w : Γ →+ R`: it scales
the coefficient of `t ^ g` by `w g`. For `Γ = ℤ` and the integer cast this is the Euler operator
`t d/dt`. -/
noncomputable def weightDerivation (w : Γ →+ R) :
    Derivation R (HahnSeries Γ R) (HahnSeries Γ R) where
  toLinearMap := weightLinearMap w
  map_one_eq_zero' := by
    ext g
    by_cases hg : g = 0 <;> simp [coeff_weightLinearMap, coeff_one, hg]
  leibniz' x y := by
    ext g
    simp only [smul_eq_mul, coeff_add]
    -- Expand all three products over the antidiagonal of the supports of `x` and `y`.
    rw [coeff_weightLinearMap, coeff_mul,
      coeff_mul_right' y.isPWO_support (support_weightLinearMap_subset w y), mul_comm y,
      coeff_mul_left' x.isPWO_support (support_weightLinearMap_subset w x), Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ij hij ↦ ?_
    rw [coeff_weightLinearMap, coeff_weightLinearMap, ← (Finset.mem_antidiagonal.mp hij).2.2,
      map_add]
    ring

/-- The coefficient of `t ^ g` in `weightDerivation w x` is `w g` times that of `x`. -/
@[simp]
theorem coeff_weightDerivation (w : Γ →+ R) (x : HahnSeries Γ R) (g : Γ) :
    (weightDerivation w x).coeff g = w g * x.coeff g :=
  (rfl)

/-- The support of `weightDerivation w x` is contained in that of `x`. -/
theorem support_weightDerivation_subset (w : Γ →+ R) (x : HahnSeries Γ R) :
    (weightDerivation w x).support ⊆ x.support :=
  support_weightLinearMap_subset w x

/-- The weight derivation sends the monomial `r t ^ g` to `w g r t ^ g`. -/
@[simp]
theorem weightDerivation_single (w : Γ →+ R) (g : Γ) (r : R) :
    weightDerivation w (single g r) = single g (w g * r) := by
  ext h
  by_cases hh : h = g
  · simp [hh]
  · simp [coeff_single_of_ne hh]

end HahnSeries

namespace TauCeti

open HahnSeries

variable (R : Type*) [CommRing R] [Algebra ℚ R]

/-- The **derivative `d/dt` of Hahn series with rational exponents** over a `ℚ`-algebra `R`,
given by `d/dt (t ^ q) = q t ^ (q - 1)`. It is `t⁻¹` times the weight derivation for the rational
cast, the Euler operator `t d/dt`.

It is a derivation for the default `R`-algebra structure on `HahnSeries ℚ R`, the one inherited
from `R⟦X⟧` through `HahnSeries.powerSeriesAlgebra`, which is only propositionally equal to the
coefficientwise structure for which `HahnSeries.weightDerivation` is stated. -/
noncomputable def ratHahnSeriesDerivation : Derivation R (HahnSeries ℚ R) (HahnSeries ℚ R) where
  toFun x := single (-1 : ℚ) (1 : R) * weightDerivation (algebraMap ℚ R : ℚ →+ R) x
  map_add' x y := by rw [map_add, mul_add]
  map_smul' r x := by
    rw [RingHom.id_apply, Algebra.smul_def, algebraMap_apply', PowerSeries.algebraMap_apply,
      Algebra.algebraMap_self, RingHom.id_apply, ofPowerSeries_C, C_mul_eq_smul]
    ext q
    simp [coeff_single_mul, mul_left_comm]
  map_one_eq_zero' := by
    simp only [LinearMap.coe_mk, AddHom.coe_mk, Derivation.map_one_eq_zero, mul_zero]
  leibniz' x y := by
    simp only [LinearMap.coe_mk, AddHom.coe_mk, Derivation.leibniz, smul_eq_mul]
    ring

variable {R}

private theorem ratHahnSeriesDerivation_apply (x : HahnSeries ℚ R) :
    ratHahnSeriesDerivation R x =
      single (-1 : ℚ) (1 : R) * weightDerivation (algebraMap ℚ R : ℚ →+ R) x :=
  (rfl)

/-- The coefficient of `t ^ q` in the derivative of `x` is `q + 1` times the coefficient of
`t ^ (q + 1)` in `x`. -/
@[simp]
theorem coeff_ratHahnSeriesDerivation (x : HahnSeries ℚ R) (q : ℚ) :
    (ratHahnSeriesDerivation R x).coeff q = (q + 1) • x.coeff (q + 1) := by
  rw [ratHahnSeriesDerivation_apply, coeff_single_mul, one_mul, sub_neg_eq_add,
    coeff_weightDerivation, AddMonoidHom.coe_ofClass, Algebra.smul_def]

/-- The coefficient of `t ^ (q - 1)` in the derivative of `x` is `q` times the coefficient of
`t ^ q` in `x`. -/
theorem coeff_ratHahnSeriesDerivation_sub_one (x : HahnSeries ℚ R) (q : ℚ) :
    (ratHahnSeriesDerivation R x).coeff (q - 1) = q • x.coeff q := by
  rw [coeff_ratHahnSeriesDerivation, sub_add_cancel]

/-- **Power rule**: the derivative of `r t ^ q` is `q r t ^ (q - 1)`. -/
@[simp]
theorem ratHahnSeriesDerivation_single (q : ℚ) (r : R) :
    ratHahnSeriesDerivation R (single q r) = single (q - 1) (q • r) := by
  ext p
  rw [coeff_ratHahnSeriesDerivation]
  by_cases hp : p = q - 1
  · simp [hp]
  · rw [coeff_single_of_ne hp, coeff_single_of_ne (by rintro rfl; simp at hp), smul_zero]

/-- **Differentiation lowers the order by at most one**: `ord x ≤ ord (dx/dt) + 1`. -/
theorem orderTop_le_orderTop_ratHahnSeriesDerivation_add_one (x : HahnSeries ℚ R) :
    x.orderTop ≤ (ratHahnSeriesDerivation R x).orderTop + 1 := by
  obtain h | h := eq_or_ne (ratHahnSeriesDerivation R x) 0
  · simp [h]
  obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.mp (orderTop_ne_top.mpr h)
  have hc := coeff_orderTop_ne hq.symm
  rw [coeff_ratHahnSeriesDerivation] at hc
  rw [← hq, ← WithTop.coe_one, ← WithTop.coe_add]
  exact orderTop_le_of_coeff_ne_zero (right_ne_zero_of_smul hc)

/-- **The kernel of `d/dt`**: the rational-exponent Hahn series with derivative zero are the
constants. -/
theorem ratHahnSeriesDerivation_eq_zero_iff {x : HahnSeries ℚ R} :
    ratHahnSeriesDerivation R x = 0 ↔ ∃ r : R, algebraMap R (HahnSeries ℚ R) r = x := by
  simp_rw [algebraMap_apply', PowerSeries.algebraMap_apply, Algebra.algebraMap_self,
    RingHom.id_apply, ofPowerSeries_C]
  refine ⟨fun h ↦ ⟨x.coeff 0, ?_⟩, ?_⟩
  · ext q
    rw [C_apply, coeff_single]
    split_ifs with hq
    · rw [hq]
    -- The coefficient of `t ^ q` is `q⁻¹` times the coefficient of `t ^ (q - 1)` in `dx/dt`.
    have hd := coeff_ratHahnSeriesDerivation_sub_one x q
    rw [h, coeff_zero] at hd
    rw [← inv_smul_smul₀ hq (x.coeff q), ← hd, smul_zero]
  · rintro ⟨r, rfl⟩
    rw [C_apply, ratHahnSeriesDerivation_single, zero_smul, single_eq_zero]

end TauCeti
