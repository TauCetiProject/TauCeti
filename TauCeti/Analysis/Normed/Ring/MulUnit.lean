/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Monoid.MulUnit
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Analysis.SpecificLimits.Normed
import TauCeti.Analysis.Normed.Group.Ultra

/-!
# Multiplicative units of normed rings

This file develops the ring-specific properties of `TauCeti.IsNormMulUnit`, whose definition
and multiplicative closure properties live in `TauCeti.Analysis.Normed.Monoid.MulUnit`.

A nontrivial normed ring with a multiplicative unit has `‖1‖ = 1`. In a norm-one seminormed ring,
a unit is multiplicative precisely when its inverse has reciprocal norm. Norm-preserving
monoid homomorphisms between seminormed rings preserve multiplicative units from a norm-one
source ring, even when they are not onto. In a complete ultrametric norm-one ring, small
perturbations of one are multiplicative units. More generally, an element `f` within less than
`‖u‖` of a multiplicative unit `u` is again a multiplicative unit: it factors as
`f = u * (1 - x)` with `x = u⁻¹ * (u - f)` of norm less than one, so its inverse is the Neumann
series `∑ₙ xⁿ * u⁻¹`, of norm `‖u‖⁻¹`.

## References

* F. Martin, *Overconvergent subanalytic subsets in the framework of Berkovich spaces*,
  J. Eur. Math. Soc. 18 (2016), Definition 1.20 and Lemma 1.21.
-/

public section

namespace TauCeti

namespace IsNormMulUnit

/-- A nontrivial normed ring with a multiplicative unit has `‖1‖ = 1`. -/
theorem norm_one {A : Type*} [NormedRing A] [Nontrivial A] {u : A} (hu : IsNormMulUnit u) :
    ‖(1 : A)‖ = 1 := by
  obtain ⟨v, rfl⟩ := hu.isUnit
  exact NormedRing.norm_one_of_norm_mul (norm_ne_zero_iff.mpr (Units.ne_zero v)) hu.norm_mul

end IsNormMulUnit

section NormOneRing

variable {R S : Type*} [SeminormedRing R] [SeminormedRing S] [NormOneClass R]

/-- In a norm-one ring, a unit is multiplicative precisely when its inverse has reciprocal norm. -/
theorem _root_.Units.isNormMulUnit_iff_norm_inv (u : Rˣ) :
    IsNormMulUnit (u : R) ↔ ‖((u⁻¹ : Rˣ) : R)‖ = ‖(u : R)‖⁻¹ := by
  have hu0 : 0 < ‖(u : R)‖ := by
    have h := norm_mul_le (u : R) ((u⁻¹ : Rˣ) : R)
    rw [Units.mul_inv, norm_one] at h
    nlinarith [norm_nonneg (u : R), norm_nonneg ((u⁻¹ : Rˣ) : R)]
  constructor
  · intro hu
    exact NormedRing.norm_units_inv_of_norm_mul hu0.ne' hu.norm_mul
  · intro h
    refine (isNormMulUnit_iff _).mpr ⟨u.isUnit, fun x ↦ le_antisymm (norm_mul_le _ _) ?_⟩
    have hx : ‖x‖ ≤ ‖(u : R)‖⁻¹ * ‖(u : R) * x‖ := by
      simpa [← h, ← mul_assoc] using norm_mul_le ((u⁻¹ : Rˣ) : R) ((u : R) * x)
    exact (le_inv_mul_iff₀ hu0).mp hx

namespace IsNormMulUnit

/-- Norm-preserving monoid homomorphisms from a norm-one ring preserve multiplicative units,
even when they are not onto. -/
theorem map {u : R} (hu : IsNormMulUnit u) (φ : R →* S)
    (hφ : ∀ x, ‖φ x‖ = ‖x‖) : IsNormMulUnit (φ u) := by
  obtain ⟨v, rfl⟩ := hu.isUnit
  let : NormOneClass S := ⟨by rw [← φ.map_one, hφ, NormOneClass.norm_one]⟩
  have hv := (Units.isNormMulUnit_iff_norm_inv v).mp hu
  apply (Units.isNormMulUnit_iff_norm_inv (Units.map φ v)).mpr
  exact (hφ _).trans (hv.trans (congrArg (·⁻¹) (hφ _).symm))

end IsNormMulUnit

end NormOneRing

section Perturbation

variable {A : Type*} [NormedRing A] [NormOneClass A]

/-- In an ultrametric norm-one ring with summable geometric series, a perturbation of one by an
element of norm less than one is a multiplicative unit. -/
theorem isNormMulUnit_one_add [HasSummableGeomSeries A] [IsUltrametricDist A] {a : A}
    (ha : ‖a‖ < 1) : IsNormMulUnit (1 + a) := by
  refine (isNormMulUnit_iff _).mpr
    ⟨by simpa using isUnit_one_sub_of_norm_lt_one (x := -a) (by simpa using ha), ?_⟩
  have hnorm : ‖1 + a‖ = 1 := by
    rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by simpa using ha.ne'),
      norm_one, max_eq_left ha.le]
  intro x
  rw [hnorm, one_mul, add_mul, one_mul]
  by_cases hx : x = 0
  · simp [hx]
  have hax : ‖a * x‖ < ‖x‖ :=
    (norm_mul_le _ _).trans_lt (by simpa using mul_lt_mul_of_pos_right ha (norm_pos_iff.mpr hx))
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hax.ne', max_eq_left hax.le]

omit [NormOneClass A] in
/-- The factorization `f = u * (1 - u⁻¹ * (u - f))` behind the Neumann series criterion. -/
private theorem eq_units_mul_one_sub (u : Aˣ) (f : A) :
    f = u * (1 - ((u⁻¹ : Aˣ) : A) * (u - f)) := by
  rw [mul_sub, mul_one, ← mul_assoc, Units.mul_inv, one_mul, sub_sub_cancel]

/-- If `‖f - u‖ < ‖u‖` for a multiplicative unit `u`, then `u⁻¹ * (u - f)` has norm less than
one. -/
private theorem norm_units_inv_mul_sub_lt_one {u : Aˣ} (hu : IsNormMulUnit (u : A)) {f : A}
    (hf : ‖f - u‖ < ‖(u : A)‖) : ‖((u⁻¹ : Aˣ) : A) * (u - f)‖ < 1 := by
  rw [hu.units_inv.norm_mul, (Units.isNormMulUnit_iff_norm_inv u).mp hu, norm_sub_rev,
    inv_mul_lt_one₀ ((norm_nonneg _).trans_lt hf)]
  exact hf

/-- **Neumann series criterion.** In an ultrametric norm-one ring with summable geometric series,
an element whose distance from a multiplicative unit `u` is less than `‖u‖` is a multiplicative
unit. -/
theorem IsNormMulUnit.of_norm_sub_lt [HasSummableGeomSeries A] [IsUltrametricDist A] {u f : A}
    (hu : IsNormMulUnit u) (hf : ‖f - u‖ < ‖u‖) : IsNormMulUnit f := by
  obtain ⟨u, rfl⟩ := hu.isUnit
  rw [eq_units_mul_one_sub u f, sub_eq_add_neg]
  exact hu.mul (isNormMulUnit_one_add (by rw [norm_neg]; exact norm_units_inv_mul_sub_lt_one hu hf))

/-- **The Neumann series of the inverse.** If `‖f - u‖ < ‖u‖` for a multiplicative unit `u`, then
`x = u⁻¹ * (u - f)` has norm less than one and `f⁻¹ = ∑ₙ xⁿ * u⁻¹`. -/
theorem IsNormMulUnit.hasSum_inverse_of_norm_sub_lt [HasSummableGeomSeries A] {u : Aˣ}
    (hu : IsNormMulUnit (u : A)) {f : A} (hf : ‖f - u‖ < ‖(u : A)‖) :
    HasSum (fun n : ℕ ↦ (((u⁻¹ : Aˣ) : A) * (u - f)) ^ n * ((u⁻¹ : Aˣ) : A))
      (Ring.inverse f) := by
  have hf' : Ring.inverse f =
      Ring.inverse (1 - ((u⁻¹ : Aˣ) : A) * (u - f)) * ((u⁻¹ : Aˣ) : A) := by
    conv_lhs => rw [eq_units_mul_one_sub u f]
    rw [Ring.inverse_mul (.inl u.isUnit), Ring.inverse_unit]
  rw [hf']
  exact (hasSum_geom_series_inverse _ (norm_units_inv_mul_sub_lt_one hu hf)).mul_right _

/-- If `‖f - u‖ < ‖u‖` for a multiplicative unit `u`, then the inverse of `f` has norm
`‖u‖⁻¹`. -/
theorem IsNormMulUnit.norm_inverse_of_norm_sub_lt [HasSummableGeomSeries A] [IsUltrametricDist A]
    {u f : A} (hu : IsNormMulUnit u) (hf : ‖f - u‖ < ‖u‖) : ‖Ring.inverse f‖ = ‖u‖⁻¹ := by
  obtain ⟨v, rfl⟩ := (hu.of_norm_sub_lt hf).isUnit
  rw [Ring.inverse_unit, (Units.isNormMulUnit_iff_norm_inv v).mp (hu.of_norm_sub_lt hf),
    ← IsUltrametricDist.norm_eq_of_norm_sub_lt_left (x := u) (by rwa [norm_sub_rev])]

end Perturbation

end TauCeti
