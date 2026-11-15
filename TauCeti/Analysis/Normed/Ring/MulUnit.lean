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
import TauCeti.Analysis.Normed.Ring.Ultra

/-!
# Multiplicative units of normed rings

This file develops the ring-specific properties of `TauCeti.IsNormMulUnit`, whose definition
and multiplicative closure properties live in `TauCeti.Analysis.Normed.Monoid.MulUnit`.

A nontrivial normed ring with a multiplicative unit has `‖1‖ = 1`. In a seminormed ring,
a unit is multiplicative precisely when its inverse has reciprocal norm. Norm-preserving
monoid homomorphisms between seminormed rings preserve multiplicative units, even when they are
not onto, and along a contractive homomorphism scaling by the image of a multiplicative unit with
`‖u‖ * c = 1` puts the product in the closed unit ball precisely when the cofactor has norm at
most `c`. In a complete ultrametric norm-one ring, small
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

section Units

variable {R S : Type*} [SeminormedRing R] [SeminormedRing S]

/-- In a seminormed ring, a unit is multiplicative precisely when its inverse has reciprocal norm.
If `‖u‖ = 0` every norm vanishes and both sides hold. -/
theorem _root_.Units.isNormMulUnit_iff_norm_inv (u : Rˣ) :
    IsNormMulUnit (u : R) ↔ ‖((u⁻¹ : Rˣ) : R)‖ = ‖(u : R)‖⁻¹ := by
  rcases eq_or_ne ‖(u : R)‖ 0 with hu0 | hu0
  · have h1 : ‖(1 : R)‖ = 0 := by
      have h := norm_mul_le ((u⁻¹ : Rˣ) : R) (u : R)
      rw [Units.inv_mul, hu0, mul_zero] at h
      exact le_antisymm h (norm_nonneg _)
    have hall (x : R) : ‖x‖ = 0 := by
      have h := norm_mul_le x (1 : R)
      rw [mul_one, h1, mul_zero] at h
      exact le_antisymm h (norm_nonneg _)
    simp only [hall, inv_zero, iff_true]
    exact (isNormMulUnit_iff _).mpr ⟨u.isUnit, fun x ↦ by simp [hall]⟩
  have hu0' : 0 < ‖(u : R)‖ := lt_of_le_of_ne (norm_nonneg _) hu0.symm
  constructor
  · intro hu
    exact NormedRing.norm_units_inv_of_norm_mul hu0 hu.norm_mul
  · intro h
    refine (isNormMulUnit_iff _).mpr ⟨u.isUnit, fun x ↦ le_antisymm (norm_mul_le _ _) ?_⟩
    have hx : ‖x‖ ≤ ‖(u : R)‖⁻¹ * ‖(u : R) * x‖ := by
      simpa [← h, ← mul_assoc] using norm_mul_le ((u⁻¹ : Rˣ) : R) ((u : R) * x)
    exact (le_inv_mul_iff₀ hu0').mp hx

namespace IsNormMulUnit

/-- Norm-preserving monoid homomorphisms between seminormed rings preserve multiplicative units,
even when they are not onto. -/
theorem map {u : R} (hu : IsNormMulUnit u) (φ : R →* S)
    (hφ : ∀ x, ‖φ x‖ = ‖x‖) : IsNormMulUnit (φ u) := by
  obtain ⟨v, rfl⟩ := hu.isUnit
  have hv := (Units.isNormMulUnit_iff_norm_inv v).mp hu
  apply (Units.isNormMulUnit_iff_norm_inv (Units.map φ v)).mpr
  exact (hφ _).trans (hv.trans (congrArg (·⁻¹) (hφ _).symm))

end IsNormMulUnit

/-- Along a contractive monoid homomorphism `φ`, scaling `b` by the image of a multiplicative unit
`u` with `‖u‖ * c = 1` puts `φ u * b` in the closed unit ball precisely when `‖b‖ ≤ c`. -/
theorem norm_map_unit_mul_le_one_iff {F : Type*} [FunLike F R S] [MonoidHomClass F R S]
    (u : Rˣ) (hu : IsNormMulUnit (u : R)) {c : ℝ} (hc : ‖(u : R)‖ * c = 1)
    {φ : F} (hφ : ∀ r, ‖φ r‖ ≤ ‖r‖) (b : S) :
    ‖φ (u : R) * b‖ ≤ 1 ↔ ‖b‖ ≤ c := by
  have hc_eq : c = ‖(u : R)‖⁻¹ := eq_inv_of_mul_eq_one_right hc
  constructor
  · intro h
    have hb : b = φ (((u⁻¹ : Rˣ) : R)) * (φ (u : R) * b) := by
      rw [← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]
    calc ‖b‖ = ‖φ (((u⁻¹ : Rˣ) : R)) * (φ (u : R) * b)‖ := congrArg norm hb
      _ ≤ ‖φ (((u⁻¹ : Rˣ) : R))‖ * ‖φ (u : R) * b‖ := norm_mul_le _ _
      _ ≤ ‖((u⁻¹ : Rˣ) : R)‖ * 1 :=
          mul_le_mul (hφ _) h (norm_nonneg _) (norm_nonneg _)
      _ = c := by rw [mul_one, (Units.isNormMulUnit_iff_norm_inv u).mp hu, hc_eq]
  · intro h
    calc ‖φ (u : R) * b‖ ≤ ‖φ (u : R)‖ * ‖b‖ := norm_mul_le _ _
      _ ≤ ‖(u : R)‖ * c := mul_le_mul (hφ _) h (norm_nonneg _) (norm_nonneg _)
      _ = 1 := hc

end Units

section Perturbation

variable {A : Type*} [NormedRing A]

variable [NormOneClass A] in
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
  rw [hnorm, one_mul]
  exact norm_one_add_mul_of_norm_lt_one ha x

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

/-- **Neumann series criterion.** In an ultrametric ring with summable geometric series,
an element whose distance from a multiplicative unit `u` is less than `‖u‖` is a multiplicative
unit. -/
theorem IsNormMulUnit.of_norm_sub_lt [HasSummableGeomSeries A] [IsUltrametricDist A] {u f : A}
    (hu : IsNormMulUnit u) (hf : ‖f - u‖ < ‖u‖) : IsNormMulUnit f := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · exact (isNormMulUnit_iff _).mpr ⟨isUnit_of_subsingleton f, fun x ↦ by
      simp [Subsingleton.elim x 0]⟩
  have : NormOneClass A := ⟨hu.norm_one⟩
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
