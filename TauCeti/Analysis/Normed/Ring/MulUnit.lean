/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Multiplicative units of normed rings

A multiplicative unit is an invertible element whose left multiplication scales every norm by
its own norm. This singles out the units needed in norm estimates over coefficient rings whose
norm need not be multiplicative. In a norm-one ring, the condition is equivalent to the inverse
having reciprocal norm, and norm-preserving ring homomorphisms preserve multiplicative units
from a norm-one source ring. In a complete ultrametric norm-one ring, small perturbations of one
are multiplicative units.

## References

* F. Martin, *Overconvergent subanalytic subsets in the framework of Berkovich spaces*,
  J. Eur. Math. Soc. 18 (2016), Definition 1.20 and Lemma 1.21.
-/

public section

namespace TauCeti.NormedRing

section Units

/-! ### Units scaling the norm exactly -/

variable {R : Type*} [SeminormedRing R] {u : Rˣ} (hu0 : 0 < ‖(u : R)‖)
  (hu : ∀ x : R, ‖(u : R) * x‖ = ‖(u : R)‖ * ‖x‖)
include hu0 hu

/-- A unit of positive norm by which left multiplication scales the norm exactly forces
`‖1‖ = 1`. -/
theorem norm_one_of_norm_units_mul : ‖(1 : R)‖ = 1 :=
  (mul_eq_left₀ hu0.ne').mp (by simpa using (hu 1).symm)

/-- A unit of positive norm by which left multiplication scales the norm exactly has inverse
of norm `‖u‖⁻¹`. -/
theorem norm_units_inv_of_norm_mul : ‖((u⁻¹ : Rˣ) : R)‖ = ‖(u : R)‖⁻¹ := by
  have h := hu ((u⁻¹ : Rˣ) : R)
  rw [Units.mul_inv, norm_one_of_norm_units_mul hu0 hu] at h
  exact eq_inv_of_mul_eq_one_right h.symm

end Units

end TauCeti.NormedRing

namespace TauCeti

variable {R S : Type*} [SeminormedRing R] [SeminormedRing S]

/-- A multiplicative unit is a unit whose left multiplication scales norms exactly. -/
def IsNormMulUnit (u : R) : Prop :=
  IsUnit u ∧ ∀ x : R, ‖u * x‖ = ‖u‖ * ‖x‖

/-- The characteristic criterion for being a multiplicative unit. -/
theorem isNormMulUnit_iff (u : R) :
    IsNormMulUnit u ↔ IsUnit u ∧ ∀ x : R, ‖u * x‖ = ‖u‖ * ‖x‖ := (Iff.rfl)

namespace IsNormMulUnit

/-- A multiplicative unit is invertible. -/
theorem isUnit {u : R} (hu : IsNormMulUnit u) : IsUnit u := hu.1

/-- Left multiplication by a multiplicative unit scales norms exactly. -/
theorem norm_mul {u : R} (hu : IsNormMulUnit u) (x : R) :
    ‖u * x‖ = ‖u‖ * ‖x‖ := hu.2 x

/-- Multiplicative units are closed under multiplication. -/
theorem mul {u v : R} (hu : IsNormMulUnit u) (hv : IsNormMulUnit v) :
    IsNormMulUnit (u * v) := by
  refine ⟨hu.isUnit.mul hv.isUnit, fun x ↦ ?_⟩
  rw [mul_assoc, hu.norm_mul, hv.norm_mul, hu.norm_mul, mul_assoc]

end IsNormMulUnit

section NormOne

variable [NormOneClass R]

/-- One is a multiplicative unit in a norm-one ring. -/
@[simp]
theorem isNormMulUnit_one : IsNormMulUnit (1 : R) :=
  ⟨isUnit_one, fun x ↦ by simp⟩

/-- In a norm-one ring, a unit is multiplicative precisely when its inverse has reciprocal norm. -/
theorem _root_.Units.isNormMulUnit_iff_norm_inv (u : Rˣ) :
    IsNormMulUnit (u : R) ↔ ‖((u⁻¹ : Rˣ) : R)‖ = ‖(u : R)‖⁻¹ := by
  have hu0 : 0 < ‖(u : R)‖ := by
    have h := norm_mul_le (u : R) ((u⁻¹ : Rˣ) : R)
    rw [Units.mul_inv, norm_one] at h
    nlinarith [norm_nonneg (u : R), norm_nonneg ((u⁻¹ : Rˣ) : R)]
  constructor
  · intro hu
    exact NormedRing.norm_units_inv_of_norm_mul hu0 hu.norm_mul
  · intro h
    refine ⟨u.isUnit, fun x ↦ le_antisymm (norm_mul_le _ _) ?_⟩
    have hx : ‖x‖ ≤ ‖(u : R)‖⁻¹ * ‖(u : R) * x‖ := by
      simpa [← h, ← mul_assoc] using norm_mul_le ((u⁻¹ : Rˣ) : R) ((u : R) * x)
    exact (le_inv_mul_iff₀ hu0).mp hx

namespace IsNormMulUnit

/-- Powers of a multiplicative unit are multiplicative units. -/
theorem pow {u : R} (hu : IsNormMulUnit u) (n : ℕ) : IsNormMulUnit (u ^ n) := by
  induction n with
  | zero => simp
  | succ n ih => simpa [pow_succ] using ih.mul hu

/-- The inverse of a multiplicative unit is again multiplicative. -/
theorem units_inv {u : Rˣ} (hu : IsNormMulUnit (u : R)) :
    IsNormMulUnit ((u⁻¹ : Rˣ) : R) := by
  rw [Units.isNormMulUnit_iff_norm_inv] at hu ⊢
  simp [hu]

/-- Norm-preserving ring homomorphisms from a norm-one ring preserve multiplicative units,
even when they are not onto. -/
theorem map {u : R} (hu : IsNormMulUnit u) (φ : R →+* S)
    (hφ : ∀ x, ‖φ x‖ = ‖x‖) : IsNormMulUnit (φ u) := by
  obtain ⟨v, rfl⟩ := hu.isUnit
  let : NormOneClass S := ⟨by rw [← φ.map_one, hφ, norm_one]⟩
  have hv := (Units.isNormMulUnit_iff_norm_inv v).mp hu
  apply (Units.isNormMulUnit_iff_norm_inv (Units.map φ.toMonoidHom v)).mpr
  exact (hφ _).trans (hv.trans (congrArg (·⁻¹) (hφ _).symm))

end IsNormMulUnit

end NormOne

/-- In a ring with multiplicative norm every unit is a multiplicative unit. -/
theorem isNormMulUnit_iff_isUnit [NormMulClass R] (u : R) :
    IsNormMulUnit u ↔ IsUnit u :=
  ⟨IsNormMulUnit.isUnit, fun hu ↦ ⟨hu, fun x ↦ norm_mul u x⟩⟩

section Perturbation

variable {A : Type*} [NormedRing A] [NormOneClass A]

/-- In an ultrametric norm-one ring with summable geometric series, a perturbation of one by an
element of norm less than one is a multiplicative unit. -/
theorem isNormMulUnit_one_add [HasSummableGeomSeries A] [IsUltrametricDist A] {a : A}
    (ha : ‖a‖ < 1) : IsNormMulUnit (1 + a) := by
  refine ⟨by simpa using isUnit_one_sub_of_norm_lt_one (x := -a) (by simpa using ha), ?_⟩
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

end Perturbation

/-- Isometric ring equivalences preserve and reflect multiplicative units. -/
theorem _root_.RingEquiv.isNormMulUnit_iff (e : R ≃+* S)
    (he : ∀ x, ‖e x‖ = ‖x‖) (u : R) : IsNormMulUnit (e u) ↔ IsNormMulUnit u := by
  have he' (x : S) : ‖e.symm x‖ = ‖x‖ := by simpa using (he (e.symm x)).symm
  constructor
  · intro hu
    refine ⟨by simpa using hu.isUnit.map e.symm.toMonoidHom, fun x ↦ ?_⟩
    rw [← he (u * x), e.map_mul, hu.norm_mul, he, he]
  · intro hu
    refine ⟨hu.isUnit.map e.toMonoidHom, fun x ↦ ?_⟩
    rw [← he' (e u * x), e.symm.map_mul, e.symm_apply_apply, hu.norm_mul, he', he]

end TauCeti
