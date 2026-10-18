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
its own norm. The predicate and its closure properties use only the multiplicative structure
and the norm. This singles out the units needed in norm estimates over coefficient rings whose
norm need not be multiplicative. In a norm-one ring, the condition is equivalent to the inverse
having reciprocal norm, and norm-preserving monoid homomorphisms between seminormed rings
preserve multiplicative units from a norm-one source ring. A nontrivial normed ring with a
multiplicative unit has `‖1‖ = 1`. Powers and finite products of multiplicative units are again
multiplicative units, and their norms are the corresponding powers and products of norms.
In a complete ultrametric norm-one ring, small perturbations of one are multiplicative units.

## References

* F. Martin, *Overconvergent subanalytic subsets in the framework of Berkovich spaces*,
  J. Eur. Math. Soc. 18 (2016), Definition 1.20 and Lemma 1.21.
-/

public section

namespace TauCeti.NormedRing

section Units

/-! ### Units scaling the norm exactly -/

/-- An element of nonzero norm by which left multiplication scales the norm exactly forces
`‖1‖ = 1`. -/
theorem norm_one_of_norm_mul {R : Type*} [MulOneClass R] [Norm R] {u : R} (hu0 : ‖u‖ ≠ 0)
    (hu : ∀ x : R, ‖u * x‖ = ‖u‖ * ‖x‖) : ‖(1 : R)‖ = 1 :=
  (mul_eq_left₀ hu0).mp (by simpa using (hu 1).symm)

/-- A unit of nonzero norm by which left multiplication scales the norm exactly has inverse
of norm `‖u‖⁻¹`. -/
theorem norm_units_inv_of_norm_mul {R : Type*} [Monoid R] [Norm R] {u : Rˣ}
    (hu0 : ‖(u : R)‖ ≠ 0) (hu : ∀ x : R, ‖(u : R) * x‖ = ‖(u : R)‖ * ‖x‖) :
    ‖((u⁻¹ : Rˣ) : R)‖ = ‖(u : R)‖⁻¹ := by
  have h := hu ((u⁻¹ : Rˣ) : R)
  rw [Units.mul_inv, norm_one_of_norm_mul hu0 hu] at h
  exact eq_inv_of_mul_eq_one_right h.symm

end Units

end TauCeti.NormedRing

namespace TauCeti

section Monoid

variable {R S : Type*} [Monoid R] [Norm R] [Monoid S] [Norm S]

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
  simp only [mul_assoc, hu.norm_mul, hv.norm_mul]

/-- A nontrivial normed ring with a multiplicative unit has `‖1‖ = 1`. -/
theorem norm_one {A : Type*} [NormedRing A] [Nontrivial A] {u : A} (hu : IsNormMulUnit u) :
    ‖(1 : A)‖ = 1 := by
  obtain ⟨v, rfl⟩ := hu.isUnit
  exact NormedRing.norm_one_of_norm_mul (norm_ne_zero_iff.mpr (Units.ne_zero v)) hu.norm_mul

end IsNormMulUnit

section NormOne

variable [NormOneClass R]

/-- One is a multiplicative unit in a norm-one monoid. -/
@[simp]
theorem isNormMulUnit_one : IsNormMulUnit (1 : R) :=
  ⟨isUnit_one, fun x ↦ by simp⟩

namespace IsNormMulUnit

/-- Powers of a multiplicative unit are multiplicative units. -/
theorem pow {u : R} (hu : IsNormMulUnit u) (n : ℕ) : IsNormMulUnit (u ^ n) := by
  induction n with
  | zero => simp
  | succ n ih => simpa [pow_succ] using ih.mul hu

/-- The norm of a power of a multiplicative unit is the power of its norm. -/
theorem norm_pow {u : R} (hu : IsNormMulUnit u) (n : ℕ) : ‖u ^ n‖ = ‖u‖ ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', hu.norm_mul, ih, pow_succ']

end IsNormMulUnit

end NormOne

namespace IsNormMulUnit

/-- The inverse of a multiplicative unit is again multiplicative. -/
theorem units_inv {u : Rˣ} (hu : IsNormMulUnit (u : R)) :
    IsNormMulUnit ((u⁻¹ : Rˣ) : R) := by
  refine ⟨Units.isUnit _, fun x ↦ ?_⟩
  by_cases hu0 : ‖(u : R)‖ = 0
  · have hall (y : R) : ‖y‖ = 0 := by
      have h := hu.norm_mul (((u⁻¹ : Rˣ) : R) * y)
      simpa [← mul_assoc, hu0] using h
    simp [hall]
  · rw [NormedRing.norm_units_inv_of_norm_mul hu0 hu.norm_mul,
      eq_inv_mul_iff_mul_eq₀ hu0]
    simpa [← mul_assoc] using (hu.norm_mul (((u⁻¹ : Rˣ) : R) * x)).symm

end IsNormMulUnit

section CommMonoid

variable {ι A : Type*} [CommMonoid A] [Norm A] [NormOneClass A] {s : Finset ι} {u : ι → A}

namespace IsNormMulUnit

/-- Finite products of multiplicative units are multiplicative units. -/
theorem prod (hu : ∀ i ∈ s, IsNormMulUnit (u i)) : IsNormMulUnit (∏ i ∈ s, u i) :=
  Finset.prod_induction _ IsNormMulUnit (fun _ _ ↦ IsNormMulUnit.mul) isNormMulUnit_one hu

/-- The norm of a finite product of multiplicative units is the product of their norms. -/
theorem norm_prod (hu : ∀ i ∈ s, IsNormMulUnit (u i)) : ‖∏ i ∈ s, u i‖ = ∏ i ∈ s, ‖u i‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i t hi ih =>
      rw [Finset.prod_insert hi, Finset.prod_insert hi,
        (hu i (Finset.mem_insert_self i t)).norm_mul,
        ih fun j hj ↦ hu j (Finset.mem_insert_of_mem hj)]

end IsNormMulUnit

end CommMonoid

/-- In a monoid with multiplicative norm every unit is a multiplicative unit. -/
theorem isNormMulUnit_iff_isUnit [NormMulClass R] (u : R) :
    IsNormMulUnit u ↔ IsUnit u :=
  ⟨IsNormMulUnit.isUnit, fun hu ↦ ⟨hu, fun x ↦ norm_mul u x⟩⟩

/-- Norm-preserving multiplicative equivalences preserve and reflect multiplicative units. -/
theorem _root_.MulEquiv.isNormMulUnit_iff (e : R ≃* S)
    (he : ∀ x, ‖e x‖ = ‖x‖) (u : R) : IsNormMulUnit (e u) ↔ IsNormMulUnit u := by
  have he' (x : S) : ‖e.symm x‖ = ‖x‖ := by simpa using (he (e.symm x)).symm
  constructor
  · intro hu
    refine ⟨by simpa using hu.isUnit.map e.symm.toMonoidHom, fun x ↦ ?_⟩
    rw [← he (u * x), e.map_mul, hu.norm_mul, he, he]
  · intro hu
    refine ⟨hu.isUnit.map e.toMonoidHom, fun x ↦ ?_⟩
    rw [← he' (e u * x), e.symm.map_mul, e.symm_apply_apply, hu.norm_mul, he', he]

end Monoid

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
    refine ⟨u.isUnit, fun x ↦ le_antisymm (norm_mul_le _ _) ?_⟩
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

end TauCeti
