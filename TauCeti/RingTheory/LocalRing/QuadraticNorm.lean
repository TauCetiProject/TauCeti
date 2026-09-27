/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.LocalRing.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Integral unit values of a quadratic norm form

Over a local ring, an integral value `x² - a y²` that is a unit has a unit coordinate.
If the second coordinate is used, the radicand is also a unit. Dividing by that coordinate
gives one of two normal forms,
`u² (1 - a t²)` or `-a u² (1 - a t²)`. This is the integral part of the local norm
calculation used to compute the quadratic norm index in residue characteristic two.

The assertion concerns integral witnesses. It does not assert that every field norm of a unit
has an integral witness in the basis `1, √a`.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §63A.
-/

public section

namespace TauCeti

section

variable {R : Type*} [Ring R] [IsLocalRing R]

/-- An integral unit value of `x² - a y²` has a unit coordinate; if the second coordinate
is used, the radicand is also a unit. -/
theorem isUnit_or_isUnit_and_isUnit_of_isUnit_sq_sub_mul_sq {a x y : R}
    (h : IsUnit (x ^ 2 - a * y ^ 2)) : IsUnit x ∨ (IsUnit a ∧ IsUnit y) := by
  have h' : IsUnit (x ^ 2 + -(a * y ^ 2)) := by simpa only [sub_eq_add_neg] using h
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add h' with hx | hy
  · exact Or.inl ((isUnit_pow_iff (by decide : 2 ≠ 0)).mp hx)
  · have hay : IsUnit (a * y ^ 2) := by simpa using hy
    exact Or.inr ⟨@isUnit_of_mul_isUnit_left R _ inferInstance a (y ^ 2) hay,
      (isUnit_pow_iff (by decide : 2 ≠ 0)).mp
        (@isUnit_of_mul_isUnit_right R _ inferInstance a (y ^ 2) hay)⟩

end

variable {R : Type*} [CommRing R] [IsLocalRing R]

/-- An integral unit is represented by the quadratic norm form exactly
when it has one of the two unit normal forms `u² (1 - a t²)` and
`-a u² (1 - a t²)`. -/
theorem exists_eq_sq_sub_mul_sq_iff_exists_unit_normal_form {a b : R} (hb : IsUnit b) :
    (∃ x y : R, b = x ^ 2 - a * y ^ 2) ↔
      (∃ (u : Rˣ) (t : R), b = (u : R) ^ 2 * (1 - a * t ^ 2)) ∨
        (∃ (u : Rˣ) (t : R), b = -a * (u : R) ^ 2 * (1 - a * t ^ 2)) := by
  constructor
  · rintro ⟨x, y, h⟩
    rcases isUnit_or_isUnit_and_isUnit_of_isUnit_sq_sub_mul_sq (h ▸ hb) with hx | ⟨ha, hy⟩
    · obtain ⟨u, rfl⟩ := hx
      refine Or.inl ⟨u, (u⁻¹ : Rˣ) * y, ?_⟩
      have hu : (u : R) * (u⁻¹ : Rˣ) = 1 := by simp
      have hu2 : (u : R) ^ 2 * (u⁻¹ : Rˣ) ^ 2 = 1 := by
        rw [← mul_pow, hu, one_pow]
      rw [h]
      linear_combination (a * y ^ 2) * hu2
    · obtain ⟨u, rfl⟩ := hy
      obtain ⟨v, rfl⟩ := ha
      refine Or.inr ⟨u, -((v⁻¹ : Rˣ) * (u⁻¹ : Rˣ) * x), ?_⟩
      have hu : (u : R) * (u⁻¹ : Rˣ) = 1 := by simp
      have hv : (v : R) * (v⁻¹ : Rˣ) = 1 := by simp
      have hvu : (v : R) ^ 2 * (u : R) ^ 2 * (v⁻¹ : Rˣ) ^ 2 *
          (u⁻¹ : Rˣ) ^ 2 = 1 := by
        calc
          _ = ((v : R) * (v⁻¹ : Rˣ)) ^ 2 * ((u : R) * (u⁻¹ : Rˣ)) ^ 2 := by ring
          _ = 1 := by rw [hv, hu]; ring
      rw [h]
      linear_combination -(x ^ 2) * hvu
  · rintro (⟨u, t, h⟩ | ⟨u, t, h⟩)
    · refine ⟨u, (u : R) * t, ?_⟩
      rw [h]
      ring
    · refine ⟨a * (u : R) * t, u, ?_⟩
      rw [h]
      ring

end TauCeti
