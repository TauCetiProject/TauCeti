/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Unimodular
public import Mathlib.RingTheory.LocalRing.Basic

/-!
# Unimodular elements: unit rescaling and coordinate vectors over a local ring

Complements to `Mathlib.LinearAlgebra.Unimodular`. Unimodularity of an element `v` of an
`R`-module (some linear functional takes the value `1` at `v`) is preserved by multiplication by a
unit, so each unit multiple of a unimodular vector can be used as a generator when constructing
projective orbit morphisms. A coordinate vector `v : ι → R` with a unit coordinate is unimodular.
Over a local ring the converse holds for finitely many coordinates: `v` is unimodular exactly when
one of its coordinates is a unit. This is the form in which homogeneous coordinates of points of
projective schemes over a local ring are normalised.

## Main results

* `TauCeti.Module.isUnimodular_units_smul`: multiplication by a unit preserves unimodularity.
* `TauCeti.Module.isUnimodular_of_isUnit_apply`: a coordinate vector with a unit coordinate is
  unimodular.
* `TauCeti.Module.isUnimodular_iff_exists_isUnit`: over a local ring, a coordinate vector with
  finitely many coordinates is unimodular if and only if one of its coordinates is a unit.
-/

public section

namespace TauCeti.Module

section Semiring

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

/-- Multiplication by a unit preserves unimodularity. -/
theorem isUnimodular_units_smul (c : Rˣ) {m : M} (hm : Module.IsUnimodular R m) :
    Module.IsUnimodular R (c • m) := by
  obtain ⟨f, hf⟩ := Module.isUnimodular_iff.mp hm
  apply Module.isUnimodular_iff.mpr
  refine ⟨(LinearMap.mulRight R (↑c⁻¹ : R)).comp f, ?_⟩
  simp [LinearMap.mulRight_apply, Units.smul_def, hf]

/-- A coordinate vector one of whose coordinates is a unit is unimodular. -/
theorem isUnimodular_of_isUnit_apply {ι : Type*} {v : ι → R} {i : ι} (hi : IsUnit (v i)) :
    Module.IsUnimodular R v :=
  Module.isUnimodular_of_apply_eq_one
    (f := (LinearMap.mulRight R (↑hi.unit⁻¹ : R)).comp (LinearMap.proj i)) (by simp)

end Semiring

/-- Over a local ring, a coordinate vector with finitely many coordinates is unimodular if and only
if one of its coordinates is a unit. -/
theorem isUnimodular_iff_exists_isUnit {R ι : Type*} [CommSemiring R] [IsLocalRing R] [Finite ι]
    {v : ι → R} : Module.IsUnimodular R v ↔ ∃ i, IsUnit (v i) := by
  refine ⟨fun h ↦ ?_, fun ⟨i, hi⟩ ↦ isUnimodular_of_isUnit_apply hi⟩
  obtain ⟨f, hf⟩ := Module.isUnimodular_iff.mp h
  classical
  have := Fintype.ofFinite ι
  -- `f v = ∑ᵢ vᵢ f(eᵢ)` is a unit, so one of its summands is
  rw [LinearMap.pi_apply_eq_sum_univ] at hf
  obtain ⟨i, -, hi⟩ := IsLocalRing.exists_of_isUnit_sum (hf ▸ isUnit_one)
  exact ⟨i, isUnit_of_mul_isUnit_left hi⟩

end TauCeti.Module
