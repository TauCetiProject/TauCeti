/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Unimodular
public import Mathlib.RingTheory.LocalRing.Basic

/-!
# Unimodular elements: scalar extension, unit rescaling, and local coordinates

Complements to `Mathlib.LinearAlgebra.Unimodular`. Unimodularity of an element `v` of an
`R`-module (some linear functional takes the value `1` at `v`) is invariant under multiplication by
units, so each unit multiple of a unimodular vector can be used as a generator when constructing
projective orbit morphisms. Extending scalars preserves unimodularity, including along maps to
noncommutative algebras. A coordinate vector `v : ι → R` with a unit coordinate is unimodular.
Over a directly finite local semiring the converse holds for finitely many coordinates: `v` is
unimodular exactly when one of its coordinates is a unit. In particular this applies to local
commutative rings, where it normalizes homogeneous coordinates of points of projective schemes.

## Main results

* `Units.isUnimodular_smul_iff`: unit rescaling leaves unimodularity unchanged.
* `Module.IsUnimodular.one_tmul`: scalar extension preserves a unimodular vector.
* `IsUnit.isUnimodular_pi`: a coordinate vector with a unit coordinate is unimodular.
* `TauCeti.Module.isUnimodular_iff_exists_isUnit`: over a directly finite local semiring, a vector
  with finitely many coordinates is unimodular if and only if one of its coordinates is a unit.
-/

public section

open scoped TensorProduct

namespace Module.IsUnimodular

/-- Extending scalars preserves a unimodular vector. No flatness or commutativity of the target
algebra is needed. -/
theorem one_tmul {R S M : Type*} [CommSemiring R] [Semiring S]
    [Algebra R S] [AddCommMonoid M] [Module R M] {m : M}
    (hm : Module.IsUnimodular R m) : Module.IsUnimodular S (1 ⊗ₜ[R] m : S ⊗[R] M) := by
  obtain ⟨φ, hφ⟩ := Module.isUnimodular_iff.mp hm
  exact Module.isUnimodular_of_apply_eq_one
    (f := (TensorProduct.AlgebraTensorModule.rid R S S).toLinearMap.comp (φ.baseChange S))
    (by simp [hφ])

end Module.IsUnimodular

section Semiring

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

/-- Unit rescaling leaves unimodularity unchanged. -/
@[simp]
theorem Units.isUnimodular_smul_iff (c : Rˣ) {m : M} :
    Module.IsUnimodular R (c • m) ↔ Module.IsUnimodular R m := by
  have forward (c : Rˣ) {m : M} (hm : Module.IsUnimodular R m) :
      Module.IsUnimodular R (c • m) := by
    obtain ⟨f, hf⟩ := Module.isUnimodular_iff.mp hm
    exact Module.isUnimodular_of_apply_eq_one
      (f := (LinearMap.mulRight R (↑c⁻¹ : R)).comp f) (by
        simp [LinearMap.mulRight_apply, Units.smul_def, hf])
  exact ⟨fun h ↦ by simpa using forward c⁻¹ h, forward c⟩

/-- A coordinate vector with a unit coordinate is unimodular. -/
theorem IsUnit.isUnimodular_pi {ι : Type*} {v : ι → R} {i : ι} (hi : IsUnit (v i)) :
    Module.IsUnimodular R v :=
  Module.isUnimodular_of_apply_eq_one
    (f := (LinearMap.mulRight R (↑hi.unit⁻¹ : R)).comp (LinearMap.proj i)) (by simp)

end Semiring

namespace TauCeti.Module

/-- Over a directly finite local semiring, a vector with finitely many coordinates is unimodular
if and only if one of its coordinates is a unit. -/
theorem isUnimodular_iff_exists_isUnit {R ι : Type*} [Semiring R] [IsLocalRing R]
    [IsDedekindFiniteMonoid R] [Finite ι]
    {v : ι → R} : Module.IsUnimodular R v ↔ ∃ i, IsUnit (v i) := by
  refine ⟨fun h ↦ ?_, fun ⟨i, hi⟩ ↦ hi.isUnimodular_pi⟩
  obtain ⟨f, hf⟩ := Module.isUnimodular_iff.mp h
  classical
  have := Fintype.ofFinite ι
  -- `f v = ∑ᵢ vᵢ f(eᵢ)` is a unit, so one of its summands is.
  rw [LinearMap.pi_apply_eq_sum_univ] at hf
  obtain ⟨i, -, hi⟩ := IsLocalRing.exists_of_isUnit_sum (hf ▸ isUnit_one)
  exact ⟨i, isUnit_of_mul_isUnit_left hi⟩

end TauCeti.Module
