/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Exact.Basic
import Mathlib.Algebra.GroupWithZero.Action.Units

/-!
# Rescaling linear maps by a unit

Multiplying a linear map over a commutative semiring by a unit `c` changes neither its kernel nor
its range. Hence it preserves bijectivity (`LinearMap.bijective_smul_iff`) and exactness in either
position (`LinearMap.exact_smul_left_iff`, `LinearMap.exact_smul_right_iff`). Over a field, every
nonzero scalar is a unit, for instance the signs `(-1) ^ m` relating the principal symbol of a
formal adjoint to the adjoint of a principal symbol.
-/

public section

open Function

namespace LinearMap

variable {R M N P : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]
  [Module R M] [Module R N] [Module R P] {c : R}

/-- Multiplying a linear map by a unit does not change its bijectivity. -/
theorem bijective_smul_iff (hc : IsUnit c) (f : M →ₗ[R] N) : Bijective (c • f) ↔ Bijective f := by
  rw [coe_smul]
  exact Bijective.of_comp_iff' hc.smul_bijective f

/-- Multiplying the second map of a pair by a unit does not change exactness. -/
theorem exact_smul_right_iff (hc : IsUnit c) (f : M →ₗ[R] N) (g : N →ₗ[R] P) :
    Exact f (c • g) ↔ Exact f g := by
  simp only [Exact, coe_smul, Pi.smul_apply, hc.smul_eq_zero]

/-- Multiplying the first map of a pair by a unit does not change exactness. -/
theorem exact_smul_left_iff (hc : IsUnit c) (f : M →ₗ[R] N) (g : N →ₗ[R] P) :
    Exact (c • f) g ↔ Exact f g := by
  obtain ⟨u, rfl⟩ := hc
  have h : Set.range ((u : R) • f) = Set.range f := by
    ext y
    refine ⟨fun ⟨x, hx⟩ ↦ ⟨(u : R) • x, by simpa using hx⟩,
      fun ⟨x, hx⟩ ↦ ⟨((u⁻¹ : Rˣ) : R) • x, ?_⟩⟩
    simp [← hx, smul_smul]
  simp only [Exact, h]

end LinearMap
