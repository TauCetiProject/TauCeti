/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.RingTheory.Ideal.Maps

/-!
# Annihilators in exact sequences

The product of annihilating ideals of the outer terms of an exact sequence annihilates the
middle term. Neither finiteness nor commutativity is required.
-/

public section

namespace LinearMap

variable {R M N P : Type*} [Semiring R]
  [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]
  [Module R M] [Module R N] [Module R P]

/-- The product of annihilating ideals of the outer terms of an exact sequence annihilates
its middle term. The maps need not be injective or surjective. -/
theorem mul_le_annihilator_of_exact (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (h : Function.Exact f g) {I J : Ideal R}
    (hI : I ≤ Module.annihilator R M) (hJ : J ≤ Module.annihilator R P) :
    I * J ≤ Module.annihilator R N := by
  refine Ideal.mul_le.mpr fun a ha b hb ↦ Module.mem_annihilator.mpr fun x ↦ ?_
  obtain ⟨y, hy⟩ := (h (b • x)).mp (by rw [map_smul, Module.mem_annihilator.mp (hJ hb)])
  rw [mul_smul, ← hy, ← map_smul, Module.mem_annihilator.mp (hI ha), map_zero]

end LinearMap
