/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LinearMap.Defs

/-!
# Composites of intertwining linear maps

A linear map `f : M → N` intertwines endomorphisms `dM` and `dN` when `dN ∘ f = f ∘ dM`. This
file records that intertwining is stable under composition, the step behind the composition law
of cochain maps assembled from maps commuting with differentials.
-/

public section

namespace LinearMap

variable {R M N P : Type*} [Semiring R] [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]
  [Module R M] [Module R N] [Module R P]

/-- If `f` intertwines `dM` with `dN` and `g` intertwines `dN` with `dP`, then `g ∘ f`
intertwines `dM` with `dP`. -/
theorem comp_comm_comp {dM : M →ₗ[R] M} {dN : N →ₗ[R] N} {dP : P →ₗ[R] P} {f : M →ₗ[R] N}
    {g : N →ₗ[R] P} (hg : dP ∘ₗ g = g ∘ₗ dN) (hf : dN ∘ₗ f = f ∘ₗ dM) :
    dP ∘ₗ (g ∘ₗ f) = (g ∘ₗ f) ∘ₗ dM := by
  rw [← comp_assoc, hg, comp_assoc, hf, comp_assoc]

end LinearMap
