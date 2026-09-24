/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LinearMap.Defs

/-!
# Additive maps underlying semilinear maps

Forgetting scalar compatibility commutes with composition of semilinear maps.
-/

public section

namespace LinearMap

variable {R S T M N P : Type*} [Semiring R] [Semiring S] [Semiring T]
  [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]
  [Module R M] [Module S N] [Module T P]
  {σ : R →+* S} {τ : S →+* T} {υ : R →+* T} [RingHomCompTriple σ τ υ]

/-- The additive map underlying a composite is the composite of the underlying additive maps. -/
@[simp] theorem toAddMonoidHom_comp (g : N →ₛₗ[τ] P) (f : M →ₛₗ[σ] N) :
    (g.comp f : M →ₛₗ[υ] P).toAddMonoidHom =
      g.toAddMonoidHom.comp f.toAddMonoidHom := rfl

end LinearMap
