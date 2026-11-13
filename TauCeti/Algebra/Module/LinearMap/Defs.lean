/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LinearMap.Defs

/-!
# Composites of semilinear maps

Forgetting scalar compatibility commutes with composition of semilinear maps
(`LinearMap.toAddMonoidHom_comp`). Composites of injective or surjective semilinear maps are
injective or surjective (`LinearMap.injective_comp`, `LinearMap.surjective_comp`); these restate
`Function.Injective.comp` and `Function.Surjective.comp` for the coercion of `g.comp f`, so that
they can be passed where a proof about exactly this coercion is expected.
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

/-- A composite of injective semilinear maps is injective, stated for the coercion of `g.comp f`. -/
theorem injective_comp {g : N →ₛₗ[τ] P} {f : M →ₛₗ[σ] N} (hg : Function.Injective g)
    (hf : Function.Injective f) : Function.Injective (g.comp f : M →ₛₗ[υ] P) :=
  hg.comp hf

/-- A composite of surjective semilinear maps is surjective, stated for the coercion of
`g.comp f`. -/
theorem surjective_comp {g : N →ₛₗ[τ] P} {f : M →ₛₗ[σ] N} (hg : Function.Surjective g)
    (hf : Function.Surjective f) : Function.Surjective (g.comp f : M →ₛₗ[υ] P) :=
  hg.comp hf

end LinearMap
