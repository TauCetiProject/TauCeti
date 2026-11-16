/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Submodule.Range

/-!
# Ranges in commuting squares of linear maps

In a commuting square `g ∘ e₁ = e₂ ∘ f` of linear maps whose left side `e₁` is surjective, the
right side `e₂` carries the range of `f` onto the range of `g`. Transporting cokernels along a
commuting square of linear isomorphisms uses this. Without surjectivity, `e₂` still sends the range
of `f` into the range of `g`, so it induces a map of cokernels.
-/

public section

namespace LinearMap

/-- In a commuting square `g ∘ e₁ = e₂ ∘ f` of linear maps with `e₁` surjective, `e₂` carries the
range of `f` onto that of `g`. -/
theorem map_range_eq_range_of_comp_eq
    {R M N M' N' : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    [AddCommMonoid M'] [Module R M'] [AddCommMonoid N'] [Module R N']
    (f : M →ₗ[R] N) {g : M' →ₗ[R] N'} {e₁ : M →ₗ[R] M'} {e₂ : N →ₗ[R] N'}
    (he₁ : Function.Surjective e₁) (h : g ∘ₗ e₁ = e₂ ∘ₗ f) :
    (range f).map e₂ = range g := by
  rw [← range_comp, ← h, range_comp_of_range_eq_top _ (range_eq_top.2 he₁)]

/-- In a commuting square `g ∘ e₁ = e₂ ∘ f` of linear maps, `e₂` sends the range of `f` into the
range of `g`. -/
theorem range_le_comap_range_of_comp_eq
    {R M N M' N' : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    [AddCommMonoid M'] [Module R M'] [AddCommMonoid N'] [Module R N']
    {f : M →ₗ[R] N} {g : M' →ₗ[R] N'} {e₁ : M →ₗ[R] M'} {e₂ : N →ₗ[R] N'}
    (h : g ∘ₗ e₁ = e₂ ∘ₗ f) :
    range f ≤ (range g).comap e₂ :=
  Submodule.map_le_iff_le_comap.1 (by rw [← range_comp, ← h]; exact range_comp_le_range e₁ g)

end LinearMap
