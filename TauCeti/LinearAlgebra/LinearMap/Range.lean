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
commuting square of linear isomorphisms uses this. In any commuting square `g ∘ i = i' ∘ f`, the
map `g` sends the range of `i` into the range of `i'`, so it induces a map of cokernels.
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

/-- A family `v` mapped into `range f` by `f.rangeRestrict` and included back by the subtype of
`range f` is its image `f ∘ v`. -/
theorem subtype_comp_rangeRestrict_comp
    {R R₂ M M₂ ι : Type*} [Semiring R] [Semiring R₂] {τ₁₂ : R →+* R₂} [RingHomSurjective τ₁₂]
    [AddCommMonoid M] [Module R M] [AddCommMonoid M₂] [Module R₂ M₂]
    (f : M →ₛₗ[τ₁₂] M₂) (v : ι → M) :
    (range f).subtype ∘ (f.rangeRestrict ∘ v) = f ∘ v := by
  rw [← Function.comp_assoc, ← coe_comp, subtype_comp_rangeRestrict]

/-- In a commuting square `g ∘ i = i' ∘ f` of linear maps, `g` sends the range of `i` into the
range of `i'`. -/
theorem range_le_comap_range_of_comp_eq
    {R M N M' N' : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    [AddCommMonoid M'] [Module R M'] [AddCommMonoid N'] [Module R N']
    {f : M →ₗ[R] M'} {g : N →ₗ[R] N'} {i : M →ₗ[R] N} {i' : M' →ₗ[R] N'}
    (h : g ∘ₗ i = i' ∘ₗ f) :
    range i ≤ (range i').comap g := by
  rintro _ ⟨x, rfl⟩
  exact ⟨f x, (LinearMap.congr_fun h x).symm⟩

end LinearMap
