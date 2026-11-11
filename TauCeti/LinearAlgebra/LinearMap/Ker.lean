/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Submodule.Ker

/-!
# Kernels in commuting squares

Two commuting squares of linear maps whose horizontal sides are linear isomorphisms and which
share a vertical side paste to a commuting square. In a commuting square `g ∘ e₁ = e₂ ∘ f` whose
source side `e₁` is surjective and whose target side `e₂` is injective, `e₁` carries the kernel
of `f` onto the kernel of `g`.
-/

public section

namespace LinearMap

variable {R : Type*} [Semiring R] {M N M' N' : Type*} [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N] [AddCommMonoid M'] [Module R M'] [AddCommMonoid N'] [Module R N']

/-- Pasting the commuting squares `g ∘ e₁ = e₂ ∘ f` and `k ∘ e₁' = e₂' ∘ g` gives the commuting
square `k ∘ (e₁' ∘ e₁) = (e₂' ∘ e₂) ∘ f`. -/
theorem comp_trans_eq_of_comp_eq {M'' N'' : Type*} [AddCommMonoid M''] [Module R M'']
    [AddCommMonoid N''] [Module R N''] {f : M →ₗ[R] N} {g : M' →ₗ[R] N'} {k : M'' →ₗ[R] N''}
    {e₁ : M ≃ₗ[R] M'} {e₂ : N ≃ₗ[R] N'} {e₁' : M' ≃ₗ[R] M''} {e₂' : N' ≃ₗ[R] N''}
    (h : g ∘ₗ e₁.toLinearMap = e₂.toLinearMap ∘ₗ f)
    (h' : k ∘ₗ e₁'.toLinearMap = e₂'.toLinearMap ∘ₗ g) :
    k ∘ₗ (e₁.trans e₁').toLinearMap = (e₂.trans e₂').toLinearMap ∘ₗ f := by
  rw [LinearEquiv.coe_trans, LinearEquiv.coe_trans, ← comp_assoc, h', comp_assoc, h, comp_assoc]

/-- In a commuting square `g ∘ e₁ = e₂ ∘ f` of linear maps with `e₁` surjective and `e₂`
injective, `e₁` carries the kernel of `f` onto that of `g`. -/
theorem map_ker_eq_ker_of_comp_eq (f : M →ₗ[R] N) {g : M' →ₗ[R] N'} {e₁ : M →ₗ[R] M'}
    {e₂ : N →ₗ[R] N'} (he₁ : Function.Surjective e₁) (he₂ : Function.Injective e₂)
    (h : g ∘ₗ e₁ = e₂ ∘ₗ f) :
    (ker f).map e₁ = ker g := by
  rw [← ker_comp_of_ker_eq_bot f (ker_eq_bot_of_injective he₂), ← h, ker_comp,
    Submodule.map_comap_eq_of_surjective he₁]

end LinearMap
