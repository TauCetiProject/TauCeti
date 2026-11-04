/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Submodule.Ker

/-!
# Kernels in commuting squares

Consider commuting squares of linear maps whose horizontal sides are linear isomorphisms. Two such
squares sharing a vertical side paste to a commuting square, and in each square the source
isomorphism carries the kernel of one vertical side onto the kernel of the other.
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

/-- In a commuting square `g ∘ e₁ = e₂ ∘ f` with `e₁` and `e₂` linear isomorphisms, `e₁` carries the
kernel of `f` onto that of `g`. -/
theorem map_ker_eq_ker_of_comp_eq (f : M →ₗ[R] N) {g : M' →ₗ[R] N'} (e₁ : M ≃ₗ[R] M')
    (e₂ : N ≃ₗ[R] N') (h : g ∘ₗ e₁.toLinearMap = e₂.toLinearMap ∘ₗ f) :
    (ker f).map e₁.toLinearMap = ker g := by
  ext y
  have hy := LinearMap.congr_fun h (e₁.symm y)
  simp only [coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearEquiv.apply_symm_apply] at hy
  rw [Submodule.mem_map_equiv, mem_ker, mem_ker, ← e₂.map_eq_zero_iff, ← hy]

end LinearMap
