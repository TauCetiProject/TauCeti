/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Exact.Basic

/-!
# Exactness by lifting and cancelling

Let `p : P → Q` be a surjective linear map whose kernel is the image of an injective
`μ : P → P`, and let `f g : P → P` lift `f' g' : Q → Q` along `p`. If `g ∘ f = μ`, `g` commutes
with `μ` and `f' ∘ g' = 0`, then `ker f' = im g'` (`Function.Exact.of_lift_of_comp_eq`). An
element of `ker f'` lifts to some `x` with `f x = μ z`; then `μ x = g (f x) = μ (g z)`, and
cancelling `μ` gives `x = g z`.

This is the step behind the exactness of the reduction of a matrix factorization, where `μ` is
multiplication by a nonzerodivisor.
-/

public section

namespace Function.Exact

variable {A P Q : Type*} [Semiring A] [AddCommMonoid P] [Module A P] [AddCommMonoid Q]
  [Module A Q] {p : P →ₗ[A] Q} {μ f g : P →ₗ[A] P} {f' g' : Q →ₗ[A] Q}

/-- **Lifting and cancelling.** Let `p : P → Q` be surjective with kernel the image of an injective
`μ : P → P`, and let `f g : P → P` lift `f' g' : Q → Q` along `p`. If `g ∘ f = μ`, `g` commutes
with `μ` and `f' ∘ g' = 0`, then `ker f' = im g'`. -/
theorem of_lift_of_comp_eq (hp : Function.Surjective p) (hμ : Function.Injective μ)
    (hμp : Function.Exact μ p) (hf : p ∘ₗ f = f' ∘ₗ p) (hg : p ∘ₗ g = g' ∘ₗ p)
    (hgf : g ∘ₗ f = μ) (hgμ : g ∘ₗ μ = μ ∘ₗ g) (hfg : f' ∘ₗ g' = 0) :
    Function.Exact g' f' := by
  intro y
  refine ⟨fun hy ↦ ?_, ?_⟩
  · obtain ⟨x, rfl⟩ := hp y
    obtain ⟨z, hz⟩ := (hμp (f x)).mp (by rw [← LinearMap.comp_apply, hf, LinearMap.comp_apply, hy])
    have hx : x = g z := hμ <|
      calc μ x = g (f x) := by rw [← hgf, LinearMap.comp_apply]
        _ = μ (g z) := by rw [← hz, ← LinearMap.comp_apply, hgμ, LinearMap.comp_apply]
    exact ⟨p z, by simpa [hx] using (LinearMap.congr_fun hg z).symm⟩
  · rintro ⟨z, rfl⟩
    rw [← LinearMap.comp_apply, hfg, LinearMap.zero_apply]

end Function.Exact
