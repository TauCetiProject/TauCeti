/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearMap

/-!
# Full faithfulness from biduality

When evaluation identifies a module `N` with its double `E`-dual (possibly over a commuting scalar
semiring `S` acting on `E`), precomposition `LinearMap.lcomp` is bijective on morphisms into `N`
(`TauCeti.bijective_lcomp_of_evalEquiv`). Specializing `S` to `R` gives the corresponding result
whenever `LinearMap.applyₗ` is bijective (`TauCeti.bijective_lcomp_of_bijective_applyₗ`). Neither
injectivity nor finiteness is required.

## Main results

* `TauCeti.bijective_lcomp_of_evalEquiv`: precomposition `(M →ₗ[R] N) → ((N →ₗ[R] E) →ₗ[S]
  (M →ₗ[R] E))` is bijective whenever evaluation identifies `N` with `(N →ₗ[R] E) →ₗ[S] E`.
* `TauCeti.bijective_lcomp_of_bijective_applyₗ`: precomposition `(M →ₗ[R] N) → ((N →ₗ[R] E) →ₗ[R]
  (M →ₗ[R] E))` is bijective whenever `LinearMap.applyₗ` is bijective on `N`.
-/

public section

noncomputable section

universe u v w z

namespace TauCeti

open LinearMap

section Semiring

variable {R : Type u} [Semiring R] {E : Type v} [AddCommMonoid E] [Module R E]

/-- If evaluation identifies `N` with its double `E`-dual for a commuting scalar action `S` on `E`,
then precomposition `(M →ₗ[R] N) → ((N →ₗ[R] E) →ₗ[S] (M →ₗ[R] E))` is bijective for every
`R`-module `M`. No injectivity, finiteness, or commutativity hypothesis is needed. -/
theorem bijective_lcomp_of_evalEquiv (S : Type*) [Semiring S] [Module S E]
    [SMulCommClass R S E] [SMulCommClass S R E] {M : Type w} [AddCommMonoid M] [Module R M]
    {N : Type z} [AddCommMonoid N] [Module R N]
    (e : N ≃ₗ[R] ((N →ₗ[R] E) →ₗ[S] E)) (he : ∀ (n : N) (φ : N →ₗ[R] E), e n φ = φ n) :
    Function.Bijective (fun f : M →ₗ[R] N ↦ f.lcomp S E) := by
  constructor
  · intro f₁ f₂ hf
    refine LinearMap.ext fun m ↦ e.injective (LinearMap.ext fun φ ↦ ?_)
    rw [he, he]
    exact LinearMap.congr_fun (LinearMap.congr_fun hf φ) m
  · intro g
    refine ⟨e.symm.toLinearMap.comp g.flip, ?_⟩
    ext φ m
    have h := congrArg (fun ψ : (N →ₗ[R] E) →ₗ[S] E ↦ ψ φ) (e.apply_symm_apply (g.flip m))
    simpa only [lcomp_apply, comp_apply, LinearEquiv.coe_coe, he, flip_apply] using h

end Semiring

section CommSemiring

variable {R : Type u} [CommSemiring R] {E : Type v} [AddCommMonoid E] [Module R E]

/-- If evaluation `N → Hom_R(Hom_R(N, E), E)` is bijective, then precomposition
`(M →ₗ[R] N) → ((N →ₗ[R] E) →ₗ[R] (M →ₗ[R] E))` is bijective for every `R`-module `M`. -/
theorem bijective_lcomp_of_bijective_applyₗ {M : Type w} [AddCommMonoid M] [Module R M]
    {N : Type z} [AddCommMonoid N] [Module R N]
    (hN : Function.Bijective (applyₗ : N →ₗ[R] (N →ₗ[R] E) →ₗ[R] E)) :
    Function.Bijective (fun f : M →ₗ[R] N ↦ f.lcomp R E) :=
  bijective_lcomp_of_evalEquiv R (LinearEquiv.ofBijective applyₗ hN) fun _ _ ↦ rfl

end CommSemiring

end TauCeti
