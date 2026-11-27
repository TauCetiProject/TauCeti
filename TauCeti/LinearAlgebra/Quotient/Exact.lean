/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Exact

/-!
# Exact sequences of quotient modules

For an injection `f : M → N` with projective cokernel and a submodule `S` of `M`, this file
provides an abstract linear isomorphism `N / f(S) ≃ (M / S) × (N / f(M))`.
This permits finite projectivity and constant ranks to be transported along injections.
-/

public section

namespace Submodule

variable {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] (p : Submodule R M)

/-- For an injective map with projective cokernel, `N ⧸ p.map f` is noncanonically linearly
isomorphic to `(M ⧸ p) × (N ⧸ LinearMap.range f)`. -/
theorem nonempty_quotient_map_equiv_prod (f : M →ₗ[R] N) (hf : Function.Injective f)
    [Module.Projective R (N ⧸ LinearMap.range f)] :
    Nonempty ((N ⧸ p.map f) ≃ₗ[R] (M ⧸ p) × (N ⧸ LinearMap.range f)) := by
  have h := p.subtype.exact_cokerToCokerComp_factor f
  obtain ⟨e, _, _⟩ := h.exists_linearEquiv_prod_of_projective
    (p.subtype.cokerToCokerComp_injective f hf) (factor_surjective _)
  let e₁ : (N ⧸ p.map f) ≃ₗ[R] N ⧸ LinearMap.range (f ∘ₗ p.subtype) :=
    quotEquivOfEq _ _ (by rw [LinearMap.range_comp, range_subtype])
  let e₂ : (M ⧸ LinearMap.range p.subtype) ≃ₗ[R] M ⧸ p :=
    quotEquivOfEq _ _ (range_subtype p)
  exact ⟨e₁.trans (e.trans (e₂.prodCongr (LinearEquiv.refl _ _)))⟩

end Submodule
