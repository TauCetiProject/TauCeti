/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Quotient.Basic
public import TauCeti.LinearAlgebra.Exact

-- Proof-only: the cokernel map has no exposed defining equation.
import all TauCeti.LinearAlgebra.Exact

/-!
# Exact sequences of quotient modules

For an injection `f : M → N` and a submodule `S` of `M`, the quotient `N / f(S)` is an
extension of `N / f(M)` by `M / S`. If the cokernel of `f` is projective, this sequence splits.
This permits finite projectivity and constant ranks to be transported along injections.
-/

public section

namespace Submodule

variable {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] (p : Submodule R M)

/-- For an injective map with projective cokernel, quotienting its target by the image of a
submodule gives a split extension of the source quotient by the cokernel. -/
theorem nonempty_quotient_map_equiv_prod (f : M →ₗ[R] N) (hf : Function.Injective f)
    [Module.Projective R (N ⧸ LinearMap.range f)] :
    Nonempty ((N ⧸ p.map f) ≃ₗ[R] (M ⧸ p) × (N ⧸ LinearMap.range f)) := by
  have hinj : Function.Injective (p.subtype.cokerToCokerComp f) := by
    rw [LinearMap.cokerToCokerComp]
    apply (mapQ_injective_iff _ _ _ _).2
    rw [LinearMap.range_comp, comap_map_eq, LinearMap.ker_eq_bot.mpr hf, sup_bot_eq]
  have h := p.subtype.exact_cokerToCokerComp_factor f
  obtain ⟨e, _, _⟩ := h.exists_linearEquiv_prod_of_projective hinj (factor_surjective _)
  let e₁ : (N ⧸ p.map f) ≃ₗ[R] N ⧸ LinearMap.range (f ∘ₗ p.subtype) :=
    quotEquivOfEq _ _ (by rw [LinearMap.range_comp, range_subtype])
  let e₂ : (M ⧸ LinearMap.range p.subtype) ≃ₗ[R] M ⧸ p :=
    quotEquivOfEq _ _ (range_subtype p)
  exact ⟨e₁.trans (e.trans (e₂.prodCongr (LinearEquiv.refl _ _)))⟩

end Submodule
