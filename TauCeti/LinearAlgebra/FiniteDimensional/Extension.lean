/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Injective linear maps from a finite-dimensional space differ by an automorphism

Let `U` be a finite-dimensional vector space over a division ring `K`. Two injective linear maps
`f₁ f₂ : U → V` differ by a linear automorphism of `V`, whatever the dimension of `V`: there is
`e : V ≃ₗ[K] V` with `e ∘ f₁ = f₂` (`TauCeti.exists_linearEquiv_comp_eq_of_injective`). The
automorphism extends the isomorphism `f₂ ∘ f₁⁻¹` from the range of `f₁` onto that of `f₂`
(`Submodule.exists_linearEquiv_restrict_eq`).

For instance the general linear group of `Kⁿ⁺¹` acts transitively on the injective linear maps
`K² → Kⁿ⁺¹`, so every line of the projective space `ℙ(Kⁿ⁺¹)` is the image of a coordinate line
under a projective linear transformation.
-/

public section

namespace TauCeti

variable {K U V : Type*} [DivisionRing K] [AddCommGroup U] [Module K U] [AddCommGroup V]
  [Module K V] [FiniteDimensional K U]

/-- **Injective linear maps from a finite-dimensional space differ by an automorphism.** For
injective linear maps `f₁ f₂ : U → V` from a finite-dimensional space, some linear automorphism
`e` of `V` satisfies `e ∘ f₁ = f₂`. -/
theorem exists_linearEquiv_comp_eq_of_injective {f₁ f₂ : U →ₗ[K] V}
    (hf₁ : Function.Injective f₁) (hf₂ : Function.Injective f₂) :
    ∃ e : V ≃ₗ[K] V, (e : V →ₗ[K] V) ∘ₗ f₁ = f₂ := by
  -- Extend the isomorphism `f₂ ∘ f₁⁻¹` of the ranges to an automorphism of `V`.
  obtain ⟨e, he⟩ := Submodule.exists_linearEquiv_restrict_eq
    ((LinearEquiv.ofInjective f₁ hf₁).symm.trans (LinearEquiv.ofInjective f₂ hf₂))
  refine ⟨e, LinearMap.ext fun u ↦ ?_⟩
  have hs : (LinearEquiv.ofInjective f₁ hf₁).symm ⟨f₁ u, LinearMap.mem_range_self f₁ u⟩ = u :=
    (LinearEquiv.ofInjective f₁ hf₁).symm_apply_eq.2
      (Subtype.ext (LinearEquiv.ofInjective_apply ..).symm)
  simpa [hs, LinearEquiv.ofInjective_apply] using (he ⟨f₁ u, LinearMap.mem_range_self f₁ u⟩).symm

end TauCeti
