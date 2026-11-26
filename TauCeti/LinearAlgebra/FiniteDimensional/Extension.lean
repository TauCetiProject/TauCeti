/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Projection

/-!
# Injective linear maps into a finite-dimensional space differ by an automorphism

Let `V` be a finite-dimensional vector space over a division ring `K`. Two injective linear maps
`f₁ f₂ : U → V` differ by a linear automorphism of `V`: there is `e : V ≃ₗ[K] V` with
`e ∘ f₁ = f₂` (`LinearMap.exists_linearEquiv_comp_eq_of_injective`). The automorphism carries the
range of `f₁` onto that of `f₂` by `f₂ ∘ f₁⁻¹`, and a complement of the first range onto a
complement of the second, the two complements having the same dimension `dim V - dim U`.

For instance the general linear group of `Kⁿ⁺¹` acts transitively on the injective linear maps
`K² → Kⁿ⁺¹`, so every line of the projective space `ℙ(Kⁿ⁺¹)` is the image of a coordinate line
under a projective linear transformation.
-/

public section

namespace LinearMap

variable {K U V : Type*} [DivisionRing K] [AddCommGroup U] [Module K U] [AddCommGroup V]
  [Module K V] [FiniteDimensional K V]

/-- **Injective linear maps into a finite-dimensional space differ by an automorphism.** For
injective linear maps `f₁ f₂ : U → V` into a finite-dimensional space, some linear automorphism
`e` of `V` satisfies `e ∘ f₁ = f₂`. -/
theorem exists_linearEquiv_comp_eq_of_injective {f₁ f₂ : U →ₗ[K] V}
    (hf₁ : Function.Injective f₁) (hf₂ : Function.Injective f₂) :
    ∃ e : V ≃ₗ[K] V, (e : V →ₗ[K] V) ∘ₗ f₁ = f₂ := by
  obtain ⟨C₁, h₁⟩ := Submodule.exists_isCompl (range f₁)
  obtain ⟨C₂, h₂⟩ := Submodule.exists_isCompl (range f₂)
  -- The ranges are isomorphic to `U`, so the complements have the same dimension.
  let r : range f₁ ≃ₗ[K] range f₂ :=
    (LinearEquiv.ofInjective f₁ hf₁).symm.trans (LinearEquiv.ofInjective f₂ hf₂)
  have hC : Module.finrank K C₁ = Module.finrank K C₂ := by
    have := Submodule.finrank_add_eq_of_isCompl h₁
    have := Submodule.finrank_add_eq_of_isCompl h₂
    have := r.finrank_eq
    omega
  refine ⟨((Submodule.prodEquivOfIsCompl _ _ h₁).symm.trans
    ((r.prodCongr (LinearEquiv.ofFinrankEq C₁ C₂ hC)))).trans
      (Submodule.prodEquivOfIsCompl _ _ h₂), LinearMap.ext fun u ↦ ?_⟩
  have hu : (Submodule.prodEquivOfIsCompl _ _ h₁).symm (f₁ u) =
      ((⟨f₁ u, mem_range_self f₁ u⟩ : range f₁), (0 : C₁)) :=
    Submodule.prodEquivOfIsCompl_symm_apply_left _ _ h₁ ⟨f₁ u, mem_range_self f₁ u⟩
  have hr : r ⟨f₁ u, mem_range_self f₁ u⟩ = ⟨f₂ u, mem_range_self f₂ u⟩ := by
    have hs : (LinearEquiv.ofInjective f₁ hf₁).symm ⟨f₁ u, mem_range_self f₁ u⟩ = u :=
      (LinearEquiv.ofInjective f₁ hf₁).symm_apply_eq.2 rfl
    simp only [r, LinearEquiv.trans_apply, hs]
    rfl
  simp [hu, hr]

end LinearMap
