/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.Prod

/-!
# Composites of intertwining linear maps

A linear map `f : M → N` intertwines endomorphisms `dM` and `dN` when `dN ∘ f = f ∘ dM`. This
file records that intertwining is stable under composition, the step behind the composition law
of cochain maps assembled from maps commuting with differentials. It also records that
precomposition with a retraction of a section is a section of precomposition
(`LinearMap.lcomp_comp_lcomp_eq_id`), that commuting squares `f' ∘ e₁ = e₂ ∘ f` and
`g' ∘ e₁' = e₂' ∘ g` give the commuting square of products
(`LinearMap.prodMap_comp_prodCongr_eq_of_comp_eq`), and that negation commutes with every linear
map (`LinearMap.comp_neg_eq_neg_comp`).
-/

public section

namespace LinearMap

variable {R M N P : Type*} [Semiring R] [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]
  [Module R M] [Module R N] [Module R P]

/-- If `f` intertwines `dM` with `dN` and `g` intertwines `dN` with `dP`, then `g ∘ f`
intertwines `dM` with `dP`. -/
theorem comp_comm_comp {dM : M →ₗ[R] M} {dN : N →ₗ[R] N} {dP : P →ₗ[R] P} {f : M →ₗ[R] N}
    {g : N →ₗ[R] P} (hg : dP ∘ₗ g = g ∘ₗ dN) (hf : dN ∘ₗ f = f ∘ₗ dM) :
    dP ∘ₗ (g ∘ₗ f) = (g ∘ₗ f) ∘ₗ dM := by
  rw [← comp_assoc, hg, comp_assoc, hf, comp_assoc]

/-- Precomposition with a retraction `p` of a section `i` is a section of precomposition with
`i`: `lcomp R N i ∘ₗ lcomp R N p = id`. -/
theorem lcomp_comp_lcomp_eq_id {R M N F : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] [AddCommMonoid F] [Module R F] {i : M →ₗ[R] F}
    {p : F →ₗ[R] M} (hpi : p ∘ₗ i = .id) : lcomp R N i ∘ₗ lcomp R N p = .id := by
  ext x : 1
  simp [lcomp_apply', comp_assoc, hpi]

/-- Commuting squares `f' ∘ e₁ = e₂ ∘ f` and `g' ∘ e₁' = e₂' ∘ g` of linear maps give the
commuting square `(f' × g') ∘ (e₁ × e₁') = (e₂ × e₂') ∘ (f × g)` of their products. -/
theorem prodMap_comp_prodCongr_eq_of_comp_eq {M' N' P P' Q Q' : Type*} [AddCommMonoid M']
    [Module R M'] [AddCommMonoid N'] [Module R N'] [AddCommMonoid P] [Module R P]
    [AddCommMonoid P'] [Module R P'] [AddCommMonoid Q] [Module R Q] [AddCommMonoid Q']
    [Module R Q'] {f : M →ₗ[R] N} {g : M' →ₗ[R] N'} {f' : P →ₗ[R] Q} {g' : P' →ₗ[R] Q'}
    {e₁ : M ≃ₗ[R] P} {e₂ : N ≃ₗ[R] Q} {e₁' : M' ≃ₗ[R] P'} {e₂' : N' ≃ₗ[R] Q'}
    (hf : f' ∘ₗ e₁.toLinearMap = e₂.toLinearMap ∘ₗ f)
    (hg : g' ∘ₗ e₁'.toLinearMap = e₂'.toLinearMap ∘ₗ g) :
    f'.prodMap g' ∘ₗ (e₁.prodCongr e₁').toLinearMap =
      (e₂.prodCongr e₂').toLinearMap ∘ₗ f.prodMap g := by
  rw [LinearEquiv.coe_prodCongr, LinearEquiv.coe_prodCongr, prodMap_comp, prodMap_comp, hf, hg]

/-- Negation of source and target commutes with a linear map: `f ∘ (-1) = (-1) ∘ f`. -/
theorem comp_neg_eq_neg_comp {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) :
    f ∘ₗ (LinearEquiv.neg R).toLinearMap = (LinearEquiv.neg R).toLinearMap ∘ₗ f := by
  ext
  simp

end LinearMap
