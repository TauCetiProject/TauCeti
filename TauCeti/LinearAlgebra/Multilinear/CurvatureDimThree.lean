/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

/-!
# Trace-free curvature-type tensors in dimension three vanish

Let `T(x, y, z, w)` be a quadrilinear form on a free module of rank `3` which is antisymmetric
in its first pair and in its last pair of arguments, as a Riemann curvature tensor
`Rm(x, y, z, w) = ⟨R(x, y)z, w⟩` is. If its Ricci-type contraction
`∑ᵢ T(eᵢ, y, z, eᵢ)` vanishes for some basis `(eᵢ)`, then `T = 0`.

Applied to the Weyl tensor, which is trace-free and has these antisymmetries, this shows that the
Weyl tensor of a three-dimensional Riemannian manifold vanishes, so that its Riemann curvature is
determined by its Ricci curvature.

The scalars form a commutative ring in which `2` is left regular, that is, multiplication by `2`
is injective. In characteristic `2` the statement fails: `T(x, y, z, w) = x₁ y₁ z₂ w₂` on `𝔽₂³`
is a counterexample.

## Main declarations

* `LinearMap.eq_zero_of_sum_basis_eq_zero_of_card_eq_three`: a quadrilinear form on a module
  with a basis of three elements, antisymmetric in both pairs of arguments and with vanishing
  contraction against that basis, is zero.

## References

* A. L. Besse, *Einstein Manifolds*, Springer (1987), Section 1.G.
-/

public section

namespace LinearMap

variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι]

/-- A quadrilinear form `T` on a module with a basis `(bᵢ)` of three elements which is
antisymmetric in its first and in its last pair of arguments, and whose contraction
`∑ᵢ T(bᵢ, y, z, bᵢ)` vanishes, is zero, provided multiplication by `2` is injective on the
scalars. For an orthonormal basis of an inner product space this contraction is the Ricci
contraction of `T`. -/
theorem eq_zero_of_sum_basis_eq_zero_of_card_eq_three (h2 : IsLeftRegular (2 : R))
    (b : Module.Basis ι R M) (hι : Fintype.card ι = 3) {T : M →ₗ[R] M →ₗ[R] M →ₗ[R] M →ₗ[R] R}
    (h₁ : ∀ x y z w, T x y z w = -T y x z w) (h₂ : ∀ x y z w, T x y z w = -T x y w z)
    (hT : ∀ y z, ∑ i, T (b i) y z (b i) = 0) : T = 0 := by
  replace h2 : ∀ a : R, a + a = 0 → a = 0 := fun a ha ↦
    h2 <| by simpa only [mul_zero, two_mul] using ha
  have hd₁ : ∀ x z w, T x x z w = 0 := fun x z w ↦ h2 _ (by linear_combination h₁ x x z w)
  have hd₂ : ∀ x y z, T x y z z = 0 := fun x y z ↦ h2 _ (by linear_combination h₂ x y z z)
  have hs : ∀ x y, T x y y x = T y x x y := fun x y ↦ by
    linear_combination h₁ x y y x - h₂ y x y x
  -- Reindex the basis by `Fin 3` and expand the contraction into its three terms.
  set e := b.reindex (Fintype.equivFinOfCardEq hι)
  have he : ∀ y z, T (e 0) y z (e 0) + T (e 1) y z (e 1) + T (e 2) y z (e 2) = 0 := by
    intro y z
    rw [← Fin.sum_univ_three (fun i ↦ T (e i) y z (e i)), ← hT y z]
    simp only [e, Module.Basis.reindex_apply]
    exact (Fintype.equivFinOfCardEq hι).symm.sum_comp (fun i ↦ T (b i) y z (b i))
  -- The components `T(eᵢ, eⱼ, eⱼ, eᵢ)` with `i ≠ j`.
  have r₀ := he (e 0) (e 0)
  have r₁ := he (e 1) (e 1)
  have r₂ := he (e 2) (e 2)
  simp only [hd₁] at r₀ r₁ r₂
  have s₀₁ : T (e 0) (e 1) (e 1) (e 0) = 0 := h2 _ <| by
    linear_combination r₀ + r₁ - r₂ + hs (e 0) (e 1) + hs (e 0) (e 2) + hs (e 1) (e 2)
  have s₀₂ : T (e 0) (e 2) (e 2) (e 0) = 0 := h2 _ <| by
    linear_combination r₀ + r₂ - r₁ + hs (e 0) (e 1) + hs (e 0) (e 2) - hs (e 1) (e 2)
  have s₁₂ : T (e 1) (e 2) (e 2) (e 1) = 0 := by linear_combination r₂ - s₀₂
  -- The components `T(eₖ, eᵢ, eⱼ, eₖ)` with `i, j, k` distinct.
  have m₀₁ := he (e 0) (e 1)
  have m₁₀ := he (e 1) (e 0)
  have m₀₂ := he (e 0) (e 2)
  have m₂₀ := he (e 2) (e 0)
  have m₁₂ := he (e 1) (e 2)
  have m₂₁ := he (e 2) (e 1)
  simp only [hd₁, hd₂, zero_add, add_zero] at m₀₁ m₁₀ m₀₂ m₂₀ m₁₂ m₂₁
  -- Every other component is one of these up to the two antisymmetries.
  refine e.ext fun i ↦ e.ext fun j ↦ e.ext fun k ↦ e.ext fun l ↦ ?_
  simp only [LinearMap.zero_apply]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
    first
    | exact hd₁ _ _ _
    | exact hd₂ _ _ _
    | assumption
    | rwa [h₁, neg_eq_zero]
    | rwa [h₂, neg_eq_zero]
    | rwa [h₁, h₂, neg_neg]

end LinearMap
