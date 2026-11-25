/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.PerfectPairing.Basic

/-!
# Perfect pairings of products

Multiplication pairs a commutative semiring `R` perfectly with itself, and the orthogonal sum of
two perfect pairings `p : M × N → R` and `q : M' × N' → R`,

```text
⟨(x, x'), (y, y')⟩ = p x y + q x' y',
```

is a perfect pairing of `M × M'` with `N × N'`. Curried, the sum is the product of the two
identifications `M ≃ Dual R N` and `M' ≃ Dual R N'` followed by the identification
`Module.dualProdDualEquivDual` of a product of duals with the dual of the product.

## Main declarations

* `LinearMap.IsPerfPair.mul`: multiplication is a perfect pairing of `R` with itself.
* `LinearMap.compl₁₂_fst_add_compl₁₂_snd_eq_dualProdDualEquivDual_comp_prodMap`: the curried
  orthogonal sum is the product of the two pairings followed by `Module.dualProdDualEquivDual`.
* `LinearMap.flip_compl₁₂_fst_add_compl₁₂_snd`: flipping the orthogonal sum flips each summand.
* `LinearMap.IsPerfPair.compl₁₂_fst_add_compl₁₂_snd`: the orthogonal sum of two perfect pairings
  is a perfect pairing.
-/

public section

open Function Module

namespace LinearMap

variable {R M N M' N' : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N] [AddCommMonoid M'] [Module R M'] [AddCommMonoid N'] [Module R N']

/-- Multiplication is a perfect pairing of a commutative semiring with itself. -/
instance IsPerfPair.mul : (LinearMap.mul R R).IsPerfPair := by
  have h : Bijective (LinearMap.mul R R) :=
    ⟨fun a b h => by simpa using LinearMap.congr_fun h 1, fun f => ⟨f 1, by ext; simp⟩⟩
  exact ⟨h, by rwa [flip_mul]⟩

/-- Curried, the orthogonal sum of two pairings is their product followed by the identification of
a product of duals with the dual of the product. -/
theorem compl₁₂_fst_add_compl₁₂_snd_eq_dualProdDualEquivDual_comp_prodMap
    (p : M →ₗ[R] N →ₗ[R] R) (q : M' →ₗ[R] N' →ₗ[R] R) :
    p.compl₁₂ (fst R M M') (fst R N N') + q.compl₁₂ (snd R M M') (snd R N N') =
      (dualProdDualEquivDual R N N').toLinearMap ∘ₗ p.prodMap q := by
  ext <;> simp

/-- Flipping the orthogonal sum of two pairings flips each summand. -/
theorem flip_compl₁₂_fst_add_compl₁₂_snd (p : M →ₗ[R] N →ₗ[R] R) (q : M' →ₗ[R] N' →ₗ[R] R) :
    (p.compl₁₂ (fst R M M') (fst R N N') + q.compl₁₂ (snd R M M') (snd R N N')).flip =
      p.flip.compl₁₂ (fst R N N') (fst R M M') + q.flip.compl₁₂ (snd R N N') (snd R M M') := by
  ext <;> simp

/-- The orthogonal sum of two perfect pairings is a perfect pairing of the products. -/
instance IsPerfPair.compl₁₂_fst_add_compl₁₂_snd (p : M →ₗ[R] N →ₗ[R] R)
    (q : M' →ₗ[R] N' →ₗ[R] R) [p.IsPerfPair] [q.IsPerfPair] :
    (p.compl₁₂ (fst R M M') (fst R N N') + q.compl₁₂ (snd R M M') (snd R N N')).IsPerfPair := by
  refine ⟨?_, ?_⟩
  · rw [compl₁₂_fst_add_compl₁₂_snd_eq_dualProdDualEquivDual_comp_prodMap, coe_comp, coe_prodMap]
    exact (LinearEquiv.bijective _).comp
      ((IsPerfPair.bijective_left p).prodMap (IsPerfPair.bijective_left q))
  · rw [flip_compl₁₂_fst_add_compl₁₂_snd,
      compl₁₂_fst_add_compl₁₂_snd_eq_dualProdDualEquivDual_comp_prodMap, coe_comp, coe_prodMap]
    exact (LinearEquiv.bijective _).comp
      ((IsPerfPair.bijective_right p).prodMap (IsPerfPair.bijective_right q))

end LinearMap
