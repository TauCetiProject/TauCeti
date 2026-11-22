/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.HermitianBundle.Basic

import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Orthogonal sums of hermitian vector bundles

For hermitian metrics `h` on `E` and `h'` on `F` over the ring of integers `O_K` of a number
field, the orthogonal sum metric on `E × F` has, at every complex embedding `σ`, the form
`h_σ(u₁, v₁) + h'_σ(u₂, v₂)` on the complex fibre `(E × F)_σ = E_σ × F_σ`. This makes `E ⊕ F` a
hermitian vector bundle, in which `E` and `F` are orthogonal and `‖(x, y)‖_σ² = ‖x‖_σ² + ‖y‖_σ²`.
The Hodge line of a product of abelian varieties is computed from the orthogonal sum of their
invariant differentials, and the Arakelov degree is additive along orthogonal sums.

## Main definitions

* `TauCeti.HermitianMetric.prod`: the orthogonal sum metric on `E × F`.
* `TauCeti.HermitianMetric.IsometryEquiv.prod`: the orthogonal sum of two isometries.
* `TauCeti.HermitianMetric.IsometryEquiv.prodComm`: `E ⊕ F ≅ F ⊕ E`.
* `TauCeti.HermitianBundle.prod`: the orthogonal sum `E ⊕ F` of hermitian vector bundles, of rank
  `rank E + rank F` (`TauCeti.HermitianBundle.rank_prod`).

## References

* J.-B. Bost, *Périodes et isogénies des variétés abéliennes sur les corps de nombres*,
  Séminaire Bourbaki 795, Appendice A.2–A.3.
* L. Szpiro, *Degrés, intersections, hauteurs*, Astérisque 127, §1.2.
-/

public noncomputable section

open scoped TensorProduct ComplexConjugate ComplexOrder

namespace TauCeti

open NumberField NumberField.ComplexEmbedding

namespace HermitianMetric

variable {K : Type*} [Field K]
variable {E F E' F' : Type*} [AddCommGroup E] [Module (𝓞 K) E] [AddCommGroup F] [Module (𝓞 K) F]
  [AddCommGroup E'] [Module (𝓞 K) E'] [AddCommGroup F'] [Module (𝓞 K) F']
variable (h : HermitianMetric K E) (h' : HermitianMetric K F)

/-- The **orthogonal sum** of hermitian metrics on `E` and `F`: the metric on `E × F` whose form at
`σ` is `h_σ(u₁, v₁) + h'_σ(u₂, v₂)` on the complex fibre `E_σ × F_σ`. -/
def prod : HermitianMetric K (E × F) where
  form σ :=
    (h.form σ ∘ₛₗ (LinearMap.fst ℂ _ _ ∘ₗ (Codomain.prodEquiv σ E F).toLinearMap)).compl₂
        (LinearMap.fst ℂ _ _ ∘ₗ (Codomain.prodEquiv σ E F).toLinearMap) +
      (h'.form σ ∘ₛₗ (LinearMap.snd ℂ _ _ ∘ₗ (Codomain.prodEquiv σ E F).toLinearMap)).compl₂
        (LinearMap.snd ℂ _ _ ∘ₗ (Codomain.prodEquiv σ E F).toLinearMap)
  isSymm_form σ := LinearMap.isSymm_def.mpr fun u v ↦ by
    simp only [LinearMap.add_apply, LinearMap.compl₂_apply, LinearMap.comp_apply, map_add,
      h.conj_form, h'.conj_form]
  form_self_pos σ u hu := by
    have hne : Codomain.prodEquiv σ E F u ≠ 0 := (LinearEquiv.map_ne_zero_iff _).mpr hu
    simp only [LinearMap.add_apply, LinearMap.compl₂_apply, LinearMap.comp_apply,
      LinearEquiv.coe_coe, LinearMap.fst_apply, LinearMap.snd_apply]
    rcases eq_or_ne (Codomain.prodEquiv σ E F u).1 0 with h₁ | h₁
    · have h₂ : (Codomain.prodEquiv σ E F u).2 ≠ 0 := fun h₂ ↦ hne (Prod.ext h₁ h₂)
      exact add_pos_of_nonneg_of_pos (h.form_self_nonneg σ _) (h'.form_self_pos σ h₂)
    · exact add_pos_of_pos_of_nonneg (h.form_self_pos σ h₁) (h'.form_self_nonneg σ _)
  form_conjugate_tmul σ x y := by
    simp only [LinearMap.add_apply, LinearMap.compl₂_apply, LinearMap.comp_apply,
      LinearEquiv.coe_coe, Codomain.prodEquiv_tmul, LinearMap.fst_apply, LinearMap.snd_apply,
      map_add, h.form_conjugate_tmul, h'.form_conjugate_tmul]

/-- The form of the orthogonal sum at `σ`, through the identification `(E × F)_σ = E_σ × F_σ`. -/
theorem prod_form_apply (σ : K →+* ℂ) (u v : Codomain σ ⊗[𝓞 K] (E × F)) :
    (h.prod h').form σ u v =
      h.form σ (Codomain.prodEquiv σ E F u).1 (Codomain.prodEquiv σ E F v).1 +
        h'.form σ (Codomain.prodEquiv σ E F u).2 (Codomain.prodEquiv σ E F v).2 :=
  (rfl)

/-- On vectors of `E × F`, the orthogonal sum form is `h_σ(x₁, y₁) + h'_σ(x₂, y₂)`. -/
@[simp]
theorem prod_form_tmul (σ : K →+* ℂ) (x y : E × F) :
    (h.prod h').form σ (1 ⊗ₜ x) (1 ⊗ₜ y) =
      h.form σ (1 ⊗ₜ x.1) (1 ⊗ₜ y.1) + h'.form σ (1 ⊗ₜ x.2) (1 ⊗ₜ y.2) := by
  rw [prod_form_apply, Codomain.prodEquiv_tmul, Codomain.prodEquiv_tmul]

/-- In the orthogonal sum, `‖(x, y)‖_σ² = ‖x‖_σ² + ‖y‖_σ²`. -/
theorem norm_prod_tmul_sq (σ : K →+* ℂ) (x : E × F) :
    (h.prod h').norm σ (1 ⊗ₜ x) ^ 2 = h.norm σ (1 ⊗ₜ x.1) ^ 2 + h'.norm σ (1 ⊗ₜ x.2) ^ 2 := by
  simp only [norm_sq, prod_form_tmul, Complex.add_re]

/-- In the orthogonal sum, `‖(x, y)‖_v² = ‖x‖_v² + ‖y‖_v²` at every infinite place `v`. -/
theorem placeNorm_prod_sq (v : InfinitePlace K) (x : E × F) :
    (h.prod h').placeNorm v x ^ 2 = h.placeNorm v x.1 ^ 2 + h'.placeNorm v x.2 ^ 2 := by
  rw [← InfinitePlace.mk_embedding v]
  simp only [placeNorm_mk, norm_prod_tmul_sq]

/-- Rescaling commutes with orthogonal sums. -/
theorem rescale_prod (c : ℝ) : (h.prod h').rescale c = (h.rescale c).prod (h'.rescale c) :=
  ext_tmul _ fun σ x y ↦ by simp only [rescale_form_apply, prod_form_tmul, mul_add]

namespace IsometryEquiv

variable {h h'} {g : HermitianMetric K E'} {g' : HermitianMetric K F'}

/-- The orthogonal sum `e × e'` of two isometries. -/
def prod (e : IsometryEquiv h g) (e' : IsometryEquiv h' g') :
    IsometryEquiv (h.prod h') (g.prod g') where
  toLinearEquiv := e.toLinearEquiv.prodCongr e'.toLinearEquiv
  form_tmul σ x y := by
    simp only [prod_form_tmul, LinearEquiv.prodCongr_apply,
      coe_toLinearEquiv, form_tmul_map]

@[simp]
theorem prod_apply (e : IsometryEquiv h g) (e' : IsometryEquiv h' g') (x : E × F) :
    e.prod e' x = (e x.1, e' x.2) :=
  (rfl)

variable (h h') in
/-- The orthogonal sums `E ⊕ F` and `F ⊕ E` are isometric, by swapping the factors. -/
def prodComm : IsometryEquiv (h.prod h') (h'.prod h) where
  toLinearEquiv := LinearEquiv.prodComm (𝓞 K) E F
  form_tmul σ x y := by
    simp only [prod_form_tmul, LinearEquiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap, add_comm]

@[simp]
theorem prodComm_apply (x : E × F) : prodComm h h' x = (x.2, x.1) :=
  (rfl)

end IsometryEquiv

end HermitianMetric

namespace HermitianBundle

universe u v

variable {K : Type u} [Field K]

/-- The **orthogonal sum** `E ⊕ F` of hermitian vector bundles: the module `E × F` with the
orthogonal sum metric. -/
def prod (E F : HermitianBundle.{u, v} K) : HermitianBundle.{u, v} K where
  carrier := E × F
  metric := E.metric.prod F.metric

/-- The rank of an orthogonal sum is the sum of the ranks. -/
@[simp]
theorem rank_prod (E F : HermitianBundle.{u, v} K) : (E.prod F).rank = E.rank + F.rank := by
  rw [rank_eq_finrank_tensorProduct, rank_eq_finrank_tensorProduct, rank_eq_finrank_tensorProduct,
    ← Module.finrank_prod]
  exact (TensorProduct.prodRight (𝓞 K) K K E F).finrank_eq

end HermitianBundle

end TauCeti
