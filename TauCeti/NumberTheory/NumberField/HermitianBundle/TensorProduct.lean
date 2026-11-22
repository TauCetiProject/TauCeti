/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.HermitianBundle.Basic

import TauCeti.Analysis.InnerProductSpace.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Projective

/-!
# Tensor products of hermitian vector bundles

For hermitian metrics `h` on `E` and `h'` on `F` over the ring of integers `O_K` of a number
field, the tensor product metric on `E ⊗[𝓞 K] F` has, at every complex embedding `σ`, the form
determined by `h_σ(x ⊗ y, x' ⊗ y') = h_σ(x, x') h'_σ(y, y')` on the complex fibre
`(E ⊗ F)_σ = E_σ ⊗_ℂ F_σ`. This makes `E ⊗ F` a hermitian vector bundle, with
`‖x ⊗ y‖_σ = ‖x‖_σ ‖y‖_σ`. Tensor products of hermitian line bundles give the group law of the
arithmetic Picard group, along which the Arakelov degree is additive.

## Main definitions

* `TauCeti.HermitianMetric.tmul`: the tensor product metric on `E ⊗[𝓞 K] F`.
* `TauCeti.HermitianMetric.IsometryEquiv.tmul`: the tensor product of two isometries.
* `TauCeti.HermitianMetric.tensorComm`, `TauCeti.HermitianMetric.tensorAssoc`: the isometries
  `E ⊗ F ≅ F ⊗ E` and `(E ⊗ F) ⊗ G ≅ E ⊗ (F ⊗ G)`.
* `TauCeti.HermitianMetric.tensorLId`, `TauCeti.HermitianMetric.tensorRId`: the isometries
  `Ō_K ⊗ E ≅ E` and `E ⊗ Ō_K ≅ E`.
* `TauCeti.HermitianBundle.tmul`: the tensor product `E ⊗ F` of hermitian vector bundles, of rank
  `rank E * rank F` (`TauCeti.HermitianBundle.rank_tmul`).

## References

* J.-B. Bost, *Périodes et isogénies des variétés abéliennes sur les corps de nombres*,
  Séminaire Bourbaki 795, Appendice A.2.
* P. Deligne, *Preuves des conjectures de Tate et de Shafarevitch*, Séminaire Bourbaki 616,
  §1.1.
-/

public noncomputable section

open scoped TensorProduct ComplexConjugate

namespace TauCeti

open NumberField NumberField.ComplexEmbedding

namespace HermitianMetric

variable {K : Type*} [Field K]
variable {E F G E' F' : Type*} [AddCommGroup E] [Module (𝓞 K) E] [AddCommGroup F]
  [Module (𝓞 K) F] [AddCommGroup G] [Module (𝓞 K) G] [AddCommGroup E'] [Module (𝓞 K) E']
  [AddCommGroup F'] [Module (𝓞 K) F']
variable (h : HermitianMetric K E) (h' : HermitianMetric K F)

/-- The tensor product form on `E_σ ⊗_ℂ F_σ`, determined by
`(u ⊗ v, u' ⊗ v') ↦ h_σ(u, u') h'_σ(v, v')`. -/
private def fiberTmulForm (σ : K →+* ℂ) :
    (Codomain σ ⊗[𝓞 K] E) ⊗[ℂ] (Codomain σ ⊗[𝓞 K] F) →ₗ⋆[ℂ]
      (Codomain σ ⊗[𝓞 K] E) ⊗[ℂ] (Codomain σ ⊗[𝓞 K] F) →ₗ[ℂ] ℂ :=
  (TensorProduct.map₂ (h.form σ) (h'.form σ)).compr₂ₛₗ (TensorProduct.lid ℂ ℂ).toLinearMap

private theorem fiberTmulForm_tmul_tmul (σ : K →+* ℂ) (u u' : Codomain σ ⊗[𝓞 K] E)
    (v v' : Codomain σ ⊗[𝓞 K] F) :
    fiberTmulForm h h' σ (u ⊗ₜ v) (u' ⊗ₜ v') = h.form σ u u' * h'.form σ v v' := by
  simp [fiberTmulForm]

private theorem conj_fiberTmulForm (σ : K →+* ℂ)
    (a b : (Codomain σ ⊗[𝓞 K] E) ⊗[ℂ] (Codomain σ ⊗[𝓞 K] F)) :
    conj (fiberTmulForm h h' σ a b) = fiberTmulForm h h' σ b a := by
  induction a using TensorProduct.inductionOn with
  | add a₁ a₂ h₁ h₂ => simp only [map_add, LinearMap.add_apply, h₁, h₂]
  | tmul u v =>
    induction b using TensorProduct.inductionOn with
    | add b₁ b₂ h₁ h₂ => simp only [map_add, LinearMap.add_apply, h₁, h₂]
    | tmul u' v' =>
      rw [fiberTmulForm_tmul_tmul, fiberTmulForm_tmul_tmul, map_mul, h.conj_form, h'.conj_form]

/-- The **tensor product** of hermitian metrics on `E` and `F`: the metric on `E ⊗[𝓞 K] F` whose
form at `σ` is the tensor product form on `E_σ ⊗_ℂ F_σ`, determined by
`h_σ(x ⊗ y, x' ⊗ y') = h_σ(x, x') h'_σ(y, y')`. -/
def tmul : HermitianMetric K (E ⊗[𝓞 K] F) where
  form σ := (fiberTmulForm h h' σ ∘ₛₗ (Codomain.tensorProductEquiv σ E F).toLinearMap).compl₂
    (Codomain.tensorProductEquiv σ E F).toLinearMap
  isSymm_form σ := LinearMap.isSymm_def.mpr fun u v ↦ conj_fiberTmulForm h h' σ _ _
  form_self_pos σ u hu := by
    simp only [LinearMap.compl₂_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
    exact apply_self_pos_of_apply_tmul_tmul (H := fiberTmulForm h h' σ)
      (fun a b c d ↦ fiberTmulForm_tmul_tmul h h' σ a c b d) (h.isSymm_form σ) (h'.isSymm_form σ)
      (fun _ ↦ h.form_self_pos σ) (fun _ ↦ h'.form_self_pos σ)
      ((Codomain.tensorProductEquiv σ E F).map_ne_zero_iff.mpr hu)
  form_conjugate_tmul σ t t' := by
    induction t using TensorProduct.inductionOn with
    | add t₁ t₂ h₁ h₂ => simp only [TensorProduct.tmul_add, map_add, LinearMap.add_apply, h₁, h₂]
    | tmul x y =>
      induction t' using TensorProduct.inductionOn with
      | add t₁ t₂ h₁ h₂ => simp only [TensorProduct.tmul_add, map_add, h₁, h₂]
      | tmul x' y' =>
        simp only [LinearMap.compl₂_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
          Codomain.tensorProductEquiv_tmul, fiberTmulForm_tmul_tmul, map_mul,
          h.form_conjugate_tmul, h'.form_conjugate_tmul]

/-- On pure tensors, the tensor product form is `h_σ(x ⊗ y, x' ⊗ y') = h_σ(x, x') h'_σ(y, y')`. -/
@[simp]
theorem tmul_form_tmul_tmul (σ : K →+* ℂ) (x x' : E) (y y' : F) :
    (h.tmul h').form σ (1 ⊗ₜ (x ⊗ₜ y)) (1 ⊗ₜ (x' ⊗ₜ y')) =
      h.form σ (1 ⊗ₜ x) (1 ⊗ₜ x') * h'.form σ (1 ⊗ₜ y) (1 ⊗ₜ y') := by
  simp only [tmul, LinearMap.compl₂_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    Codomain.tensorProductEquiv_tmul, fiberTmulForm_tmul_tmul]

/-- In the tensor product, `‖x ⊗ y‖_σ = ‖x‖_σ ‖y‖_σ`. -/
@[simp]
theorem norm_tmul_tmul (σ : K →+* ℂ) (x : E) (y : F) :
    (h.tmul h').norm σ (1 ⊗ₜ (x ⊗ₜ y)) = h.norm σ (1 ⊗ₜ x) * h'.norm σ (1 ⊗ₜ y) := by
  rw [norm_def, tmul_form_tmul_tmul, h.form_self_eq_norm_sq, h'.form_self_eq_norm_sq,
    ← Complex.ofReal_mul, Complex.ofReal_re, ← mul_pow,
    Real.sqrt_sq (mul_nonneg (h.norm_nonneg _ _) (h'.norm_nonneg _ _))]

/-- In the tensor product, `‖x ⊗ y‖_v = ‖x‖_v ‖y‖_v` at every infinite place `v`. -/
@[simp]
theorem placeNorm_tmul (v : InfinitePlace K) (x : E) (y : F) :
    (h.tmul h').placeNorm v (x ⊗ₜ y) = h.placeNorm v x * h'.placeNorm v y := by
  rw [← InfinitePlace.mk_embedding v]
  simp only [placeNorm_mk, norm_tmul_tmul]

variable {h h'}

/-- The forms of a metric on `E ⊗[𝓞 K] F` and of a metric on `G`, pulled back along a linear map
`f : E ⊗[𝓞 K] F → G`, agree on all of `E ⊗[𝓞 K] F` once they agree on pure tensors. -/
theorem form_tmul_map_eq_of_tmul_tmul {g : HermitianMetric K (E ⊗[𝓞 K] F)}
    {g' : HermitianMetric K G} (f : E ⊗[𝓞 K] F →ₗ[𝓞 K] G) (σ : K →+* ℂ)
    (hf : ∀ (x x' : E) (y y' : F), g'.form σ (1 ⊗ₜ f (x ⊗ₜ y)) (1 ⊗ₜ f (x' ⊗ₜ y')) =
      g.form σ (1 ⊗ₜ (x ⊗ₜ y)) (1 ⊗ₜ (x' ⊗ₜ y')))
    (t t' : E ⊗[𝓞 K] F) :
    g'.form σ (1 ⊗ₜ f t) (1 ⊗ₜ f t') = g.form σ (1 ⊗ₜ t) (1 ⊗ₜ t') := by
  induction t using TensorProduct.inductionOn with
  | add t₁ t₂ h₁ h₂ => simp only [map_add, TensorProduct.tmul_add, LinearMap.add_apply, h₁, h₂]
  | tmul x y =>
    induction t' using TensorProduct.inductionOn with
    | add t₁ t₂ h₁ h₂ => simp only [map_add, TensorProduct.tmul_add, h₁, h₂]
    | tmul x' y' => exact hf x x' y y'

variable (h h')

/-- Rescaling the two factors by `c` and `d` rescales their tensor product by `c + d`. -/
theorem rescale_tmul_rescale (c d : ℝ) :
    (h.rescale c).tmul (h'.rescale d) = (h.tmul h').rescale (c + d) :=
  ext_tmul _ fun σ t t' ↦ form_tmul_map_eq_of_tmul_tmul (g := (h.tmul h').rescale (c + d))
    LinearMap.id σ (fun x x' y y' ↦ by
      simp only [LinearMap.id_apply, tmul_form_tmul_tmul, rescale_form_apply]
      rw [show -2 * (c + d) = -2 * c + -2 * d by ring, Real.exp_add, Complex.ofReal_mul]
      ring) t t'

namespace IsometryEquiv

variable {h h'} {g : HermitianMetric K E'} {g' : HermitianMetric K F'}

/-- The tensor product `e ⊗ e'` of two isometries. -/
def tmul (e : IsometryEquiv h g) (e' : IsometryEquiv h' g') :
    IsometryEquiv (h.tmul h') (g.tmul g') where
  toLinearEquiv := TensorProduct.congr e.toLinearEquiv e'.toLinearEquiv
  form_tmul σ := form_tmul_map_eq_of_tmul_tmul _ σ fun x x' y y' ↦ by
    simp only [LinearEquiv.coe_coe, TensorProduct.congr_tmul, coe_toLinearEquiv,
      tmul_form_tmul_tmul, form_tmul_map]

@[simp]
theorem tmul_apply_tmul (e : IsometryEquiv h g) (e' : IsometryEquiv h' g') (x : E) (y : F) :
    e.tmul e' (x ⊗ₜ y) = e x ⊗ₜ e' y :=
  (rfl)

end IsometryEquiv

/-- The tensor products `E ⊗ F` and `F ⊗ E` are isometric, by swapping the factors. -/
def tensorComm : IsometryEquiv (h.tmul h') (h'.tmul h) where
  toLinearEquiv := TensorProduct.comm (𝓞 K) E F
  form_tmul σ := form_tmul_map_eq_of_tmul_tmul _ σ fun x x' y y' ↦ by
    simp only [LinearEquiv.coe_coe, TensorProduct.comm_tmul, tmul_form_tmul_tmul, mul_comm]

@[simp]
theorem tensorComm_apply_tmul (x : E) (y : F) : tensorComm h h' (x ⊗ₜ y) = y ⊗ₜ x :=
  (rfl)

/-- The tensor products `(E ⊗ F) ⊗ G` and `E ⊗ (F ⊗ G)` are isometric, by reassociating. -/
def tensorAssoc (h'' : HermitianMetric K G) :
    IsometryEquiv ((h.tmul h').tmul h'') (h.tmul (h'.tmul h'')) where
  toLinearEquiv := TensorProduct.assoc (𝓞 K) E F G
  form_tmul σ := form_tmul_map_eq_of_tmul_tmul _ σ fun t t' z z' ↦ by
    -- Reduce the first factor `t ∈ E ⊗ F` to pure tensors as well.
    induction t using TensorProduct.inductionOn with
    | add t₁ t₂ h₁ h₂ =>
      simp only [TensorProduct.add_tmul, map_add, TensorProduct.tmul_add, LinearMap.add_apply,
        h₁, h₂]
    | tmul x y =>
      induction t' using TensorProduct.inductionOn with
      | add t₁ t₂ h₁ h₂ =>
        simp only [TensorProduct.add_tmul, map_add, TensorProduct.tmul_add, h₁, h₂]
      | tmul x' y' =>
        simp only [LinearEquiv.coe_coe, TensorProduct.assoc_tmul, tmul_form_tmul_tmul, mul_assoc]

@[simp]
theorem tensorAssoc_apply_tmul (h'' : HermitianMetric K G) (x : E) (y : F) (z : G) :
    tensorAssoc h h' h'' ((x ⊗ₜ y) ⊗ₜ z) = x ⊗ₜ (y ⊗ₜ z) :=
  (rfl)

section NumberField

variable [NumberField K]

/-- The tensor product `Ō_K ⊗ E` is isometric to `E`, through `a ⊗ x ↦ a • x`. -/
def tensorLId : IsometryEquiv ((trivial K).tmul h) h where
  toLinearEquiv := TensorProduct.lid (𝓞 K) E
  form_tmul σ := form_tmul_map_eq_of_tmul_tmul _ σ fun a b x y ↦ by
    simp only [LinearEquiv.coe_coe, TensorProduct.lid_tmul, tmul_form_tmul_tmul,
      trivial_form_tmul, form_tmul_smul_tmul_smul]

@[simp]
theorem tensorLId_apply_tmul (a : 𝓞 K) (x : E) : tensorLId h (a ⊗ₜ x) = a • x :=
  (rfl)

/-- The tensor product `E ⊗ Ō_K` is isometric to `E`, through `x ⊗ a ↦ a • x`. -/
def tensorRId : IsometryEquiv (h.tmul (trivial K)) h where
  toLinearEquiv := TensorProduct.rid (𝓞 K) E
  form_tmul σ := form_tmul_map_eq_of_tmul_tmul _ σ fun x y a b ↦ by
    simp only [LinearEquiv.coe_coe, TensorProduct.rid_tmul, tmul_form_tmul_tmul,
      trivial_form_tmul, form_tmul_smul_tmul_smul, mul_comm]

@[simp]
theorem tensorRId_apply_tmul (x : E) (a : 𝓞 K) : tensorRId h (x ⊗ₜ a) = a • x :=
  (rfl)

end NumberField

end HermitianMetric

namespace HermitianBundle

universe u v

variable {K : Type u} [Field K]

/-- The **tensor product** `E ⊗ F` of hermitian vector bundles: the module `E ⊗[𝓞 K] F` with the
tensor product metric. -/
def tmul (E F : HermitianBundle.{u, v} K) : HermitianBundle.{u, v} K where
  carrier := E ⊗[𝓞 K] F
  metric := E.metric.tmul F.metric

/-- The rank of a tensor product is the product of the ranks. -/
@[simp]
theorem rank_tmul (E F : HermitianBundle.{u, v} K) : (E.tmul F).rank = E.rank * F.rank := by
  rw [rank_eq_finrank_tensorProduct, rank_eq_finrank_tensorProduct, rank_eq_finrank_tensorProduct,
    ← Module.finrank_tensorProduct]
  exact (TensorProduct.AlgebraTensorModule.distribBaseChange (𝓞 K) K E F).finrank_eq

end HermitianBundle

end TauCeti
